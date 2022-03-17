module Main where

import Control.Concurrent (getNumCapabilities, setNumCapabilities)
import Control.Concurrent.STM
  ( STM,
    TVar,
    atomically,
    newTVar,
    newTVarIO,
    readTVar,
    readTVarIO,
    writeTVar,
  )
import Control.Monad (forM_, when)
import Control.Monad.State
  ( MonadState (..),
    State,
    evalState,
  )
import Data.List (intercalate, intersperse)
import qualified Data.PQueue.Prio.Min as Q
import qualified Data.Sequence as S
import Data.Traversable (for)
import Data.Tuple (swap)
import Data.Vector
  ( Vector,
    (!),
    (//),
  )
import qualified Data.Vector as V
import GHC.Stats (elapsed_ns, getRTSStats)
import System.Environment (getArgs)
import System.Random (StdGen, getStdGen, uniformR)
import Text.Printf (printf)

type RandState = State StdGen

type Vertex = Int

type Cost = Int

type Graph = Vector [Edge] -- "incidence list" representation

type Queue = Q.MinPQueue

data Edge = Edge Vertex Vertex Cost
  deriving (Eq)

instance Show Edge where
  show (Edge s t w) = printf "%6d %6d %6d" s t w

-- | "vanilla" implementation, parallelizes neither the outer `loop` nor the inner `visitNext`
-- Only used for outlining the algorithm / verifying that impure versions of the
-- algorithm produce the same results as this one.
dijkstra :: Graph -> Vertex -> Vector Cost
dijkstra graph src =
  -- initialize dists to +inf except at i=source vertex, which has dist 0
  let n = length graph
      initDists = V.replicate n (maxBound :: Cost) // [(src, 0)] :: Vector Cost
      initQueue = Q.singleton 0 src :: Queue Cost Vertex
   in loop initQueue initDists
  where
    loop :: Queue Cost Vertex -> Vector Cost -> Vector Cost
    loop queue dists
      | Q.null queue =
        dists
      | -- base case: queue is empty, we're done
        otherwise =
        let (d, u) = peek queue
         in if d <= dists ! u
              then
                let (queue', dists') = visitNext queue -- "inner loop"
                 in loop queue' dists'
              else loop (Q.deleteMin queue) dists
      where
        relax :: Edge -> (Vertex, Cost)
        relax (Edge u v c) = (v, c + dists ! u)
        visitNext :: Queue Cost Vertex -> (Queue Cost Vertex, Vector Cost)
        visitNext q =
          let ((d, node), q') = pop q
              dists' = dists // updates
              updates = [(v, c) | (v, c) <- relax <$> adj node, c < dists ! v]
              q'' = q' `Q.union` Q.fromList [(c, v) | (v, c) <- updates]
           in (q'', dists')

    adj v = graph V.! v
    pop q = Q.deleteFindMin q
    peek q = Q.findMin q

-- | same as vanilla dijkstra above, but within the STM monad.
-- also just for templating / sanity before rewriting in IO
dijkstraSTM :: Graph -> Vertex -> STM (Vector (TVar Cost))
dijkstraSTM graph src = do
  -- initialize dists to +inf except at i=source vertex, which has dist 0
  let n = length graph
  initQueue <- newTVar $ Q.singleton 0 src
  initDists <- mapM newTVar $ V.replicate n (maxBound :: Cost) // [(src, 0)]
  loop initQueue initDists
  where
    loop ::
      TVar (Queue Cost Vertex) ->
      Vector (TVar Cost) ->
      STM (Vector (TVar Cost))
    loop queue dists = do
      q <- readTVar queue
      if Q.null q
        then pure dists -- base case: queue is empty, we're done
        else do
          visitNext queue dists
          loop queue dists
      where
        visitNext :: TVar (Queue Cost Vertex) -> Vector (TVar Cost) -> STM ()
        visitNext queue dists = do
          q <- readTVar queue
          let ((d, u), q') = pop q
          writeTVar queue q'
          d' <- readTVar $ dists ! u
          when (d < d') $ forM_ (adj u) relax
          where
            relax :: Edge -> STM ()
            relax (Edge u v c) = do
              old <- readTVar $ dists ! v
              alt <- readTVar $ dists ! u
              when (alt + c < old) $ do
                q <- readTVar queue -- only touches the TVar (Queue) when necessary
                writeTVar (dists ! v) (alt + c)
                writeTVar queue (q `Q.union` Q.singleton (alt + c) v)

    adj v = graph V.! v
    pop q = Q.deleteFindMin q
    pop_ q = Q.deleteMin q
    peek q = Q.findMin q

-- | Implementation parallelized at the "outer loop" of the algorithm;
-- This is done by modifying the algorithm so that instead of a queue containing
-- vertices we "visit" by relaxing its incident edges, we keep a queue of edges which we
-- relax `nThreads` at a time.
-- The upshot is that we should almost always be able to put every single thread to work, the
-- downside is that the queue has O(|E|) entries instead of O(|V|), and
-- duplicate/stale entries are probably more common.
-- NOTE: results suggest that the trade-off isn't really worth it either for
-- dense or sparser graphs -- Might be worth trying but with a proper
-- decrease-key queue?
dijkstraIO' :: Graph -> Vertex -> Int -> IO (Vector Cost)
dijkstraIO' graph src nThreads = do
  initQueue <- newTVarIO $ Q.fromList [(0, e) | e <- adj src]
  initDists <-
    mapM newTVarIO $ V.replicate (length graph) (maxBound :: Cost) // [(src, 0)]
  tdists <- loop initQueue initDists
  for tdists readTVarIO
  where
    loop ::
      TVar (Queue Cost Edge) -> Vector (TVar Cost) -> IO (Vector (TVar Cost))
    loop queue dists = do
      q <- readTVarIO queue
      if Q.null q
        then pure dists -- base case: queue is empty, we're done
        else visitNext queue dists >> loop queue dists
      where
        visitNext :: TVar (Queue Cost Edge) -> Vector (TVar Cost) -> IO ()
        visitNext queue dists = do
          q <- readTVarIO queue
          let (edges, q') = popN nThreads q -- each thread can try to relax an edge, even if it's already been relaxed
          atomically $ writeTVar queue q'
          forM_ edges relax
          where
            relax :: (Cost, Edge) -> IO ()
            relax (c, Edge u v w) = do
              cur <- readTVarIO $ dists ! v -- shortest known path to reach this edge's dest
              alt <- readTVarIO $ dists ! u -- shortest known path to reach this edge's src
              let stale = alt < c -- we've found a better path to `u` since inserting (so this edge was duplicated in the queue)
                  improves = alt + w < cur
              when (not stale && improves) $ do
                atomically $ writeTVar (dists ! v) (alt + w)
                atomically $ do
                  q <- readTVar queue -- note: only logs a read of the TVar (Queue) when we plan to update it, which should help minimize rollbacks
                  writeTVar
                    queue
                    (q `Q.union` Q.fromList [(alt + w, e) | e <- adj v])

    adj v = graph V.! v
    pop q = Q.deleteFindMin q
    pop_ q = Q.deleteMin q
    popN n q = Q.splitAt n q
    peek q = Q.findMin q

-- | same as dijkstraSTM but in IO monad
-- parallelizes the innermost part of the algorithm, so is limited by the
-- average outdegree of the vertices.
dijkstraIO :: Graph -> Vertex -> IO (Vector Cost)
dijkstraIO graph src = do
  let fringe = (0, src) : [(w, v) | (Edge u v w) <- adj src]
  initQueue <- newTVarIO $ Q.fromList fringe -- Q.singleton 0 src
  initDists <-
    mapM newTVarIO $ V.replicate (length graph) (maxBound :: Cost) // (swap <$> fringe) -- ((src, 0) : [(v, w) | (Edge u v w) <- adj src]) -- [(src, 0)]
  tdists <- loop initQueue initDists
  for tdists readTVarIO
  where
    loop ::
      TVar (Queue Cost Vertex) -> Vector (TVar Cost) -> IO (Vector (TVar Cost))
    loop queue dists = do
      q <- readTVarIO queue
      if Q.null q
        then pure dists -- base case: queue is empty, we're done
        else visitNext queue dists >> loop queue dists
      where
        visitNext :: TVar (Queue Cost Vertex) -> Vector (TVar Cost) -> IO ()
        visitNext queue dists = do
          q <- readTVarIO queue
          let ((d, u), q') = pop q
          atomically $ writeTVar queue q'
          d' <- readTVarIO $ dists ! u -- dist to src
          when (d <= d') $ forM_ (adj u) relax
          where
            relax :: Edge -> IO ()
            relax (Edge u v c) = do
              old <- readTVarIO $ dists ! v
              alt <- readTVarIO $ dists ! u
              when (alt + c < old) $ do
                q <- readTVarIO queue -- note: only logs a read of the TVar (Queue) when we plan to update it,
                -- which should help minimize rollbacks
                atomically $ writeTVar (dists ! v) (alt + c)
                atomically $ writeTVar queue (q `Q.union` Q.singleton (alt + c) v)

    adj v = graph V.! v
    pop q = Q.deleteFindMin q
    pop_ q = Q.deleteMin q
    peek q = Q.findMin q


readGraph :: FilePath -> IO Graph
readGraph infile = do
  contents <- lines <$> readFile infile
  let n = read (head . words . head $ contents) :: Int -- first line is |V| and |E|
  let edges =
        V.fromList
          [ ( read u :: Int,
              Edge (read u :: Vertex) (read v :: Vertex) (read w :: Vertex)
            )
            | [u, v, w] <- words <$> tail contents
          ]
      graph =
        V.accumulate (flip (:)) (V.fromList (replicate n [])) edges :: Graph
  return graph

distanceRange :: (Int, Int)
distanceRange = (10, 99)

-- | Erdos-Renyi graph construction of a graph with |V|=n, and average out-degree=k.
randomGraphER :: Int -> Int -> IO Graph
randomGraphER n k = do
  gen <- getStdGen
  let p :: Double
      p = fromIntegral k / fromIntegral (n -1)
      edges = V.fromList [(v, Edge v u w) | Just (v, u, w) <- randomEdges n p `evalState` gen]
      graph = V.accumulate (flip (:)) (V.fromList (replicate n [])) edges
  pure graph
  where
    randomEdges :: Int -> Double -> RandState [Maybe (Int, Int, Int)]
    randomEdges n p =
      concat <$> do
        for [0 .. n - 1] $ \src -> do
          let dests = [v | v <- [1 .. n -1], v /= src]
          for dests $ \dest -> do
            r <- state . uniformR $ (0 :: Double, 1 :: Double)
            if r <= p
              then do
                distance <- state . uniformR $ (10, 99)
                pure $ Just (src, dest, distance)
              else pure Nothing

writeGraphER :: Int -> Int -> IO ()
writeGraphER n k = do
  g <- randomGraphER n k
  let edges = map show (concat $ V.toList g)
      header = show (length g) ++ " " ++ show (length edges)
      output = unlines (header : edges)
      outfile = "N" ++ show n ++ "k" ++ show k ++ ".graph"
  writeFile outfile output


writeGraph :: Graph -> FilePath -> IO ()
writeGraph g outfile = do
  let edges = map show (concat $ V.toList g)
      header = show (length g) ++ " " ++ show (length edges)
      output = unlines (header : edges)
  writeFile outfile output

main :: IO ()
main = do
  (fname : alg : _) <- getArgs
  if alg == "0"
    then benchmarkDijkstra fname
    else benchmarkDijkstra' fname

benchmarkDijkstra graphFile = do
  graph <- readGraph graphFile
  let nVertices = length graph
      nEdges = length $ concat (V.toList graph)
      meanDeg = (fromIntegral nVertices / fromIntegral nEdges) :: Double
      outfile = graphFile ++ ".inner_parallel.results"
  writeFile outfile "nThreads,time\n"
  maxThreads <- getNumCapabilities
  forM_ (1:[8,16 .. maxThreads]) $ \nThreads -> do
    setNumCapabilities nThreads
    -- printf "NTHREADS: %8d \n" nThreads
    -- printf "GRAPH: |V|:%d, |E|:%d, mean degree:%4.4f\n" nVertices nEdges meanDeg
    -- time 5 runs across the first few non-dead-end vertices
    forM_  [src | src <- [0 .. nVertices - 1], not (null $ graph ! src)] $ \src -> do
      t0 <- elapsed_ns <$> getRTSStats
      dijkstraIO graph src
      t1 <- elapsed_ns <$> getRTSStats
      let elapsed = fromIntegral (t1 - t0) / 10 ^ 9 :: Double
      appendFile outfile $ show nThreads ++ "," ++ show elapsed ++ "\n"

benchmarkDijkstra' graphFile = do
  graph <- readGraph graphFile
  let nVertices = length graph
      nEdges = length $ concat (V.toList graph)
      meanDeg = (fromIntegral nEdges / fromIntegral nVertices) :: Double
      outfile = graphFile ++ ".outer_parallel.results"
  writeFile outfile "nThreads,time\n"
  maxThreads <- getNumCapabilities
  forM_ (1:[8,16 .. maxThreads]) $ \nThreads -> do
    -- printf "NTHREADS: %8d \n" nThreads
    -- printf "GRAPH: |V|:%d, |E|:%d, mean degree:%4.4f\n" nVertices nEdges meanDeg
    -- time 5 runs across the first few non-dead-end vertices
    forM_ [src | src <- [0 .. nVertices - 1], not (null $ graph ! src)] $ \src -> do
      -- "parallelized outer" (edge-based queue)
      t0 <- elapsed_ns <$> getRTSStats
      dijkstraIO' graph src nThreads
      t1 <- elapsed_ns <$> getRTSStats
      let elapsed = fromIntegral (t1 - t0) / 10 ^ 9 :: Double
      -- putStrLn $ "time elapsed: " ++ show elapsed
      appendFile outfile $ show nThreads ++ "," ++ show elapsed ++ "\n"
