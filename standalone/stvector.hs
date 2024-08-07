#!/usr/bin/env stack
-- stack --resolver lts-20.20 script

-- from https://byorgey.github.io/blog/posts/2024/06/21/cpih-product-divisors.html
-- factoring with unboxed arrays

import Control.Monad (forM_, when)
import Data.Array.ST (newListArray, readArray, runSTUArray, writeArray)
import Data.Array.Unboxed (UArray)

maxN = 100

-- creates an array with the smallest factor of each number
-- using a sieve
smallest :: UArray Int Int -- unboxed array
smallest = runSTUArray $ do
  a <- newListArray (2, maxN) [2 ..] -- initialize with contents=index
  forM_ [2 .. maxN] $ \k -> do
    k' <- readArray a k
    when (k == k') $ do -- prime, as wasn't overwritten by the sieve
      forM_ [k * k, k * (k + 1) .. maxN] $ \n -> do -- all relevant multiples - k^2 is the minimum relevant, or would have a smaller factor
        cur <- readArray a n
        writeArray a n (min cur k)
  return a

-- >>> smallest
-- array (2,100) [(2,2),(3,3),(4,2),(5,5),(6,2),(7,7),(8,2),(9,3),(10,2),(11,11),(12,2),(13,13),(14,2),(15,3),(16,2),(17,17),(18,2),(19,19),(20,2),(21,3),(22,2),(23,23),(24,2),(25,5),(26,2),(27,3),(28,2),(29,29),(30,2),(31,31),(32,2),(33,3),(34,2),(35,5),(36,2),(37,37),(38,2),(39,3),(40,2),(41,41),(42,2),(43,43),(44,2),(45,3),(46,2),(47,47),(48,2),(49,7),(50,2),(51,3),(52,2),(53,53),(54,2),(55,5),(56,2),(57,3),(58,2),(59,59),(60,2),(61,61),(62,2),(63,3),(64,2),(65,5),(66,2),(67,67),(68,2),(69,3),(70,2),(71,71),(72,2),(73,73),(74,2),(75,3),(76,2),(77,7),(78,2),(79,79),(80,2),(81,3),(82,2),(83,83),(84,2),(85,5),(86,2),(87,3),(88,2),(89,89),(90,2),(91,7),(92,2),(93,3),(94,2),(95,5),(96,2),(97,97),(98,2),(99,3),(100,2)]
