#!/usr/bin/env stack
-- stack --resolver lts-20.20 script

-- from https://research.chalmers.se/publication/517894/file/517894_Fulltext.pdf

import Control.Applicative
import Data.Foldable (foldl', foldr')
import Data.Function (on)
import Data.List (nubBy)
import Data.List qualified as L
import GHC.Generics
import Test.QuickCheck

-- code under test
data BST k v = Leaf | Branch (BST k v) k v (BST k v)
  deriving (Eq, Show, Generic)

find :: Ord k => k -> BST k v -> Maybe v
find k Leaf = Nothing
find k (Branch ltree ck v rtree)
  | ck == k = Just v
  | k < ck = find k ltree
  | otherwise = find k rtree

nil :: BST k v
nil = Leaf

-- trivial implementation, doesn't try to balance the tree
insert :: Ord k => k -> v -> BST k v -> BST k v
insert k v Leaf = Branch nil k v nil
insert k v (Branch ltree ck cv rtree)
  | k == ck = Branch ltree k v rtree
  | k < ck = Branch (insert k v ltree) ck cv rtree
  | otherwise = Branch ltree ck cv (insert k v rtree)

-- broken implementation who allows duplicate keys
-- insert :: Ord k => k -> v -> BST k v -> BST k v
-- insert k v Leaf = Branch nil k v nil
-- insert k v (Branch ltree ck cv rtree)
--   | k <= ck = Branch (insert k v ltree) ck cv rtree
--   | otherwise = Branch ltree ck cv (insert k v rtree)

delete :: Ord k => k -> BST k v -> BST k v
delete k Leaf = Leaf
delete k (Branch ltree ck cv rtree)
  | k == ck = ltree `union` rtree
  | k < ck = Branch (delete k ltree) ck cv rtree
  | otherwise = Branch ltree ck cv (delete k rtree)

union :: Ord k => BST k v -> BST k v -> BST k v
union t1 t2 = foldr' (uncurry insert) t2 (toList t1) -- left biased

toList :: BST k v -> [(k, v)]
toList Leaf = []
toList (Branch ltree ck cv rtree) = toList ltree <> [(ck, cv)] <> toList rtree

keys :: BST k v -> [k]
keys t = fst <$> toList t

-- quickcheck  stuff

instance (Ord k, Arbitrary k, Arbitrary v) => Arbitrary (BST k v) where
  arbitrary = do
    kvs :: [(k, v)] <- arbitrary
    return $ foldr (uncurry insert) nil kvs
  shrink = filter valid . genericShrink

-- fix types for testing
type Key = Int

type Val = Int

type Tree = BST Key Val

-- tree validity test for quickcheck
-- quadratic but no assumptions on tree structure
valid :: Ord a => BST a v -> Bool
valid Leaf = True
valid (Branch l k v r) =
  valid l
    && valid r
    && all (< k) (keys l)
    && all (> k) (keys r)

validT :: Tree -> Bool -- restrict type so inference saves me from typing each property
validT = valid

prop_NilValid = validT (nil :: Tree)

prop_InsertValid k v t = validT (insert k v t)

prop_DeleteValid k t = validT (delete k t)

prop_UnionValid t t0 = validT (t `union` t0)

prop_ArbitraryValid = validT

-- test shrink validity
prop_ShrinkValid_bad t = all validT (shrink t)

-- same as above, but with a precondition to prevent shrinking once shrink fails
prop_ShrinkValid t = validT t ==> all validT (shrink t)

-- postconditions

prop_InsertPost :: Key -> Val -> Tree -> Key -> Property
prop_InsertPost k v t k0 = find k0 (insert k v t) === if k == k0 then Just v else find k0 t

prop_DeletePost :: Key -> Tree -> Property
prop_DeletePost k t = find k (delete k t) === Nothing

prop_UnionPost :: Tree -> Tree -> Key -> Property
prop_UnionPost t t' k = find k (t `union` t') === (find k t <|> find k t') -- works if left biased

prop_FindPostPresent :: Key -> Val -> Tree -> Property
prop_FindPostPresent k v t = find k (insert k v t) === Just v

prop_FindPostAbsent :: Key -> Tree -> Property
prop_FindPostAbsent k t = find k (delete k t) === Nothing

-- implies the last 2, but stronger
prop_InsertDeleteComplete :: Key -> Tree -> Property
prop_InsertDeleteComplete k t = case find k t of
  Nothing -> t === delete k t
  Just v -> t === insert k v t

-- metamorphic - A metamorphic property tests a single function by making
-- (usually) two related calls, and checking the expected relationship between
-- the two results

-- define tree equivalence
(=~) :: Tree -> Tree -> Property
t1 =~ t2 = toList t1 === toList t2

(==~) :: Tree -> Tree -> Bool
t1 ==~ t2 = toList t1 == toList t2

prop_InsertInsert :: (Key, Val) -> (Key, Val) -> Tree -> Property
prop_InsertInsert (k, v) (k', v') t = insert k v (insert k' v' t) =~ if k == k' then insert k v t else insert k' v' (insert k v t)

prop_InsertInsertWeak (k, v) (k', v') t = k /= k' ==> insert k v (insert k' v' t) =~ insert k' v' (insert k v t) -- condition on different keys needed because insert order matters

prop_InsertDelete (k, v) k' t = insert k v (delete k' t) =~ if k == k' then insert k v t else delete k' (insert k v t)

prop_InsertUnion (k, v) t t' = insert k v (t `union` t') =~ (insert k v t `union` t')

-- preservation of equivalence
-- the naive test is useless as randomly generated trees will almost never be equivalent
prop_InsertPreservesEquivNaive k v t t' = toList t == toList t' ==> insert k v t =~ insert k v t'

-- to properly test i need to generate couples of equivalent trees
data Equivs k v = BST k v :~: BST k v deriving (Show)

instance (Arbitrary k, Arbitrary v, Ord k, Eq v) => Arbitrary (Equivs k v) where
  arbitrary = do
    kvs <- nubBy ((==) `on` fst) <$> arbitrary
    kvs0 <- shuffle kvs
    return (tree kvs :~: tree kvs0)
    where
      tree = foldr (uncurry insert) nil
  shrink (t1 :~: t2) = [t' :~: t'' | t' <- shrink t1, t'' <- shrink t2, toList t' == toList t''] -- super inefficient, but have few ideas how to do it better

prop_InsertPreservesEquiv k v (t :~: t') = insert k v t =~ insert k v t'

prop_DeletePreservesEquiv k (t :~: t') = delete k t =~ delete k t'

prop_UnionPreservesEquiv (t1 :~: t1') (t2 :~: t2') = union t1 t2 =~ union t1' t2'

prop_FindPreservesEquiv :: Key -> Equivs Key Val -> Property
prop_FindPreservesEquiv k (t :~: t') = find k t === find k t'

prop_Equivs (t :~: t') = t =~ t'

prop_ShrinkEquivs (t :~: t') = t ==~ t' ==> all (\(t :~: t') -> t ==~ t') (shrink (t :~: t'))

-- inductive testing - the following 2 completely define union...
prop_UnionNil1 :: Tree -> Property
prop_UnionNil1 t = union nil t === t

prop_UnionInsert t t' (k, v) = union (insert k v t) t' =~ insert k v (t `union` t')

-- ... except prop_UnionInsert  assumes every tree can be trconstructed by insertions (except equivalence)
-- we need to prove that
insertions :: Tree -> [(Key, Val)]
insertions Leaf = []
insertions (Branch l k v r) = (k, v) : insertions l ++ insertions r

prop_InsertComplete t = t === foldl' (flip $ uncurry insert) nil (insertions t)

-- line abowe woud be enough if we didn't generate all our trees by insertions
-- let's extend t others
prop_InsertCompleteForDelete k t = prop_InsertComplete (delete k t)

prop_InsertCompleteForUnion t t' = prop_InsertComplete (t `union` t')

-- Model-based Properties
-- equivalence of list operations and tree operations
prop_NilModel = toList (nil :: Tree) === []

prop_InsertModel k v t = toList (insert k v t) === L.insert (k, v) (deleteKey k $ toList t)

prop_DeleteModel k t = toList (delete k t) === deleteKey k (toList t)

prop_UnionModel :: Tree -> Tree -> Property
prop_UnionModel t t' = toList (t `union` t') === L.sort (L.unionBy ((==) `on` fst) (toList t) (toList t'))

prop_FindModel :: Key -> Tree -> Property
prop_FindModel k t = find k t === L.lookup k (toList t)

deleteKey :: Key -> [(Key, Val)] -> [(Key, Val)]
deleteKey k = filter ((/= k) . fst)

main :: IO ()
main = do
  quickCheck prop_ArbitraryValid
  quickCheck prop_NilValid
  quickCheck prop_InsertValid
  quickCheck prop_DeleteValid
  quickCheck prop_UnionValid
  -- test shrinker (default one failed!)
  quickCheck prop_ShrinkValid -- commented out because they're slow. uncomment to perform a full test
  -- postconditions
  quickCheck prop_InsertPost
  quickCheck prop_DeletePost
  quickCheck prop_UnionPost
  quickCheck prop_FindPostPresent
  quickCheck prop_FindPostAbsent
  quickCheck prop_InsertDeleteComplete
  -- metamorphic
  quickCheck prop_InsertInsert
  quickCheck prop_InsertDelete
  quickCheck prop_InsertUnion
  -- equivalence preservation
  quickCheck prop_InsertPreservesEquiv
  quickCheck prop_DeletePreservesEquiv
  quickCheck prop_UnionPreservesEquiv
  quickCheck prop_FindPreservesEquiv
  -- test equivalent shrinker
  quickCheck prop_ShrinkEquivs -- commented out because they're slow. uncomment to perform a full test
  quickCheck prop_Equivs
  quickCheck prop_UnionNil1
  quickCheck prop_UnionInsert
  quickCheck prop_InsertComplete
  quickCheck prop_InsertCompleteForDelete
  quickCheck prop_InsertCompleteForUnion
  -- model based
  quickCheck prop_NilModel
  quickCheck prop_InsertModel
  quickCheck prop_DeleteModel
  quickCheck prop_UnionModel
  quickCheck prop_FindModel
