#!/usr/bin/env stack
-- stack --resolver lts-20.20 script

-- from https://blog.sumtypeofway.com/posts/introduction-to-recursion-schemes.html
-- about Functional Programming with Bananas, Lenses, Envelopes and Barbed Wire
-- https://hackage.haskell.org/package/recursion-schemes https://hackage.haskell.org/package/compdata https://hackage.haskell.org/package/fixplate
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

import Control.Arrow (Arrow ((&&&)), (<<<), (>>>), (|||))
import Control.Comonad
import Control.Comonad.Cofree (Cofree ((:<)), ComonadCofree (unwrap))
import Control.Comonad.Identity
import Data.Char (isSpace)
import Data.Function ((&))
import Data.List (partition)
import GHC.Num (Natural)
import System.Random qualified as Random
import Text.PrettyPrint (Doc)
import Text.PrettyPrint qualified as P
import Text.Read (readMaybe)

data Expr
  = Index Expr Expr
  | Call Expr [Expr]
  | Unary String Expr
  | Binary Expr String Expr
  | Paren Expr
  | Literal Int -- Lit
  deriving (Show, Eq)

-- naive flatten needs lots of boilerplate to become total
flatten :: Expr -> Expr
flatten (Paren e) = e

-- generic applyexpr simplifies flatten but is generic
applyExpr :: (Expr -> Expr) -> Expr -> Expr
applyExpr f (Literal i) = Literal i
applyExpr f (Paren p) = Paren (f p)
applyExpr f (Index e i) = Index (f e) (f i)
applyExpr f (Call e args) = Call (f e) (map f args)
applyExpr f (Unary op arg) = Unary op (f arg)
applyExpr f (Binary l op r) = Binary (f l) op (f r)

-- simplified flatten
flatten' :: Expr -> Expr
flatten' (Paren e) = e
flatten' e = applyExpr flatten' e

data ExprF a
  = IndexF a a
  | IdentF {name :: String}
  | CallF a [a]
  | UnaryF String a
  | BinaryF a String a
  | ParenF a
  | LiteralF Int
  deriving (Show, Eq, Functor)

-- we get fmap for free, works like applyexpr
-- but ExprF is not recursive - for a triple nest I need ExprF (ExprF (EpprF Lit))), and a simple Expr to do the same and more

-- Y combinator and fixed point
-- y f = f (f (f (f ...)))

newtype Term f = In {out :: f (Term f)} -- fixed point combinator

type Expr' = Term ExprF -- defining recursive types using fixed-points of functors is an example of codata

instance Show Expr' where
  show (In a) = "Term (" <> show a <> ")"

-- can define a literal because has a non-recursive base case, LiteralF Lit
arbitrarelyNested :: Expr'
arbitrarelyNested = In $ ParenF $ In $ ParenF $ In (LiteralF 1)

-- recursion scheme(s) for Term . limited on type and returning a Term a
topDown, bottomUp :: Functor a => (Term a -> Term a) -> Term a -> Term a
topDown f = In <<< fmap (topDown f) <<< out <<< f
bottomUp fn =
  -- same as fn . In . fmap (bu fn) . out
  out -- 1) unpack
    >>> fmap (bottomUp fn) -- 2) recurse
    >>> In -- 3) repack
    >>> fn -- 4) apply

flattenTerm :: Expr' -> Expr'
flattenTerm (In (ParenF e)) = e -- remove all Parens
flattenTerm other = other -- do nothing otherwise

flatten'' :: Expr' -> Expr'
flatten'' = bottomUp flattenTerm

-- >>> flatten'' arbitrarelyNested
-- Term (LiteralF 1)

------------------------------------- Catamorphism - generalised foldr - like bottomUp without In - bottomUp f = cata (In >>> f)
type Algebra f a = f a -> a

cata :: Functor f => Algebra f b -> Term f -> b
cata fn = out >>> fmap (cata fn) >>> fn

-- laws:
-- cata In ≍ id
-- cata (alg >>> fmap func) ≍ (cata alg) >>> func

countNodes :: Algebra ExprF Int
countNodes (UnaryF _ arg) = arg + 1
countNodes (BinaryF left _ right) = left + right + 1
countNodes (CallF fn args) = fn + sum args + 1
countNodes (IndexF it idx) = it + idx + 1
countNodes (ParenF arg) = arg + 1
countNodes (LiteralF _) = 1
countNodes (IdentF _) = 1

ten, add, call :: Term ExprF
ten = In (LiteralF 10)
add = In (IdentF "add")
call = In (CallF add [ten, ten])

-- >>> cata countNodes call
-- 4

prettyPrint :: Algebra ExprF Doc
prettyPrint (LiteralF i) = P.int i
prettyPrint (IdentF s) = P.text s
prettyPrint (CallF f as) = f <> P.parens (mconcat (P.punctuate "," as)) ---f(a,b...)
prettyPrint (IndexF it idx) = it <> P.brackets idx ---a[b]
prettyPrint (UnaryF op it) = P.text op <> it ---op x
prettyPrint (BinaryF l op r) = l <> P.text op <> r ---lhs op rhs
prettyPrint (ParenF exp) = P.parens exp ---(op)

-- >>> cata prettyPrint call
-- add(10,10)

------------------------------------- Anamorphism - generalised unfoldr - like topDown without out - topDown f = ana (out <<< f)
type Coalgebra f a = a -> f a

ana :: (Functor f) => Coalgebra f a -> a -> Term f
ana f = In <<< fmap (ana f) <<< f

nested :: Int -> Term ExprF
nested n = ana go n
  where
    go :: Coalgebra ExprF Int
    go 0 = LiteralF n
    go n = ParenF (n - 1)

-- >>> nested 2
-- Term (ParenF Term (ParenF Term (LiteralF 2)))
----------------------------- Paramorphism - cata + access to current Term
type RAlgebra f a = f (Term f, a) -> a

para :: (Functor f) => RAlgebra f a -> Term f -> a
para rAlg = out >>> fmap fanout >>> rAlg
  where
    fanout t = (t, para rAlg t)

type RAlgebra' f a = Term f -> f a -> a -- kind of uncurried RAlgebra

para'' :: Functor f => RAlgebra' f a -> Term f -> a
para'' alg t = out t & fmap (para'' alg) & alg t

cata' :: Functor f => Algebra f a -> Term f -> a -- cata expressed as para
cata' f = para'' (const f)

fastPretty :: RAlgebra' ExprF Doc -- like prettyPrint but replacing id with its argument - cata can't deal with this as it's not an Algebra
fastPretty _ (LiteralF i) = P.int i
fastPretty _ (IdentF s) = P.text s
fastPretty (In (CallF (In (IdentF "id")) _)) (CallF _ [theArg]) = theArg
fastPretty _ (CallF f args) = f <> P.parens (mconcat ("," `P.punctuate` args))
fastPretty _ (IndexF it idx) = it <> P.brackets idx
fastPretty _ (UnaryF op it) = P.text op <> it
fastPretty _ (BinaryF l op r) = l <> P.text op <> r
fastPretty _ (ParenF ex) = P.parens ex

nestedCall = In $ CallF (In $ IdentF "id") [call]

-- >>> cata' prettyPrint nestedCall
-- >>> para'' fastPretty nestedCall
-- id(add(10,10))
-- add(10,10)
----------------------------------- Apomorphism, dual of paramorphism
-- RAlgebra holds both a Term f and an a, RCoalgebra either one or the other
type RCoalgebra f a = a -> f (Either (Term f) a)

-- apo :: Functor f => RCoalgebra f a -> a -> Term f
-- apo f = In <<< fmap fanin <<< f where fanin = either id (apo f)
apo :: Functor f => RCoalgebra f a -> a -> Term f
apo f = In <<< fmap (id ||| apo f) <<< f

nested2 :: Int -> Term ExprF
nested2 n = apo go n
  where
    go :: RCoalgebra ExprF Int
    go 0 = LiteralF n -- will never get here unless we pass
    go 1 = ParenF $ Left (In $ LiteralF 10) -- terminates the recursion - ana can't do that
    go n = ParenF $ Right (n - 1)

-- >>> nested2 2
-- Term (ParenF Term (ParenF Term (LiteralF 10)))

------------------------------ histomorphism -- history preserving cata
data Attr f a = Attr {attribute :: a, hole :: f (Attr f a)} -- like term plus an attribute - acts like an adaptiva cache over any functor
-- isomorphic to Cofree comonad data: Cofree f a = a :< (f (Cofree f a))

type CVAlgebra f a = f (Attr f a) -> a

-- histo :: Functor f => CVAlgebra f a -> Term f -> a
-- histo h = out >>> fmap worker >>> h where worker t = Attr (histo h t) (fmap worker (out t))
histo :: Functor f => CVAlgebra f a -> Term f -> a
histo h = worker >>> attribute
  where
    worker = out >>> fmap worker >>> (h &&& id) >>> mkAttr
    mkAttr (a, b) = Attr a b -- uncurry Attr

type Cent = Int

coins :: [Cent]
coins = [50, 25, 10, 5, 1]

data Nat a
  = Zero
  | Next a
  deriving (Functor)

expand :: Int -> Term Nat
expand 0 = In Zero
expand n = In (Next (expand (n - 1)))

compress :: Nat (Attr Nat a) -> Int
compress Zero = 0
compress (Next (Attr _ x)) = 1 + compress x

change :: Cent -> Int
change amt = histo go (expand amt)
  where
    go :: Nat (Attr Nat Int) -> Int -- CVAlgebra Nat Int
    go Zero = 1
    go curr@(Next attr) =
      let given = compress curr
          validCoins = filter (<= given) coins
          remaining = map (given -) validCoins
          (zeroes, toProcess) = partition (== 0) remaining
          results = sum (map (lookUp attr) toProcess) -- always < given -> always cached (as a right fold, we start computing from the last case)
       in length zeroes + results
    lookUp :: Attr Nat a -> Int -> a
    lookUp cache 0 = attribute cache
    lookUp cache n = lookUp inner (n - 1) where (Next inner) = hole cache

-- >>> change 12
-- 4

-- rewrite cata and para based on histo:
-- cata :: Functor f => Algebra f a -> Term f -> a
-- cata f = histo (fmap attribute >>> f)
-- para :: Functor f => RAlgebra f a -> Term f -> a
-- para f = histo (fmap worker >>> f) where worker (Attr a h) = (In (fmap (worker >>> fst) h), a)

------------------ Futumorphisms reverse histo
data CoAttr f a = Automatic a | Manual (f (CoAttr f a)) -- isomorphic to free monad  --data Free f a = Pure a | Impure (f (Free f a))

type CVCoalgebra f a = a -> f (CoAttr f a)

futu :: Functor f => CVCoalgebra f a -> a -> Term f
futu f = In <<< fmap worker <<< f
  where
    worker (Automatic a) = futu f a -- continue through this level
    worker (Manual g) = In (fmap worker g) -- omit folding this level,delegating to the worker to perform any needed unfolds later on.

-- ana and apo defined on futu
-- ana :: (Functor f) => Coalgebra f a -> a -> Term f
-- ana f = futu (fmap Automatic <<< f)
-- apo :: Functor f => RCoalgebra f a -> a -> Term f
-- apo f = futu (fmap (either termToCoattr Automatic) <<< f) where termToCoattr = Manual <<< fmap termToCoattr <<< out

-- example: grow Plants
data Plant a
  = Root a -- every plant starts here
  | Stalk a -- and continues upwards
  | Fork a a a -- but can trifurcate at any moment
  | Bloom -- eventually terminating in a flower
  deriving (Show, Functor)

data Action
  = Flower -- stop growing now
  | Upwards -- grow up with a Stalk
  | Branch -- grow up with a Fork

data Seed = Seed {height :: Int, rng :: Random.StdGen}

grow :: Seed -> (Action, Seed, Seed)
grow seed@(Seed h rand) = (choose choice, left {height = h + 1}, right {height = h + 1})
  where
    (choice, _) = Random.randomR (1 :: Int, 5) rand
    (leftR, rightR) = Random.split rand
    left = Seed h leftR
    right = Seed h rightR
    choose 1 = Flower
    choose 2 = Branch
    choose _ = Upwards

sow :: CVCoalgebra Plant Seed
sow seed =
  let (action, left, right) = grow seed
   in case (action, height seed) of
        (_, 0) -> Root (Automatic left) -- start at root
        (_, 10) -> Bloom -- stop at depth 10
        (Flower, _) -> Bloom
        (Upwards, _) -> Stalk (Automatic right)
        (Branch, _) ->
          Fork
            (Manual (Stalk (Automatic left)))
            (Manual Bloom)
            (Manual (Stalk (Automatic right)))

instance Show (Term Plant) where
  show (In a) = "Term {" <> show a <> "}" -- TODO generate an ascii tree from Plant (CoAttr Plant Seed) with cata

-- >>> futu sow $ Seed 5 $ Random.mkStdGen 50
-- Term {Stalk Term {Stalk Term {Stalk Term {Fork Term {Stalk Term {Fork Term {Stalk Term {Bloom}} Term {Bloom} Term {Stalk Term {Bloom}}}} Term {Bloom} Term {Stalk Term {Stalk Term {Bloom}}}}}}}
------------------------------------ base functors
type family Base t :: * -> *

class (Functor (Base t)) => Recursive t where -- added b suffix to avoid name clashes
  projectb :: t -> Base t t
  catab :: (Base t a -> a) -> t -> a
  catab f = c where c = f . fmap c . projectb

-- define Base and Recursive, you get a Term free cata
data ListF a b
  = Cons a b
  | Nil
  deriving (Show, Eq, Functor)

type instance Base [a] = ListF a

instance Recursive [a] where
  projectb (x : xs) = Cons x xs
  projectb [] = Nil

sumList :: Num a => [a] -> a
sumList = catab go
  where
    go Nil = 0
    go (Cons a acc) = a + acc

-- >>> sumList [1,2,3,4]
-- 10

-- some packages can also derive ExprF from Expr with templatehaskell makeBaseFunctor ''Expr

class Functor (Base t) => Corecursive t where
  embedb :: Base t t -> t
  anab :: (a -> Base t a) -> a -> t
  anab g = a where a = embedb . fmap a . g

instance Corecursive [a] where
  embedb (Cons x xs) = x : xs
  embedb Nil = []

---------------- hylomorphism - cata + ana in one
hylo :: Functor f => Algebra f b -> Coalgebra f a -> a -> b -- kmett's doesn't need Term or base: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo alg coalg = ana coalg >>> cata alg

hylo' :: Functor f => Algebra f b -> Coalgebra f a -> a -> b -- more efficient, less clear
hylo' alg coalg = coalg >>> fmap (hylo' alg coalg) >>> alg

data Token
  = Lit Int
  | Op (Int -> Int -> Int)

parseToken :: String -> Token
parseToken "+" = Op (+)
parseToken "-" = Op (-)
parseToken "*" = Op (*)
parseToken "/" = Op div
parseToken num = Lit $ read num

parseRPN :: Coalgebra (ListF Token) String -- String -> ListF Token String
parseRPN "" = Nil
parseRPN str = Cons token newSeed
  where
    (x, rest) = break isSpace str
    token = parseToken x
    newSeed = dropWhile isSpace rest

type Stack = [Int]

-- evalRPN :: Algebra (ListF Token) Stack -- rpn requires a left fold, cata is a right fold (so is hylo) so the naive defition won't work
evalRPN :: Algebra (ListF Token) (Stack -> Stack) -- continuation passing style -- will accumulate thunks and eval on Nil, starting with the innermost function, aka left
evalRPN Nil stack = stack
evalRPN (Cons (Lit i) cont) stack = cont (i : stack)
evalRPN (Cons (Op fn) cont) (a : b : rest) = cont (fn b a : rest)
evalRPN _ stack = error ("too few arguments on stack: " <> show stack)

rpn :: String -> Stack
rpn s = hylo evalRPN parseRPN s []

---------------- chronomorphisms
chrono :: Functor f => CVAlgebra f b -> CVCoalgebra f a -> a -> b
chrono cvalg cvcoalg = futu cvcoalg >>> histo cvalg

-- >>> rpn "15 7 1 1 + - / 3 * 2 1 1 + + -"
-- [5]
---------------- elgot, like hylomorphism but with error handling
elgot :: Functor f => Algebra f b -> (a -> Either b (f a)) -> a -> b
elgot alg coalg = coalg >>> (id ||| (fmap (elgot alg coalg) >>> alg))

-- coelgot :: Functor f => ((a, f b) -> b) -> (a -> f a) -> a -> b
coelgot :: Functor f => ((a, f b) -> b) -> Coalgebra f a -> a -> b
coelgot alg coalg = alg <<< (id &&& (fmap (coelgot alg coalg) <<< coalg))

data Result
  = Success Stack
  | ParseError String
  | TooFewArguments Stack
  deriving (Eq, Show)

type Cont = Result -> Result

safeToken :: String -> Either Cont Token
safeToken "+" = Right (Op (+))
safeToken "-" = Right (Op (-))
safeToken "*" = Right (Op (*))
safeToken "/" = Right (Op div)
safeToken str = case readMaybe str of
  Just num -> Right (Lit num)
  Nothing -> Left (const (ParseError str))

safeParse :: String -> Either Cont (ListF Token String)
safeParse "" = return Nil
safeParse str = do
  let (x, rest) = break isSpace str
  let newSeed = dropWhile isSpace rest
  parsed <- safeToken x
  return $ Cons parsed newSeed

safeEval :: Algebra (ListF Token) Cont
safeEval (Cons (Lit i) cont) (Success stack) = cont (Success (i : stack))
safeEval (Cons (Op fn) cont) (Success s) =
  cont
    ( case s of
        (a : b : rest) -> Success (fn b a : rest)
        _ -> TooFewArguments s
    )
safeEval _ result = result

safeRPN :: String -> Result
safeRPN s = elgot safeEval safeParse s (Success [])

-- >>> safeRPN "15 7 1 1 + - / 3 * 2 1 1 + + -"
-- >>> safeRPN "a"
-- >>> rpn "a"
-- Success [5]
-- ParseError "a"
-- Prelude.read: no parse

--------------- hypomorphism?
hypo :: Functor f => RAlgebra f b -> RCoalgebra f a -> a -> b
hypo ralg rcoalg = apo rcoalg >>> para ralg

-- cata :: (Base t a -> a) -> t -> a
-- para :: (Base t (t, a) -> a) -> t -> a
-- histo :: (Base t (Cofree (Base t) a) -> a) -> t -> a
-- type WDistLaw f w = forall b. f (w b) -> w (f b)

-- type WAlgebra f w a = f (w a) -> a

-- distCata :: Functor f => f (Identity a) -> Identity (f a)
-- distCata f = Identity (fmap runIdentity f)

-- distHisto :: Functor f => f (Cofree f a) -> Cofree f (f a)
-- distHisto fc = fmap extract fc :< fmap (distHisto . unwrap) fc

-- distPara :: Comonad f => f (t, a) -> (t, f a)
-- distPara f = (fst (extract f), fmap snd f)

-- gcata depending on distribution does the job of cata, para, and histo. Can be extended with more distribution WDistLaw instances

-- gcata ::
--   (Functor f, Comonad w) =>
--   WDistLaw f w -> -- | a distributive law
--   WAlgebra f w a -> -- | a w-algebra returning 'a'
--   Term f ->
--   a

-- distParaT from recursion-schemes converts one of the above distributors in a specific one for a given comonad:
-- newtype Ledger t f a = Ledger {getLedger :: EnvT t (Cofree f) a} deriving (Functor)
-- distLedger'' :: Corecursive t => Base t (Ledger t (Base t) a) -> Ledger t (Base t) (Base t a)
-- distLedger'' = fmap getLedger >>> distParaT distHisto >>> Ledger

-- gana ::
--   (Corecursive t, Monad m) => -- | a distributive law
--   (forall b. m (Base t b) -> Base t (m b)) -> -- | a Base-t-m coalgebra
--   (a -> Base t (m a)) -> -- | a seed
--   a ->
--   t