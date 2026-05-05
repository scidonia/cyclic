{-# LANGUAGE RankNTypes #-}

{-|
Hard but semantically equivalent program transformations in a pure functional language.

This file is intended as a readable catalogue of examples, using Haskell-style code.
Some examples are executable; others are schematic and included to show the shape
of the transformation and the equivalence claim.
-}

module HardPureFunctionalTransformations where

--------------------------------------------------------------------------------
-- 1. Direct style -> Continuation-Passing Style (CPS)
--------------------------------------------------------------------------------

fact :: Integer -> Integer
fact n =
  if n == 0 then 1
  else n * fact (n - 1)

factCPS :: Integer -> (Integer -> r) -> r
factCPS n k =
  if n == 0 then k 1
  else factCPS (n - 1) (\r -> k (n * r))

-- Equivalence:
--   fact n == factCPS n id

--------------------------------------------------------------------------------
-- 2. Higher-order functions -> defunctionalized first-order code
--------------------------------------------------------------------------------

data Fun
  = AddOne
  | TimesTwo
  deriving (Eq, Show)

applyFun :: Fun -> Integer -> Integer
applyFun AddOne   x = x + 1
applyFun TimesTwo x = x * 2

mapD :: Fun -> [Integer] -> [Integer]
mapD _ []     = []
mapD f (x:xs) = applyFun f x : mapD f xs

-- Equivalence examples:
--   map (\x -> x + 1) xs == mapD AddOne xs
--   map (\x -> x * 2) xs == mapD TimesTwo xs

--------------------------------------------------------------------------------
-- 3. foldr -> foldl with continuations
--------------------------------------------------------------------------------

foldrViaFoldl :: (a -> b -> b) -> b -> [a] -> b
foldrViaFoldl f z xs =
  foldl (\k x -> \acc -> k (f x acc)) id xs z

-- Equivalence:
--   foldr f z xs == foldrViaFoldl f z xs

--------------------------------------------------------------------------------
-- 4. Fusion: producer/consumer elimination
--------------------------------------------------------------------------------

sumMap :: Num b => (a -> b) -> [a] -> b
sumMap f xs = sum (map f xs)

sumMapFused :: Num b => (a -> b) -> [a] -> b
sumMapFused f xs = foldr (\x acc -> f x + acc) 0 xs

-- Equivalence:
--   sum (map f xs) == foldr (\x acc -> f x + acc) 0 xs

--------------------------------------------------------------------------------
-- 5. Short-cut fusion / Church-encoded lists
--------------------------------------------------------------------------------

build :: (forall b. (a -> b -> b) -> b -> b) -> [a]
build g = g (:) []

mapBuild :: (a -> b) -> [a] -> [b]
mapBuild f xs =
  build (\cons nil -> foldr (\x acc -> cons (f x) acc) nil xs)

-- Equivalence:
--   map f xs == mapBuild f xs

--------------------------------------------------------------------------------
-- 6. Explicit recursion -> catamorphism over trees
--------------------------------------------------------------------------------

data Tree a
  = Empty
  | Node (Tree a) a (Tree a)
  deriving (Eq, Show)

sumTree :: Num a => Tree a -> a
sumTree Empty        = 0
sumTree (Node l x r) = sumTree l + x + sumTree r

foldTree :: b -> (b -> a -> b -> b) -> Tree a -> b
foldTree z _ Empty        = z
foldTree z f (Node l x r) = f (foldTree z f l) x (foldTree z f r)

sumTreeFold :: Num a => Tree a -> a
sumTreeFold = foldTree 0 (\l x r -> l + x + r)

-- Equivalence:
--   sumTree t == sumTreeFold t

--------------------------------------------------------------------------------
-- 7. Catamorphism fusion
--------------------------------------------------------------------------------

-- Schematic fusion law:
--
-- Given:
--   h z = z'
--   h (f l x r) = g (h l) x (h r)
--
-- Then:
--   h (foldTree z f t) == foldTree z' g t
--
-- This is hard because the equivalence depends on proving algebraic laws,
-- not merely rearranging syntax.

--------------------------------------------------------------------------------
-- 8. Naive reverse -> accumulator-passing reverse
--------------------------------------------------------------------------------

reverseNaive :: [a] -> [a]
reverseNaive []     = []
reverseNaive (x:xs) = reverseNaive xs ++ [x]

revAcc :: [a] -> [a] -> [a]
revAcc []     acc = acc
revAcc (x:xs) acc = revAcc xs (x:acc)

reverseAcc :: [a] -> [a]
reverseAcc xs = revAcc xs []

-- Equivalence:
--   reverseNaive xs == reverseAcc xs
--
-- Strengthened lemma usually needed for the proof:
--   revAcc xs acc == reverseNaive xs ++ acc

--------------------------------------------------------------------------------
-- 9. Difference lists
--------------------------------------------------------------------------------

type DList a = [a] -> [a]

toList :: DList a -> [a]
toList d = d []

reverseDList :: [a] -> [a]
reverseDList xs = toList (go xs id)
  where
    go :: [a] -> DList a -> DList a
    go []     k = k
    go (y:ys) k = go ys (\zs -> k (y:zs))

-- Equivalence:
--   reverseNaive xs == reverseDList xs
--
-- The hard part is that intermediate lists are represented as functions.

--------------------------------------------------------------------------------
-- 10. Explicit state threading -> State representation
--------------------------------------------------------------------------------

fresh :: Integer -> (Integer, Integer)
fresh s = (s, s + 1)

newtype State s a = State { runState :: s -> (a, s) }

freshM :: State Integer Integer
freshM = State (\s -> (s, s + 1))

-- Equivalence:
--   runState freshM s == fresh s

--------------------------------------------------------------------------------
-- 11. Applicative / monadic normalization
--------------------------------------------------------------------------------

-- Schematic equivalences, valid under the relevant Applicative/Monad laws:
--
--   pure f <*> x <*> y == liftA2 f x y
--
--   do a <- x
--      b <- y
--      pure (f a b)
--
-- is equivalent to:
--
--   x >>= \a -> y >>= \b -> pure (f a b)
--
-- Hard because the proof depends on abstract laws, not concrete evaluation.

--------------------------------------------------------------------------------
-- 12. Stream fusion
--------------------------------------------------------------------------------

data Step s a
  = Done
  | Skip s
  | Yield a s
  deriving (Eq, Show)

data Stream a = forall s. Stream (s -> Step s a) s

-- A list pipeline such as:
--   sum (map f (filter p xs))
--
-- can be transformed into a stream pipeline and then into one state machine.
-- Constructors disappear operationally, but the denotation remains a list-like
-- computation.

--------------------------------------------------------------------------------
-- 13. Parametricity / free theorem rewrite
--------------------------------------------------------------------------------

-- For a total polymorphic function:
--   g :: [a] -> [a]
--
-- Parametricity gives laws of the shape:
--   map f (g xs) == g (map f xs)
--
-- The hard part is that the equivalence follows from the type, not from
-- inspecting the implementation of g.

--------------------------------------------------------------------------------
-- 14. Laziness-sensitive transformation
--------------------------------------------------------------------------------

takeMap :: Int -> (a -> b) -> [a] -> [b]
takeMap n f xs = take n (map f xs)

mapTake :: Int -> (a -> b) -> [a] -> [b]
mapTake n f xs = map f (take n xs)

-- Equivalence, for pure f:
--   take n (map f xs) == map f (take n xs)
--
-- This is especially interesting for infinite lists, where preserving
-- productivity and termination behavior matters.

--------------------------------------------------------------------------------
-- 15. Yoneda-style transformation
--------------------------------------------------------------------------------

newtype Yoneda f a = Yoneda { runYoneda :: forall b. (a -> b) -> f b }

liftYoneda :: Functor f => f a -> Yoneda f a
liftYoneda fa = Yoneda (\k -> fmap k fa)

lowerYoneda :: Yoneda f a -> f a
lowerYoneda y = runYoneda y id

mapViaYoneda :: Functor f => (a -> b) -> f a -> f b
mapViaYoneda f xs = lowerYoneda (Yoneda (\k -> runYoneda (liftYoneda xs) (k . f)))

-- Equivalence:
--   fmap f xs == mapViaYoneda f xs
--
-- The representation changes from concrete mapping to continuation-like
-- composition, but the meaning is preserved.
