{-# LANGUAGE TupleSections #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}

module Lib (trappedRain0,
            trappedRain1,
            trappedRain1',
            trappedRain2,
            trappedRain2',
            trappedRain2'',
            rain0, rain1, rain2, rain3
           ) where

import Control.Monad
import Data.Semigroup
import Control.Category
import Prelude hiding (id, (.))
import Data.Functor.Identity
import Data.Functor.Compose
import Control.Arrow
import Control.Monad.State
import Control.Lens
import Control.Scanl qualified as SL
import Prelude hiding (id, (.))

---

-- The classic haskell answer.
trappedRain0 :: [Int] -> Int
trappedRain0 heights = sum $ zipWith3 (\h l r -> max 0 (min l r - h)) heights leftMax rightMax
  where
    leftMax = scanl1 max heights
    rightMax = scanr1 max heights

---

-- An anwer that uses `foldl` packages `Scan`.

scanMax' :: (Ord o) => o -> SL.Scan o o
scanMax' low =
  SL.Scan
    ( \i -> do
        sofar <- get
        put (max i sofar)
        pure sofar
    )
    low

type Height = Int

data Step1 = Step1 {height :: Height, rightMax :: Height}

calc :: Int -> Int -> Int -> Int
calc height leftMax rightMax = max 0 (min rightMax leftMax - height)

trappedRain1 :: [Int] -> Int
trappedRain1 = sum . addLeftMax . addRightMax
  where
    addRightMax = SL.scan $ proc height -> do
      rightMax <- scanMax' 0 -< height
      returnA -< Step1 {..}

    addLeftMax = SL.scanr $ proc Step1 {..} -> do
      leftMax <- scanMax' 0 -< height
      returnA -< calc height leftMax rightMax

trappedRain1' :: [Int] -> Int
trappedRain1' heights = sum $ zipWith3 (\h l r -> max 0 (min l r - h)) heights leftMaxs rightMaxs
  where
    rightMaxs :: [Int]
    rightMaxs = SL.scan (scanMax' 0) heights

    leftMaxs :: [Int]
    leftMaxs = SL.scanr (scanMax' 0) heights

---

data Scan a b where
  MkScan :: Applicative f => (a -> f b) -> (forall x. f x -> x) -> Scan a b

instance Functor (Scan a) where
  fmap f (MkScan g h) = MkScan (fmap f . g) h

instance Category Scan where
  id = MkScan (Identity) runIdentity
  MkScan f1 g1 . MkScan f2 g2 = MkScan (Compose . fmap f1 . f2) (g1 . g2 . getCompose)

instance Arrow Scan where
  arr f = MkScan (Identity . f) runIdentity
  (MkScan f1 g1) *** (MkScan f2 g2) =
    MkScan (\(a1,a2) -> MkDay (f1 a1) (f2 a2) (,)) (runDay g1 g2)
  (MkScan f1 g1) &&& (MkScan f2 g2) =
    MkScan (\a -> MkDay (f1 a) (f2 a) (,))
           (runDay g1 g2)
  first (MkScan f g) = MkScan (\(a, c) -> (,c) <$> f a) g
  second (MkScan f g) = MkScan (\(c, a) -> (c,) <$> f a) g

scan :: Traversable t => Scan a b -> t a -> t b
scan (MkScan f g) xs = g $ traverse f xs

rev :: Scan a b -> Scan a b
rev (MkScan f g) = MkScan (Back . f) (g . runBack)

scanBin :: (a -> b -> b) -> b -> Scan a b
scanBin b s = MkScan (\a -> state (\s' -> let r = b a s' in (r, r))) (\act -> evalState act s)

scanMax :: Scan Int Int
scanMax = scanBin max 0

-------------------------------------

data Day f g a where
  MkDay :: f x -> g y -> (x -> y -> a) -> Day f g a

runDay :: (forall x. f x -> x) -> (forall y. g y -> y) -> Day f g a -> a
runDay f g (MkDay fx gy h) = h (f fx) (g gy)

instance (Functor f, Functor g) => Functor (Day f g)where
  fmap h (MkDay fx gy f) = MkDay fx gy (\x y -> h (f x y))

instance (Applicative f, Applicative g) => Applicative (Day f g) where
  pure x = MkDay (pure ()) (pure ()) (\_ _ -> x)
  MkDay fx1 gy1 f <*> MkDay fx2 gy2 g = MkDay ((,) <$> fx1 <*> fx2) ((,) <$> gy1 <*> gy2) (\(x1,x2) (y1,y2) -> f x1 y1 (g x2 y2))

newtype Back f a = Back { runBack :: f a }
  deriving (Functor)

instance Applicative f => Applicative (Back f) where
  pure x = Back $ pure x
  Back f <*> Back x = Back $ (&) <$> x <*> f

---

trappedRain2 :: [Int] -> Int
trappedRain2 = sum . go
  where
    go = scan $ proc height -> do
      rightMax <- scanMax -< height
      leftMax <- rev scanMax -< height
      returnA -< calc height leftMax rightMax


trappedRain2' :: [Int] -> Int
trappedRain2' heights = sum $ zipWith3 (\h l r -> max 0 (min l r - h)) heights leftMaxs rightMaxs
  where
    rightMaxs :: [Int]
    rightMaxs = scan scanMax heights

    leftMaxs :: [Int]
    leftMaxs = scan (rev scanMax) heights

trappedRain2'' :: [Int] -> Int
trappedRain2'' = sum . scan go
  where
    go :: Scan Int Int
    go = (id &&& scanMax &&& rev scanMax)
         >>> arr (\(height, (rightMax, leftMax)) -> calc height leftMax rightMax)

---

-- Examples

rain0, rain1, rain2, rain3 :: [Int]
rain0 = [0,1,0,2,1,0,1,3,2,1,2,1]
rain1 = [0,1,0,2,1,0,1,3,2,1,2,1]
rain2 = [3,0,2,0,4,0,0,0,3,2,0,1,0,0,2,1,0,3,1,0,2,0,1,4,0,0,1,2,0,0,3]


rain3 = stimes (100000 :: Int) rain0

---

scanBin' :: (a -> b -> b) -> b -> Scan a b
scanBin' b s = MkScan (\a -> MkSt (\k s' -> let r = b a s' in k r r)) (evalStatek s)

scanMax'' :: Scan Int Int
scanMax'' = scanBin' max 0

newtype Statek s a = MkSt { unSt :: forall r. (a -> s -> r) -> s -> r }
  deriving (Functor)

evalStatek :: s -> Statek s a -> a
evalStatek s (MkSt a) = a (\x _ -> x) s

instance Applicative (Statek s) where
  pure a = MkSt $ \k s -> k a s
  (<*>) = ap

instance Monad (Statek s) where
  (MkSt a) >>= f = MkSt $ \k s -> a (\x s' -> unSt (f x) k s') s
