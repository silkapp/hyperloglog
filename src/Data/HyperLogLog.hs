--------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2013-2015
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
-- See the original paper for details:
-- <http://algo.inria.fr/flajolet/Publications/FlFuGaMe07.pdf>
--------------------------------------------------------------------
{-# LANGUAGE
    BangPatterns
  , DeriveGeneric
  , FlexibleContexts
  , FlexibleInstances
  , PolyKinds
  , ScopedTypeVariables
  , UndecidableInstances
  #-}
{-# OPTIONS_GHC
  -fno-cse
  -fno-float-in
  -fno-full-laziness
  #-}
module Data.HyperLogLog
  ( HyperLogLog (..)
  , Cardinality (..)
  , size
  , insert
  , insertHash
  , intersectionSize
  ) where

import Control.Applicative
import Control.Monad
import Data.ByteArray.Hash
import Data.Bits
import Data.Bits.Extras
import Data.Bytes.Put (runPutS)
import Data.Bytes.Serial
import Data.Proxy
import Data.Reflection
import Data.Semigroup
import GHC.Generics (Generic)
import GHC.Int
import GHC.Word
import qualified Data.Vector.Unboxed         as V
import qualified Data.Vector.Unboxed.Mutable as MV

type Rank = Int8

data Cardinality
  = Cardinality
  { lowerBound :: Int64
  , estimated  :: Int64
  , upperBound :: Int64
  } deriving Show

instance Num Cardinality where
  Cardinality la ma ha + Cardinality lb mb hb = Cardinality (la + hb) (ma + mb) (ha + lb)
  {-# INLINE (+) #-}
  Cardinality la ma ha * Cardinality lb mb hb = Cardinality (minimum extrema) (ma * mb) (maximum extrema)
    where extrema = (*) <$> [la, ha] <*> [lb, hb]
  {-# INLINE (*) #-}
  negate (Cardinality l m h) = Cardinality (-h) (-m) (-l)
  {-# INLINE negate #-}
  Cardinality la ma ha - Cardinality lb mb hb = Cardinality (la - hb) (ma - mb) (ha - lb)
  {-# INLINE (-) #-}
  abs (Cardinality la ma ha) = Cardinality (min lb hb) (abs ma) (max lb hb) where
    lb = abs la
    hb = abs ha
  {-# INLINE abs #-}
  signum (Cardinality la ma ha) = Cardinality (signum la) (signum ma) (signum ha)
  {-# INLINE signum #-}
  fromInteger i = let a = fromInteger i in Cardinality a a a
  {-# INLINE fromInteger #-}

mapCard :: (Int64 -> Int64) -> Cardinality -> Cardinality
mapCard f (Cardinality la ma ha) = Cardinality (f la) (f ma) (f ha)

newtype HyperLogLog p
  = HyperLogLog
  { runHyperLogLog :: V.Vector Rank
  } deriving (Eq, Generic)

instance Reifies p Integer => Show (HyperLogLog p) where
  show h = show $ size h

instance Semigroup (HyperLogLog p) where
  HyperLogLog a <> HyperLogLog b = HyperLogLog (V.zipWith max a b)
  {-# INLINE (<>) #-}

instance Reifies p Integer => Monoid (HyperLogLog p) where
  mempty = HyperLogLog $ V.replicate (numBuckets (reflect (Proxy :: Proxy p))) 0
  {-# INLINE mempty #-}
  mappend = (<>)
  {-# INLINE mappend #-}

sipKey :: SipKey
sipKey = SipKey 4 7

siphash :: Serial a => a -> Word64
siphash a = h
  where
    !bs = runPutS (serialize a)
    (SipHash !h) = sipHash sipKey bs
{-# INLINE siphash #-}

insert :: (Reifies s Integer, Serial a) => a -> HyperLogLog s -> HyperLogLog s
insert = insertHash . w32 . siphash
{-# INLINE insert #-}

insertHash :: Reifies s Integer => Word32 -> HyperLogLog s -> HyperLogLog s
insertHash h m@(HyperLogLog v) = HyperLogLog $ V.modify (\x -> do
      old <- MV.read x bk
      when (rnk > old) $ MV.write x bk rnk) v
  where
    !n   = reflect m
    !bk  = calcBucket n h
    !rnk = calcRank n h
{-# INLINE insertHash #-}

size :: Reifies p Integer => HyperLogLog p -> Cardinality
size m@(HyperLogLog bs) = Cardinality
  { lowerBound = l
  , estimated  = expected
  , upperBound = h
  }
  where
    numZeros = fromIntegral . V.length . V.filter (== 0) $ bs
    expected = round res
    raw      = rawFact n * (1 / sm)
    sm       = V.sum $ V.map (\x -> 1 / (2 ^^ x)) bs
    sd       = 1.04 / sqrt m'
    n        = reflect m
    m'       = fromIntegral (numBuckets n)
    l        = floor $ max (res * (1 - 3 * sd)) 0
    h        = ceiling $ res * (1 + 3 * sd)
    res      = case raw < smallRange n of
      True
        | numZeros > 0 -> m' * log (m' / numZeros) -- 13.47 bits max error
        | otherwise    -> raw
        -- numZeros > 0 -> m' / 1 / (log m' - log numZeros) -- 6.47 bits max error
      False
        | raw <= interRange -> raw
        | otherwise         -> raw + (raw / lim32) * raw
        -- otherwise -> -1 * lim32 * log (1 - raw / lim32) -- 44 bits max error
        -- raw / lim32 < -1.7563532969399233e-6 -> - log (1 - (raw / lim32)) * lim32 -- 5.39 bits max error
{-# INLINE size #-}

intersectionSize :: Reifies p Integer => [HyperLogLog p] -> Cardinality
intersectionSize []     = 0
intersectionSize (x:xs) = mapCard (max 0) $ size x + intersectionSize xs - intersectionSize (mappend x <$> xs)
{-# INLINE intersectionSize #-}

-- ========================================= Config ========================================

lim32 :: Double
lim32 = fromInteger (bit 32)
{-# INLINE lim32 #-}

numBuckets :: Integer -> Int
numBuckets b = unsafeShiftL 1 (fromIntegral b)
{-# INLINE numBuckets #-}

smallRange :: Integer -> Double
smallRange b = 5/2 * fromIntegral (numBuckets b)
{-# INLINE smallRange #-}

interRange :: Double
interRange = lim32 / 30
{-# INLINE interRange #-}

rawFact :: Integer -> Double
rawFact b = alpha b * m * m where
  m = fromIntegral (numBuckets b)
{-# INLINE rawFact #-}

alpha :: Integer -> Double
alpha b = 0.7213 / (1 + 1.079 / fromIntegral (numBuckets b))
{-# INLINE alpha #-}

bucketMask :: Integer -> Word32
bucketMask b = fromIntegral (numBuckets b) - 1
{-# INLINE bucketMask #-}

-- ========================================= Util ========================================

calcBucket :: Integer -> Word32 -> Int
calcBucket t w = fromIntegral (w .&. bucketMask t)
{-# INLINE calcBucket #-}

calcRank :: Integer -> Word32 -> Int8
calcRank t w = fromIntegral $ rank $ shiftR w $ fromIntegral t
{-# INLINE calcRank #-}
