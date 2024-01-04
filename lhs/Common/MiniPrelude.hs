{-# LANGUAGE TypeOperators #-}

{- ver. 2017 -}

module Common.MiniPrelude (
   module Prelude ,
   module Common.MiniPrelude
  ) where
-- import GHC.Types hiding ((:))
-- import qualified GHC.Types as GTypes
import Prelude
  hiding ( -- lists
           head, tail, init, last, (++)
         , take, drop, takeWhile, dropWhile
         , concat, concatMap, foldr, foldr1
         , foldl, foldl1, map, filter, zip, unzip
         , null, length, sum, product, elem, notElem
         , maximum, minimum
         , and, or, any, all, ($)
         -- arithmetics
         , (+), (-), (*), negate, abs, signum, (/), (^)
         , fromIntegral, truncate, round, ceiling, floor
         , properFraction)
import qualified Prelude
import Data.Char

type List a = [a]
type ListP a = List a
type a :* b = (a , b)
-- type Nat = Int

-- Lists

-- cons :: a -> List a -> List a
-- cons = (GTypes.:)

head :: List a -> a
head = Prelude.head

tail :: List a -> List a
tail = Prelude.tail

init :: List a -> List a
init = Prelude.init

last :: List a -> a
last = Prelude.last

(++) :: List a -> List a -> List a
(++) = (Prelude.++)

concat :: List (List a) -> List a
concat = Prelude.concat

concatMap :: (a -> List b) -> List a -> List b
concatMap = Prelude.concatMap

take :: Int -> List a -> List a
take = Prelude.take

drop :: Int -> List a -> List a
drop = Prelude.drop

takeWhile :: (a -> Bool) -> List a -> List a
takeWhile = Prelude.takeWhile

dropWhile :: (a -> Bool) -> List a -> List a
dropWhile = Prelude.dropWhile

filter :: (a -> Bool) -> List a -> List a
filter = Prelude.filter

zip :: List a -> List b -> List (a, b)
zip = Prelude.zip

unzip :: List (a, b) -> (List a, List b)
unzip = Prelude.unzip

map :: (a -> b) -> List a -> List b
map = Prelude.map

foldr :: (a -> b -> b) -> b -> List a -> b
foldr = Prelude.foldr

foldr1 :: (a -> a -> a) -> List a -> a
foldr1 = Prelude.foldr1

foldl :: (b -> a -> b) -> b -> List a -> b
foldl = Prelude.foldl

foldl1 :: (a -> a -> a) -> List a -> a
foldl1 = Prelude.foldl1

null :: List a -> Bool
null = Prelude.null

length :: List a -> Int
length = Prelude.length

sum :: Num a => List a -> a
sum = Prelude.sum

product :: Num a => List a -> a
product = Prelude.product

elem :: Eq a => a -> List a -> Bool
elem = Prelude.elem

notElem :: Eq a => a -> List a -> Bool
notElem = Prelude.notElem

maximum :: Ord a => List a -> a
maximum = Prelude.maximum

minimum :: Ord a => List a -> a
minimum = Prelude.minimum

and :: List Bool -> Bool
and = Prelude.and

or :: List Bool -> Bool
or = Prelude.or

any :: (a -> Bool) -> List a -> Bool
any = Prelude.any

all :: (a -> Bool) -> List a -> Bool
all = Prelude.all

-- Arithmetics

infixl 7 *, /
infixl 6 +, -

(+), (-), (*) :: Int -> Int -> Int
(+) = (Prelude.+)
(-) = (Prelude.-)
(*) = (Prelude.*)

negate, abs, signum :: Int -> Int
negate = Prelude.negate
abs    = Prelude.abs
signum = Prelude.signum

-- Nat

data Nat = Zero | Suc Nat

infixl 7 *:
infixl 6 +:

(+:) :: Nat -> Nat -> Nat
Zero +: n = n
(Suc m) +: n = Suc (m +: n)

(*:) :: Nat -> Nat -> Nat
Zero *: n = Zero
(Suc m) *: n = n +: (m *: n)

(-:) :: Nat -> Nat -> Nat
m     -: Zero  = m
Zero  -: n     = Zero
Suc m -: Suc n = m -: n

toInt :: Nat -> Int
toInt Zero    = 0
toInt (Suc m) = 1 + toInt m

fromInt :: Int -> Nat
fromInt n | n > 0 = Suc (fromInt ((Prelude.-) n 1))
          | otherwise = Zero

instance Eq Nat where
  Zero  == Zero  = True
  Suc m == Suc n = m == n
  _     == _     = False

instance Num Nat where
  (+) = (+:)
  (*) = (*:)
  (-) = (-:)
  abs = id
  signum _ = Suc Zero
  fromInteger 0 = Zero
  fromInteger n | n > 0 = Suc (fromInteger ((Prelude.-) n 1))
                | otherwise = Zero

instance Show Nat where
  show n = show (toInt n)

instance Ord Nat where
  compare Zero    Zero    = EQ
  compare Zero    (Suc n) = LT
  compare (Suc m) Zero    = GT
  compare (Suc m) (Suc n) = compare m n

instance Enum Nat where
  succ = Suc
  pred Zero = Zero
  pred (Suc n) = n
  toEnum   = fromInt
  fromEnum = toInt

-- Float

infixl 7 *., /.
infixl 6 +., -.

(+.), (-.), (*.) :: Float -> Float -> Float
(+.) = (Prelude.+)
(-.) = (Prelude.-)
(*.) = (Prelude.*)

(/), (/.) :: Float -> Float -> Float
(/)  = (Prelude./)
(/.) = (Prelude./)

infixr 8 ^, ^.

(^) :: Int -> Int -> Int
(^) = (Prelude.^)

(^.) :: Float -> Int -> Float
(^.) = (Prelude.^)

fromIntegral :: Int -> Float
fromIntegral = Prelude.fromIntegral

truncate, round, ceiling, floor :: Float -> Int
truncate = Prelude.truncate
round = Prelude.round
ceiling = Prelude.ceiling
floor = Prelude.floor

properFraction :: Float -> (Int, Float)
properFraction = Prelude.properFraction

-- equality
infixr 0 ===, <=>, <==
(===) :: a -> a -> a
(===) = undefined
(<=>) :: Bool -> Bool -> Bool
(<=>) = undefined
(<==) :: Bool -> Bool -> Bool
(<==) = undefined

-- raising precedence of ($) a bit to allow (===)
infixr 1 $

($) = (Prelude.$)
