-- author: Kevin Slagle

{-# LANGUAGE BangPatterns, TupleSections #-}

{-# OPTIONS_GHC -Wall -O -Wno-unused-imports -Wno-unused-top-binds #-}
-- -rtsopts -prof -fprof-auto
-- +RTS -xc -s -p

-- import GHC.Exts (groupWith, sortWith, the)

import Control.Applicative
-- import Control.Exception (assert)
import Control.Monad
import Data.Bifunctor
-- import Data.Bits
import Data.Either
import Data.Function
import Data.Foldable
import Data.List
import Data.Maybe
import Data.Ord
import Data.Tuple
import Data.Traversable
import Debug.Trace
import Safe
import Safe.Exact

import qualified System.IO as IO

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Data.Set (Set)
import qualified Data.Set as Set

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap hiding (fromList, insert, delete, adjust, adjustWithKey, update, updateWithKey)

--

assert :: Bool -> a -> a
assert True  = id
assert False = error "assert"
-- assert _ = id

asserting :: (a -> Bool) -> a -> a
asserting q x = assert (q x) x

todo :: a
todo = undefined

if' :: Bool -> a -> a -> a
if' True  x _ = x
if' False _ y = y

infixr 1 ?
(?) :: Bool -> a -> a -> a
(?) = if'

boole :: Num a => Bool -> a
boole False = 0
boole True  = 1

infixl 7 //
(//) :: Integral a => a -> a -> a
x // y = assert (m==0) d
  where (d,m) = divMod x y

infixr 9 .*
{-# INLINE (.*) #-}
(.*) :: (c -> c') -> (a -> b -> c) -> a -> b -> c'
f .* g = \x y -> f $ g x y

infixl 1 `applyIf'`
applyIf' :: (a -> a) -> (a -> Bool) -> a -> a
applyIf' f q x = if' (q x) (f x) x

justIf :: Bool -> a -> Maybe a
justIf True  = Just
justIf False = const Nothing

justIf' :: (a -> Bool) -> a -> Maybe a
justIf' f x = justIf (f x) x

foreach :: Functor f => f a -> (a -> b) -> f b
foreach = flip fmap

xor'IntSet :: IntSet -> IntSet -> IntSet
xor'IntSet x y = IntSet.union x y `IntSet.difference` IntSet.intersection x y

xor'Set :: Ord a => Set a -> Set a -> Set a
xor'Set x y = Set.union x y `Set.difference` Set.intersection x y

fromList'IntSet :: [Int] -> IntSet
fromList'IntSet xs = assert (length xs == IntSet.size s) s
  where s = IntSet.fromList xs

fromList'Set :: Ord a => [a] -> Set a
fromList'Set xs = assert (length xs == Set.size s) s
  where s = Set.fromList xs

allPairs :: (a -> a -> Bool) -> [a] -> Bool
allPairs f xs = and $ do
  (x:ys) <- tails xs
  y      <- ys
  return $ f x y

-- Z2Matrix

data Z2Mat = Z2Mat (IntMap IntSet) (IntMap IntSet)

fromSymmetric'Z2Mat :: IntMap IntSet -> Z2Mat
fromSymmetric'Z2Mat mat = Z2Mat mat mat

popRow'Z2Mat :: Z2Mat -> Maybe (IntSet, Z2Mat)
popRow'Z2Mat (Z2Mat rows cols) = case IntMap.minViewWithKey rows of
    Nothing               -> Nothing
    Just ((i,row), rows') -> let cols' = IntSet.foldl' (flip $ IntMap.alter $ justIf' (not . IntSet.null) . IntSet.delete i . fromJust) cols row
                             in Just (row, Z2Mat rows' cols')

xorRow'Z2Mat :: IntSet -> Int -> Z2Mat -> Z2Mat
xorRow'Z2Mat row i (Z2Mat rows cols) = Z2Mat rows' cols'
  where rows'     = IntMap.alter (xorMay row . fromJust) i rows
        cols'     = IntSet.foldl' (flip $ IntMap.alter $ maybe (Just i0) $ xorMay i0) cols row
        i0        = IntSet.singleton i
        xorMay    = justIf' (not . IntSet.null) .* xor'IntSet

-- rankZ2

fastRankZ2 :: [IntSet] -> Int
fastRankZ2 rows0 = go 0 $ Z2Mat rowMap colMap
  where
    rowMap = IntMap.fromListWith undefined $ zip [1..] rows0
    colMap = IntMap.fromListWith IntSet.union $ do
             (i,js) <- zip [1..] rows0
             j <- IntSet.toList js
             return (j, IntSet.singleton i)
    go :: Int -> Z2Mat -> Int
    go !n mat_ = case popRow'Z2Mat mat_ of
        Nothing -> n
        Just (row, mat@(Z2Mat _ cols)) -> go (n+1) $
            let j  = IntSet.findMin row
            in case IntMap.lookup j cols of
                    Nothing -> mat
                    Just is -> IntSet.foldl' (flip $ xorRow'Z2Mat row) mat is

-- rankZ2

rankZ2 :: [IntSet] -> Int
rankZ2 = fst . rankZ2_

rankZ2_ :: [IntSet] -> (Int, IntSet->IntSet)
rankZ2_ = foldl' rankZ2__ (0, id)

rankZ2__ :: (Int, IntSet->IntSet) -> IntSet -> (Int, IntSet->IntSet)
rankZ2__ (!n,f) row0 = IntSet.null row
                    ? (n, f)
                    $ (n+1,) $ (xor'IntSet row `applyIf'` memberQ j) . f
    where row = f row0
          j   = findMin row
          findMin x = IntSet.findMin x
          memberQ x y = IntSet.member x y

--

class MShow a where
  mShow :: a -> String

instance MShow Int where
  mShow = show

instance MShow a => MShow [a] where
  mShow xs = "{" ++ concat (intersperse "," $ map mShow xs) ++ "}"

instance (MShow a, MShow b) => MShow (a,b) where
  mShow (x,y) = "{" ++ mShow x ++ "," ++ mShow y ++ "}"

--

type X = [Int]

data Lattice = Lattice { d'L :: Int, ns'L :: [Int] }
  deriving Show

n'L :: Lattice -> Int
n'L = product . ns'L

--

type Maj     = X
type MajProd = Set Maj

type Stab = MajProd

commQ'P :: MajProd -> MajProd -> Bool
commQ'P = (even . Set.size) .* Set.intersection

translate'P :: X -> MajProd -> MajProd
translate'P x = Set.map $ zipWith (+) $ x ++ repeat 0

--

infixl 1 |*|
(|*|) :: MajProd -> MajProd -> MajProd
(|*|) = xor'Set


infix 2 +.
(+.) :: MajProd -> X -> MajProd
(+.) = flip translate'P

--

type Ls = [Int]
type TorusMajProd = IntSet

commQ'TP :: TorusMajProd -> TorusMajProd -> Bool
commQ'TP = (even . IntSet.size) .* IntSet.intersection

i_x :: Ls -> [Int] -> Int
i_x ls x = foldl' (\i (l,x0) -> i*l + mod x0 l) 0 $ zipExact ls x

x_i :: Ls -> Int -> [Int]
x_i ls i0 = map snd $ init $ scanr (\l (i,_) -> divMod i l) (i0,0) ls

finite'P :: Ls -> Lattice -> MajProd -> TorusMajProd
finite'P ls0 l p = assert (length ls0 == d'L l) $
  fromList'IntSet $ map (i_x $ ls0 ++ ns'L l) $ Set.toList p

torus'P :: Ls -> Lattice -> MajProd -> [TorusMajProd]
torus'P ls0 l p = assert (length ls0 == d'L l) $ do
  x <- traverse (\l0 -> [0..l0-1]) ls0
  return $ fromList'IntSet $ foreach (Set.toList p) $
    i_x (ls0 ++ ns'L l) . zipWith (+) (x ++ repeat 0)

degenLog2'S :: Ls -> Lattice -> [Stab] -> Int
degenLog2'S ls0 l stabs = product (ls0 ++ ns'L l) // 2 - rankZ2 stabs'
  where stabs' = assert (allPairs commQ'TP stabs0 || trace "degenLog2'S not all commute" False) stabs0
        stabs0 = concatMap (torus'P ls0 l) stabs

--

type RawMajProd = [Maj]

type RawSigma   = ([Int],Int)
fromRawSigma'P :: RawSigma -> RawMajProd
fromRawSigma'P (x,k) = assert (1<=k && k<=3) $ [x ++ [0], x ++ [k]]

type RawSigmaProd = [RawSigma]
fromRawSigmaProd'P :: [RawSigma] -> MajProd
fromRawSigmaProd'P = fromList'Set . concatMap fromRawSigma'P

majStab'S :: [Int] -> Stab
majStab'S x = fromList'Set $ map ((x++) . pure) [0..3]

majStabs'S :: Lattice -> [Stab]
majStabs'S l = do
  let x = replicate (d'L l) 0
  ks <- traverse (\n -> [0..n-1]) $ init $ ns'L l
  return $ majStab'S $ x ++ ks


-- XY&XZ plane 2+1D topo -> 3+1D topo
-- degen = 2^6 for Ly,Lz multiples of 4
-- 2x 3+1D topo?

hL :: Lattice
hL = Lattice 3 [2,4,4]

hStabs, sMaj :: [Stab]
hStabs = (++sMaj) $ map fromRawSigmaProd'P
       $ map (map $ \([x,y,z,r],k) -> let (z',a) = divMod (y+z) 2 in ([x,y,z',a,r],k))
  [ [([ 0, 0, 1, 0], 1), ([ 0, 0, 1, 1], 1), ([ 0, 0, 1, 2], 1), ([ 0, 0, 1, 3], 1), ([-1, 0, 1, 0], 1), ([-1, 0, 1, 1], 1), ([ 0,-1, 1, 2], 1), ([ 0, 0, 0, 3], 1)], -- z=1 3D charged
    [([ 0, 0, 0, 0], 1), ([ 0, 0, 0, 2], 1), ([-1, 0, 0, 0], 1), ([ 0,-1, 0, 2], 1)], -- z=0 XY-plane charge
    [([ 0, 0, 0, 1], 1), ([ 0, 0, 0, 3], 1), ([-1, 0, 0, 1], 1), ([ 0, 0,-1, 3], 1)], -- z=0 XZ-plane charge
    [([ 0, 0, 0, 0], 3), ([ 1, 0, 0, 2], 3), ([ 0, 0, 0, 2], 3), ([ 0, 1, 0, 0], 3)], -- z=0 XY-plane flux
    [([ 0, 0, 0, 1], 3), ([ 1, 0, 0, 3], 3), ([ 0, 0, 0, 3], 3), ([ 0, 0, 1, 1], 3)], -- z=0 XZ-plane flux
    [([ 0, 0, 1, 0], 3), ([ 1, 0, 1, 2], 3), ([ 0, 0, 1, 2], 3), ([ 0, 1, 1, 0], 3)], -- z=1 XY-plane flux
    [([ 0, 0, 1, 1], 3), ([ 1, 0, 1, 3], 3), ([ 0, 0, 1, 3], 3), ([ 0, 0, 2, 1], 3)], -- z=1 XZ-plane flux
    [([ 0, 0,-1, 2], 3), ([ 0, 1,-1, 2], 3), ([ 0, 2,-1, 3], 3), ([ 0, 2, 0, 3], 3),
     ([ 0, 0,-1, 3], 3), ([ 0, 0, 0, 3], 3), ([ 0, 0, 1, 2], 3), ([ 0, 1, 1, 2], 3)], -- double-size YZ-plane flux
--     [([ 0, 1, 0, 2], 3), ([ 0, 2, 0, 2], 3), ([ 0, 3, 0, 3], 3), ([ 0, 3, 1, 3], 3),
--      ([ 0, 1, 0, 3], 3), ([ 0, 1, 1, 3], 3), ([ 0, 1, 2, 2], 3), ([ 0, 2, 2, 2], 3)], -- double-size YZ-plane flux -- redundant
    [([ 0, 0, 1, 0], 3), ([ 0, 0, 1, 1], 3)]                                          -- z=1 x-axis ZZ from symmetry breaking
  ]
sMaj = majStabs'S hL

main :: IO ()
main = traverse_ print [([l,l,l],degenLog2'S ls hL hStabs) | l <- [4,8..], let ls=[l,l//2,l//2] ]
-- main = traverse_ print [([lx,ly,lz],degenLog2'S ls hL hStabs - 6) | lx <- [2..], ly <- [4,8..lx], lz <- [4,8..ly], let ls=[lx,ly//2,lz//2] ]


-- 3+1D topo -> YZ-plane 2+1D topo
-- degen = 2^Lx for even Lx
-- YZ-plane 2+1D topo with doubled unit cell

-- hL :: Lattice
-- hL = Lattice 3 [2,3,4]
-- 
-- hStabs, sMaj :: [Stab]
-- hStabs = (++sMaj) $ map fromRawSigmaProd'P
--        $ map (map $ \([x,y,z,r],k) -> let (x',a) = divMod x 2 in ([x',y,z,a,r],k))
--   [ [([ 0, 0, 0, 1], 1), ([ 0, 0, 0, 2], 1), ([ 0, 0, 0, 3], 1), ([-1, 0, 0, 1], 1), ([ 0,-1, 0, 2], 1), ([ 0, 0,-1, 3], 1)], -- x=0 3D charge
--     [([ 1, 0, 0, 1], 1), ([ 1, 0, 0, 2], 1), ([ 1, 0, 0, 3], 1), ([ 0, 0, 0, 1], 1), ([ 1,-1, 0, 2], 1), ([ 1, 0,-1, 3], 1)], -- x=1 3D charge
--     [([ 0, 0, 0, 2], 3), ([ 0, 1, 0, 3], 3), ([ 0, 0, 0, 3], 3), ([ 0, 0, 1, 2], 3)], -- x=0 YZ-plane flux
--     [([ 1, 0, 0, 2], 3), ([ 1, 1, 0, 3], 3), ([ 1, 0, 0, 3], 3), ([ 1, 0, 1, 2], 3)], -- x=1 YZ-plane flux
--     [([ 0, 0, 0, 1], 3), ([ 1, 0, 0, 2], 3), ([ 0, 0, 0, 2], 3), ([ 0, 1, 0, 1], 3)], -- x=0 XY-plane flux
--     [([ 0, 0, 0, 1], 3), ([ 1, 0, 0, 3], 3), ([ 0, 0, 0, 3], 3), ([ 0, 0, 1, 1], 3)], -- x=0 XZ-plane flux
--     [([ 1, 0, 0, 1], 1)] -- x=1 x-axis X from symmetry breaking
--   ]
-- sMaj = majStabs'S hL
-- 
-- main :: IO ()
-- main = traverse_ print [([l,l,l],degenLog2'S ls hL hStabs) | l <- [2,4..], let ls=[l//2,l,l] ]
-- -- main = traverse_ print [([lx,ly,lz],degenLog2'S ls hL hStabs - lx) | lx <- [2,4..], ly <- [2..lx], lz <- [2..ly], let ls=[lx//2,ly,lz] ]


-- XY&XZ plane 2+1D topo -> X-cube intermediate phase
-- degen = 2^(Lx+2Ly+2Lz-3) for even Lx
-- X-cube with doubled unit cell?

-- hL :: Lattice
-- hL = Lattice 3 [2,4,4]
-- 
-- hStabs, sMaj :: [Stab]
-- hStabs = (++sMaj) $ map fromRawSigmaProd'P
--        $ map (map $ \([x,y,z,r],k) -> let (x',a) = divMod x 2 in ([x',y,z,a,r],k))
--   [ [([ 0, 0, 0, 0], 3), ([ 1, 0, 0, 2], 3), ([ 0, 0, 0, 2], 3), ([ 0, 1, 0, 0], 3)], -- x=0 XY-plane flux
--     [([ 0, 0, 0, 1], 3), ([ 1, 0, 0, 3], 3), ([ 0, 0, 0, 3], 3), ([ 0, 0, 1, 1], 3)], -- x=0 XZ-plane flux
--     [([ 1, 0, 0, 0], 3), ([ 2, 0, 0, 2], 3), ([ 1, 0, 0, 2], 3), ([ 1, 1, 0, 0], 3),
--      ([ 1, 0, 0, 1], 3), ([ 2, 0, 0, 3], 3), ([ 1, 0, 0, 3], 3), ([ 1, 0, 1, 1], 3),
--      ([ 1, 0, 1, 0], 3), ([ 2, 0, 1, 2], 3), ([ 1, 0, 1, 2], 3), ([ 1, 1, 1, 0], 3),
--      ([ 1, 1, 0, 1], 3), ([ 2, 1, 0, 3], 3), ([ 1, 1, 0, 3], 3), ([ 1, 1, 1, 1], 3)], -- x=1 facton
--     [([ 1, 0, 0, 0], 1), ([ 1, 0, 0, 1], 1)],                                         -- x=1 x-axis XX from symmetry breaking
--     [([ 0, 0, 0, 0], 1), ([ 0, 0, 0, 2], 1), ([-1, 0, 0, 0], 1), ([ 0,-1, 0, 2], 1)], -- x=0 XY-plane charge
--     [([ 0, 0, 0, 1], 1), ([ 0, 0, 0, 3], 1), ([-1, 0, 0, 1], 1), ([ 0, 0,-1, 3], 1)], -- x=0 XZ-plane charge
--     [([ 1, 0, 0, 0], 1), ([ 1, 0, 0, 2], 1), ([ 0, 0, 0, 0], 1), ([ 1,-1, 0, 2], 1)], -- x=1 XY-plane charge
--     [([ 1, 0, 0, 1], 1), ([ 1, 0, 0, 3], 1), ([ 0, 0, 0, 1], 1), ([ 1, 0,-1, 3], 1)]  -- x=1 XZ-plane charge
--   ]
-- sMaj = majStabs'S hL
-- 
-- main :: IO ()
-- main = traverse_ print [([l,l,l],degenLog2'S ls hL hStabs) | l <- [2,4..], let ls=[l//2,l,l] ]
-- -- main = traverse_ print [([lx,ly,lz],degenLog2'S ls hL hStabs - (lx+2*ly+2*lz-3)) | lx <- [2,4..], ly <- [2..lx], lz <- [2..ly], let ls=[lx//2,ly,lz] ]


-- X-cube -> YZ plane intermediate phase
-- degen = 2^(2Lx+3) for Ly,Lz multiples of 4
-- 2x YZ plane toric code + 3D Z2 topo, except(?):
-- a 3D charge can split into two 2D charges (one of each flavor)
-- 2D fluxes are parts of 3D flux loops

-- hL :: Lattice
-- hL = Lattice 3 [2,3,4]
-- 
-- hStabs, sMaj :: [Stab]
-- hStabs = (++sMaj) $ map fromRawSigmaProd'P
--        $ map (map $ \([x,y,z,r],k) -> let (z',a) = divMod (y+z) 2 in ([x,y,z',a,r],k))
--   [ [([-1, 0, 0, 1], 1), ([ 0, 0, 0, 1], 1), ([ 0,-1, 0, 2], 1), ([ 0, 0, 0, 2], 1)], -- z=0 XY-plane charge
--     [([-1, 0, 0, 1], 1), ([ 0, 0, 0, 1], 1), ([ 0, 0,-1, 3], 1), ([ 0, 0, 0, 3], 1)], -- z=0 XZ-plane charge
--     [([ 0,-1, 1, 2], 1), ([ 0, 0, 1, 2], 1), ([ 0, 0, 0, 3], 1), ([ 0, 0, 1, 3], 1)], -- z=1 YZ-plane charge
--     [([ 0, 0, 1, 1], 3)],                                                             -- z=1 x-axis Z
--     [([ 0, 0,-1, 2], 3), ([ 0, 1,-1, 2], 3), ([ 0, 2,-1, 3], 3), ([ 0, 2, 0, 3], 3),
--      ([ 0, 0,-1, 3], 3), ([ 0, 0, 0, 3], 3), ([ 0, 0, 1, 2], 3), ([ 0, 1, 1, 2], 3)], -- double-size YZ-plane flux
--     [([ 0, 0, 0, 1], 3), ([ 0, 0, 0, 2], 3), ([ 0, 0, 0, 3], 3),
--      ([ 0, 1, 1, 1], 3), ([ 1, 0, 0, 2], 3), ([ 1, 0, 0, 3], 3),
--      ([ 0, 1, 0, 1], 3), ([ 1, 0, 1, 2], 3), ([ 0, 1, 0, 3], 3),
--      ([ 0, 0, 1, 1], 3), ([ 0, 0, 1, 2], 3), ([ 1, 1, 0, 3], 3)], -- z=0 fracton
--     [([ 0, 0, 1, 1], 3), ([ 0, 0, 1, 2], 3), ([ 0, 0, 1, 3], 3),
--      ([ 0, 1, 2, 1], 3), ([ 1, 0, 1, 2], 3), ([ 1, 0, 1, 3], 3),
--      ([ 0, 1, 1, 1], 3), ([ 1, 0, 2, 2], 3), ([ 0, 1, 1, 3], 3),
--      ([ 0, 0, 2, 1], 3), ([ 0, 0, 2, 2], 3), ([ 1, 1, 1, 3], 3)]  -- z=1 fracton
--   ]
-- sMaj = majStabs'S hL
-- 
-- main :: IO ()
-- main = traverse_ print [([l,l,l],degenLog2'S ls hL hStabs - (2*l+3)) | l <- [4,8..], let ls=[l,l//2,l//2] ]
-- -- main = traverse_ print [([lx,ly,lz],degenLog2'S ls hL hStabs - (2*lx+3)) | lx <- [2..], ly <- [4,8..lx], lz <- [4,8..ly], let ls=[lx,ly//2,lz//2] ]


-- X-cube
-- degen = 2^(2Lx+2Ly+2Lz-3)

-- hL :: Lattice
-- hL = Lattice 3 [3,4]

-- hStabs, sMaj :: [Stab]
-- hStabs = map fromRawSigmaProd'P
--   [ [([-1, 0, 0, 1], 1), ([ 0, 0, 0, 1], 1), ([ 0,-1, 0, 2], 1), ([ 0, 0, 0, 2], 1)],
--     [([-1, 0, 0, 1], 1), ([ 0, 0, 0, 1], 1), ([ 0, 0,-1, 3], 1), ([ 0, 0, 0, 3], 1)],
--     [([ 0, 0, 0, 1], 3), ([ 0, 0, 0, 2], 3), ([ 0, 0, 0, 3], 3),
--      ([ 0, 1, 1, 1], 3), ([ 1, 0, 0, 2], 3), ([ 1, 0, 0, 3], 3),
--      ([ 0, 1, 0, 1], 3), ([ 1, 0, 1, 2], 3), ([ 0, 1, 0, 3], 3),
--      ([ 0, 0, 1, 1], 3), ([ 0, 0, 1, 2], 3), ([ 1, 1, 0, 3], 3)]
--   ] ++ sMaj
-- sMaj   = majStabs'S hL

-- main :: IO ()
-- main = traverse_ print [(ls,degenLog2'S ls hL hStabs) | l <- [2..], let ls=[l,l,l] ]
-- -- main = traverse_ print [(ls,degenLog2'S ls hL hStabs - (2*lx+2*ly+2*lz-3)) | lx <- [2..], ly <- [2..lx], lz <- [2..ly], let ls=[lx,ly,lz] ]
