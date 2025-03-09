{-# Language DataKinds #-}
{-# Language DeriveGeneric #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language GADTs #-}
{-# Language KindSignatures #-}
{-# Language MultiParamTypeClasses #-}
{-# Language OverloadedStrings #-}
{-# Language RankNTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language StrictData #-}
{-# Language TupleSections #-}
{-# OPTIONS_GHC -Wwarn #-}
module Main (main) where

import           Hedgehog
import           Hedgehog.Function
import qualified Hedgehog.Gen                  as Gen
import           Hedgehog.Range

import qualified Data.List.NonEmpty            as NE
import qualified Data.Map.Strict               as M
import qualified Data.Set                      as S
import Data.Text (Text)
import Data.Set (Set)
import Data.Map (Map)
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.List (sortBy, groupBy)
import Data.Ord (comparing)
import Data.Function (on)
import Control.Category ((>>>))
import Data.Maybe
import Control.Monad (void)


main :: IO ()
main = void . checkSequential $ Group "HedgehogFnShrinkTest" [
      ("shrink_fails", prop_shrink_fails)
    ]


newtype K = K Int
    deriving (Eq, Ord, Show, Generic, Num)

instance Vary K
instance Arg K

newtype V = VInt Int
    deriving (Eq, Ord, Show, Generic, Num)


instance Vary V
instance Arg V

data TRes = TRes
    { tresNaive  :: [(K, V)]
    }


-- | NOTE: it seems during shrinking on certain conditions Fn will error out
-- with 'empty generator in function'. Trying to rerun and getting a different
-- shrink path can work then.
data Ops
    = MapValuesOp (Fn K (Fn V V))
    | RekeyIndependentlyOp {- [(K,V)] -}  (Fn K (Fn V [(K,V)]))
    | RekeyIndependentlyWithCombinerOp (Fn K (Fn V [(K,V)])) (VSetFn (Maybe V))
    | RekeyMonotonicOp
    | ReduceByKeyOp ({-Fn K-} (VSetFn (Maybe V)))
    | ReduceByKeyPrefixOp {- div factor as prefix fun -} Int (Fn {-prefix-} K (VSetFn (Maybe V)))
    | PersistedOp
  deriving Show


_opName :: Ops -> Text
_opName o = case o of
    MapValuesOp _ -> "MapValuesOp"
    RekeyIndependentlyOp _ -> "RekeyIndependentlyOp"
    RekeyIndependentlyWithCombinerOp _ _ -> "RekeyIndependentlyWithCombinerOp"
    RekeyMonotonicOp -> "RekeyMonotonicOp"
    ReduceByKeyOp _ -> "ReduceByKeyOp"
    ReduceByKeyPrefixOp _ _ -> "ReduceByKeyPrefixOp"
    PersistedOp -> "PersistedOp"

kKeySmall, kValueSmall :: Int
kKeySmall = 20
kValueSmall = 20

data VSetFn r
    = AllInSet (Map (Set V) r) r
    | AnyInSet (Set V) r r
    | Single (Fn K (Fn V r)) r
  deriving Show

genVsetFn :: Gen r -> Gen (VSetFn r)
genVsetFn gr = Gen.choice
    [ do
        ps <- Gen.list
            (linear 1 2)
            ((,) <$> (S.fromList <$> Gen.list (linear 1 3) gv) <*> gr)
        AllInSet (M.fromList ps) <$> gr
    , do
        vs <- S.fromList <$> Gen.list (linear 1 3) gv
        AnyInSet vs <$> gr <*> gr
    , Single <$> fn (fn gr) <*> gr
    ]
    where
    -- | Sufficiently small values, so set has chance to match.
          gv = genV kValueSmall

genV :: Int -> Gen V
genV maxValueSize = VInt <$> Gen.int (linear 0 maxValueSize)

genOp :: Gen Ops
genOp = Gen.choice
    [ MapValuesOp <$> fn (fn gv)
    , RekeyIndependentlyOp <$> fn (fn gkvs)
    ,RekeyIndependentlyWithCombinerOp <$> fn (fn gkvs) <*> genVsetFn gmv
    ,ReduceByKeyOp <$> {- fn -} (genVsetFn gmv)
    ,ReduceByKeyPrefixOp <$> Gen.element [1,2,4,8] <*> fn (genVsetFn gmv)
    , pure RekeyMonotonicOp
    ,pure PersistedOp
    ]
  where
    gv   = genV kValueSmall
    gkvs = Gen.list (linear 0 3) (genKV kKeySmall kValueSmall)
    gmv  = Gen.choice [pure Nothing, Just <$> gv]

genKV :: Int -> Int -> Gen (K, V)
genKV maxKeySize maxValueSize = do
    k <- K <$> Gen.int (linear 1 maxKeySize)
    v <- genV maxValueSize
    pure $! (k, v)

performOps :: Bool -> [Ops] -> TRes -> TRes
performOps ruined = go (0 :: Int)
  where
    go _ [] r = r
    go n (o : rest) (TRes vs) =
            go
                (n + 1)
                rest
                ( case o of
                        MapValuesOp sf -> doMapValues n sf vs
                        RekeyIndependentlyOp sf ->
                            doRekeyIndependently sf vs
                        RekeyIndependentlyWithCombinerOp sf comb ->
                            doRekeyIndependentlyWithCombiner sf
                                                             comb
                                                             vs
                        ReduceByKeyOp sf -> doReduceByKey sf vs
                        ReduceByKeyPrefixOp dscale sf ->
                            doReduceByKeyPrefix dscale sf vs
                        PersistedOp      -> doPersist vs
                        -- Can't exec these on Dup.
                        RekeyMonotonicOp -> TRes vs
                )
    --
    doPersist vs = TRes vs
    doMapValues n sf vs =
        let f  = apply . apply sf
            moddy x = if ruined && n == 4 && x == 9 then x+1  -- artificial ruining of test run here, to trigger shrink
                       else x
            ns = map (\(k, v) -> (k, moddy (f k v))) vs
        in  TRes ns
    doRekeyIndependently sf vs =
        let f  = apply . (apply sf)
            -- f = const (const sf)
            ns = sortOn fst (vs >>= (\(k, v) -> f k v))
        in  TRes ns
    doRekeyIndependentlyWithCombiner sf comb vs =
        let
            f  = apply . (apply sf)
            fc = applyVfs comb
            ns =
                sortOn fst (vs >>= (\(k, v) -> f k v))
                    &>  NE.groupBy ((==) `on` fst)
                    >>> mapMaybe
                            (\(ka :| kas) ->
                                let k = fst ka
                                in  (k, ) <$> fc k (snd ka) (map snd kas)
                            )
        in
            TRes ns
    doReduceByKey sf vs =
        let
            f = applyVfs sf
            ns = vs &> NE.groupBy ((==) `on` fst) >>> mapMaybe
                (\(ka :| kas) ->
                    let k = fst ka in (k, ) <$> f k (snd ka) (map snd kas)
                )
        in
            TRes ns
    doReduceByKeyPrefix dscale sf vs =
        let f    = applyVfs . apply sf
            pref = \(K x) -> K (x `div` dscale)
            ns = vs &> NE.groupBy ((==) `on` (pref . fst)) >>> mapMaybe
                (\(ka :| kas) ->
                    let k = fst ka
                        p = pref k
                    in  (p, ) <$> f p k (snd ka) (map snd kas)
                )
        in  TRes ns

    --
    applyVfs sf k a as =
        let inset = S.fromList (a : as)
        in  case sf of
                AllInSet mr dr -> fromMaybe dr (M.lookup inset mr)
                AnyInSet ss hit miss ->
                    if any (flip S.member ss) (a : as) then hit else miss
                Single gf dr -> if null as then apply (apply gf k) a else dr


prop_shrink_fails :: Property
prop_shrink_fails = withTests 5000 . property $ do
    sortedKvs   <- do
        kvs <- forAll $ Gen.list (linear 1 {-X-} 5) (genKV kKeySmall kValueSmall)
        -- let kvs = [(K 7, VInt 4)]
        pure $! sortOn fst kvs
    ops <- forAll $ Gen.list (linear 1 {-X-} 6) genOp
    footnoteShow ("sortedIn" :: Text, sortedKvs)
    let tresIn    = TRes sortedKvs
        tresOut = performOps False ops tresIn
        tresOutRuined = performOps True ops tresIn
    -- print ops  -- actually this will loop on some (unreduced?) Fn values?
    let (naiveOut, readKvs) = (tresNaive tresOut, tresNaive tresOutRuined)
    footnoteShow ("naiveOut" :: Text, naiveOut, readKvs)
    ((===) `on` subsortOnSameKeys) naiveOut readKvs

subsortOnSameKeys :: (Ord a, Ord b) => [(a, b)] -> [(a, b)]
subsortOnSameKeys = concatMap (sortOn snd) . groupBy ((==) `on` fst)


-- * Protolude stuff

sortOn :: (Ord o) => (a -> o) -> [a] -> [a]
sortOn = sortBy . comparing

-- * Some custom stuff

infixr 0 &>

-- | Flipped apply with precedence 0, so it plays nicely with (>>>) which is
-- precedence 1.
(&>) :: a -> (a -> b) -> b
(&>) = flip ($)


