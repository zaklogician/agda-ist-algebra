{-# OPTIONS --omega-in-omega --no-pattern-matching #-}

module IST.MetricSpaces where

open import Agda.Primitive
open import IST.Safe.MetricSpaces public

open import IST.Base
open SafeImportTools

st-MetricSpace : st MetricSpace
st-MetricSpace = declared-in-safe-module MetricSpace

st-MetricSpace-Carrier : st MetricSpace.Carrier
st-MetricSpace-Carrier = declared-in-safe-module MetricSpace.Carrier

st-MetricSpace-distance : st MetricSpace.distance
st-MetricSpace-distance = declared-in-safe-module MetricSpace.distance

st-MetricSpace-Carrier-full : (M : MetricSpace) → st M → st (MetricSpace.Carrier M)
st-MetricSpace-Carrier-full M st-M = st-fun _ _ MetricSpace.Carrier M st-MetricSpace-Carrier st-M

st-MetricSpace-distance-full : (M : MetricSpace) → st M → st (MetricSpace.distance M)
st-MetricSpace-distance-full M st-M = declared-in-safe-module (MetricSpace.distance M) 
