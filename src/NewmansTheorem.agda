{-# OPTIONS --omega-in-omega --no-pattern-matching #-}

module IST.NewmansTheorem where

open import Agda.Primitive
open import IST.Safe.NewmansTheorem public

open import IST.Base
open SafeImportTools

st-NewmanSpace : st NewmanSpace
st-NewmanSpace = declared-in-safe-module NewmanSpace

st-NewmanSpace-asMetricSpace : st NewmanSpace.asMetricSpace
st-NewmanSpace-asMetricSpace = declared-in-safe-module NewmanSpace.asMetricSpace

st-NewmanSpace-inhabitant : st NewmanSpace.inhabitant
st-NewmanSpace-inhabitant = declared-in-safe-module NewmanSpace.inhabitant

st-NewmanSpace-newman-constant : st NewmanSpace.newman-constant
st-NewmanSpace-newman-constant = declared-in-safe-module NewmanSpace.newman-constant
