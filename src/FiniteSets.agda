{-# OPTIONS --omega-in-omega --no-pattern-matching #-}

module IST.FiniteSets where

open import Agda.Primitive
open import IST.Safe.FiniteSets public

open import IST.Base
open SafeImportTools

st-FiniteSet : st FiniteSet
st-FiniteSet = declared-in-safe-module FiniteSet

st-FiniteSet-Carrier : st FiniteSet.Carrier
st-FiniteSet-Carrier = declared-in-safe-module FiniteSet.Carrier
