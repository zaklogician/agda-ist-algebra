module IST.Safe.FiniteSets where

open import IST.Safe.Base

record IsFiniteSet
  (Carrier : Set)
  : Set where
  field
    list-of-elements : List Carrier
    has-all-elements : (x : Carrier) → x ∈ list-of-elements

record FiniteSet : Set₁ where
  field
    Carrier : Set
    isFiniteSet : IsFiniteSet Carrier
  open IsFiniteSet isFiniteSet public
