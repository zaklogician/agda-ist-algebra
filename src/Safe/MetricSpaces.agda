module IST.Safe.MetricSpaces where

open import IST.Safe.Base
open import IST.Safe.Reals

record IsMetricSpace
  (Carrier : Set)
  (distance : Carrier → Carrier → ℝ)
  : Set where
  field
    nonnegative : ∀ x y → distance x y < 0r → ⊥
    reflexive-1 : ∀ x y → distance x y ≡ 0r → x ≡ y
    reflexive-2 : ∀ x → distance x x ≡ 0r
    symmetry : ∀ x y → distance x y ≡ distance y x
    triangle-≤ᵣ : ∀ x y z → distance x z ≤ᵣ distance x y + distance y z
  triangle : ∀ x y z b → (distance x y + distance y z < b) → distance x z < b
  triangle x y z b p with triangle-≤ᵣ x y z
  triangle x y z b p | inl eq = transport (sym eq) {λ p → p < b} p
  triangle x y z b p | inr lt = <-tran _ _ _ lt p

record MetricSpace : Set₁ where
  field
    Carrier : Set
    distance : Carrier → Carrier → ℝ
    isMetricSpace : IsMetricSpace Carrier distance
  open IsMetricSpace isMetricSpace public