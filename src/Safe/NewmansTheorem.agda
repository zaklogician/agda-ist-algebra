module IST.Safe.NewmansTheorem where

open import IST.Safe.Base
open import IST.Safe.Naturals
open import IST.Safe.Reals
open import IST.Safe.MetricSpaces
open import IST.Safe.Groups
open import IST.Safe.GroupActions


-- Formally proving Newman's theorem lies outside the scope of our work, and so
-- we do not give a definition of compact metric manifolds. Instead, we work with
-- Newman spaces: metric spaces that satisfy Corollary 2.3.6. By Newman's theorem
-- (Theorem 2.3.5.) all compact metric manifolds form Newman spaces.

record IsNewmanSpace
  (M : MetricSpace)
  (ν : ℝ)
  : Set₁ where
  open MetricSpace M
  field
    isPositive : 0r < ν
    isNewmanConstant :
      ∀ (G : FiniteGroup) →
      ∀ (g : FiniteGroup.Carrier G) → (g ≡ FiniteGroup.identity G → ⊥) →
      
      ∀ (A : DiscreteAction G M) → 
      
      (∀ (x : FiniteGroup.Carrier G) → (x ≡ FiniteGroup.identity G → ⊥) →
      ∃ λ (m : Carrier) → DiscreteAction.Map A x m ≡ m → ⊥) →
      
      ∃ λ (n : ℕ) → ∃ λ (m : Carrier) → (n ≤ FiniteGroup.order G g) ∧
      (ν < distance m (DiscreteAction.Map A (FiniteGroup.power G g n) m))

record NewmanSpace : Set₁ where
  field
    asMetricSpace : MetricSpace
    inhabitant : MetricSpace.Carrier asMetricSpace
    newman-constant : ℝ
    isNewmanSpace : IsNewmanSpace asMetricSpace newman-constant
  open MetricSpace asMetricSpace public
  open IsNewmanSpace isNewmanSpace public
