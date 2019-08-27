module IST.Safe.Util where

-- Here we define standard constructions from type theory, including
-- the usual dependent sum types and equality. This development
-- takes place in ordinary MLTT/Agda, without the external hierarchy.

open import Agda.Primitive
open import IST.Safe.Base

lemma-product-equality : {ℓ₁ ℓ₂ : Level} {X : Set ℓ₁} {Y : Set ℓ₂} {x₁ x₂ : X} → ∀ {y₁ y₂ : Y} →
                         x₁ ≡ x₂ → y₁ ≡ y₂ → (x₁ , y₁) ≡ (x₂ , y₂)
lemma-product-equality refl refl = refl
