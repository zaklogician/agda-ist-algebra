module IST.Safe.Naturals where

open import Agda.Primitive
open import IST.Safe.Base

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-induction : {ℓ : Level} → {φ : ℕ → Set ℓ} →
              φ 0 → (∀ k → φ k → φ (suc k)) → ∀ n → φ n
ℕ-induction base-case inductive-case zero = base-case
ℕ-induction base-case inductive-case (suc n) = inductive-case n (ℕ-induction base-case inductive-case n)

data _≤_ : ℕ → ℕ → Set where
  ≤-zero : {x : ℕ} → 0 ≤ x
  ≤-suc : {x y : ℕ} → x ≤ y → suc x ≤ suc y

≤-tran : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
≤-tran .0 y z ≤-zero q = ≤-zero
≤-tran .(suc _) .(suc _) .(suc _) (≤-suc p) (≤-suc q) = ≤-suc (≤-tran _ _ _ p q)

≤-than-zero : (x : ℕ) → x ≤ 0 → x ≡ 0
≤-than-zero .0 ≤-zero = refl

≤-refl : ∀ x → x ≤ x
≤-refl zero = ≤-zero
≤-refl (suc x) = ≤-suc (≤-refl x)

≤-not-suc : ∀ x → suc x ≤ x → ⊥
≤-not-suc zero ()
≤-not-suc (suc x) (≤-suc p) = ≤-not-suc x p

≤-match : (x y : ℕ) → x ≤ suc y → (x ≤ y) ∨ (x ≡ suc y)
≤-match .0 y ≤-zero = inl ≤-zero
≤-match (suc a) zero (≤-suc p) = inr (cong suc (≤-than-zero a p))
≤-match (suc a) (suc b) (≤-suc p) with ≤-match a b p
≤-match (suc a) (suc b) (≤-suc p) | inl q = inl (≤-suc q)
≤-match (suc a) (suc b) (≤-suc p) | inr q = inr (cong suc q)
