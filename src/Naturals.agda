{-# OPTIONS --omega-in-omega --no-pattern-matching #-}

module IST.Naturals where

open import Agda.Primitive
open import IST.Safe.Naturals public

open import IST.Base
open SafeImportTools

st-ℕ : st {lsuc lzero} ℕ
st-ℕ = declared-in-safe-module ℕ

st-zero : st zero
st-zero = declared-in-safe-module zero

st-suc : st suc
st-suc = declared-in-safe-module suc

st-ℕ-induction : {ℓ : Level} → st λ {φ} → ℕ-induction {ℓ} {φ}
st-ℕ-induction {ℓ} = declared-in-safe-module λ {φ} → ℕ-induction {ℓ} {φ}

st-ℕ-induction-full : {ℓ : Level} → (φ : ℕ → Set ℓ) → st (ℕ-induction {ℓ} {φ})
st-ℕ-induction-full _ = declared-in-safe-module ℕ-induction

st-≤ : st _≤_
st-≤ = declared-in-safe-module _≤_

external-induction : {φ : ℕ → ESet} → φ zero → (∀ k → st k → φ k → φ (suc k)) → ∀ n → st n → φ n
external-induction {φ} base-case inductive-case n st-n =
  ax-Standard-2 φ n st-n (ψ-forall n) where
  ψ : ℕ → Set
  ψ = ⟦ φ ⟧
  st-ψ : st ψ
  st-ψ = ax-Standard-1 φ
  ψ-base : ψ zero
  ψ-base = ax-Standard-3 φ zero st-zero base-case
  ψ-inductive-st : ∀ k → st k → ψ k → ψ (suc k)
  ψ-inductive-st k st-k ψ-k =
    ax-Standard-3 φ (suc k) (st-fun _ _ suc k st-suc st-k) (inductive-case k st-k (ax-Standard-2 φ k st-k ψ-k))
  ψ-inductive : ∀ k → ψ k → ψ (suc k)
  ψ-inductive = ax-Transfer-EI (∀' ℕ (λ k → int' (ψ k → ψ (suc k))))
    (λ k st-k → fromInternal (ψ-inductive-st k st-k))
    (st-ℕ , λ a st-a → st-→ (⟦ φ ⟧ a) (st-fun _ _ ψ a st-ψ st-a)
    (⟦ φ ⟧ (suc a)) (st-fun _ _ ψ (suc a) st-ψ (st-fun _ _ suc a st-suc st-a)))
  ψ-forall : ∀ n → ψ n
  ψ-forall = ℕ-induction ψ-base ψ-inductive

bounded-st : ∀ (b : ℕ) → st b → ∀ (n : ℕ) → n ≤ b → st n
bounded-st = external-induction {λ b → ∀ m → m ≤ b → st m} base-case inductive-case where
  base-case : ∀ m → m ≤ zero → st m
  base-case m m≤0 = transport* (sym (≤-than-zero m m≤0)) {λ n → st {lzero} {ℕ} n} st-zero
  inductive-case : ∀ k → st k → (∀ m → m ≤ k → st m) → ∀ n → n ≤ suc k → st n
  inductive-case k st-k inductive-hypothesis n n≤k+1 =
    by-cases* {lzero} {lzero} {n ≤ k} (st n) case-A case-B (≤-match n k n≤k+1) where
      case-A : n ≤ k → st n
      case-A = inductive-hypothesis n
      st-k+1 : st (suc k)
      st-k+1 = st-fun _ _ suc k st-suc st-k
      case-B : n ≡ suc k → st n
      case-B n-equals-k+1 = transport* (sym n-equals-k+1) {λ n → st {lzero} {ℕ} n} st-k+1
