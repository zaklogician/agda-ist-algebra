{-# OPTIONS --omega-in-omega --no-pattern-matching #-}

module IST.Util where

-- We prove a bunch of useful lemmata.

open import Agda.Primitive
open import IST.Safe.Util public

open import IST.Base

-- If x and y are standard, then so is (x , y).
lemma-pairing : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} → (x : A) → (y : B) →
                st {ℓ₁} {A} x → st {ℓ₂} {B} y → st {ℓ₁ ⊔ ℓ₂} {A ∧ B} (x , y)
lemma-pairing {ℓ₁} {ℓ₂} {A} {B} x y st-x st-y = st-pair-x-y where
  pair : A → B → A ∧ B
  pair = _,_
  st-pair : st pair
  st-pair = st-∃-_,_-full
  st-pair-x : st (pair x)
  st-pair-x = st-fun A (B → A ∧ B) pair x st-pair st-x
  st-pair-x-y : st (pair x y)
  st-pair-x-y = st-fun B (A ∧ B) (pair x) y st-pair-x st-y

lemma-proj₁ : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} → (ab : A ∧ B) → st ab → st (proj₁ ab)
lemma-proj₁ {ℓ₁} {ℓ₂} {A} {B} ab st-ab = st-sproj-ab where
  sproj : A ∧ B → A
  sproj = proj₁
  st-sproj : st sproj
  st-sproj = st-∃-proj₁-full
  st-sproj-ab : st (sproj ab)
  st-sproj-ab = st-fun _ _ sproj ab st-sproj st-ab

lemma-proj₁-d : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : A → Set ℓ₂} → (ab : ∃ λ a → B a) → st ab → st (proj₁ ab)
lemma-proj₁-d {ℓ₁} {ℓ₂} {A} {B} ab st-ab = st-sproj-ab where
  sproj : (∃ λ a → B a) → A
  sproj = proj₁
  st-sproj : st sproj
  st-sproj = st-∃-proj₁-full
  st-sproj-ab : st (sproj ab)
  st-sproj-ab = st-fun _ _ sproj ab st-sproj st-ab

lemma-proj₂ : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} → (ab : A ∧ B) → st ab → st (proj₂ ab)
lemma-proj₂ {ℓ₁} {ℓ₂} {A} {B} ab st-ab = st-sproj-ab where
  sproj : A ∧ B → B
  sproj = proj₂
  st-sproj : st sproj
  st-sproj = st-∃-proj₂-full
  st-sproj-ab : st (sproj ab)
  st-sproj-ab = st-fun _ _ sproj ab st-sproj st-ab

-- If b is standard, then so is any constant function returning b.
lemma-constfun : {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} → {B : Set ℓ₂} → (b : B) → st b → st (λ (a : A) → b)
lemma-constfun {_} {_} {A} {B} b st-b = st-K-b where
  K : B → A → B
  K x y = x
  st-K : st K
  st-K = st-abs-K B A
  st-K-b : st (K b)
  st-K-b = st-fun _ _ K b st-K st-b

lemma-constfun-h : {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} → {B : Set ℓ₂} → (b : B) → st b → st (λ {a : A} → b)
lemma-constfun-h {ℓ₁} {ℓ₂} {A} {B} b st-b = st-K-b where
  K : B → {a : A} → B
  K x {y} = x
  st-K : st K
  st-K = st-abs-K-h B A
  st-K-b : st (λ {a : A} → K b {a})
  st-K-b = st-fun _ _ K b st-K st-b
