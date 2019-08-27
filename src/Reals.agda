{-# OPTIONS --omega-in-omega --no-pattern-matching #-}

module IST.Reals where

open import IST.Safe.Reals public

open import IST.Base
open SafeImportTools

st-ℝ : st ℝ
st-ℝ = declared-in-safe-module ℝ

st-+ : st _+_
st-+ = declared-in-safe-module _+_

st-minus : st minus
st-minus = declared-in-safe-module minus

st-· : st _·_
st-· = declared-in-safe-module _·_

st-inv : st inv
st-inv = declared-in-safe-module inv

st-< : st _<_
st-< = declared-in-safe-module _<_

st-≤ᵣ : st _≤ᵣ_
st-≤ᵣ = declared-in-safe-module _≤ᵣ_

st-0r : st 0r
st-0r = declared-in-safe-module 0r

st-1r : st 1r
st-1r = declared-in-safe-module 1r

st-inv-v : ∀ x → (e : x ≠ 0r) → st x → st (inv x e)
st-inv-v x e _ = declared-in-safe-module (inv x e)

st-2r : st 2r
st-2r = st-fun _ _ (_+_ 1r) 1r (st-fun _ _ _+_ 1r st-+ st-1r) st-1r

st-1/2r : st 1/2r
st-1/2r = st-inv-v 2r (λ _ → pos-2r) st-2r

st-/2r-v : (x : ℝ) → st x → st (x /2r)
st-/2r-v x st-x = st-fun _ _ (_·_ 1/2r) x (st-fun _ _ _·_ 1/2r st-· st-1/2r) st-x
