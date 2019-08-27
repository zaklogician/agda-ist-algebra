module IST.Safe.Reals where

open import Agda.Primitive
open import IST.Safe.Base

-- We present an ordered field axiomatically. We do not give a completeness axiom.

-- ℝ forms a commutative ring.
infixr 5 _+_
infixr 6 _·_
postulate
  ℝ : Set
  _+_ : ℝ → ℝ → ℝ
  0r : ℝ
  +-comm : ∀ {x y : ℝ} → x + y ≡ y + x
  +-assoc : ∀ {x y z : ℝ} → (x + y) + z ≡ x + (y + z)
  +-unit-left : ∀ {x : ℝ} → 0r + x ≡ x
  minus : ℝ → ℝ
  +-inverse-left : ∀ {x : ℝ} → x + minus x ≡ 0r

  _·_ : ℝ → ℝ → ℝ
  1r : ℝ
  ·-comm : ∀ {x y : ℝ} → x · y ≡ y · x
  ·-assoc : ∀ {x y z : ℝ} → (x · y) · z ≡ x · (y · z)
  ·-unit-left : ∀ {x : ℝ} → 1r · x ≡ x
  ·-null-left : ∀ {x : ℝ} → x · 0r ≡ 0r
  
  distr-left : ∀ {x y z : ℝ} → x · (y + z) ≡ x · y + x · z

-- The right laws follow by commutativity.

+-unit-right : ∀ {x : ℝ} → x + 0r ≡ x
+-unit-right = tran +-comm +-unit-left

·-unit-right : ∀ {x : ℝ} → x · 1r ≡ x
·-unit-right = tran ·-comm ·-unit-left

·-null-right : ∀ {x : ℝ} → 0r · x ≡ 0r
·-null-right = tran ·-comm ·-null-left

distr-right : ∀ {x y z : ℝ} → (x + y) · z ≡ x · z + y · z
distr-right {x} {y} {z} = step-3 where
  step-1 : z · x + z · y ≡ x · z + z · y
  step-1 = cong (λ p → p + z · y) ·-comm
  step-2 : x · z + z · y ≡ x · z + y · z
  step-2 = cong (λ p → x · z + p) ·-comm
  step-3 : (x + y) · z ≡ x · z + y · z
  step-3 = tran (tran (tran ·-comm distr-left) step-1) step-2

-- ℝ forms an ordered commutative ring.

infix 4 _<_
infix 4 _≤ᵣ_
postulate
  _<_ : ℝ → ℝ → Set
  <-trichotomy-strong : ∀ x y → (x ≡ y) ∨ ((x < y) ∨ (y < x))
  <-asym-1 : ∀ x y → x < y → x ≡ y → ⊥
  <-asym-2 : ∀ x y → x < y → y < x → ⊥ 
  <-tran : ∀ x y z → x < y → y < z → x < z
  <-plus : ∀ x y c → x < y → x + c < y + c
  <-mult : ∀ x y c → 0r < c → x < y → c · x < c · y
  <-nontrivial : 0r < 1r

-- ℝ forms a field

_≠_ : ℝ → ℝ → Set
x ≠ y = ((x < y) → ⊥) → y < x

postulate
  inv : (r : ℝ) → (r ≠ 0r) → ℝ
  ·-inverse-left : ∀ {x : ℝ} → (p : x ≠ 0r) → inv x p · x ≡ 1r
  
+-inverse-right : ∀ {x : ℝ} → minus x + x ≡ 0r
+-inverse-right = tran +-comm +-inverse-left

·-inverse-right : ∀ {x : ℝ} → (x≠0 : x ≠ 0r) → x · inv x x≠0 ≡ 1r
·-inverse-right x≠0 = tran ·-comm (·-inverse-left x≠0)

-- We state and prove some useful elementary theorems about ℝ.

·-minus : ∀ {x : ℝ} → minus x ≡ (minus 1r) · x
·-minus {x} = sym step-9 where
  step-1 : x + minus 1r · x ≡ (1r · x) + minus 1r · x
  step-1 = cong (λ p → p + minus 1r · x) (sym (·-unit-left))
  step-2 : 1r · x + minus 1r · x ≡ (1r + minus 1r) · x
  step-2 = sym (distr-right)
  step-3 : (1r + minus 1r) · x ≡ 0r
  step-3 = tran (cong (λ p → p · x) +-inverse-left) ·-null-right
  step-4 : x + minus 1r · x ≡ 0r
  step-4 = tran (tran step-1 step-2) step-3
  step-5 : minus x + (x + minus 1r · x) ≡ minus x + 0r
  step-5 = cong (λ p → minus x + p) step-4
  step-6 : minus x + (x + minus 1r · x) ≡ minus x
  step-6 = tran step-5 +-unit-right
  step-7 : (minus x + x) + minus 1r · x ≡ minus x
  step-7 = tran +-assoc step-6
  step-8 : 0r + minus 1r · x ≡ minus x
  step-8 = tran (cong (λ p → p + minus 1r · x) (sym +-inverse-right)) step-7
  step-9 : minus 1r · x ≡ minus x
  step-9 = tran (sym +-unit-left) step-8

<-trichotomy : ∀ {φ : Set} → ∀ x y → (x < y → φ) → (x ≡ y → φ) → (y < x → φ) → φ
<-trichotomy {φ} x y p q r with <-trichotomy-strong x y
<-trichotomy {φ} x y p q r | inl x-equals-y = q x-equals-y
<-trichotomy {φ} x y p q r | inr (inl x-under-y) = p x-under-y
<-trichotomy {φ} x y p q r | inr (inr y-under-x) = r y-under-x

<-minus : ∀ {x : ℝ} → 0r < x → minus x < 0r
<-minus {x} positive-x = <-trichotomy 0r (minus x)
  (λ z → absurd (not-positive z))
  (λ z → absurd (not-zero z))
  (λ z → z) where
  not-positive : 0r < minus x → ⊥
  not-positive positive-minus-x = <-asym-2 0r x positive-x negative-x  where
    step-1 : 0r + x < minus x + x
    step-1 = <-plus 0r (minus x) x positive-minus-x
    step-2 : 0r + x < 0r
    step-2 = transport +-inverse-right {λ p → 0r + x < p} step-1
    negative-x : x < 0r
    negative-x = transport +-unit-left {λ p → p < 0r} step-2
  not-zero : 0r ≡ minus x → ⊥
  not-zero zero-minus-x = <-asym-1 0r x positive-x (sym zero-x) where
    step-1 : x + 0r ≡ 0r
    step-1 = transport (sym zero-minus-x) {λ p → x + p ≡ 0r} +-inverse-left
    zero-x : x ≡ 0r
    zero-x = transport (+-unit-right {x}) {λ p → p ≡ 0r} step-1

<-inverse : ∀ {x : ℝ} → (p : 0r < x) → 0r < inv x (λ _ → p)
<-inverse {x} p = <-trichotomy 0r (inv x (λ _ → p))
  (λ z → z)
  (λ z → absurd (not-zero z))
  (λ z → absurd (not-negative z)) where
  not-zero : 0r ≡ inv x (λ _ → p) → ⊥
  not-zero 0r-inverse = <-asym-1 _ _ <-nontrivial step-3 where
    step-1 : 0r · x ≡ inv x (λ _ → p) · x
    step-1 = cong (λ p → p · x) 0r-inverse
    step-2 : 0r · x ≡ 1r
    step-2 = tran step-1 (·-inverse-left (λ _ → p))
    step-3 : 0r ≡ 1r
    step-3 = tran (sym ·-null-right) step-2
  not-negative : inv x (λ _ → p) < 0r → ⊥
  not-negative negative-invx = <-asym-2 _ _ <-nontrivial step-3 where
    x' : ℝ
    x' = inv x (λ _ → p)
    step-1 : x · x' < x · 0r
    step-1 = <-mult x' 0r x p negative-invx
    step-2 : 1r < x · 0r
    step-2 = transport (·-inverse-right (λ _ → p)) {λ p → p < x · 0r} step-1
    step-3 : 1r < 0r
    step-3 = transport ·-null-left {λ p → 1r < p} step-2

<-plus-both : ∀ (x X y Y : ℝ) → x < X → y < Y → x + y < X + Y
<-plus-both x X y Y p q = <-tran _ _ _ step-1 step-4 where
  step-1 : x + y < X + y
  step-1 = <-plus x X y p
  step-2 : y + X < Y + X
  step-2 = <-plus y Y X q
  step-3 : X + y < Y + X
  step-3 = transport (+-comm {y} {X}) {λ z → z < Y + X} step-2 
  step-4 : X + y < X + Y
  step-4 = transport (+-comm {Y} {X}) {λ z → X + y < z} step-3

<-plus-left : ∀ x y c → x < y → (c + x) < (c + y)
<-plus-left x y c p = step-3 where
  step-1 : x + c < y + c
  step-1 = <-plus x y c p
  step-2 : c + x < y + c
  step-2 = transport +-comm {λ p → p < y + c} step-1
  step-3 : c + x < c + y
  step-3 = transport +-comm {λ p → c + x < p} step-2

lemma-ε-of-room : ∀ (x : ℝ) → (∀ (ε : ℝ) → 0r < ε → x < ε) → (x < 0r → ⊥) → x ≡ 0r
lemma-ε-of-room x x<ε x≥0 = <-trichotomy {x ≡ 0r} x 0r
  (λ z → absurd (x≥0 z))
  (λ z → z)
  (λ z → absurd (<-asym-2 x x (x<ε x z) (x<ε x z)))

lemma-ε-of-room-plus : ∀ (x y : ℝ) → (∀ (ε : ℝ) → 0r < ε → x < y + ε) → (x ≡ y → ⊥) → x < y
lemma-ε-of-room-plus x y x<ε x≥y = <-trichotomy {x < y} x y
  (λ z → z)
  (λ z → absurd (x≥y z))
  (λ z → x<y z) where
    0<x-y : y < x → 0r < x + minus y
    0<x-y y<x = absurd (<-asym-1 x x x<x refl) where
      step-1 : y + minus y < x + minus y
      step-1 = <-plus y x (minus y) y<x
      step-2 : 0r < x + minus y
      step-2 = transport +-inverse-left {λ z → z < x + minus y} step-1
      step-3 : x < y + x + minus y
      step-3 = x<ε (x + minus y) step-2
      step-4 : y + x + minus y ≡ y + minus y + x
      step-4 = cong (λ z → y + z) (+-comm {x} {minus y})
      step-5 : (y + minus y) + x ≡ x
      step-5 = tran (cong (λ z → z + x) +-inverse-left) +-unit-left
      step-6 : y + x + minus y ≡ x
      step-6 = tran step-4 (tran (sym +-assoc) step-5)
      x<x : x < x
      x<x = transport step-6 {λ z → x < z} step-3
    x<y : y < x → x < y
    x<y y<x = absurd (<-asym-1 x x x<x refl) where
      x<y+x-y : x < y + x + minus y
      x<y+x-y = x<ε (x + minus y) (0<x-y y<x)
      y+x-y-equals-x : y + x + minus y ≡ x
      y+x-y-equals-x =
        tran (cong (λ z → y + z) +-comm)
        (tran (sym +-assoc) (tran (cong (λ z → z + x) +-inverse-left) +-unit-left))
      x<x : x < x
      x<x = transport y+x-y-equals-x {λ z → x < z} x<y+x-y

-- We prove some theorems about 1/2 that we need to work with metric spaces.

2r : ℝ
2r = 1r + 1r

pos-2r : 0r < 2r
pos-2r = <-tran 0r 1r 2r <-nontrivial step-2 where
  step-1 : 0r + 1r < 1r + 1r
  step-1 = <-plus 0r 1r 1r <-nontrivial
  step-2 : 1r < 1r + 1r
  step-2 = transport +-unit-left {λ p → p < 1r + 1r} step-1

1r-less-than-2r : 1r < 2r
1r-less-than-2r = step-2 where
  step-1 : 0r + 1r < 1r + 1r
  step-1 = <-plus 0r 1r 1r <-nontrivial
  step-2 : 1r < 1r + 1r
  step-2 = transport +-unit-left {λ p → p < 1r + 1r} step-1

1/2r : ℝ
1/2r = inv 2r (λ _ → pos-2r)

pos-1/2r : 0r < 1/2r
pos-1/2r = <-inverse pos-2r

1/2r-less-than-1r : 1/2r < 1r
1/2r-less-than-1r = step-3 where
  step-1 : 1/2r · 1r < 1/2r · 2r
  step-1 = <-mult 1r 2r 1/2r pos-1/2r 1r-less-than-2r
  step-2 : 1/2r < 1/2r · 2r
  step-2 = transport ·-unit-right {λ p → p < 1/2r · 2r} step-1
  step-3 : 1/2r < 1r
  step-3 = transport (·-inverse-left (λ _ → pos-2r)) {λ p → 1/2r < p} step-2

1/2r-half : 1/2r + 1/2r ≡ 1r
1/2r-half = tran step-6 (tran step-5 (tran step-4 step-3)) where
  step-1 : 2r · (1/2r + 1/2r) ≡ 2r · 1/2r + 2r · 1/2r
  step-1 = distr-left {2r} {1/2r} {1/2r}
  step-2 : 2r · 1/2r + 2r · 1/2r ≡ 2r
  step-2 = cong (λ p → p + p) (·-inverse-right (λ _ → pos-2r))
  step-3 : 1/2r · 2r · (1/2r + 1/2r) ≡ 1r
  step-3 = tran (cong (λ p → 1/2r · p) (tran step-1 step-2)) (·-inverse-left (λ _ → pos-2r))
  step-4 : (1/2r · 2r) · (1/2r + 1/2r) ≡ 1/2r · 2r · (1/2r + 1/2r)
  step-4 = ·-assoc
  step-5 : 1r · (1/2r + 1/2r) ≡ (1/2r · 2r) · (1/2r + 1/2r)
  step-5 = cong (λ p → p · (1/2r + 1/2r)) (sym (·-inverse-left (λ _ → pos-2r)))
  step-6 : 1/2r + 1/2r ≡ 1r · (1/2r + 1/2r)
  step-6 = sym ·-unit-left

_/2r : ℝ → ℝ
x /2r = 1/2r · x

pos-/2r-v : (x : ℝ) → 0r < x → 0r < x /2r
pos-/2r-v x pos-x = transport ·-null-left {λ p → p < 1/2r · x} (<-mult 0r x 1/2r pos-1/2r pos-x)

x/2r-less-than-x : (x : ℝ) → 0r < x → (x /2r) < x
x/2r-less-than-x x pos-x = step-3 where
  step-1 : x · 1/2r < x · 1r
  step-1 = <-mult 1/2r 1r x pos-x 1/2r-less-than-1r
  step-2 : x /2r < x · 1r
  step-2 = transport (·-comm {x} {1/2r}) {λ p → p < x · 1r} step-1
  step-3 : x /2r < x
  step-3 = transport (·-unit-right {x}) {λ p → x /2r < p} step-2

/2r-half : ∀ {x : ℝ} → x /2r + x /2r ≡ x
/2r-half {x} = tran step-1 step-2 where
  step-1 : x /2r + x /2r ≡ (1/2r + 1/2r) · x
  step-1 = sym (distr-right {1/2r} {1/2r} {x})
  step-2 : (1/2r + 1/2r) · x ≡ x
  step-2 = tran (cong (λ p → p · x) 1/2r-half) ·-unit-left

-- We prove some results about ≤ that we need for Lipschitz conditions.

_≤ᵣ_ : ℝ → ℝ → Set
a ≤ᵣ b = (a ≡ b) ∨ (a < b)

≤ᵣ-tran : ∀ x y z → x ≤ᵣ y → y ≤ᵣ z → x ≤ᵣ z
≤ᵣ-tran x .x .x (inl refl) (inl refl) = inl refl
≤ᵣ-tran x .x z (inl refl) (inr p) = inr p
≤ᵣ-tran x y .y (inr p) (inl refl) = inr p
≤ᵣ-tran x y z (inr p) (inr q) = inr (<-tran x y z p q)
≤ᵣ-plus : ∀ x y c → x ≤ᵣ y → (x + c) ≤ᵣ (y + c)
≤ᵣ-plus x .x c (inl refl) = inl refl
≤ᵣ-plus x y c (inr p) = inr (<-plus x y c p)
≤ᵣ-mult : ∀ x y c → 0r ≤ᵣ c → x ≤ᵣ y → (c · x) ≤ᵣ (c · y)
≤ᵣ-mult x .x .0r (inl refl) (inl refl) = inl refl
≤ᵣ-mult x y .0r (inl refl) (inr q) = inl (tran ·-null-right (sym ·-null-right))
≤ᵣ-mult x .x c (inr p) (inl refl) = inl refl
≤ᵣ-mult x y c (inr p) (inr q) = inr (<-mult x y c p q)
≤ᵣ-nontrivial : 0r ≤ᵣ 1r
≤ᵣ-nontrivial = inr <-nontrivial

≤ᵣ-minus : ∀ {x : ℝ} → 0r ≤ᵣ x → minus x ≤ᵣ 0r
≤ᵣ-minus (inl refl) = inl (tran (sym +-unit-left) +-inverse-left)
≤ᵣ-minus (inr p) = inr (<-minus p)

≤ᵣ-plus-both : ∀ (x X y Y : ℝ) → x ≤ᵣ X → y ≤ᵣ Y → x + y ≤ᵣ X + Y
≤ᵣ-plus-both x .x y .y (inl refl) (inl refl) = inl refl
≤ᵣ-plus-both x .x y Y (inl refl) (inr q) = inr step-3 where
  step-1 : y + x < Y + x
  step-1 = <-plus y Y x q
  step-2 : x + y < Y + x
  step-2 = transport +-comm {λ p → p < Y + x} step-1
  step-3 : x + y < x + Y
  step-3 = transport +-comm {λ p → x + y < p} step-2
≤ᵣ-plus-both x X y .y (inr p) (inl refl) = inr (<-plus x X y p)
≤ᵣ-plus-both x X y Y (inr p) (inr q) = inr (<-plus-both x X y Y p q) 

≤ᵣ-plus-left : ∀ x y c → x ≤ᵣ y → (c + x) ≤ᵣ (c + y)
≤ᵣ-plus-left x y c p = step-3 where
  step-1 : x + c ≤ᵣ y + c
  step-1 = ≤ᵣ-plus x y c p
  step-2 : c + x ≤ᵣ y + c
  step-2 = transport +-comm {λ p → p ≤ᵣ y + c} step-1
  step-3 : c + x ≤ᵣ c + y
  step-3 = transport +-comm {λ p → c + x ≤ᵣ p} step-2

≤ᵣ-dichotomy : ∀ x y → (x ≤ᵣ y) ∨ (y ≤ᵣ x)
≤ᵣ-dichotomy x y with <-trichotomy-strong x y
≤ᵣ-dichotomy x y | inl x-equals-y = inl (inl x-equals-y)
≤ᵣ-dichotomy x y | inr (inl x-under-y) = inl (inr x-under-y)
≤ᵣ-dichotomy x y | inr (inr y-under-x) = inr (inr y-under-x)

lemma-lesser : ∀ (x y : ℝ) → (∀ (ε : ℝ) → 0r < ε → x ≤ᵣ y + ε) → ∀ (ε : ℝ) → 0r < ε → x < y + ε
lemma-lesser x y p ε pos-ε = step-3 where
  step-1 : x ≤ᵣ y + (ε /2r)
  step-1 = p (ε /2r) (pos-/2r-v ε pos-ε)
  step-2 : y + (ε /2r) < y + ε
  step-2 = <-plus-left (ε /2r) ε y (x/2r-less-than-x ε pos-ε)
  step-3 : x < y + ε
  step-3 with step-1
  step-3 | inl refl = step-2
  step-3 | inr p = <-tran _ _ _ p step-2

lemma-ε-of-room-plus-≤ᵣ : ∀ (x y : ℝ) → (∀ (ε : ℝ) → 0r < ε → x ≤ᵣ y + ε) → x ≤ᵣ y
lemma-ε-of-room-plus-≤ᵣ x y p with ≤ᵣ-dichotomy x y
lemma-ε-of-room-plus-≤ᵣ x y p | inl (inl x-equals-y) = inl x-equals-y
lemma-ε-of-room-plus-≤ᵣ x y p | inl (inr x-under-y) = inr x-under-y
lemma-ε-of-room-plus-≤ᵣ x y p | inr (inl y-equals-x) = inl (sym y-equals-x)
lemma-ε-of-room-plus-≤ᵣ x y p | inr (inr y-under-x) =
  inr (lemma-ε-of-room-plus x y p' x-neq-y) where
  p' : ∀ (ε : ℝ) → 0r < ε → x < y + ε
  p' = lemma-lesser x y p
  x-neq-y : x ≡ y → ⊥
  x-neq-y x-equals-y = <-asym-1 y y (transport x-equals-y {λ p → y < p} y-under-x) refl
