module IST.Safe.Base where

-- Here we define standard constructions from type theory, including
-- the usual dependent sum types and equality. This development
-- takes place in ordinary MLTT/Agda, without the external hierarchy.

open import Agda.Primitive


-- TRIVIAL DATA TYPES --

-- The empty type and ex falso quodlibet.

data ⊥ : Set where

absurd : {ℓ : Level} → ⊥ → ∀ {A : Set ℓ} → A
absurd ()

-- The singleton type.

data ⊤ : Set where
  tt : ⊤


-- EXISTENTIAL QUANTIFICATION --

-- Now we deal with existential quantifiers. Alas, unlike the ∀
-- case, Agda does not provide a builtin for this, so we need to
-- declare two variants, ∃ (for the internal hierarchy) and ∃*
-- (for the external hierarchy). Here we declare the internal
-- variant ∃, and define ∧ in terms of it.

infixr 4 _,_
record ∃ {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (B : A → Set ℓ₂) : Set (ℓ₂ ⊔ ℓ₁) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
open ∃ public

_∧_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₂ ⊔ ℓ₁)
A ∧ B = ∃ λ (x : A) → B


-- LISTS / FINITE SETS --

data List {ℓ : Level} (A : Set ℓ) : Set ℓ where
  [] : List A
  _∷_ : A → (xs : List A) → List A

List-induction : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : List A → Set ℓ₂} →
                 B [] → (∀ x → ∀ xs → B xs → B (x ∷ xs)) → ∀ y → B y
List-induction base-case inductive-case [] = base-case
List-induction base-case inductive-case (x ∷ xs) =
  inductive-case x xs (List-induction base-case inductive-case xs)

data _∈_ {ℓ} {A : Set ℓ} (x : A) : List A → Set ℓ where
  ∈-head : ∀ {ys} → x ∈ (x ∷ ys)
  ∈-tail : ∀ {y ys} → x ∈ ys → x ∈ (y ∷ ys)


-- DISJUNCTION --

-- We could encode (constructive) disjunction using ∃ and a two-element
-- type, but declaring an explicit data type keeps reasoning much
-- more legible.

data _∨_ {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  inl : A → A ∨ B
  inr : B → A ∨ B

by-cases : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} →
           (P : Set ℓ₃) → (A → P) → (B → P) → A ∨ B → P
by-cases P A-implies-P B-implies-P (inl a) = A-implies-P a
by-cases P A-implies-P B-implies-P (inr b) = B-implies-P b

postulate
  by-LEM : {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₂} → {B : Set ℓ₂} → ((A → ⊥) → B) → A ∨ B
  

-- EQUALITY --

-- We define equality onlu for the internal hierarchy, but only
-- with the internal induction principle. Later on,
-- we will admit a transport* principle for the external
-- hierarchy. This counts as a "hidden axiom" of IST, because
-- first-order logic is assumed to have equality. Really, we'd need
-- to check that the Nelson translation of (x = y) → st(x) → st(y) is
-- provable in ZFC.

infix 4 _≡_
data _≡_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set where
  refl : x ≡ x

sym : {ℓ : Level} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

tran : {ℓ : Level} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
tran refl refl = refl

cong : {ℓ : Level} {A B : Set ℓ} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

transport : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {x y : A} → x ≡ y → ∀ {φ : A → Set ℓ₂} → φ x → φ y
transport refl z = z

≡-ind : {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} → {x : A} → (φ : (x ≡ x) → Set ℓ₂) → φ refl → ∀ e → φ e
≡-ind φ p refl = p


-- COMBINATORIAL (CLOSED) LAMBDA TERMS --

-- We cannot use induction on Set-types, so how do we prove them
-- standard? In IST, we do not have to deal with this problem,
-- since we normally encode functions as their graphs (sets of
-- ordered pairs), and IST already provides rules for the
-- standardness of sets.

-- In Agda, functions do not coincide with sets of ordered pairs,
-- and we need to ensure that all MLTT-definable functions are
-- indeed standard. To accomplish this, the rules below suffice:
-- 1. All pure combinatorial λ-terms with standard co/domain are themselves standard.
-- 2. Functions defined by induction are standard.
-- 3. Applying a standard value to a standard function yields a standard result.
-- These rules exhaust all possible ways of defining functions
-- in MLTT.

-- E.g. to prove that (λi. _=_ (f i) (g i)) is standard, we would
-- argue as follows:
-- 1. (\a.\b.\c. a b c) is a purely combinatorial λ-term, so standard.
-- 2. (\b.\c _=_ b c) is standard when both _=_ and (\a.\b.\c. a b c) are standard.
-- 3. (\c _=_ (f i) c) is standard when both (f i) and (\b.\c _=_ b c) are standard.
-- 4. (_=_ (f i) (g i)) is standard when both (g i) and (\c. _=_ (f i) (g i)) are standard.
-- So we'd conclude that the inhabitant (λi. _=_ (f i) (g i))
-- of the type Set is standard as long as (f i) and (g i) are.

-- Here we declare the combinatorial instances that we actually use
-- in our development, so that we can safely declare them standard in
-- IST.Base.

abs-5 : (I : Set) → ({X : Set} → X → X → Set) →
        (b : I → Set) →
        (f : (i : I) → b i) →
        (g : (i : I) → b i) →
        (i : I) → Set
abs-5 I = λ (a : {X : Set} → X → X → Set) →
          λ (b : I → Set) →
          λ (f : (i : I) → b i) →
          λ (g : (i : I) → b i) →
          λ (i : I) → a {b i} (f i) (g i)

abs-4 : (A M X : Set) →
        (f : A → M → M) →
        (e : X → A) →
        X → M → M
abs-4 A M X f e x m = f (e x) m

abs-K : {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : Set ℓ₂) → A → B → A
abs-K A B = λ (a : A) → λ (b : B) → a

abs-K-h : {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : Set ℓ₂) → A → {_ : B} → A
abs-K-h A B = λ (a : A) → λ {b : B} → a


-- We admit the law of excluded middle.

postulate
  excluded-middle : {ℓ : Level} → (A : Set ℓ) → A ∨ (A → ⊥)
