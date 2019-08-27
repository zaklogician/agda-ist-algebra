{-# OPTIONS --omega-in-omega #-}

module IST.Base where

open import Agda.Primitive
open import IST.Safe.Base public

-- We start by defining the sort of the external sets.
-- Internal sets belong to the first segment of the universe hierarchy,
-- while external sets belong to the second segment:
-- Set 0 : Set 1 : Set 2 : ...  Set ω : Set (ω + 1) : ...
-- \_________________________/  \_______________________/
--      internal sets                external sets
-- Alas, Agda does not support higher segments of the hierarchy yet,
-- so we work under --omega-in-omega. Everything here should be typable
-- in the full hierarchy, however, by replacing some occurrences of
-- Set ω with Set (ω + 1).

ESet : Setω
ESet = Setω

ESet₁ : Setω
ESet₁ = Setω

-- We postulate a predicate st(-) asserting that its argument is standard.
-- Note that the value of st(-) lives in the external hierarchy.
-- This ensures that the type (I → Set ℓ) ranges over internal predicates
-- only, whenever ℓ < ω.

-- By declaring ST as a private data type, we ensure the following:
-- 1. st(x) is treated as a contractible type for all x.
-- 2. Outside of this module, the only way to produce a value of st(-)
--    is by using the rules/axioms presented here.

private
  data ST {ℓ : Level} {S : Set ℓ} (x : S) : ESet where
    trust-me-its-standard : ST x

st : {ℓ : Level} → {S : Set ℓ} → S → ESet
st = ST

-- A Safe module does not have access to any extended features (st predicates,
-- IST axioms, Setω), so a top-level definition `t : T` in a Safe module
-- corresponds to a derivation `⊢ˢ t : T` in extended type theory.
-- By the admissibility of the St-Con rule, we can mark any such definition
-- standard. This is accomplished by opening SafeImportTools, and using
-- the provided constructor.

module SafeImportTools where
  declared-in-safe-module : {ℓ : Level} {S : Set ℓ} (x : S) → st x
  declared-in-safe-module _ = trust-me-its-standard

-- The internal hierarchy consists only of standard universes. This follows
-- from the admissibility of the St-Con rule.

st-Set : {ℓ : Level} → st (Set ℓ)
st-Set = trust-me-its-standard

-- FUNCTION TYPES --

-- We declare that the type former ∀ (and by extension →) preserve standardness.
-- This is an easy consequence of the Transfer rules.

st-→ : {ℓ₁ ℓ₂ : Level} → (A : Set ℓ₁) → st A → (B : Set ℓ₂) → st B → st (A → B)
st-→ A st-A B st-B = trust-me-its-standard

st-∀ : {ℓ₁ ℓ₂ : Level} → (A : Set ℓ₁) → st A → (B : A → Set ℓ₂) → st B → st (∀ a → B a)
st-∀ A st-A B st-B = trust-me-its-standard

-- Function application preserves standardness, i.e. if f and x are standard,
-- then so is f(x). Notice that this principle occurs as a theorem in Nelson's
-- Internal Set Theory, and follows from St-Fun for our extended type theory.
-- We add variations for dependent and simple function types, with or without
-- hidden arguments.

st-fun-d : {ℓ₁ ℓ₂ : Level} → (A : Set ℓ₁) → (B : A → Set ℓ₂) →
         (f : (x : A) → B x) → (x : A) →
         st f → st x → st (f x)
st-fun-d A B f x st-f st-x = trust-me-its-standard

st-fun-hd : {ℓ₁ ℓ₂ : Level} → (A : Set ℓ₁) → (B : A → Set ℓ₂) →
           (f : {x : A} → B x) → (x : A) →
           st (λ x → f {x}) → st x → st (f {x})
st-fun-hd A B f x st-f st-x = st-fun-d A B (λ x → f {x}) x st-f st-x

st-fun : {ℓ₁ ℓ₂ : Level} → (A : Set ℓ₁) → (B : Set ℓ₂) →
         (f : A → B) → (x : A) →
         st f → st x → st (f x)
st-fun A B f x st-f st-x = st-fun-d A (λ _ → B) f x st-f st-x

st-fun-h : {ℓ₁ ℓ₂ : Level} → (A : Set ℓ₁) → (B : Set ℓ₂) →
           (f : {a : A} → B) → (x : A) →
           st (λ x → f {x}) → st x → st (f {x})
st-fun-h A B f x st-f st-x = st-fun A B (λ x → f {x}) x st-f st-x

-- That leaves function abstraction.
-- It would be convenient to have the following converse:
--   st-λ : {ℓ₁ ℓ₂ : Level} → (A : Set ℓ₁) → st A → (B : A → Set ℓ₂) → (∀ a → st a → st (B a)) → st B
--   st-λ A st-A B st-Ba = trust-me-its-standard
-- Alas, this principle does not hold. Consider e.g.
-- the function f : ℕ → {0,1} with f(n)=0 ↔ n=ω, which is not
-- standard, but takes standard values everywhere.

-- So how do we prove Set-types standard? In IST, we do not
-- have to deal with this problem, since we normally encode
-- functions as their graphs (sets of ordered pairs), and IST
-- already provides rules for the standardness of sets.

-- In Agda, functions do not coincide with sets of ordered pairs,
-- and we need to ensure that all MLTT-definable functions are
-- indeed standard, even if we define them in terms of standard
-- objects constructed by Standardization, i.e. necessarily
-- outside of a Safe module. . To accomplish this, we can make the following observations:
-- 1. All combinatorial (closed) λ-terms are constructible in the Safe fragment, and hence standard.
-- 2. The eliminators of all data types available in the Safe fragment are themselves standard.
-- 3. Applying a standard value to a standard function yields a standard result.
-- These rules exhaust all possible ways of defining functions in MLTT.

-- E.g. to prove that (λi. _=_ (f i) (g i)) is standard, we can
-- argue as follows:
-- 1. (\a.\b.\c. a b c) is a purely combinatorial λ-term, so standard.
-- 2. (\b.\c _=_ b c) is standard when both _=_ and (\a.\b.\c. a b c) are standard.
-- 3. (\c _=_ (f i) c) is standard when both (f i) and (\b.\c _=_ b c) are standard.
-- 4. (_=_ (f i) (g i)) is standard when both (g i) and (\c. _=_ (f i) (g i)) are standard.
-- So we'd conclude that the inhabitant (λi. _=_ (f i) (g i))
-- of the type Set is standard as long as (f i) and (g i) are.

-- We face one problem: the difficulty of encoding the
-- standardness of combinatorial λ-terms in Agda. To simplify
-- our life, we pre-declare instances that we actually use
-- during the present development.

st-abs-5 : (I : Set) → st (abs-5 I)
st-abs-5 I = trust-me-its-standard

st-abs-4 : st abs-4
st-abs-4 = trust-me-its-standard

st-abs-K : {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : Set ℓ₂) → st (abs-K A B)
st-abs-K A B = trust-me-its-standard

st-abs-K-h : {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : Set ℓ₂) → st (abs-K-h A B)
st-abs-K-h A B = trust-me-its-standard


-- TRIVIAL DATA TYPES --

absurd* : {ℓ : Level} → ⊥ → ∀ {A : ESet} → A
absurd* ()

st-⊥ : st ⊥
st-⊥ = trust-me-its-standard

st-⊤ : st ⊤
st-⊤ = trust-me-its-standard

st-tt : st tt
st-tt = trust-me-its-standard


-- EXISTENTIAL QUANTIFICATION --

-- Now we deal with existential quantifiers. Alas, unlike the ∀
-- case, Agda does not provide a builtin for this, so we need to
-- declare two variants, ∃ (for the internal hierarchy) and ∃*
-- (for the external hierarchy).

st-∃ : ∀ {ℓ₁ ℓ₂ : Level} → st (λ {A : Set ℓ₁} → ∃ {ℓ₁} {ℓ₂} {A})
st-∃ = trust-me-its-standard

st-∃-full : ∀ {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} → st (∃ {ℓ₁} {ℓ₂} {A})
st-∃-full = trust-me-its-standard

st-∃-_,_ : ∀ {ℓ₁ ℓ₂ : Level} → st (λ {A : Set ℓ₁} → λ (B : A → Set ℓ₂) → ∃._,_ {ℓ₁} {ℓ₂} {A} {B})
st-∃-_,_ = trust-me-its-standard

st-∃-_,_-full : ∀ {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} → {B : A → Set ℓ₂} → st (∃._,_ {ℓ₁} {ℓ₂} {A} {B})
st-∃-_,_-full = trust-me-its-standard

st-∃-proj₁ : ∀ {ℓ₁ ℓ₂ : Level} → st (λ {A : Set ℓ₁} → λ (B : A → Set ℓ₂) → ∃.proj₁ {ℓ₁} {ℓ₂} {A} {B})
st-∃-proj₁ = trust-me-its-standard

st-∃-proj₁-full : ∀ {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} → {B : A → Set ℓ₂} → st (∃.proj₁ {ℓ₁} {ℓ₂} {A} {B})
st-∃-proj₁-full = trust-me-its-standard

st-∃-proj₂ : ∀ {ℓ₁ ℓ₂ : Level} → st (λ {A : Set ℓ₁} → λ (B : A → Set ℓ₂) → ∃.proj₂ {ℓ₁} {ℓ₂} {A} {B})
st-∃-proj₂ = trust-me-its-standard

st-∃-proj₂-full : ∀ {ℓ₁ ℓ₂ : Level} → {A : Set ℓ₁} → {B : A → Set ℓ₂} → st (∃.proj₂ {ℓ₁} {ℓ₂} {A} {B})
st-∃-proj₂-full = trust-me-its-standard

st-∧ : ∀ {ℓ₁ ℓ₂ : Level} → st (_∧_ {ℓ₁} {ℓ₂})
st-∧ = trust-me-its-standard

record ∃* {ℓ : Level} {A : Set ℓ} (B : A → ESet) : ESet where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
open ∃* public

record _*∧*_ (A B : ESet) : ESet where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _*∧*_ public


-- LISTS / FINITE SETS --

st-List : {ℓ : Level} → st (List {ℓ})
st-List = trust-me-its-standard

st-[] : {ℓ : Level} → st (λ {A : Set ℓ} → [] {ℓ} {A})
st-[] = trust-me-its-standard

st-∷ : {ℓ : Level} → st (λ {A : Set ℓ} → _∷_ {ℓ} {A})
st-∷ = trust-me-its-standard


-- DISJUNCTION --

-- We could encode the disjunction A ∨ B using ¬ A → B, or
-- in a more constructive spirit as ∃n:ℕ. (n = 0 → A) ∧ (n ≠ 0) → B,
-- but we find it more legible to use the inductive definition, along
-- with a strong elimination principle.

st-∨ : {ℓ₁ ℓ₂ : Level} → st (_∨_ {ℓ₁} {ℓ₂})
st-∨ = trust-me-its-standard

st-inl : {ℓ₁ ℓ₂ : Level} → st (λ {A : Set ℓ₁} → λ {B : Set ℓ₂} → inl {ℓ₁} {ℓ₂} {A} {B})
st-inl = trust-me-its-standard

st-inr : {ℓ₁ ℓ₂ : Level} → st (λ {A : Set ℓ₁} → λ {B : Set ℓ₂} → inr {ℓ₁} {ℓ₂} {A} {B})
st-inr = trust-me-its-standard

by-cases* : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} →
           (P : ESet) → (A → P) → (B → P) → A ∨ B → P
by-cases* P A-implies-P B-implies-P (inl a) = A-implies-P a
by-cases* P A-implies-P B-implies-P (inr b) = B-implies-P b


-- EQUALITY --

-- We introduced equality only for the internal hierarchy, at
-- least for now. This satisfies the usual principles.
-- We declare a variant of transport (equality preserves all
-- properties) that works for external predicates. Note that
-- this is a logical axiom in IST, which makes it invisible.
-- Technically, one should have x = y → st(x) → st(y) as an
-- axiom even there, we fix this omission in our version
-- of the Nelson translation.

transport* : {ℓ : Level} {A : Set ℓ} {x y : A} → x ≡ y → ∀ {φ : A → Setω} → φ x → φ y
transport* refl z = z

st-≡ : {ℓ : Level} → st (λ {A : Set ℓ} → _≡_ {ℓ} {A})
st-≡ = trust-me-its-standard

st-≡-full : {ℓ : Level} → {A : Set ℓ} → st (_≡_ {ℓ} {A})
st-≡-full = trust-me-its-standard

st-refl : {ℓ : Level} → st (λ {A : Set ℓ} → λ {x : A} → refl {ℓ} {A} {x})
st-refl = trust-me-its-standard

st-≡-ind : {ℓ₁ ℓ₂ : Level} → st (λ {A : Set ℓ₁} → λ {x : A} → ≡-ind {ℓ₁} {ℓ₂} {A} {x})
st-≡-ind = trust-me-its-standard


-- AXIOM: TRANSFER --

-- TransferPred implements the Transfer rules Dfun and Dsum.
-- This has the advantage that it does no branching. We do not
-- rely on Transfer for non-prenex formulae in our development,
-- so this suffices.

-- Notice that TransferPred does not satisfy strict positivity.
-- We do not export an elimination rule, so we cannot use it in
-- a dangerous/inconsistent way. If the need for an eliminator
-- ever arises, we can make it strictly positive by indexing
-- over the number of free variables.

data internal {ℓ : Level} (φ : Set ℓ) : ESet where
  fromInternal : φ → internal φ

toInternal : {ℓ : Level} → (φ : Set ℓ) → internal φ → φ
toInternal φ (fromInternal x) = x

data TransferPred : ESet where
  ∀' : (A : Set) → ((φ : A) → TransferPred) → TransferPred
  ∃' : (E : Set) → ((φ : E) → TransferPred) → TransferPred
  int' : (φ : Set) → TransferPred

toTransferI : TransferPred → Set
toTransferI (∀' A φ) = ∀ (a : A) → toTransferI (φ a)
toTransferI (∃' E φ) = ∃ λ (e : E) → toTransferI (φ e)
toTransferI (int' φ) = φ

toTransferE : TransferPred → ESet
toTransferE (∀' A φ) = ∀ (a : A) → st a → toTransferE (φ a)
toTransferE (∃' E φ) = ∃* λ (e : E) → st e *∧* toTransferE (φ e)
toTransferE (int' φ) = internal φ

std-params : TransferPred → ESet
std-params (∀' A φ) = st A *∧* ∀ (a : A) → st a → std-params (φ a)
std-params (∃' E φ) = st E *∧* ∀ (e : E) → st e → std-params (φ e)
std-params (int' φ) = st φ

postulate
  ax-Transfer-IE : (φ : TransferPred) → toTransferI φ → std-params φ → toTransferE φ
  ax-Transfer-EI : (φ : TransferPred) → toTransferE φ → std-params φ → toTransferI φ


-- AXIOM: Standardization --

postulate
  ⟦_⟧ : ∀ {ℓ} → {A : Set ℓ} → (A → ESet) → A → Set ℓ
  ax-Standard-1 : ∀ {ℓ} → {A : Set ℓ} → (φ : A → ESet) → st ⟦ φ ⟧
  ax-Standard-2 : ∀ {ℓ} → {A : Set ℓ} → (φ : A → ESet) →
    (∀ x → st x → ⟦ φ ⟧ x → φ x)
  ax-Standard-3 : ∀ {ℓ} → {A : Set ℓ} → (φ : A → ESet) →
    (∀ x → st x → φ x → ⟦ φ ⟧ x)


-- AXIOM: Idealization --

postulate
  ax-Ideal-1 : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} (φ : A → B → Set ℓ₃) →
               (∀ (xs : List A) → st xs → ∃ λ b → ∀ (x : A) → x ∈ xs → φ x b) →
               ∃* λ b → ∀ (x : A) → st x → φ x b
  ax-Ideal-2 : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} → (φ : A → B → Set ℓ₃) →
               (∃* λ b → ∀ (x : A) → st x → φ x b) →
               ∀ (xs : List A) → st xs → ∃ λ b → ∀ (x : A) → x ∈ xs → φ x b
