{-# OPTIONS --omega-in-omega #-}

-- TODO: Make sure that this confirms to the new coding standards.
-- This is taken from an older version of the proof code.
-- Note that our main proof does not rely on these arguments.

module IST.Ultrafilters where

open import Agda.Primitive
open import IST.Base
open import IST.Util

⋂ : {I : Set} → List (I → Set) → I → Set
⋂ [] i = ⊤
⋂ (φ ∷ []) i = φ i
⋂ (φ ∷ φs) i = φ i ∧ (⋂ φs i)

lemma-⋂ : {I : Set} → (φs : List (I → Set)) → ∀ (i : I) → ⋂ φs i → ∀ φ → φ ∈ φs → φ i
lemma-⋂ (.φ ∷ []) i has-i φ ∈-head = has-i
lemma-⋂ (.φ ∷ (ψ ∷ φs)) i has-i φ ∈-head = proj₁ has-i
lemma-⋂ (ψ ∷ []) i has-i φ (∈-tail ())
lemma-⋂ (ψ₁ ∷ (ψ₂ ∷ ψs)) i has-i φ (∈-tail φ∈φs) = lemma-⋂ (ψ₂ ∷ ψs) i (proj₂ has-i) φ φ∈φs  

_⊆_ : {I : Set} → List (I → Set) → ((I → Set) → Set) → Set
[] ⊆ UF = ⊤
(φ ∷ []) ⊆ UF = UF φ
(φ ∷ φs) ⊆ UF = UF φ ∧ (φs ⊆ UF)

_⇒_ : {I : Set} → (I → Set) → (I → Set) → Set
φ ⇒ ψ = ∀ i → φ i → ψ i

~ : {I : Set} → (I → Set) → I → Set
~ φ i = φ i → ⊥

module Stage1
  (I : Set)
  (st-I : st I)
  (UF : (I → Set) → Set)
  (UF-upward : {φ ψ : I → Set} → φ ⇒ ψ → UF φ → UF ψ)
  (UF-inhabit : {φ : I → Set} → UF φ → ∃ λ i → φ i)
  (UF-fip : {φs : List (I → Set)} → φs ⊆ UF → UF (⋂ φs))
  (UF-alt : {φ : I → Set} → (UF φ → ⊥) → UF (~ φ))
  where
  ∅ : I → Set
  ∅ i = ⊥

  U : I → Set
  U i = ⊤

  step-1 : UF ∅ → ⊥
  step-1 has-∅ = proj₂ (UF-inhabit has-∅)
 
  step-2 : UF U
  step-2 = UF-upward {~ ∅} {U} (λ i _ → tt) (UF-alt step-1)

  arbitrary : I
  arbitrary = proj₁ (UF-inhabit step-2)

  Element : Set₁
  Element = ∃ λ (φ : I → Set) → UF φ

  reduce : List Element → List (I → Set)
  reduce [] = []
  reduce (φ ∷ φs) = (proj₁ φ) ∷ reduce φs

  lemma-reduce : (φs : List Element) → reduce φs ⊆ UF
  lemma-reduce [] = tt
  lemma-reduce (φ ∷ []) = proj₂ φ
  lemma-reduce (φ ∷ (ψ ∷ φs)) = proj₂ φ , lemma-reduce (ψ ∷ φs)

  step-3 : ∀ (φs : List Element) → st φs → ∃ λ (i : I) → ∀ (φ : Element) → φ ∈ φs → proj₁ φ i 
  step-3 φs _ = proj₁ ⋂-inhabit , λ φ φ∈φs → jump (proj₁ φ) (lemma φ φs φ∈φs) where
    ⋂-inhabit : ∃ λ (i : I) → ⋂ (reduce φs) i
    ⋂-inhabit = UF-inhabit (UF-fip {reduce φs} (lemma-reduce φs))
    jump : ∀ (φ : I → Set) → φ ∈ reduce φs → φ (proj₁ ⋂-inhabit)
    jump = lemma-⋂ (reduce φs) (proj₁ ⋂-inhabit) (proj₂ ⋂-inhabit)
    lemma : (φ : Element) → (φs : List Element) → φ ∈ φs → proj₁ φ ∈ reduce φs
    lemma φ .(φ ∷ _) ∈-head = ∈-head
    lemma φ (ψ ∷ φs) (∈-tail p) = ∈-tail (lemma φ φs p)

  thm-1 : ∃* λ (i : I) → ∀ (φ : Element) → st φ → proj₁ φ i
  thm-1 = ax-Ideal-1 _ step-3

  ω : I
  ω = proj₁ thm-1

  module Stage2
    (st-UF : st UF)
    (UF-2val* : (φ : ESet) → (A : I → Set) → (UF A ≡ ⊤ → φ) → (UF A ≡ ⊥ → φ) → φ)
    where

    _~UF~_ : {A : I → Set} → (∀ (i : I) → A i) → (∀ (i : I) → A i) → Set
    f ~UF~ g = UF (λ i → f i ≡ g i)

    _~ω~_ : {A : I → Set} → (∀ (i : I) → A i) → (∀ (i : I) → A i) → Set
    f ~ω~ g = f ω ≡ g ω

    thm-2 : {A : I → Set} → st A → (f : ∀ (i : I) → A i) → st f → (g : ∀ (i : I) → A i) → st g →
            f ~UF~ g → f ~ω~ g
    thm-2 {A} st-A f st-f g st-g p = using-thm-1 where
      st-f=g : st (λ i → f i ≡ g i)
      st-f=g = st-req-f-g where
        recombinator : ({X : Set} → X → X → Set) → (b : I → Set) → (f : (i : I) → b i) → (g : (i : I) → b i) → I → Set
        recombinator = λ (a : {X : Set} → X → X → Set) → λ (b : I → Set) → λ (f : (i : I) → b i) → λ (g : (i : I) → b i) →
                       λ (i : I) → a {b i} (f i) (g i)
        st-recombinator : st recombinator
        st-recombinator = st-abs-5 I
        recombinator-≡ : (b : I → Set) → (f : (i : I) → b i) → (g : (i : I) → b i) → I → Set
        recombinator-≡ = recombinator (_≡_ {lzero})
        st-recombinator-≡ : st recombinator-≡
        st-recombinator-≡ = st-fun _ _ recombinator (_≡_ {lzero}) st-recombinator st-≡
        req : (f : ∀ i → A i) → (g : ∀ i → A i) → I → Set
        req = recombinator-≡ A
        st-req : st req
        st-req = st-fun-d _ _ recombinator-≡ A st-recombinator-≡ st-A
        req-f : (g : ∀ i → A i) → I → Set
        req-f = req f
        st-req-f : st req-f
        st-req-f = st-fun _ _ req f st-req st-f
        req-f-g : I → Set
        req-f-g = req-f g
        st-req-f-g : st req-f-g
        st-req-f-g = st-fun _ _ req-f g st-req-f st-g
      eq : I → Set
      eq i = f i ≡ g i
      pair : (A : I → Set) → UF A → Element
      pair A a = A , a
      st-pair : st pair
      st-pair = st-∃-_,_-full
      st-pair-eq : st (pair eq)
      st-pair-eq = st-fun-d _ _ pair eq st-pair st-f=g
      st-pair-eq-p : st (pair eq p)
      st-pair-eq-p = st-fun-d _ _ (pair eq) p st-pair-eq (st-UF-p p) where
        if-⊥ : UF eq ≡ ⊥ → ∀ (p : UF eq) → st p
        if-⊥ x = transport* (sym x) {λ S → ∀ (p : S) → st p} λ ()
        if-⊤ : UF eq ≡ ⊤ → ∀ (p : UF eq) → st p
        if-⊤ x = transport* (sym x) {λ S → ∀ (p : S) → st p} helper where
          helper : (p : ⊤) → st p
          helper tt = st-tt
        st-UF-p : ∀ (p : UF eq) → st p
        st-UF-p = UF-2val* (∀ (p : UF eq) → st p) eq if-⊤ if-⊥
      using-thm-1 : f ω ≡ g ω
      using-thm-1 = proj₂ thm-1 (eq , p) st-pair-eq-p

-- we get the converse of thm-2 by the exact same argument, as ¬(f ~UF~ g) → UF (λ i → ¬ (f i ≡ g i))
