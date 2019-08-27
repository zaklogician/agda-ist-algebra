{-# OPTIONS --omega-in-omega --no-pattern-matching #-}

module IST.Results.ExtensionTheorem where

open import IST.Base
open import IST.Util
open import IST.Approximation
open import IST.PredicatedTopologies


-- Theorem: If H approximates G via ι, then we can extend every
-- function f : H → M (where M is a standard compact Hausdorff space) to a
-- function f' : G → M using standardization, setting
-- f' = ⟦ (g,m) ∈ G × M | ∃ h ∈ H. ι(h)=g ∧ f(h)=m ⟧.
record ExtensionTheorem : ESet where
  field
    G : Set
    H : Set
    A : Approximation H G
    M# : CompactHausdorffSpace
    st-M : st (CompactHausdorffSpace.Carrier M#)
    f : H → CompactHausdorffSpace.Carrier M#
  open CompactHausdorffSpace M# hiding (Carrier)
  open Approximation A
  private
    -- We refer to the underlying set of the space M# as M, and the
    -- approximation proper as ι.
    
    M : Set
    M = CompactHausdorffSpace.Carrier M#

    ι : H → G → ESet
    ι = Approximation.Map A

    -- Recall that by definition of approximation, G is standard.
    st-G : st G
    st-G = Approximation.Target-st A

    -- We construct the set f' = ⟦ ∃ˢ h. ι(h) = g ∧ m o- f(h) ⟧ by Standardization.
    pre-ext : G ∧ M → ESet
    pre-ext gm = ∃* λ (h : H) → ι h (proj₁ gm) *∧* nearby (proj₂ gm) (f h)

  -- Construction:
  -- The set f' forms the graph of the function we seek.
  f' : G ∧ M → Set
  f' = ⟦ pre-ext ⟧

  st-f' : st f'
  st-f' = ax-Standard-1 pre-ext

  private
    st-f'gm : (g : G) → (m : M) → st g → st m → st (f' (g , m))
    st-f'gm g m st-g st-m = st-fun (G ∧ M) Set f' (g , m) st-f' (lemma-pairing g m st-g st-m)

  -- We prove that for standard g, there is always some standard m such that (g,m) ∈ f'. 
  f'-exists-st : ∀ (g : G) → st g → ∃* λ (m : M) → st m *∧* internal (f' (g , m))
  f'-exists-st g st-g = m , st-m , fromInternal f'-gm where
    -- Take a standard g, and pick an approximation h with ι(h)=g.
    h : H
    h = proj₁ (Map-exists g st-g)
    ι-h-g : ι h g
    ι-h-g = proj₂ (Map-exists g st-g)
    -- Compute f(h). Use the compactness of M to find a standard point
    -- near f(h).
    m : M
    m = proj₁ (compact (f h))
    st-m : st m
    st-m = proj₁ (proj₂ (compact (f h)))
    m-near-fh : nearby m (f h)
    m-near-fh = proj₂ (proj₂ (compact (f h)))
    -- Since ι(h)=g and m lies near f(h), by definition (g,m) belongs to f'.
    pre-ext-gm : pre-ext (g , m)
    pre-ext-gm = h , (ι-h-g , m-near-fh)
    st-gm : st (g , m)
    st-gm = lemma-pairing g m st-g st-m
    f'-gm : f' (g , m)
    f'-gm = ax-Standard-3 pre-ext _ st-gm pre-ext-gm

  -- Existence conclusion:
  -- By transfer, for any g, there is some m such that (g,m) ∈ f'.
  f'-exists : ∀ (g : G) → ∃ λ (m : M) → f' (g , m)
  f'-exists = ax-Transfer-EI Φ f'-exists-st st-params-Φ where
    Φ : TransferPred
    Φ = ∀' G λ g → ∃' M λ m → int' (f' (g , m))
    st-params-Φ : std-params Φ
    st-params-Φ = st-G , λ a st-a →
                  st-M , λ e st-e → st-fun _ _ f' (a , e) st-f' (lemma-pairing a e st-a st-e)

  private
    -- Now we prove for standard g the uniqueness of the m such that (g,m) ∈ f'.
    -- This proves that f' forms (the graph of) a function.
    f'-unique-st :
      ∀ (g : G)  → st g → ∀ (m₁ : M) → st m₁ → ∀ (m₂ : M) → st m₂ →
      f' (g , m₁) → f' (g , m₂) →
      m₁ ≡ m₂
    f'-unique-st g st-g m₁ st-m₁ m₂ st-m₂ f'-gm₁ f'-gm₂ = m₁-equals-m₂ where
      -- Since (g,mᵢ) are standard, they satisfy the defining formula of f',
      -- so we can find hᵢ near gᵢ such that mᵢ lies near f(hᵢ).
      -- First, we pick h₁.
      st-gm₁ : st (g , m₁)
      st-gm₁ = lemma-pairing g m₁ st-g st-m₁
      pre-ext-gm₁ : pre-ext (g , m₁)
      pre-ext-gm₁ = ax-Standard-2 pre-ext (g , m₁) st-gm₁ f'-gm₁
      h₁ : H
      h₁ = proj₁ pre-ext-gm₁
      ι-h₁-g : ι h₁ g
      ι-h₁-g = proj₁ (proj₂ pre-ext-gm₁)
      m₁-near-fh₁ : nearby m₁ (f h₁)
      m₁-near-fh₁ = proj₂ (proj₂ pre-ext-gm₁)
      -- Now, we pick h₂.
      st-gm₂ : st (g , m₂)
      st-gm₂ = lemma-pairing g m₂ st-g st-m₂
      pre-ext-gm₂ : pre-ext (g , m₂)
      pre-ext-gm₂ = ax-Standard-2 pre-ext (g , m₂) st-gm₂ f'-gm₂
      h₂ : H
      h₂ = proj₁ pre-ext-gm₂
      ι-h₂-g : ι h₂ g
      ι-h₂-g = proj₁ (proj₂ pre-ext-gm₂)
      m₂-near-fh₂ : nearby m₂ (f h₂)
      m₂-near-fh₂ = proj₂ (proj₂ pre-ext-gm₂)
      -- Now, h₁ and h₂ both approximate g, so by the approximation
      -- uniqueness clause, h₁ = h₂.
      h₁-equals-h₂ : h₁ ≡ h₂
      h₁-equals-h₂ = Map-unique-Source g st-g h₁ ι-h₁-g h₂ ι-h₂-g
      fh₁-equals-fh₂ : f h₁ ≡ f h₂
      fh₁-equals-fh₂ = cong f h₁-equals-h₂
      -- Since m₂ lies near f(h₂), and h₁ = h₂, we have that
      -- m₂ lies near f(h₁) as well.
      m₂-near-fh₁ : nearby m₂ (f h₁)
      m₂-near-fh₁ =
        transport* (sym fh₁-equals-fh₂) {λ z -> nearby m₂ z} m₂-near-fh₂
      -- But then m₁ and m₂ share a common neighbor, f(h₁). By the Hausdorff
      -- property, this implies m₁ = m₂.
      m₁-equals-m₂ : m₁ ≡ m₂
      m₁-equals-m₂ = hausdorff m₁ st-m₁ m₂ st-m₂ (f h₁) m₁-near-fh₁ m₂-near-fh₁

  -- Uniqueness conclusion:
  -- Since uniqueness holds for standard g, Transfer gives that it holds for arbitrary g.
  -- Hence, the set f' forms the graph of a function.
  f'-unique : ∀ (g : G) → ∀ (m₁ : M) → ∀ (m₂ : M) → f' (g , m₁) → f' (g , m₂) → m₁ ≡ m₂
  f'-unique = ax-Transfer-EI Φ
    (λ g st-g m₁ st-m₁ m₂ st-m₂ → fromInternal (f'-unique-st g st-g m₁ st-m₁ m₂ st-m₂)) st-params-Φ where
    Φ : TransferPred
    Φ = ∀' G λ g → ∀' M λ m₁ → ∀' M λ m₂ → int' (f' (g , m₁) → f' (g , m₂) → m₁ ≡ m₂)
    st-params-Φ : std-params Φ
    st-params-Φ =
      st-G , λ g st-g →
      st-M , λ m₁ st-m₁ →
      st-M , λ m₂ st-m₂ → st-Φ g st-g m₁ st-m₁ m₂ st-m₂ where
      st-f'-gm₁ : (g : G) → st g → (m₁ : M) → st m₁ → st (f' (g , m₁))
      st-f'-gm₁ g st-g m₁ st-m₁ = st-fun _ _ f' (g , m₁) st-f' (lemma-pairing g m₁ st-g st-m₁)
      st-f'-gm₂ : (g : G) → st g → (m₂ : M) → st m₂ → st (f' (g , m₂))
      st-f'-gm₂ g st-g m₂ st-m₂ = st-fun _ _ f' (g , m₂) st-f' (lemma-pairing g m₂ st-g st-m₂)
      st-m₁≡m₂ : (m₁ : M) → st m₁ → (m₂ : M) → st m₂ → st (m₁ ≡ m₂)
      st-m₁≡m₂ m₁ st-m₁ m₂ st-m₂ = st-fun M Set (_≡_ m₁) m₂ (st-fun M (M → Set) _≡_ m₁ st-≡-full st-m₁) st-m₂
      st-f'-gm₂-st-m₁≡m₂ : (g : G) → st g → (m₁ : M) → st m₁ → (m₂ : M) → st m₂ → st (f' (g , m₂) → m₁ ≡ m₂)
      st-f'-gm₂-st-m₁≡m₂ g st-g m₁ st-m₁ m₂ st-m₂ =
        st-→ _ (st-f'-gm₂ g st-g m₂ st-m₂) _ (st-m₁≡m₂ m₁ st-m₁ m₂ st-m₂)
      st-Φ : (g : G) → st g → (m₁ : M) → st m₁ → (m₂ : M) → st m₂ → st (f' (g , m₁) → f' (g , m₂) → m₁ ≡ m₂)
      st-Φ g st-g m₁ st-m₁ m₂ st-m₂ =
        st-→ (f' (g , m₁)) (st-f'-gm₁ g st-g m₁ st-m₁) (f' (g , m₂) → m₁ ≡ m₂)
             (st-f'-gm₂-st-m₁≡m₂ g st-g m₁ st-m₁ m₂ st-m₂)

{-
-- Theorem 2: If the sequence H approximates the structure G in the sense of
-- Zilber, then there is some H(ω) that approximates G in the sense above.
module Thm2
  (I : Set)
  (H : I → Set)
  (_~D~_ : (∀ i → H i) → (∀ i → H i) → Set)
  (st-D : st _~D~_)
  (ω : I)
  (ax-ω-1 : ∀ (f g : ∀ i → H i) → st f → st g → f ~D~ g → f ω ≡ g ω)
  (ax-ω-2 : ∀ (f g : ∀ i → H i) → st f → st g → f ω ≡ g ω → f ~D~ g)
  (G : Set)
  (st-G : st G)
  (φ : G → (∀ i → H i) → Set)
  (φ-exists : ∀ (g : G) → ∃ λ (h : ∀ i → H i) → φ g h)
  (lim : (∀ i → H i) → G)
  (lim-surjective : ∀ (g : G) → ∃ λ (h : ∀ i → H i) → lim h ≡ g)
  (lim-respects-D : ∀ (h₁ h₂ : ∀ i → H i) → h₁ ~D~ h₂ → lim h₁ ≡ lim h₂)
  (lim-preserves-φ : ∀ (g : G) → ∀ (h : ∀ i → H i) → φ g h → _≡_ g (lim h))
  where
  colim : G → (∀ i → H i)
  colim g = ∃.proj₁ (φ-exists g)

  colim-splits-lim : ∀ (g : G) → lim (colim g) ≡ g
  colim-splits-lim g = sym step-2 where
    step-1 : φ g (colim g)
    step-1 = ∃.proj₂ (φ-exists g)
    step-2 : g ≡ lim (colim g)
    step-2 = lim-preserves-φ g (colim g) step-1

  ι : H ω → G → Setω
  ι h g = internal (colim g ω ≡ h)

  ι-exists : ∀ (g : G) → st g → ∃* λ (h : H ω) → ι h g
  ι-exists g st-g = colim g ω , fromInternal refl
  
  ι-unique : ∀ (g : G) → st g → ∀ (h₁ : H ω) → ι h₁ g → ∀ (h₂ : H ω) → ι h₂ g → h₁ ≡ h₂
  ι-unique g st-g h₁ (fromInternal ι-h₁-g) h₂ (fromInternal ι-h₂-g) = tran (sym ι-h₁-g) ι-h₂-g

  open Thm1 G (H ω) st-G ι ι-exists ι-unique

-- If furthermore everything in Thm2 is standard, then we have co-uniquness as well.
module Thm2-X
  (I : Set)
  (H : I → Set)
  (_~D~_ : (∀ i → H i) → (∀ i → H i) → Set)
  (st-D : st _~D~_)
  (ω : I)
  (ax-ω-1 : ∀ (f g : ∀ i → H i) → st f → st g → f ~D~ g → f ω ≡ g ω)
  (ax-ω-2 : ∀ (f g : ∀ i → H i) → st f → st g → f ω ≡ g ω → f ~D~ g)
  (G : Set)
  (st-G : st G)
  (φ : G → (∀ i → H i) → Set)
  (φ-exists : ∀ (g : G) → ∃ λ (h : ∀ i → H i) → φ g h)
  (lim : (∀ i → H i) → G)
  (lim-surjective : ∀ (g : G) → ∃ λ (h : ∀ i → H i) → lim h ≡ g)
  (lim-respects-D : ∀ (h₁ h₂ : ∀ i → H i) → h₁ ~D~ h₂ → lim h₁ ≡ lim h₂)
  (lim-preserves-φ : ∀ (g : G) → ∀ (h : ∀ i → H i) → φ g h → _≡_ g (lim h))
  (φ-exists-st : ∀ (g : G) → st g → st (proj₁ (φ-exists g)) )
  where

    open Thm2 I H _~D~_ st-D ω ax-ω-1 ax-ω-2 G st-G φ φ-exists lim lim-surjective lim-respects-D lim-preserves-φ

    st-colim-v : ∀ (g : G) → st g → st (colim g)
    st-colim-v g st-g = φ-exists-st g st-g
    
    ι-counique : ∀ (h : H ω) → ∀ (g₁ g₂ : G) → st g₁ → st g₂ → ι h g₁ → ι h g₂ → g₁ ≡ g₂
    ι-counique h g₁ g₂ st-g₁ st-g₂ ι-h-g₁ ι-h-g₂ = equality where
      step-1 : ι (colim g₁ ω) g₁
      step-1 with proj₂ (ι-exists g₁ st-g₁)
      step-1 | fromInternal x = fromInternal x
      step-2 : colim g₁ ω ≡ h
      step-2 = sym (ι-unique g₁ st-g₁ h ι-h-g₁ (colim g₁ ω) step-1)
      step-3 : ι (colim g₂ ω) g₂
      step-3 with proj₂ (ι-exists g₂ st-g₂)
      step-3 | fromInternal x = fromInternal x
      step-4 : colim g₂ ω ≡ h
      step-4 = sym (ι-unique g₂ st-g₂ h ι-h-g₂ (colim g₂ ω) step-3)
      step-5 : colim g₁ ω ≡ colim g₂ ω
      step-5 = tran step-2 (sym step-4)
      step-6 : colim g₁ ~D~ colim g₂
      step-6 = ax-ω-2 (colim g₁) (colim g₂) (st-colim-v g₁ st-g₁) (st-colim-v g₂ st-g₂) step-5
      step-7 : lim (colim g₁) ≡ lim (colim g₂)
      step-7 = lim-respects-D (colim g₁) (colim g₂) step-6
      equality : g₁ ≡ g₂
      equality = tran (sym (colim-splits-lim g₁)) (tran step-7 (colim-splits-lim g₂))
-}
