{-# OPTIONS --omega-in-omega --no-pattern-matching #-}

module IST.Results.MainTheorem where

open import IST.Base
open import IST.Util
open import IST.Approximation
open import IST.MetricSpaces
open import IST.Reals
open import IST.Naturals
open import IST.PredicatedTopologies
open import IST.Results.ExtensionTheorem
open import IST.Groups
open import IST.GroupActions
open import IST.NewmansTheorem


-- Theorem. Assume that the finite group H approximates the standard group G as a group via an external
--          predicate ι. Consider a faithful K-Lipschitz faithful action of H on M, for some standard K > 0.
--          Every periodic subgroup of $G$ also admits a standard faithful $K$-Lipschitz action on $M$.
record MainTheorem : ESet where
  field
    G# : Group
    st-G# : st G#
    H# : FiniteGroup
    ι# : FiniteGroupApproximation H# G#
    M# : NewmanSpace
    st-M# : st M#
    A# : DiscreteAction H# (NewmanSpace.asMetricSpace M#)
  -- We first name everything in context.
  open Group G# renaming
    ( Carrier to G
    ; identity to 1G
    ; operation to xG
    ; inverse to iG
    ; assoc to G-associative
    ; unit-left to G-unit-left
    ; unit-right to G-unit-right
    ; inverse-left to G-inverse-left
    ; inverse-right to G-inverse-right
    )
  open FiniteGroup H# renaming
    ( Carrier to H
    ; identity to 1H
    ; operation to xH
    ; inverse to iH
    ; assoc to H-associative
    ; unit-left to H-unit-left
    ; unit-right to H-unit-right
    ; inverse-left to H-inverse-left
    ; inverse-right to H-inverse-right
    )
  open MetricSpace (NewmanSpace.asMetricSpace M#) renaming (Carrier to M)
  open DiscreteAction A# renaming (Map to act)
  open FiniteGroupApproximation ι# renaming (Map to ι)
  private
    M#' : MetricSpace
    M#' = NewmanSpace.asMetricSpace M#
    st-M#' : st M#'
    st-M#' = st-fun _ _ NewmanSpace.asMetricSpace M# st-NewmanSpace-asMetricSpace st-M#
    st-G : st G
    st-G = st-fun _ _ Group.Carrier G# st-Group-Carrier st-G#
    st-xG : st xG
    st-xG = st-fun-d _ _ Group.operation G# st-Group-operation st-G#
    st-1G : st 1G
    st-1G = st-fun-d _ _ Group.identity G# st-Group-identity st-G#
    st-M : st M
    st-M = st-fun _ _ MetricSpace.Carrier M#' st-MetricSpace-Carrier st-M#'
    st-distance : st distance
    st-distance = st-fun-d _ _ MetricSpace.distance M#' st-MetricSpace-distance st-M#'
    st-asMetricSpace-M# : st (NewmanSpace.asMetricSpace M#)
    st-asMetricSpace-M# =
      st-fun _ _ NewmanSpace.asMetricSpace M# st-NewmanSpace-asMetricSpace st-M#
    M## : HausdorffEquivalenceSpace
    M## = metric-to-hausdorff-equivalence (NewmanSpace.asMetricSpace M#) st-asMetricSpace-M#
  open HausdorffEquivalenceSpace M## renaming (Carrier to M-Carrier)
  -- The theorem requires one additional assumption to ensure the continuity of the resulting
  -- action. This can e.g. be a Lipschitz constant.
  field
    act-faithful : ∀ (g : H) → (g ≡ 1H → ⊥) → ∃ λ (m : M) → act g m ≡ m → ⊥
    isCompactSpace : IsCompactSpace M nearby
    K : ℝ
    st-K : st K
    positive-K : 0r < K
    lipschitz : ∀ (g : H) → ∀ (x y : M) → distance (act g x) (act g y) ≤ᵣ (K · distance x y)
  open IsCompactSpace isCompactSpace
  private
    K' : ℝ
    K' = inv K (λ _ → positive-K)
    st-K' : st K'
    st-K' = st-inv-v K (λ _ → positive-K) st-K
    positive-K' : 0r < K'
    positive-K' = <-inverse positive-K

    -- We prove the continuity of the action of H.
    S-continuity : ∀ (g : H) → ∀ (x : M) → st x → ∀ (y : M) → nearby x y → nearby (act g x) (act g y)
    S-continuity g x st-x y x-near-y ε st-ε positive-ε = agx-near-agy where
      s : ℝ
      s = K' · ε
      st-s : st s
      st-s = st-fun _ _ (_·_ K') ε (st-fun _ _ _·_ K' st-· st-K') st-ε
      positive-s : 0r < s
      positive-s = step-3 where
        step-1 : K' · 0r < s
        step-1 = <-mult 0r ε K' positive-K' positive-ε
        step-2 : K' · 0r ≡ 0r
        step-2 = ·-null-left
        step-3 : 0r < s
        step-3 = transport step-2 {λ x → x < s} step-1
      dxy-under-s : distance x y < s
      dxy-under-s = x-near-y s st-s positive-s
      kdxy-under-ks : K · distance x y < K · s
      kdxy-under-ks = <-mult (distance x y) s K positive-K (x-near-y s st-s positive-s)
      kK'ε-equals-ε : K · s ≡ ε
      kK'ε-equals-ε = tran (tran step-1 step-2) step-3 where
        step-1 : K · (K' · ε) ≡ (K · K') · ε
        step-1 = sym ·-assoc
        step-2 : (K · K') · ε ≡ 1r · ε
        step-2 = cong (λ x → x · ε) (·-inverse-right (λ _ → positive-K))
        step-3 : 1r · ε ≡ ε
        step-3 = ·-unit-left
      kdxy-under-ε : K · distance x y < ε
      kdxy-under-ε = transport kK'ε-equals-ε {λ p → (K · distance x y) < p} kdxy-under-ks
      agx-near-agy : distance (act g x) (act g y) < ε
      agx-near-agy = by-cases _ case-1 case-2 (lipschitz g x y) where
        case-1 :  distance (act g x) (act g y) ≡ K · distance x y →
                  distance (act g x) (act g y) < ε
        case-1 p = transport (sym p) {λ p → p < ε} kdxy-under-ε
        case-2 : distance (act g x) (act g y) < K · distance x y →
                 distance (act g x) (act g y) < ε
        case-2 p = <-tran _ _ _ p kdxy-under-ε

    -- We prove that continuity of the action over a compact manifold implies uniform continuity.
    -- TODO: move this proof to a more appropriate module.
    S-uniform-continuity : ∀ (g : H) → ∀ (x : M) → ∀ (y : M) → nearby x y → nearby (act g x) (act g y)
    S-uniform-continuity g x y x-near-y = fx-near-fy where
      x' : M
      x' = proj₁ (compact x)
      st-x' : st x'
      st-x' = proj₁ (proj₂ (compact x))
      x'-near-x : nearby x' x
      x'-near-x = proj₂ (proj₂ (compact x))
      x'-near-y : nearby x' y
      x'-near-y = transitive _ _ _ x'-near-x x-near-y
      fx'-near-fx : nearby (act g x') (act g x)
      fx'-near-fx = S-continuity g x' st-x' x x'-near-x
      fx'-near-fy : nearby (act g x') (act g y)
      fx'-near-fy = S-continuity g x' st-x' y x'-near-y
      fx-near-fy : nearby (act g x) (act g y)
      fx-near-fy = transitive _ _ _ (symmetric _ _ fx'-near-fx) fx'-near-fy

    -- Group approximations of standard groups preserve and reflect unit elements.
    ι-preserves-unit : ι 1H 1G
    ι-preserves-unit = Map-preserves-unit st-G#

    ι-preserves-unit-Target : ∀ (g : G) → st g → ι 1H g → g ≡ 1G
    ι-preserves-unit-Target = Map-preserves-unit-Target st-G#

    -- We wish to apply the Extension Theorem to extend the action.
    -- To do that, we prove that a group approximation between H and G
    -- induces an appropriate set approximation between products (H × M)
    -- and (G × M).
    ι' : (H ∧ M) → G ∧ M → ESet
    ι' hm₁ gm₂ = ι (proj₁ hm₁) (proj₁ gm₂) *∧* internal (proj₂ hm₁ ≡ proj₂ gm₂)
    -- ι' (h , m₁) (g , m₂) = ι h g ∧* internal (m₁ ≡ m₂)

    ι'-exists : ∀ (gm : G ∧ M) → st gm → ∃* λ (hm : H ∧ M) → ι' hm gm
    ι'-exists gm st-gm = (h , m) , ι'-hm-gm where
      g : G
      g = proj₁ gm
      m : M
      m = proj₂ gm
      st-g : st g
      st-g = lemma-proj₁ (g , m) st-gm
      st-m : st m
      st-m = lemma-proj₂ (g , m) st-gm
      h : H
      h = proj₁ (Map-exists g st-g)
      ι-h-g : ι h g
      ι-h-g = proj₂ (Map-exists g st-g)
      ι'-hm-gm : ι' (h , m) (g , m)
      ι'-hm-gm = ι-h-g , fromInternal refl

    ι'-unique-Source : ∀ (gm : G ∧ M) → st gm →
                       ∀ (h₁m : H ∧ M) → ι' h₁m gm →
                       ∀ (h₂m : H ∧ M) → ι' h₂m gm →
                       h₁m ≡ h₂m 
    ι'-unique-Source gm st-gm h₁m ι-h₁m-gm h₂m ι-h₂m-gm =
      h₁m-equals-h₂m where
      g : G
      g = proj₁ gm
      m : M
      m = proj₂ gm
      h₁ : H
      h₁ = proj₁ h₁m
      m₁ : M
      m₁ = proj₂ h₁m
      h₂ : H
      h₂ = proj₁ h₂m
      m₂ : M
      m₂ = proj₂ h₂m
      st-g : st g
      st-g = lemma-proj₁ (g , m) st-gm
      st-m : st m
      st-m = lemma-proj₂ (g , m) st-gm
      m₁-equals-m : m₁ ≡ m
      m₁-equals-m = toInternal _ (proj₂ ι-h₁m-gm)
      m₂-equals-m : m₂ ≡ m
      m₂-equals-m = toInternal _ (proj₂ ι-h₂m-gm)
      m₁-equals-m₂ : m₁ ≡ m₂
      m₁-equals-m₂ = tran m₁-equals-m (sym m₂-equals-m)
      h₁-equals-h₂ : h₁ ≡ h₂
      h₁-equals-h₂ = Map-unique-Source g st-g h₁ (proj₁ ι-h₁m-gm) h₂ (proj₁ ι-h₂m-gm)
      pair : H → M → H ∧ M
      pair x y = (x , y)
      product-lemma : ∀ {x₁ x₂ : H} → ∀ {y₁ y₂ : M} →
                     x₁ ≡ x₂ → y₁ ≡ y₂ → (pair x₁ y₁) ≡ (pair x₂ y₂)
      product-lemma = lemma-product-equality
      h₁m-equals-h₂m : (h₁ , m₁) ≡ (h₂ , m₂)
      h₁m-equals-h₂m = product-lemma h₁-equals-h₂ m₁-equals-m₂

    ι'-unique-Target : ∀ (g₁m : G ∧ M) → st g₁m →
                       ∀ (g₂m : G ∧ M) → st g₂m →
                       ∀ (hm : H ∧ M) → ι' hm g₁m → ι' hm g₂m →
                       g₁m ≡ g₂m
    ι'-unique-Target g₁m st-g₁m g₂m st-g₂m hm ι'-hm-g₁m ι'-hm-g₂m =
      g₁m-equals-g₂m where
      g₁ : G
      g₁ = proj₁ g₁m
      m₁ : M
      m₁ = proj₂ g₁m
      g₂ : G
      g₂ = proj₁ g₂m
      m₂ : M
      m₂ = proj₂ g₂m
      h : H
      h = proj₁ hm
      m : M
      m = proj₂ hm
      st-g₁ : st g₁
      st-g₁ = lemma-proj₁ (g₁ , m₁) st-g₁m
      st-g₂ : st g₂
      st-g₂ = lemma-proj₁ (g₂ , m₂) st-g₂m
      st-m₁ : st m₁
      st-m₁ = lemma-proj₂ (g₁ , m₁) st-g₁m
      st-m₂ : st m₂
      st-m₂ = lemma-proj₂ (g₂ , m₂) st-g₂m
      m₁-equals-m : m ≡ m₁
      m₁-equals-m = toInternal _ (proj₂ ι'-hm-g₁m)
      m₂-equals-m : m ≡ m₂
      m₂-equals-m = toInternal _ (proj₂ ι'-hm-g₂m)
      m₁-equals-m₂ : m₁ ≡ m₂
      m₁-equals-m₂ = tran (sym m₁-equals-m) (m₂-equals-m)
      ι-h-g₁ : ι h g₁
      ι-h-g₁ = proj₁ ι'-hm-g₁m
      ι-h-g₂ : ι h g₂
      ι-h-g₂ = proj₁ ι'-hm-g₂m
      g₁-equals-g₂ : g₁ ≡ g₂
      g₁-equals-g₂ = Map-unique-Target g₁ st-g₁ g₂ st-g₂ h ι-h-g₁ ι-h-g₂
      pair : G → M → G ∧ M
      pair x y = (x , y)
      product-lemma : ∀ {x₁ x₂ : G} → ∀ {y₁ y₂ : M} →
                     x₁ ≡ x₂ → y₁ ≡ y₂ → (pair x₁ y₁) ≡ (pair x₂ y₂)
      product-lemma = lemma-product-equality
      g₁m-equals-g₂m : (g₁ , m₁) ≡ (g₂ , m₂)
      g₁m-equals-g₂m = product-lemma g₁-equals-g₂ m₁-equals-m₂

    st-G∧M : st (G ∧ M)
    st-G∧M = st-fun _ _ (_∧_ G) M (st-fun _ _ _∧_ G st-∧ st-G) st-M

    A#∧M : Approximation (H ∧ M) (G ∧ M)
    A#∧M = record { Map = ι'
                  ; isApproximation = record { Target-st = st-G∧M
                                             ; Map-exists = ι'-exists
                                             ; Map-unique-Source = ι'-unique-Source
                                             ; Map-unique-Target = ι'-unique-Target
                                             }
                  }
    -- Now we can invoke the extension theorem to extend the action to a map G × M → M.
    by-extension : ExtensionTheorem
    by-extension =
      record { G = G ∧ M
             ; H = H ∧ M
             ; A = A#∧M
             ; M# = record
                      { Carrier = M
                      ; nearby = nearby
                      ; isHausdorffSpace = isHausdorffSpace
                      ; isCompactSpace = isCompactSpace
                      }
             ; st-M = st-M
             ; f = λ hm → act (proj₁ hm) (proj₂ hm) }
    open ExtensionTheorem by-extension hiding (G; H; A; M#; st-M; f) renaming
      ( f' to act-G
      ; st-f' to st-act-G
      ; f'-exists to act-G-exists
      ; f'-exists-st to act-G-exists-st
      ; f'-unique to act-G-unique
      )

    -- The extension theorem extends the action with signature H × M → M to a
    -- function with signature G × M → M. Here we prove the result standard-valued.
    act' : G → M → M
    act' g m = proj₁ (act-G-exists (g , m))

    act'-property : ∀ (g : G) → ∀ (m : M) → act-G ((g , m) , act' g m)
    act'-property g m = proj₂ (act-G-exists (g , m))

    act'-st-valued : ∀ (g : G) → st g → ∀ (m : M) → st m → st (act' g m)
    act'-st-valued g st-g m st-m = st-act'-g-m where
      gm : G ∧ M
      gm = (g , m)
      sm : ∃* λ (m' : M) → st m' *∧* internal (act-G ((g , m) , m'))
      sm = act-G-exists-st (g , m) (lemma-pairing g m st-g st-m)
      st-sm : st (proj₁ sm)
      st-sm = proj₁ (proj₂ sm)
      f'-gm-sm : act-G (gm , (proj₁ sm))
      f'-gm-sm = toInternal _ (proj₂ (proj₂ sm))
      sm-equals-act-G-m : proj₁ sm ≡ act' g m -- act-G ((g , m) , ?)
      sm-equals-act-G-m = act-G-unique (g , m) (proj₁ sm) (act' g m) f'-gm-sm (act'-property g m)
      st-act'-g-m : st (act' g m)
      st-act'-g-m = transport* sm-equals-act-G-m {st} st-sm

    act'-property-st : ∀ (g : G) → st g → ∀ (m : M) → st m →
                       ∃* λ (hm : H ∧ M) → ι' hm (g , m) *∧* nearby (act' g m) (act (proj₁ hm) (proj₂ hm)) 
    act'-property-st g st-g m st-m =
      ax-Standard-2 _ ((g , m) , act' g m) act-G-pair (act'-property g m) where
      st-gm : st (g , m)
      st-gm = lemma-pairing g m st-g st-m
      act-G-pair : st ((g , m) , act' g m)
      act-G-pair = lemma-pairing (g , m) (act' g m) st-gm (act'-st-valued g st-g m st-m)

    -- The main lemma: if h approximates g, then the result of the action of h
    -- lies near the result of the action of g.
    act'-lemma : ∀ (g : G) → st g → ∀ (m : M) → st m → ∀ (h : H) → ι h g →
                 nearby (act' g m) (act h m)
    act'-lemma g st-g m st-m h ι-h-g = agm-near-ahm where
      ι'-hm-gm : ι' (h , m) (g , m)
      ι'-hm-gm = ι-h-g , fromInternal refl
      hm'-exists : ∃* λ (hm' : H ∧ M) → ι' hm' (g , m) *∧* nearby (act' g m) (act (proj₁ hm') (proj₂ hm'))
      hm'-exists = act'-property-st g st-g m st-m
      h' : H
      h' = proj₁ (proj₁ hm'-exists)
      m' : M
      m' = proj₂ (proj₁ hm'-exists)
      ι'-hm'-gm : ι' (h' , m') (g , m)
      ι'-hm'-gm = proj₁ (proj₂ hm'-exists)
      hm'-equals-hm : (h' , m') ≡ (h , m)
      hm'-equals-hm =
        ι'-unique-Source (g , m) (lemma-pairing g m st-g st-m) (h' , m') ι'-hm'-gm (h , m) ι'-hm-gm
      h'-equals-h : h' ≡ h
      h'-equals-h = cong proj₁ hm'-equals-hm
      m'-equals-m : m' ≡ m
      m'-equals-m = cong proj₂ hm'-equals-hm
      agm-near-ahm' : nearby (act' g m) (act h' m')
      agm-near-ahm' = proj₂ (proj₂ hm'-exists)
      agm-near-ahm : nearby (act' g m) (act h m)
      agm-near-ahm =
        transport* h'-equals-h {λ z → nearby (act' g m) (act z m)}
          (transport* m'-equals-m {λ z → nearby (act' g m) (act h' z)} agm-near-ahm')

    -- First we prove that the identity acts via the identity function.
    act'-identity-st : ∀ (m : M) → st m → internal (act' 1G m ≡ m)
    act'-identity-st m st-m = fromInternal a1Gm-equals-m where
      a1Gm-near-a1Hm : nearby (act' 1G m) (act 1H m)
      a1Gm-near-a1Hm = act'-lemma 1G st-1G m st-m 1H ι-preserves-unit
      a1Gm-near-m : nearby (act' 1G m) m
      a1Gm-near-m = transport* (action-identity m) {λ z → nearby (act' 1G m) z} a1Gm-near-a1Hm
      a1Gm-equals-m : act' 1G m ≡ m
      a1Gm-equals-m = hausdorff (act' 1G m) st-a1Gm m st-m m a1Gm-near-m (reflexive m) where
        st-a1Gm : st (act' 1G m)
        st-a1Gm = act'-st-valued 1G st-1G m st-m

    act'-identity : ∀ (m : M) → act' 1G m ≡ m
    act'-identity = ax-Transfer-EI (∀' M (λ m → int' (act' 1G m ≡ m))) act'-identity-st std-Φ where
      Φ : TransferPred
      Φ = ∀' M λ m → int' (act' 1G m ≡ m)
      std-Φ : st M *∧* ∀ (m : M) → st m → st (act' 1G m ≡ m)
      std-Φ = st-M , λ m st-m →
              st-fun _ _ (eq (act' 1G m)) m
              (st-fun _ _ eq (act' 1G m) st-eq (help1 m st-m)) st-m where
        eq : M → M → Set
        eq = _≡_
        st-eq : st eq
        st-eq = st-≡-full
        help1 : (m : M) → st m → st (act' 1G m)
        help1 m st-m = act'-st-valued 1G st-1G m st-m

    -- Now we prove that the action is a homomorphism with respect to the operations.
    act'-operation-st : ∀ (g : G) → st g → ∀ (h : G) → st h → ∀ (m : M) → st m →
                        internal (act' g (act' h m) ≡ act' (xG g h) m)
    act'-operation-st g st-g h st-h m st-m = fromInternal (sym (a'ghm-equals-a'ga'hm)) where
      -- Book-keeping: We must prove that if g' approximates g and
      -- h' approximates h then g'h' approximates gh.
      gh : G
      gh = xG g h
      st-gh : st gh
      st-gh = st-fun _ _ (xG g) h (st-fun _ _ xG g st-xG st-g) st-h
      g' : H
      g' = proj₁ (Map-exists g st-g)
      ι-g'-g : ι g' g
      ι-g'-g = proj₂ (Map-exists g st-g) 
      h' : H
      h' = proj₁ (Map-exists h st-h)
      ι-h'-h : ι h' h
      ι-h'-h = proj₂ (Map-exists h st-h)
      g'h' : H
      g'h' = xH g' h'
      ι-g'h'-gh : ι g'h' gh
      ι-g'h'-gh = Map-homomorphism g' h' g st-g h st-h ι-g'-g ι-h'-h 
      -- It follows on one hand that applying gh to m results in a neighbor
      -- of applying g'h' to m.
      a'ghm-near-ag'ah'm : nearby (act' gh m) (act g'h' m)
      a'ghm-near-ag'ah'm = act'-lemma gh st-gh m st-m g'h' ι-g'h'-gh
      ag'h'm-equals-ag'ah'm : act g'h' m ≡ act g' (act h' m)
      ag'h'm-equals-ag'ah'm = sym (action-operation g' h' m)
      one-hand : nearby (act' gh m) (act g' (act h' m))
      one-hand = transport* ag'h'm-equals-ag'ah'm {λ z → nearby (act' gh m) z} a'ghm-near-ag'ah'm
      -- It follows on the other hand that the result of applying g' to h' at m
      -- neighbors the same element.
      a'ga'hm-near-ag'a'hm : nearby (act' g (act' h m)) (act g' (act' h m))
      a'ga'hm-near-ag'a'hm = act'-lemma g st-g (act' h m) (act'-st-valued h st-h m st-m) g' ι-g'-g
      a'hm-near-ah'm : nearby (act' h m) (act h' m)
      a'hm-near-ah'm = act'-lemma h st-h m st-m h' ι-h'-h
      ag'a'hm-near-ag'ah'm : nearby (act g' (act' h m)) (act g' (act h' m))
      ag'a'hm-near-ag'ah'm = S-uniform-continuity g' (act' h m) (act h' m) a'hm-near-ah'm
      other-hand : nearby (act' g (act' h m)) (act g' (act h' m))
      other-hand = transitive _ _ _ a'ga'hm-near-ag'a'hm ag'a'hm-near-ag'ah'm
      -- These both satisfy standardness!
      st-one : st (act' gh m)
      st-one = act'-st-valued gh st-gh m st-m
      st-other : st (act' g (act' h m))
      st-other = act'-st-valued g st-g (act' h m) (act'-st-valued h st-h m st-m)
      -- By Hausdorff separation standard values with common neighbors are equal.
      a'ghm-equals-a'ga'hm : act' gh m ≡ act' g (act' h m)
      a'ghm-equals-a'ga'hm =
        hausdorff (act' gh m) st-one
                  (act' g (act' h m)) st-other
                  (act g' (act h' m)) one-hand other-hand

    act'-operation : ∀ (g : G) → ∀ (h : G) → ∀ (m : M) → act' g (act' h m) ≡ act' (xG g h) m
    act'-operation = ax-Transfer-EI Φ act'-operation-st std-Φ where
      Φ : TransferPred
      Φ = ∀' G λ g → ∀' G λ h → ∀' M λ m → int' (act' g (act' h m) ≡ act' (xG g h) m)
      eq : M → M → Set
      eq = _≡_
      st-eq : st eq
      st-eq = st-≡-full
      st-one : ∀ (g h : G) → ∀ (m : M) → st g → st h → st m → st (act' (xG g h) m)
      st-one g h m st-g st-h st-m =
        act'-st-valued (xG g h) (st-fun _ _ (xG g) h (st-fun _ _ xG g st-xG st-g) st-h) m st-m
      st-other : ∀ (g h : G) → ∀ (m : M) → st g → st h → st m → st (act' g (act' h m))
      st-other g h m st-g st-h st-m = act'-st-valued g st-g (act' h m) (act'-st-valued h st-h m st-m)
      std-Φ : st G *∧* ∀ (g : G) → st g → st G *∧* ∀ (h : G) → st h → st M *∧*
              ∀ (m : M) → st m → st (act' g (act' h m) ≡ act' (xG g h) m)
      std-Φ = st-G , λ g st-g →
              st-G , λ h st-h →
              st-M , λ m st-m →  st-fun _ _ (eq (act' g (act' h m))) (act' (xG g h) m)
              (st-fun _ _ eq (act' g (act' h m)) st-eq (st-other g h m st-g st-h st-m))
              (st-one g h m st-g st-h st-m)
    -- At this point we know that act' has all the properties of an action of G on M.
    -- But it might be a trivial action - we have to rule that out!

    -- Before discussing faithfulness, we note that act' is a standard action, and therefore
    -- it satisfies both S-continuity and ε-δ continuity.

    act'-lipschitz-st! :  ∀ (g : G) → st g →
                         ∀ (x : M) → st x →
                         ∀ (y : M) → st y → internal (
                           distance (act' g x) (act' g y) ≤ᵣ (K · distance x y)
                         )
    act'-lipschitz-st! g st-g x st-x y st-y = fromInternal difference-0 where
      h : H
      h = proj₁ (Map-exists g st-g)
      ι-h-g : ι h g
      ι-h-g = proj₂ (Map-exists g st-g)
      difference-ε-st : ∀ (ε : ℝ) → st ε → 0r < ε → distance (act' g x) (act' g y) ≤ᵣ K · distance x y + ε
      difference-ε-st ε st-ε positive-ε = by-cases _ case-1 case-2 (lipschitz h y x) where
        ε/2 : ℝ
        ε/2 = ε /2r
        st-ε/2 : st ε/2
        st-ε/2 = st-/2r-v ε st-ε
        positive-ε/2 : 0r < ε/2
        positive-ε/2 = pos-/2r-v ε positive-ε
        case-2 : distance (act h y) (act h x) < K · distance y x →
                 distance (act' g x) (act' g y) ≤ᵣ K · distance x y + ε
        case-2 final-1 = inr final-13 where
          final-2 : distance (act h y) (act h x) < K · distance x y
          final-2 = transport (symmetry y x) {λ z → distance (act h y) (act h x) < K · z} final-1
          final-3 : distance (act' g x) (act h x) < ε/2
          final-3 = act'-lemma g st-g x st-x h ι-h-g ε/2 st-ε/2 positive-ε/2
          final-4 : distance (act h x) (act' g x) < ε/2
          final-4 = transport (symmetry (act' g x) (act h x)) {λ z → z < ε/2} final-3
          final-5 : distance (act h y) (act h x) + distance (act h x) (act' g x) < K · distance x y + ε/2
          final-5 = <-plus-both (distance (act h y) (act h x)) _ _ _ final-2 final-4
          final-6 : distance (act h y) (act' g x) < K · distance x y + ε/2
          final-6 = triangle (act h y) (act h x) (act' g x) (K · distance x y + ε/2) final-5
          final-7 : distance (act' g y) (act h y) < ε/2
          final-7 = act'-lemma g st-g y st-y h ι-h-g ε/2 st-ε/2 positive-ε/2
          final-8 : distance (act h y) (act' g y) < ε/2
          final-8 = transport (symmetry (act' g y) (act h y)) {λ z → z < ε/2} final-7
          final-9 : distance (act' g x) (act h y) < K · distance x y + ε/2
          final-9 = transport (symmetry (act h y) (act' g x)) {λ z → z < K · distance x y + ε/2} final-6
          final-10 :
            distance (act' g x) (act h y) + distance (act h y) (act' g y) < (K · distance x y + ε/2) + ε/2
          final-10 = <-plus-both (distance (act' g x) (act h y)) _ _ _ final-9 final-8
          final-11 : distance (act' g x) (act' g y) < (K · distance x y + ε/2) + ε/2
          final-11 = triangle (act' g x) (act h y) (act' g y)
                       ((K · distance x y + ε/2) + ε/2) final-10
          final-12 : distance (act' g x) (act' g y) < K · distance x y + ε/2 + ε/2
          final-12 = transport +-assoc {λ z → distance (act' g x) (act' g y) < z} final-11
          final-13 : distance (act' g x) (act' g y) < K · distance x y + ε
          final-13 =
            transport (/2r-half {ε}) {λ z → distance (act' g x) (act' g y) < K · distance x y + z} final-12

        case-1 : distance (act h y) (act h x) ≡ K · distance y x →
                 distance (act' g x) (act' g y) ≤ᵣ K · distance x y + ε
        case-1 final-1 = final-x12 where
          final-x1 :
            distance (act' g x) (act' g y) ≤ᵣ distance (act' g x) (act h y) + distance (act h y) (act' g y)
          final-x1 = triangle-≤ᵣ (act' g x) (act h y) (act' g y)
          final-x2 :
            distance (act h y) (act' g x) ≤ᵣ distance (act h y) (act h x) + distance (act h x) (act' g x)
          final-x2 = triangle-≤ᵣ (act h y) (act h x) (act' g x)
          final-x3 :
            distance (act' g x) (act' g y) ≤ᵣ distance (act h y) (act' g x) + distance (act h y) (act' g y)
          final-x3 = transport (symmetry (act' g x) (act h y))
                       {λ p → distance (act' g x) (act' g y) ≤ᵣ p + distance (act h y) (act' g y)} final-x1
          final-x4 :
             distance (act h y) (act' g x) + distance (act h y) (act' g y) ≤ᵣ
             (distance (act h y) (act h x) + distance (act h x) (act' g x)) + distance (act h y) (act' g y)
          final-x4 = ≤ᵣ-plus _ _ (distance (act h y) (act' g y)) final-x2
          final-x5 :
             distance (act' g x) (act' g y) ≤ᵣ
             (distance (act h y) (act h x) + distance (act h x) (act' g x)) + distance (act h y) (act' g y)
          final-x5 = ≤ᵣ-tran _ _ _ final-x3 final-x4
          final-x6 :
             distance (act' g x) (act' g y) ≤ᵣ
             distance (act h y) (act h x) + (distance (act h x) (act' g x) + distance (act h y) (act' g y))
          final-x6 = transport +-assoc {λ p → distance (act' g x) (act' g y) ≤ᵣ p} final-x5
          final-3 : distance (act' g x) (act h x) < ε/2
          final-3 = act'-lemma g st-g x st-x h ι-h-g ε/2 st-ε/2 positive-ε/2
          final-4 : distance (act h x) (act' g x) < ε/2
          final-4 = transport (symmetry (act' g x) (act h x)) {λ z → z < ε/2} final-3
          final-7 : distance (act' g y) (act h y) < ε/2
          final-7 = act'-lemma g st-g y st-y h ι-h-g ε/2 st-ε/2 positive-ε/2
          final-8 : distance (act h y) (act' g y) < ε/2
          final-8 = transport (symmetry (act' g y) (act h y)) {λ z → z < ε/2} final-7
          final-x7 :
            distance (act h x) (act' g x) + distance (act h y) (act' g y) ≤ᵣ ε/2 + ε/2
          final-x7 = ≤ᵣ-plus-both _ _ _ _ (inr final-4) (inr final-8)
          final-x8 :
            distance (act h x) (act' g x) + distance (act h y) (act' g y) ≤ᵣ ε
          final-x8 = transport (/2r-half {ε})
                       {λ p → distance (act h x) (act' g x) + distance (act h y) (act' g y) ≤ᵣ p}
                       final-x7
          final-x9 :
            distance (act h y) (act h x) + (distance (act h x) (act' g x) + distance (act h y) (act' g y)) ≤ᵣ
            distance (act h y) (act h x) + ε
          final-x9 = ≤ᵣ-plus-left _ _ (distance (act h y) (act h x)) final-x8
          final-x10 :
            distance (act' g x) (act' g y) ≤ᵣ distance (act h y) (act h x) + ε
          final-x10 = ≤ᵣ-tran _ _ _ final-x6 final-x9
          final-x11 :
            distance (act' g x) (act' g y) ≤ᵣ K · distance y x + ε
          final-x11 = transport final-1 {λ p → distance (act' g x) (act' g y) ≤ᵣ p + ε} final-x10
          final-x12 :
            distance (act' g x) (act' g y) ≤ᵣ K · distance x y + ε
          final-x12 = transport (symmetry y x) {λ p → distance (act' g x) (act' g y) ≤ᵣ K · p + ε} final-x11

      difference-ε : ∀ (ε : ℝ) → 0r < ε → distance (act' g x) (act' g y) ≤ᵣ K · distance x y + ε
      difference-ε = ax-Transfer-EI Φ (λ ε → λ st-ε → fromInternal (difference-ε-st ε st-ε)) std-Φ where
        Φ : TransferPred
        Φ = ∀' ℝ λ ε → int' (0r < ε → distance (act' g x) (act' g y) ≤ᵣ K · distance x y + ε)
        std-Φ :
          st ℝ *∧* (∀ (a : ℝ) → st a → st (0r < a → distance (act' g x) (act' g y) ≤ᵣ K · distance x y + a))
        std-Φ =
          st-ℝ , λ a st-a →
          st-→ _ (st-fun _ _ (_<_ 0r) a (st-fun _ _ _<_ 0r st-< st-0r) st-a) _
             (st-fun _ _ (_≤ᵣ_ (distance (act' g x) (act' g y)))
             (K · distance x y + a)
             (st-fun _ _ _≤ᵣ_ (distance (act' g x) (act' g y))
             st-≤ᵣ (st-fun _ _ (distance (act' g x)) (act' g y)
             (st-fun _ _ distance (act' g x)
             st-distance (act'-st-valued g st-g x st-x))
             (act'-st-valued g st-g y st-y)))
             (st-fun _ _ (_+_ (K · distance x y)) a
             (st-fun _ _ _+_ (K · distance x y)
             st-+ (st-fun _ _ (_·_ K) (distance x y)
             (st-fun _ _ _·_ K st-· st-K)
             (st-fun _ _ (distance x) y (st-fun _ _ distance x st-distance st-x) st-y))) st-a))
      difference-0 : distance (act' g x) (act' g y) ≤ᵣ K · distance x y
      difference-0 = lemma-ε-of-room-plus-≤ᵣ _ _ difference-ε

    act'-lipschitz! :  ∀ (g : G) →
                       ∀ (x : M) →
                       ∀ (y : M) →
                       distance (act' g x) (act' g y) ≤ᵣ (K · distance x y)
    act'-lipschitz! = ax-Transfer-EI Φ act'-lipschitz-st! std-Φ where
      Φ : TransferPred
      Φ = ∀' G λ g → ∀' M λ x → ∀' M λ y → int' (distance (act' g x) (act' g y) ≤ᵣ K · distance x y)
      std-Φ : st G *∧* (∀ (g : G) → st g → st M *∧* (∀ (x : M) → st x → st M *∧* (∀ (y : M) → st y →
              st (distance (act' g x) (act' g y) ≤ᵣ K · distance x y))))
      std-Φ = st-G , λ g st-g → st-M , λ x st-x → st-M , λ y st-y →
        st-fun _ _ (_≤ᵣ_ (distance (act' g x) (act' g y)))
          (K · distance x y)
          (st-fun _ _ _≤ᵣ_ (distance (act' g x) (act' g y))
          st-≤ᵣ (st-fun _ _ (distance (act' g x)) (act' g y)
          (st-fun _ _ distance (act' g x)
          st-distance (act'-st-valued g st-g x st-x)) (act'-st-valued g st-g y st-y)))
          (st-fun _ _ (_·_ K) (distance x y)
          (st-fun _ _ _·_ K st-· st-K) (st-fun _ _ (distance x) y
          (st-fun _ _ distance x st-distance st-x) st-y))

    act'-S-uniform-continuity : ∀ (g : G) →
                                ∀ (x : M) → 
                                ∀ (y : M) → nearby x y → nearby (act' g x) (act' g y)
    act'-S-uniform-continuity g x y x-near-y ε st-ε positive-ε = agx-near-agy where
      s : ℝ
      s = K' · ε
      st-s : st s
      st-s = st-fun _ _ (_·_ K') ε (st-fun _ _ _·_ K' st-· st-K') st-ε
      positive-s : 0r < s
      positive-s = step-3 where
        step-1 : K' · 0r < s
        step-1 = <-mult 0r ε K' positive-K' positive-ε
        step-2 : K' · 0r ≡ 0r
        step-2 = ·-null-left
        step-3 : 0r < s
        step-3 = transport step-2 {λ x → x < s} step-1
      dxy-under-s : distance x y < s
      dxy-under-s = x-near-y s st-s positive-s
      kdxy-under-ks : K · distance x y < K · s
      kdxy-under-ks = <-mult (distance x y) s K positive-K (x-near-y s st-s positive-s)
      kK'ε-equals-ε : K · s ≡ ε
      kK'ε-equals-ε = tran (tran step-1 step-2) step-3 where
        step-1 : K · (K' · ε) ≡ (K · K') · ε
        step-1 = sym ·-assoc
        step-2 : (K · K') · ε ≡ 1r · ε
        step-2 = cong (λ x → x · ε) (·-inverse-right (λ _ → positive-K))
        step-3 : 1r · ε ≡ ε
        step-3 = ·-unit-left
      kdxy-under-ε : K · distance x y < ε
      kdxy-under-ε = transport kK'ε-equals-ε {λ p → (K · distance x y) < p} kdxy-under-ks
      agx-near-agy : distance (act' g x) (act' g y) < ε
      agx-near-agy = by-cases _ case-1 case-2 (act'-lipschitz! g x y) where
        case-1 : distance (act' g x) (act' g y) ≡ K · distance x y →
                 distance (act' g x) (act' g y) < ε
        case-1 p = transport (sym p) {λ p → p < ε} kdxy-under-ε
        case-2 : distance (act' g x) (act' g y) < K · distance x y →
                 distance (act' g x) (act' g y) < ε
        case-2 p = <-tran _ _ _ p kdxy-under-ε
      
    act'-continuity : ∀ (g : G) → ∀ (m : M) →
                      ∀ (ε : ℝ) → 0r < ε →
                      ∃ λ (δ : ℝ) → (0r < δ) ∧ (
                      ∀ (m' : M) → distance m m' < δ → distance (act' g m) (act' g m') < ε)
    act'-continuity x m ε positive-ε = K' · ε , (positive-K'ε , helper) where
      positive-K'ε : 0r < K' · ε
      positive-K'ε = transport (·-null-left) {λ z → z < K' · ε} (<-mult 0r ε K' positive-K' positive-ε)
      helper : (m' : M) → distance m m' < K' · ε → distance (act' x m) (act' x m') < ε
      helper m' p = step-5 where
        step-1 : distance (act' x m) (act' x m') ≤ᵣ K · distance m m'
        step-1 = act'-lipschitz! x m m'
        step-2 : K · distance m m' < K · (K' · ε)
        step-2 = <-mult _ _ _ positive-K p
        step-3 : K · (K' · ε) ≡ ε
        step-3 =
          tran (sym (·-assoc {K} {K'} {ε})) (
          tran (cong (λ z → z · ε) (
          ·-inverse-right (λ _ → positive-K))) ·-unit-left)
        step-4 : K · distance m m' < ε
        step-4 = transport step-3 {λ z → K · distance m m' < z} step-2
        step-5 : distance (act' x m) (act' x m') < ε
        step-5 = by-cases _ case-1 case-2 step-1 where
          case-1 : distance (act' x m) (act' x m') ≡ K · distance m m' →
                   distance (act' x m) (act' x m') < ε
          case-1 p = transport (sym p) {λ p → p < ε} step-4
          case-2 : distance (act' x m) (act' x m') < K · distance m m' →
                   distance (act' x m) (act' x m') < ε
          case-2 p = <-tran _ _ _ p step-4

  -- We prove that the action G × M → M we constructed satisfies faithfulness on every
  -- finite subgroup X < G. We need ∀X.∀x∈X.∃m∈M. x≠1 → x@m≠m. By internality, it suffices
  -- to prove ∀ˢᵗX.∀ˢᵗx∈X.∃m∈M. x≠1 → x@m≠m, so we establish the latter.
  record Faithfulness : ESet where
    field
      X<G : PeriodicSubgroup G#
    open PeriodicSubgroup X<G renaming
      ( Source to X#
      ; Map to emb
      ; Map-identity to emb-identity
      ; Map-operation to emb-operation
      ; Map-injective to emb-injective
      ; Map-power to emb-power
      )
    field
      st-X# : st X#
      st-emb : st emb
    open PeriodicGroup X# renaming
      ( Carrier to X
      ; identity to 1X
      ; operation to xX
      ; inverse to iX
      ; assoc to X-associative
      ; unit-left to X-unit-left
      ; unit-right to X-unit-right
      ; inverse-left to X-inverse-left
      ; inverse-right to X-inverse-right
      ; order to X-order
      ; order-minimal to X-order-minimal
      )

    st-X : st X
    st-X = st-fun _ _ PeriodicGroup.Carrier X# st-PeriodicGroup-Carrier st-X#

    st-1X : st 1X
    st-1X = st-fun-d _ _ PeriodicGroup.identity X# st-PeriodicGroup-identity st-X#

    st-X-order : st X-order
    st-X-order = st-fun-d _ _ PeriodicGroup.order X# st-PeriodicGroup-order st-X#

    -- We prove that X acts on M using a meet-in-the-middle argument.
    xact : X → M → M
    xact x m = act' (emb x) m

    xact-st-valued : ∀ (x : X) → st x → ∀ (m : M) → st m → st (act' (emb x) m)
    xact-st-valued x st-x m st-m = act'-st-valued (emb x) (st-fun _ _ emb x st-emb st-x) m st-m

    xact-identity : ∀ (m : M) → xact 1X m ≡ m
    xact-identity m = tran xact-1X-equals-act'-1G (act'-identity m) where
      xact-1X-equals-act'-1G : xact 1X m ≡ act' 1G m
      xact-1X-equals-act'-1G = transport emb-identity {λ z → xact 1X m ≡ act' z m} refl

    xact-operation : ∀ (x y : X) (m : M) → xact x (xact y m) ≡ xact (xX x y) m
    xact-operation x y m = tran step-1 step-2 where
      step-1 : xact x (xact y m) ≡ act' (xG (emb x) (emb y)) m
      step-1 = act'-operation (emb x) (emb y) m
      step-2 : act' (xG (emb x) (emb y)) m ≡ act' (emb (xX x y)) m
      step-2 = cong (λ z → act' z m) (sym (emb-operation x y))

    xact-continuity : ∀ (x : X) → ∀ (m : M) →
                      ∀ (ε : ℝ) → 0r < ε →
                      ∃ λ (δ : ℝ) → (0r < δ) ∧ (
                      ∀ (m' : M) → distance m m' < δ → distance (xact x m) (xact x m') < ε)
    xact-continuity x m ε positive-ε = act'-continuity (emb x) m ε positive-ε
    
    X-Action : PeriodicDiscreteAction X# M#'
    X-Action =
      record { Map = xact
             ; isPeriodicDiscreteAction =
               record { isGroupAction =
                 record { action-identity = xact-identity
                        ; action-operation = xact-operation }
                      ; continuity = xact-continuity
                      }
             }

    module Given (x : X) (st-x : st x) (x-not-id : x ≡ 1X → ⊥) where
      st-emb-x : st (emb x)
      st-emb-x = st-fun _ _ emb x st-emb st-x

      -- We have a standard element x ∈ G, so we can pick a h with ι(h,x).
      h : H
      h = proj₁ (Map-exists (emb x) st-emb-x)

      ι-h-x : ι h (emb x)
      ι-h-x = proj₂ (Map-exists (emb x) st-emb-x)

      -- Since x≠1, h≠1.

      emb-x-not-id : emb x ≡ 1G → ⊥
      emb-x-not-id emb-x-equals-id = x-not-id (emb-injective _ _ (tran emb-x-equals-id (sym emb-identity)))

      h-not-id : h ≡ 1H → ⊥
      h-not-id h-equals-id = emb-x-not-id step-2 where
        step-1 : ι 1H (emb x)
        step-1 = transport* h-equals-id {λ z → ι z (emb x)} ι-h-x
        step-2 : emb x ≡ 1G
        step-2 = Map-unique-Target (emb x) st-emb-x 1G st-1G 1H step-1 ι-preserves-unit

      -- We prove that ι(h,x) → ι(hⁿ,xⁿ) for all standard n ∈ ℕ. Note that this requires
      -- a style of argument known as external induction, and the implication would not
      -- hold for nonstandard n.

      ι-hn-xn : ∀ (n : ℕ) → st n → ι (FiniteGroup.power H# h n) (Group.power G# (emb x) n)
      ι-hn-xn n st-n = external-induction
                         {λ n → ι (FiniteGroup.power H# h n) (Group.power G# (emb x) n)}
                         (Map-preserves-unit st-G#) ψ-inductive n st-n where
        ψ-inductive : ∀ k → st k → ι (FiniteGroup.power H# h k) (Group.power G# (emb x) k) →
                      ι (FiniteGroup.power H# h (suc k)) (Group.power G# (emb x) (suc k))
        ψ-inductive k st-k ι-hk-xk =
          Map-homomorphism h hk (emb x) st-emb-x xk st-xk ι-h-x ι-hk-xk where
          hk : H
          hk = FiniteGroup.power H# h k
          xk : G
          xk = Group.power G# (emb x) k
          st-xk : st xk
          st-xk =
            st-fun _ _ (Group.power G# (emb x)) k
            (st-fun _ _ (Group.power G#) (emb x)
            (st-fun-d _ _ Group.power G# st-Group-power st-G#) st-emb-x) st-k

      -- Since we have ι(hⁿ,xⁿ) for all standard n∈ℕ, and the order ord(x) belongs to the
      -- standard naturals, it follows that ord(h) < ord(x), and hence ord(h) also belongs
      -- among the standard naturals.

      h-ordx-equals-1H : FiniteGroup.power H# h (X-order x) ≡ 1H
      h-ordx-equals-1H = step-6  where
        step-1 : ι (FiniteGroup.power H# h (X-order x)) (Group.power G# (emb x) (X-order x))
        step-1 = ι-hn-xn (X-order x) (st-fun _ _ X-order x st-X-order st-x)
        step-2 : PeriodicGroup.power X# x (X-order x) ≡ 1X
        step-2 = PeriodicGroup.order-identity X# x
        step-3 : emb (PeriodicGroup.power X# x (X-order x)) ≡ 1G
        step-3 = tran (cong emb step-2) emb-identity
        step-4 : Group.power G# (emb x) (X-order x) ≡ 1G
        step-4 = tran (sym (emb-power x (X-order x))) step-3
        step-5 : ι (FiniteGroup.power H# h (X-order x)) 1G
        step-5 = transport* step-4 {λ z → ι (FiniteGroup.power H# h (X-order x)) z}
                   step-1
        step-6 : FiniteGroup.power H# h (X-order x) ≡ 1H
        step-6 = Map-unique-Source 1G st-1G (FiniteGroup.power H# h (X-order x))
                   step-5 1H (Map-preserves-unit st-G#)

      h-order : FiniteGroup.order H# h ≤ X-order x
      h-order =
        ℕ-induction {_} {λ n → X-order x ≡ n → FiniteGroup.order H# h ≤ n} case-A case-B (X-order x) refl where
        case-A : X-order x ≡ 0 → FiniteGroup.order H# h ≤ 0
        case-A ordx-equals-0 = absurd (PeriodicGroup.order-nonzero X# x ordx-equals-0)
        case-B : ∀ (k : ℕ) → (X-order x ≡ k → FiniteGroup.order H# h ≤ k) →
                             X-order x ≡ suc k → FiniteGroup.order H# h ≤ (suc k)
        case-B k ihyp ord-x-equals-suc-k = step-2 where
          step-1 : FiniteGroup.power H# h (suc k) ≡ 1H
          step-1 = transport ord-x-equals-suc-k {λ n → FiniteGroup.power H# h n ≡ 1H} h-ordx-equals-1H
          step-2 : FiniteGroup.order H# h ≤ suc k
          step-2 = FiniteGroup.order-minimal H# h k step-1

      open import IST.NewmansTheorem

      -- We apply the corollary of Newman's theorem to obtain a standard ν
      -- such that for any finite group G, g∈G and faithful discrete action
      -- @ of G on the manifold M, we can find some n < ord(g) and m'∈M
      -- such that gⁿ@m' is ν-far from m'.
      -- In particular, we shall find n < ord(h) and m'∈M such that
      -- hⁿ@m' is ν-far m'. Since ord(h) is standard, so is n.

      by-newman-1 : ∃ λ (ν : ℝ) → (0r < ν) ∧ (
        ∀ (G : FiniteGroup) →
        ∀ (g : FiniteGroup.Carrier G) →
        ∀ (A : DiscreteAction G M#') →
        (g ≡ FiniteGroup.identity G → ⊥) →
        (∀ (x : FiniteGroup.Carrier G) → (x ≡ FiniteGroup.identity G → ⊥) →
          ∃ λ (m : M) →
          DiscreteAction.Map A x m ≡ m → ⊥) →
        ∃ λ (n : ℕ) → ∃ λ (m : M) →
        (n ≤ FiniteGroup.order G g) ∧
        (ν < distance m (DiscreteAction.Map A (FiniteGroup.power G g n) m)))
      by-newman-1 =
        NewmanSpace.newman-constant M# , (NewmanSpace.isPositive M#) ,
        (λ G g A p → NewmanSpace.isNewmanConstant M# G g p A) -- newman-corollary M#

      ν : ℝ
      ν = proj₁ by-newman-1

      st-ν : st ν
      st-ν = st-fun _ _ NewmanSpace.newman-constant M# st-NewmanSpace-newman-constant st-M#

      positive-ν : 0r < ν
      positive-ν = proj₁ (proj₂ by-newman-1)

      by-newman-2 : 
        ∀ (G : FiniteGroup) →
        ∀ (g : FiniteGroup.Carrier G) →
        ∀ (A : DiscreteAction G M#') →
        (g ≡ FiniteGroup.identity G → ⊥) →
        (∀ (x : FiniteGroup.Carrier G) → (x ≡ FiniteGroup.identity G → ⊥) →
          ∃ λ (m : M) →
          DiscreteAction.Map A x m ≡ m → ⊥) →
        ∃ λ (n : ℕ) → ∃ λ (m : M) →
        (n ≤ FiniteGroup.order G g) ∧
        (ν < distance m (DiscreteAction.Map A (FiniteGroup.power G g n) m))
      by-newman-2 = proj₂ (proj₂ by-newman-1)

      by-newman-3 :
        ∃ λ (n : ℕ) → ∃ λ (m : M) →
        (n ≤ FiniteGroup.order H# h) ∧
        (ν < distance m (act (FiniteGroup.power H# h n) m))
      by-newman-3 = by-newman-2 H# h A# h-not-id act-faithful

      n' : ℕ
      n' = proj₁ by-newman-3

      m' : M
      m' = proj₁ (proj₂ by-newman-3)

      n'-less-than-order : n' ≤ FiniteGroup.order H# h
      n'-less-than-order = proj₁ (proj₂ (proj₂ by-newman-3))

      st-n' : st n'
      st-n' = bounded-st (X-order x) (st-fun _ _ X-order x st-X-order st-x) n'
        (≤-tran n' (FiniteGroup.order H# h) (X-order x) n'-less-than-order h-order)

      hn' : H
      hn' = FiniteGroup.power H# h n'

      hn'm'-ν-far-from-m' : ν < distance m' (act hn' m')
      hn'm'-ν-far-from-m' = proj₂ (proj₂ (proj₂ by-newman-3))

      hn'm'-not-near-m' : nearby (act hn' m') m' → ⊥
      hn'm'-not-near-m' hn'm'-near-m' = <-asym-1 _ _ step-3 refl where
        step-1 : ν < distance (act hn' m') m'
        step-1 = transport (symmetry m' (act hn' m')) {λ z → ν < z} hn'm'-ν-far-from-m'
        step-2 : distance (act hn' m') m' < ν
        step-2 = hn'm'-near-m' ν st-ν positive-ν
        step-3 : ν < ν
        step-3 = <-tran ν (distance (act hn' m') m') ν step-1 step-2

      -- The manifold element m'∈M might not satisfy standardness. Fortunately, by the
      -- compactness of M, we can find a standard neighbor m∈M. 

      m : M
      m = proj₁ (compact m')

      st-m : st m
      st-m = proj₁ (proj₂ (compact m'))

      m-near-m' : nearby m m'
      m-near-m' = proj₂ (proj₂ (compact m'))

      hn'm-near-hn'm' : nearby (act hn' m) (act hn' m')
      hn'm-near-hn'm' = S-uniform-continuity hn' m m' m-near-m'

      hn'm-not-near-m : nearby (act hn' m) m → ⊥
      hn'm-not-near-m hn'm-near-m = hn'm'-not-near-m' step-3 where
        step-1 : nearby (act hn' m') (act hn' m)
        step-1 = symmetric _ _ hn'm-near-hn'm'
        step-2 : nearby (act hn' m') m
        step-2 = transitive _ _ _ step-1 hn'm-near-m
        step-3 : nearby (act hn' m') m'
        step-3 = transitive _ _ _ step-2 m-near-m'

      -- By the standardness of m, we have xⁿ@m near hⁿ@m, and since
      -- hⁿ@m lies far from m, so does xⁿ@m. Hence, xⁿ@m ≠ m.

      xn' : X
      xn' = PeriodicGroup.power X# x n'
      
      st-xn' : st xn'
      st-xn' = st-fun _ _ (PeriodicGroup.power X# x) n'
        (st-fun _ _ (PeriodicGroup.power X#) x
        (st-fun-d _ _ PeriodicGroup.power X# st-PeriodicGroup-power st-X#) st-x) st-n'

      xn'm-near-hn'm : nearby (xact xn' m) (act hn' m)
      xn'm-near-hn'm = act'-lemma (emb xn') st-emb-xn' m st-m hn' ι-hn'-xn' where
        st-emb-xn' : st (emb xn')
        st-emb-xn' = st-fun _ _ emb xn' st-emb
          (st-fun _ _ (PeriodicGroup.power X# x) n'
          (st-fun _ _ (PeriodicGroup.power X#) x
          (st-fun-d _ _ PeriodicGroup.power X# st-PeriodicGroup-power st-X#) st-x) st-n' )
        ι-hn'-xn' : ι hn' (emb xn')
        ι-hn'-xn' = transport* (sym (emb-power x n')) {λ z → ι hn' z} (ι-hn-xn n' st-n')

      xn'm-not-near-m : nearby (xact xn' m) m → ⊥
      xn'm-not-near-m xn'm-near-m = hn'm-not-near-m step-2 where
        step-1 : nearby (act hn' m) (xact xn' m)
        step-1 = symmetric _ _ xn'm-near-hn'm
        step-2 : nearby (act hn' m) m
        step-2 = transitive _ _ _ step-1 xn'm-near-m

      xn'm-not-equals-m : xact xn' m ≡ m → ⊥
      xn'm-not-equals-m xn'm-equals-m = xn'm-not-near-m xn'm-near-m where
        xn'm-near-m : nearby (xact xn' m) m
        xn'm-near-m = transport* (sym xn'm-equals-m) {λ z → nearby z m} (reflexive m)

      -- From xⁿ@m ≠ m, it follows that x@m ≠ m. We chose x arbitrarily, so we get
      -- faithfulness.

      xm-not-equals-m : xact x m ≡ m → ⊥
      xm-not-equals-m xm-equals-m =
        xn'm-not-equals-m (PeriodicDiscreteAction.power-faithful X-Action x m n' xm-equals-m)

      exists-xm-not-equals-m : ∃* λ (m : M) → (st m) *∧* internal (xact x m ≡ m → ⊥)
      exists-xm-not-equals-m = m , st-m , fromInternal xm-not-equals-m
    open Given

    faithfulness-st : ∀ (x : X) → st x → (x ≡ 1X → ⊥) →
                      ∃* λ (m : M) → (st m) *∧* internal (xact x m ≡ m → ⊥)
    faithfulness-st = exists-xm-not-equals-m

    faithfulness-var : ∀ (x : X) → st x → ∃* λ (m : M) → (st m) *∧* internal ((x ≡ 1X → ⊥) → xact x m ≡ m → ⊥)
    faithfulness-var x st-x = by-cases* _ case-1 case-2 (excluded-middle (x ≡ 1X)) where
      zm : M
      zm = NewmanSpace.inhabitant M#
      st-zm : st zm
      st-zm = st-fun-d _ _ NewmanSpace.inhabitant M# st-NewmanSpace-inhabitant st-M#
      case-1 : x ≡ 1X →
               ∃* λ (m : M) → (st m) *∧* internal ((x ≡ 1X → ⊥) → xact x m ≡ m → ⊥)
      case-1 x-equals-1 = zm , st-zm , fromInternal (λ x-neq-1 → absurd (x-neq-1 x-equals-1))
      case-2 : (x ≡ 1X → ⊥) →
               ∃* λ (m : M) → (st m) *∧* internal ((x ≡ 1X → ⊥) → xact x m ≡ m → ⊥)
      case-2 x-neq-1 = vm , st-vm , fromInternal (λ z → step-2) where
        step-1 : ∃* (λ m₁ → st m₁ *∧* internal (xact x m₁ ≡ m₁ → ⊥))
        step-1 = faithfulness-st x st-x x-neq-1
        vm : M
        vm = proj₁ step-1
        st-vm : st vm
        st-vm = proj₁ (proj₂ step-1)
        step-2 : xact x vm ≡ vm → ⊥
        step-2 = toInternal _ (proj₂ (proj₂ step-1))

    faithfulness : ∀ (x : X) → ∃ λ (m : M) → (x ≡ 1X → ⊥) → xact x m ≡ m → ⊥
    faithfulness = ax-Transfer-EI Φ faithfulness-var std-Φ where
      Φ : TransferPred
      Φ = ∀' X λ x → ∃' M λ m → int' ((x ≡ 1X → ⊥) → xact x m ≡ m → ⊥)
      std-Φ : st X *∧* (∀ (a : X) → st a → st M *∧*
        (∀ (e : M) → st e → st ((a ≡ 1X → ⊥) → xact a e ≡ e → ⊥)))
      std-Φ =
        st-X , λ a st-a → st-M , λ e st-e → st-→ (a ≡ 1X → ⊥)
        (st-→ (a ≡ 1X) (st-fun _ _ (_≡_ a) 1X (st-fun _ _ _≡_ a st-≡-full st-a) st-1X) ⊥ st-⊥) (xact a e ≡ e → ⊥)
        (st-→ (xact a e ≡ e) (st-fun _ _ (_≡_ (xact a e)) e (st-fun _ _ _≡_ (xact a e)
        st-≡-full (xact-st-valued a st-a e st-e)) st-e) ⊥ st-⊥)
