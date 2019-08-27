{-# OPTIONS --omega-in-omega --no-pattern-matching #-}

module IST.PredicatedTopologies where

open import Agda.Primitive
open import IST.Base
open import IST.Reals

----
-- Def. A relational space consists of a carrier set C and a reflexive
-- binary predicate (the 'nearness predicate') on C.

record IsPredicatedSpace
  (Carrier : Set)
  (nearby : Carrier → Carrier → ESet)
  : ESet where
  field
    reflexive : ∀ x → nearby x x

record PredicatedSpace : ESet₁ where
  field
    Carrier : Set
    nearby : Carrier → Carrier → ESet
    isPredicatedSpace : IsPredicatedSpace Carrier nearby
  open IsPredicatedSpace isPredicatedSpace public


-- Def. A separable space is a relational space where no two standard points
-- are neighbors. (normally known as T1 space, we refer to those as Kolmogorov)

record IsSeparableSpace
  (Carrier : Set)
  (nearby : Carrier → Carrier → ESet)
  : ESet where
  field
    isPredicatedSpace : IsPredicatedSpace Carrier nearby
    separable : ∀ x → st x → ∀ y → st y → nearby x y → nearby y x → x ≡ y

record SeparableSpace : ESet₁ where
  field
    Carrier : Set
    nearby : Carrier → Carrier → ESet
    isSeparableSpace : IsSeparableSpace Carrier nearby
  open IsSeparableSpace isSeparableSpace public
  open IsPredicatedSpace isPredicatedSpace public


-- Def. A compact space is a relation space where every every element is near
-- a standard element.

record IsCompactSpace
  (Carrier : Set)
  (nearby : Carrier → Carrier → ESet)
  : ESet where
  field
    isPredicatedSpace : IsPredicatedSpace Carrier nearby
    compact : ∀ x → ∃* λ y → st y *∧* nearby y x

record CompactSpace : ESet₁ where
  field
    Carrier : Set
    nearby : Carrier → Carrier → ESet
    isCompactSpace : IsCompactSpace Carrier nearby
  open IsCompactSpace isCompactSpace public
  open IsPredicatedSpace isPredicatedSpace public


-- Def. A Hausdorff space is a relational space where two different standard
-- points do not share a neighbor.

record IsHausdorffSpace
  (Carrier : Set)
  (nearby : Carrier → Carrier → ESet)
  : ESet where
  field
    isPredicatedSpace : IsPredicatedSpace Carrier nearby
    hausdorff : ∀ x → st x → ∀ y → st y → ∀ z → nearby x z → nearby y z → x ≡ y

record HausdorffSpace : ESet₁ where
  field
    Carrier : Set
    nearby : Carrier → Carrier → ESet
    isHausdorffSpace : IsHausdorffSpace Carrier nearby
  open IsHausdorffSpace isHausdorffSpace public
  open IsPredicatedSpace isPredicatedSpace public
  -- Thm. Every Hausdorff space is separable.
  private
    separable : ∀ x → st x → ∀ y → st y → nearby x y → nearby y x → x ≡ y
    separable x st-x y st-y x-near-y y-near-x =
      hausdorff x st-x y st-y x (reflexive x) y-near-x
    isSeparableSpace : IsSeparableSpace Carrier nearby
    isSeparableSpace = record { isPredicatedSpace = isPredicatedSpace; separable = separable }
  open IsSeparableSpace isSeparableSpace public


-- Def. A compact Hausdorff space is a relational space that is also a compact
-- space. Duh.

record IsCompactHausdorffSpace
  (Carrier : Set)
  (nearby : Carrier → Carrier → ESet)
  : ESet where
  field
    isHausdorffSpace : IsHausdorffSpace Carrier nearby
    isCompactSpace : IsCompactSpace Carrier nearby

record CompactHausdorffSpace : ESet₁ where
  field
    Carrier : Set
    nearby : Carrier → Carrier → ESet
    isHausdorffSpace : IsHausdorffSpace Carrier nearby
    isCompactSpace : IsCompactSpace Carrier nearby
  open IsHausdorffSpace isHausdorffSpace public
  open IsPredicatedSpace isPredicatedSpace public
  open IsCompactSpace isCompactSpace public


-- Def. An equivalence space is a relational space whose
-- nearness predicate is transitive and symmetric.

record IsEquivalenceSpace
  (Carrier : Set)
  (nearby : Carrier → Carrier → ESet)
  : ESet where
  field
    isPredicatedSpace : IsPredicatedSpace Carrier nearby
    transitive : ∀ x y z → nearby x y → nearby y z → nearby x z
    symmetric : ∀ x y → nearby x y → nearby y x

record EquivalenceSpace : ESet₁ where
  field
    Carrier : Set
    nearby : Carrier → Carrier → ESet
    isEquivalenceSpace : IsEquivalenceSpace Carrier nearby
  open IsEquivalenceSpace isEquivalenceSpace public
  open IsPredicatedSpace isPredicatedSpace public


-- Def. A Hausdorff equivalence space is an equivalence space that is
-- also a Hausdorff space. Duh.

record IsHausdorffEquivalenceSpace
  (Carrier : Set)
  (nearby : Carrier → Carrier → ESet)
  : ESet where
  field
    isHausdorffSpace : IsHausdorffSpace Carrier nearby
    isEquivalenceSpace : IsEquivalenceSpace Carrier nearby

record HausdorffEquivalenceSpace : ESet₁ where
  field
    Carrier : Set
    nearby : Carrier → Carrier → ESet
    isHausdorffSpace : IsHausdorffSpace Carrier nearby
    isEquivalenceSpace : IsEquivalenceSpace Carrier nearby
  open IsHausdorffSpace isHausdorffSpace public
  open IsPredicatedSpace isPredicatedSpace public
  open IsEquivalenceSpace isEquivalenceSpace public


-- Def. A compact Hausdorff equivalence space is an equivalence space that is also a compact
-- space. Duh.

record IsCompactHausdorffEquivalenceSpace
  (Carrier : Set)
  (nearby : Carrier → Carrier → ESet)
  : ESet where
  field
    isHausdorffSpace : IsHausdorffSpace Carrier nearby
    isCompactSpace : IsCompactSpace Carrier nearby
    isEquivalenceSpace : IsEquivalenceSpace Carrier nearby

record CompactHausdorffEquivalenceSpace : ESet₁ where
  field
    Carrier : Set
    nearby : Carrier → Carrier → ESet
    isHausdorffSpace : IsHausdorffSpace Carrier nearby
    isCompactSpace : IsCompactSpace Carrier nearby
    isEquivalenceSpace : IsEquivalenceSpace Carrier nearby
  open IsHausdorffSpace isHausdorffSpace public
  open IsPredicatedSpace isPredicatedSpace public
  open IsCompactSpace isCompactSpace public
  open IsEquivalenceSpace isEquivalenceSpace public


open import IST.MetricSpaces

-- Thm. Every standard metric space induces a Hausdorff equivalence space by setting
-- x o- y ↔ ∀ˢ ε > 0. d(x,y) < ε
metric-to-hausdorff-equivalence : (MS : MetricSpace) → st MS → HausdorffEquivalenceSpace
metric-to-hausdorff-equivalence MS st-MS =
  record { Carrier = M
         ; nearby = nearby
         ; isHausdorffSpace = isHausdorffSpace
         ; isEquivalenceSpace = isEquivalenceSpace
         } where
  M : Set
  M = MetricSpace.Carrier MS

  st-M : st M
  st-M = st-MetricSpace-Carrier-full MS st-MS

  d : M → M → ℝ
  d = MetricSpace.distance MS

  st-d : st d
  st-d = st-MetricSpace-distance-full MS st-MS

  nearby : M → M → ESet
  nearby x y = ∀ (ε : ℝ) → st ε → 0r < ε → d x y < ε

  reflexive : ∀ x → nearby x x
  reflexive x ε st-ε 0r<ε = dxx<ε where
    open MetricSpace MS
    dxx<ε : d x x < ε
    dxx<ε = transport (sym (reflexive-2 x)) {λ z → z < ε} 0r<ε

  symmetric : ∀ x y → nearby x y → nearby y x
  symmetric x y x-near-y ε st-ε pos-ε = dyx<ε where
    open MetricSpace MS
    dxy<ε : d x y < ε
    dxy<ε = x-near-y ε st-ε pos-ε
    dyx<ε : d y x < ε
    dyx<ε = transport (symmetry x y) {λ p → p < ε} dxy<ε

  transitive : ∀ x y z → nearby x y → nearby y z → nearby x z
  transitive x y z x-near-y y-near-z ε st-ε pos-ε = dxz' where
    open MetricSpace MS
    ε/2 : ℝ
    ε/2 = ε /2r
    st-ε/2 : st ε/2
    st-ε/2 = st-/2r-v ε st-ε
    pos-ε/2 : 0r < ε/2
    pos-ε/2 = pos-/2r-v ε pos-ε
    dxy : d x y < ε/2
    dxy = x-near-y ε/2 st-ε/2 pos-ε/2
    dyz : d y z < ε/2
    dyz = y-near-z ε/2 st-ε/2 pos-ε/2
    dxy-dyx : d x y + d y z < ε/2 + ε/2
    dxy-dyx = <-tran _ _ _ step-1 step-2 where
      step-1 : d x y + d y z < ε/2 + d y z
      step-1 = <-plus (d x y) ε/2 (d y z) dxy
      step-2 : ε/2 + d y z < ε/2 + ε/2
      step-2 = transport +-comm {λ p → p < ε/2 + ε/2} (<-plus (d y z) ε/2 ε/2 dyz)
    dxz : d x z < ε/2 + ε/2
    dxz = triangle x y z (ε/2 + ε/2) dxy-dyx
    dxz' : d x z < ε
    dxz' = transport /2r-half {λ p → d x z < p} dxz

  isPredicatedSpace : IsPredicatedSpace M nearby
  isPredicatedSpace = record { reflexive = reflexive }

  isEquivalenceSpace : IsEquivalenceSpace M nearby
  isEquivalenceSpace =
    record { isPredicatedSpace = isPredicatedSpace
           ; transitive = transitive
           ; symmetric = symmetric
           }
  hausdorff : ∀ x → st x → ∀ y → st y → ∀ z → nearby x z → nearby y z → x ≡ y
  hausdorff x st-x y st-y z x-near-z y-near-z = reflexive-1 x y zero-dxy where
    open MetricSpace MS
    x-near-y : nearby x y
    x-near-y = transitive x z y x-near-z (symmetric y z y-near-z)
    x-near-y-int : (ε : ℝ) → st ε → internal (0r < ε → d x y < ε)
    x-near-y-int ε st-ε = fromInternal (x-near-y ε st-ε)
    st-dxy : st (d x y)
    st-dxy = st-fun _ _ (d x) y (st-fun _ _ d x st-d st-x) st-y
    Φ : TransferPred
    Φ = ∀' ℝ λ ε → int' (0r < ε → d x y < ε)
    std-Φ : st ℝ *∧* ((ε : ℝ) → st ε → st (0r < ε → d x y < ε))
    std-Φ = st-ℝ , (λ ε st-ε → st-→ (0r < ε)
                                    (st-fun _ _ (_<_ 0r) ε (st-fun _ _ _<_ 0r st-< st-0r) st-ε)
                                    (d x y < ε)
                                    (st-fun _ _ (_<_ (d x y)) ε (st-fun _ _ _<_ (d x y) st-< st-dxy) st-ε))
    dxy<ε : ∀ (ε : ℝ) → 0r < ε → d x y < ε
    dxy<ε = ax-Transfer-EI Φ x-near-y-int std-Φ
    zero-dxy : d x y ≡ 0r
    zero-dxy = lemma-ε-of-room (d x y) dxy<ε (nonnegative x y)
  
  isHausdorffSpace : IsHausdorffSpace M nearby
  isHausdorffSpace =
    record { isPredicatedSpace = isPredicatedSpace
           ; hausdorff = hausdorff
           }
