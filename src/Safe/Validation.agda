module IST.Safe.Validation where

-- T. Chow on Hirsch-style criticism of mechanized proofs:
-- "As you know, one thing that a skeptic can say even when shown a formal 
-- proof is, Yes, you've produced a formal proof of *something*, but what 
-- you've proved isn't the statement that we know [..]"

-- To avoid Hirsch-style criticism, we give some basic examples to convince
-- the reader that our notion of group, periodic group, finite group, metric
-- space corresponds to the usual notions.

open import Agda.Primitive
open import IST.Safe.Base
open import IST.Safe.Naturals
open import IST.Safe.FiniteSets
open import IST.Safe.Reals
open import IST.Safe.Groups
open import IST.Safe.GroupActions
open import IST.Safe.MetricSpaces
open import IST.Safe.NewmansTheorem

-- ℤ/2ℤ forms a (finite, a fortiori periodic) group.

data ℤ₂ : Set where
  0₂ : ℤ₂
  1₂ : ℤ₂

infixl 10 _+₂_
_+₂_ : ℤ₂ → ℤ₂ → ℤ₂
0₂ +₂ y = y
1₂ +₂ 0₂ = 1₂
1₂ +₂ 1₂ = 0₂

+₂-assoc : ∀ (x y z : ℤ₂) → x +₂ y +₂ z ≡ x +₂ (y +₂ z)
+₂-assoc 0₂ y z = refl
+₂-assoc 1₂ 0₂ z = refl
+₂-assoc 1₂ 1₂ 0₂ = refl
+₂-assoc 1₂ 1₂ 1₂ = refl

+₂-unit-right : ∀ (x : ℤ₂) → x +₂ 0₂ ≡ x
+₂-unit-right 0₂ = refl
+₂-unit-right 1₂ = refl

+₂-inverse : ∀ (x : ℤ₂) → x +₂ x ≡ 0₂
+₂-inverse 0₂ = refl
+₂-inverse 1₂ = refl

ℤ/2ℤ : Group
ℤ/2ℤ = record
         { Carrier = ℤ₂
         ; identity = 0₂
         ; operation = _+₂_
         ; inverse = λ x → x
         ; isGroup = record
                       { assoc = +₂-assoc
                       ; unit-left = λ _ → refl
                       ; unit-right = +₂-unit-right
                       ; inverse-left = +₂-inverse
                       ; inverse-right = +₂-inverse
                       }
         }

order₂ : ℤ₂ → ℕ
order₂ 0₂ = suc zero
order₂ 1₂ = suc (suc zero)

order₂-identity : (g : ℤ₂) → IsGroup.power (Group.isGroup ℤ/2ℤ) g (order₂ g) ≡ 0₂
order₂-identity 0₂ = refl
order₂-identity 1₂ = refl

order₂-nonzero : (g : ℤ₂) → order₂ g ≡ 0 → ⊥
order₂-nonzero 0₂ ()
order₂-nonzero 1₂ ()

order₂-minimal : (g : ℤ₂) → (n : ℕ) → IsGroup.power (Group.isGroup ℤ/2ℤ) g (suc n) ≡ 0₂ → order₂ g ≤ suc n
order₂-minimal 0₂ n p = ≤-suc ≤-zero 
order₂-minimal 1₂ (suc zero) refl = ≤-suc (≤-suc ≤-zero)
order₂-minimal 1₂ (suc (suc n)) p = ≤-suc (≤-suc ≤-zero)

ℤ/2ℤ' : PeriodicGroup
ℤ/2ℤ' = record
          { Carrier = ℤ₂
          ; identity = 0₂
          ; operation = _+₂_
          ; inverse = λ x → x
          ; isPeriodicGroup = record
                                { isGroup =  Group.isGroup ℤ/2ℤ
                                ; order = order₂
                                ; order-identity = order₂-identity
                                ; order-minimal = order₂-minimal
                                ; order-nonzero = order₂-nonzero
                                }
          }

-- the order is determined by the definition

order₂-unique : ∀ (p : IsPeriodicGroup ℤ₂ 0₂ _+₂_ (λ x → x)) →
                (IsPeriodicGroup.order p 0₂ ≡ 1) ∧ (IsPeriodicGroup.order p 1₂ ≡ 2)
order₂-unique p = ord-0₂-equals-1 , ord-1₂-equals-2 where
  open IsPeriodicGroup p
  ord-0₂-equals-1 : order 0₂ ≡ 1
  ord-0₂-equals-1 = lemma (order 0₂) (order-minimal 0₂ zero refl) (order-nonzero 0₂) where
    lemma : ∀ x → x ≤ 1 → (x ≡ 0 → ⊥) → x ≡ 1
    lemma zero p q = absurd (q refl)
    lemma (suc .0) (≤-suc ≤-zero) q = refl
  ord-1₂-under-2 : order 1₂ ≤ 2
  ord-1₂-under-2 = order-minimal 1₂ (suc zero) refl
  ord-1₂-neq-1 : order 1₂ ≡ 1 → ⊥
  ord-1₂-neq-1 assumption = absurd (0₂-neq-1₂ 0₂-equals-1₂) where
    step-1 : IsGroup.power isGroup 1₂ (order 1₂) ≡ 0₂
    step-1 = order-identity 1₂
    step-2 : IsGroup.power isGroup 1₂ 1 ≡ 0₂
    step-2 = transport assumption {λ p → IsGroup.power isGroup 1₂ p ≡ 0₂} step-1
    step-3 : IsGroup.power isGroup 1₂ 1 ≡ 1₂
    step-3 = refl
    0₂-neq-1₂ : 0₂ ≡ 1₂ → ⊥
    0₂-neq-1₂ ()
    0₂-equals-1₂ : 0₂ ≡ 1₂
    0₂-equals-1₂ = tran (sym step-2) step-3
  ord-1₂-equals-2 : order 1₂ ≡ 2
  ord-1₂-equals-2 = lemma (order 1₂) ord-1₂-under-2 (order-nonzero 1₂) ord-1₂-neq-1 where
    lemma : ∀ x → x ≤ 2 → (x ≡ 0 → ⊥) → (x ≡ 1 → ⊥) → x ≡ 2
    lemma .0 ≤-zero q r = absurd (q refl)
    lemma .1 (≤-suc ≤-zero) q r = absurd (r refl)
    lemma .2 (≤-suc (≤-suc ≤-zero)) q r = refl
  

-- ℤ₂ forms a finite group

list₂ : List ℤ₂
list₂ = 0₂ ∷ (1₂ ∷ [])

has-all-elements₂ : ∀ (x : ℤ₂) → x ∈ list₂
has-all-elements₂ 0₂ = ∈-head
has-all-elements₂ 1₂ = ∈-tail ∈-head

finite₂ : IsFiniteSet ℤ₂
finite₂ = record { list-of-elements = list₂ ; has-all-elements = has-all-elements₂ }

ℤ/2ℤ'' : FiniteGroup
ℤ/2ℤ'' = record
           { Carrier = ℤ₂
           ; identity = 0₂
           ; operation = _+₂_
           ; inverse = λ x → x
           ; isFiniteGroup = record
                               { isGroup = Group.isGroup ℤ/2ℤ
                               ; isFiniteSet = finite₂
                               ; order = order₂
                               ; order-identity = order₂-identity
                               ; order-minimal = order₂-minimal
                               ; order-nonzero = order₂-nonzero
                               }
           }

-- The set of natural numbers is not finite.

infinite-ℕ : IsFiniteSet ℕ → ⊥
infinite-ℕ finite-ℕ = ≤-not-suc M contradiction where
  open IsFiniteSet finite-ℕ renaming (list-of-elements to list; has-all-elements to all)
  max : ∀ (x y : ℕ) → ∃ λ M → (x ≤ M) ∧ (y ≤ M)
  max zero y = y , ≤-zero , ≤-refl y
  max (suc x) zero = suc x , ≤-refl (suc x) , ≤-zero
  max (suc x) (suc y) with max x y
  max (suc x) (suc y) | M , x≤M , y≤M = suc M , ≤-suc x≤M , ≤-suc y≤M
  maximum : ∀ (nats : List ℕ) → ∃ λ M → ∀ z → z ∈ nats → z ≤ M
  maximum [] = zero , (λ x ())
  maximum (x ∷ xs) with maximum xs
  maximum (x ∷ xs) | M , M-dominates-xs with max x M
  maximum (x ∷ xs) | M , M-dominates-xs | M' , x≤M' , M≤M' = M' , M'-dominates-xs where
    M'-dominates-xs : ∀ z → z ∈ (x ∷ xs) → z ≤ M'
    M'-dominates-xs z ∈-head = x≤M'
    M'-dominates-xs z (∈-tail p) = ≤-tran z M M' (M-dominates-xs z p) M≤M'
  M : ℕ
  M = proj₁ (maximum list)
  M-dominates-list : ∀ (x : ℕ) → x ∈ list → x ≤ M
  M-dominates-list = proj₂ (maximum list)
  M-largest : ∀ (x : ℕ) → x ≤ M
  M-largest x = M-dominates-list x (all x)
  contradiction : suc M ≤ M
  contradiction = M-largest (suc M)

-- Metric spaces exist, in particular the discrete metric is a metric.

discrete : ℤ₂ → ℤ₂ → ℝ
discrete 0₂ 0₂ = 0r
discrete 0₂ 1₂ = 1r
discrete 1₂ 0₂ = 1r
discrete 1₂ 1₂ = 0r

discrete-nonnegative : ∀ (x y : ℤ₂) → discrete x y < 0r → ⊥
discrete-nonnegative 0₂ 0₂ p = <-asym-1 0r 0r p refl
discrete-nonnegative 0₂ 1₂ p = <-asym-2 0r 1r <-nontrivial p
discrete-nonnegative 1₂ 0₂ p = <-asym-2 0r 1r <-nontrivial p
discrete-nonnegative 1₂ 1₂ p = <-asym-1 0r 0r p refl

discrete-reflexive-1 : ∀ (x y : ℤ₂) → discrete x y ≡ 0r → x ≡ y
discrete-reflexive-1 0₂ 0₂ refl = refl
discrete-reflexive-1 0₂ 1₂ p = absurd (<-asym-1 0r 1r <-nontrivial (sym p))
discrete-reflexive-1 1₂ 0₂ p = absurd (<-asym-1 0r 1r <-nontrivial (sym p))
discrete-reflexive-1 1₂ 1₂ refl = refl

discrete-reflexive-2 : ∀ (x : ℤ₂) → discrete x x ≡ 0r
discrete-reflexive-2 0₂ = refl
discrete-reflexive-2 1₂ = refl

discrete-symmetry : ∀ (x y : ℤ₂) → discrete x y ≡ discrete y x
discrete-symmetry 0₂ 0₂ = refl
discrete-symmetry 0₂ 1₂ = refl
discrete-symmetry 1₂ 0₂ = refl
discrete-symmetry 1₂ 1₂ = refl

discrete-triangle : ∀ (x y z : ℤ₂) → discrete x z ≤ᵣ discrete x y + discrete y z
discrete-triangle 0₂ 0₂ 0₂ = inl (sym +-unit-left)
discrete-triangle 0₂ 0₂ 1₂ = inl (sym +-unit-left)
discrete-triangle 0₂ 1₂ 0₂ = inr pos-2r
discrete-triangle 0₂ 1₂ 1₂ = inl (sym +-unit-right)
discrete-triangle 1₂ 0₂ 0₂ = inl (sym +-unit-right)
discrete-triangle 1₂ 0₂ 1₂ = inr pos-2r
discrete-triangle 1₂ 1₂ 0₂ = inl (sym +-unit-left)
discrete-triangle 1₂ 1₂ 1₂ = inl (sym +-unit-left)

ℤ₂-metric : MetricSpace
ℤ₂-metric =
  record { Carrier = ℤ₂
         ; distance = discrete
         ; isMetricSpace = record
             { nonnegative = discrete-nonnegative
             ; reflexive-1 = discrete-reflexive-1
             ; reflexive-2 = discrete-reflexive-2
             ; symmetry = discrete-symmetry
             ; triangle-≤ᵣ = discrete-triangle
             }
         }

-- Faithful, K-Lipschitz actions exist.

act : ℤ₂ → ℤ₂ → ℤ₂
act x y = x +₂ y

act-identity : ∀ m → act 0₂ m ≡ m
act-identity = Group.unit-left ℤ/2ℤ

act-operation : ∀ (g h : ℤ₂) → ∀ m → act g (act h m) ≡ act (g +₂ h) m
act-operation g h m = sym (+₂-assoc g h m)

action₂ : GroupAction ℤ/2ℤ ℤ₂
action₂ = record
  { Map = act
  ; isGroupAction = record
    { action-identity = act-identity
    ; action-operation = act-operation
    }
  }

act-faithful : ∀ (g : ℤ₂) → (g ≡ 0₂ → ⊥) → ∃ λ (m : ℤ₂) → act g m ≡ m → ⊥
act-faithful 0₂ p = absurd (p refl)
act-faithful 1₂ p = 1₂ , lemma 1₂ where
  lemma : ∀ x → act 1₂ x ≡ x → ⊥
  lemma 0₂ ()
  lemma 1₂ ()

K : ℝ
K = 1r

act-lipschitz : ∀ (g : ℤ₂) → ∀ (x y : ℤ₂) → discrete (act g x) (act g y) ≤ᵣ (K · discrete x y)
act-lipschitz 0₂ 0₂ 0₂ = transport (sym (·-null-left {K})) {λ p → 0r ≤ᵣ p} (inl refl)
act-lipschitz 0₂ 0₂ 1₂ = transport (sym (·-unit-right {K})) {λ p → 1r ≤ᵣ p} (inl refl)
act-lipschitz 0₂ 1₂ 0₂ = transport (sym (·-unit-right {K})) {λ p → 1r ≤ᵣ p} (inl refl)
act-lipschitz 0₂ 1₂ 1₂ = transport (sym (·-null-left {K})) {λ p → 0r ≤ᵣ p} (inl refl)
act-lipschitz 1₂ 0₂ 0₂ = transport (sym (·-null-left {K})) {λ p → 0r ≤ᵣ p} (inl refl)
act-lipschitz 1₂ 0₂ 1₂ = transport (sym (·-unit-right {K})) {λ p → 1r ≤ᵣ p} (inl refl)
act-lipschitz 1₂ 1₂ 0₂ = transport (sym (·-unit-right {K})) {λ p → 1r ≤ᵣ p} (inl refl)
act-lipschitz 1₂ 1₂ 1₂ = transport (sym (·-null-left {K})) {λ p → 0r ≤ᵣ p} (inl refl)

-- Newman spaces exist.

nonzero-lemma : ∀ n → (n ≡ 0 → ⊥) → 1 ≤ n
nonzero-lemma zero p = absurd (p refl)
nonzero-lemma (suc n) p = ≤-suc ≤-zero

alt-lemma-1 : ∀ g → (g ≡ 0₂ → ⊥) → g ≡ 1₂
alt-lemma-1 0₂ p = absurd (p refl)
alt-lemma-1 1₂ p = refl

alt-lemma-0 : ∀ g → (g ≡ 1₂ → ⊥) → g ≡ 0₂
alt-lemma-0 0₂ p = refl
alt-lemma-0 1₂ p = absurd (p refl)

ℤ₂-newman : NewmanSpace
ℤ₂-newman = record
              { asMetricSpace = ℤ₂-metric
              ; inhabitant = 0₂
              ; newman-constant = 1/2r
              ; isNewmanSpace = record
                { isPositive = pos-1/2r
                ; isNewmanConstant = newman
                }
              } where
  newman : (G : FiniteGroup) (g : FiniteGroup.Carrier G) → (g ≡ FiniteGroup.identity G → ⊥) →
           (A : DiscreteAction G ℤ₂-metric) →
           ( ∀ x → (x ≡ FiniteGroup.identity G → ⊥) → ∃ λ m → DiscreteAction.Map A x m ≡ m → ⊥) →
           ∃ λ n → ∃ λ m → (n ≤ FiniteGroup.order G g) ∧
           (1/2r < MetricSpace.distance ℤ₂-metric m (DiscreteAction.Map A (FiniteGroup.power G g n) m))
  newman G g p A nontriv-A  with nontriv-A g p
  newman G g p A nontriv-A | 0₂ , q = 1 , 0₂ , nonzero-lemma _ step-1 , step-3 where
    step-1 : IsFiniteGroup.order (FiniteGroup.isFiniteGroup G) g ≡ 0 → ⊥
    step-1 = FiniteGroup.order-nonzero G g
    m : ℤ₂
    m = DiscreteAction.Map A (FiniteGroup.operation G g (FiniteGroup.identity G)) 0₂
    m' : ℤ₂
    m' = DiscreteAction.Map A g 0₂
    m-equals-m' : m ≡ m'
    m-equals-m' = cong (λ z → DiscreteAction.Map A z 0₂) (FiniteGroup.unit-right G g)
    m'-equals-1₂ : m' ≡ 1₂
    m'-equals-1₂ = alt-lemma-1 m' q
    1₂-equals-m : 1₂ ≡ m
    1₂-equals-m = sym (tran m-equals-m' m'-equals-1₂)
    step-2 : discrete 0₂ m ≡ 1r
    step-2 = transport 1₂-equals-m {λ z → discrete 0₂ z ≡ 1r} refl
    step-3 : 1/2r < discrete 0₂ m
    step-3 = transport (sym step-2) {λ z → 1/2r < z} 1/2r-less-than-1r
  newman G g p A nontriv-A | 1₂ , q = 1 , 1₂ , nonzero-lemma _ step-1 , step-3 where
    step-1 : IsFiniteGroup.order (FiniteGroup.isFiniteGroup G) g ≡ 0 → ⊥
    step-1 = FiniteGroup.order-nonzero G g
    m : ℤ₂
    m = DiscreteAction.Map A (FiniteGroup.operation G g (FiniteGroup.identity G)) 1₂
    m' : ℤ₂
    m' = DiscreteAction.Map A g 1₂
    m-equals-m' : m ≡ m'
    m-equals-m' = cong (λ z → DiscreteAction.Map A z 1₂) (FiniteGroup.unit-right G g)
    m'-equals-0₂ : m' ≡ 0₂
    m'-equals-0₂ = alt-lemma-0 m' q
    0₂-equals-m : 0₂ ≡ m
    0₂-equals-m = sym (tran m-equals-m' m'-equals-0₂)
    step-2 : discrete 1₂ m ≡ 1r
    step-2 = transport 0₂-equals-m {λ z → discrete 1₂ z ≡ 1r} refl
    step-3 : 1/2r < discrete 1₂ m
    step-3 = transport (sym step-2) {λ z → 1/2r < z} 1/2r-less-than-1r
