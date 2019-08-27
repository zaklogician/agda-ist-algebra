module IST.Safe.Groups where

open import IST.Safe.Base
open import IST.Safe.FiniteSets
open import IST.Safe.Naturals

record IsGroup
  (Carrier : Set)
  (identity : Carrier)
  (operation : Carrier → Carrier → Carrier)
  (inverse : Carrier → Carrier)
  : Set where
  field
    assoc : ∀ (x y z : Carrier) → operation (operation x y) z ≡ operation x (operation y z)
    unit-left : ∀ (x : Carrier) → operation identity x ≡ x
    unit-right : ∀ (x : Carrier) → operation x identity ≡ x
    inverse-left : ∀ (x : Carrier) → operation (inverse x) x ≡ identity
    inverse-right : ∀ (x : Carrier) → operation x (inverse x) ≡ identity
  power : Carrier → ℕ → Carrier
  power x zero = identity
  power x (suc n) = operation x (power x n)

record Group : Set₁ where
  field
    Carrier : Set
    identity : Carrier
    operation : Carrier → Carrier → Carrier
    inverse : Carrier → Carrier
    isGroup : IsGroup Carrier identity operation inverse
  open IsGroup isGroup public


record IsPeriodicGroup
  (Carrier : Set)
  (identity : Carrier)
  (operation : Carrier → Carrier → Carrier)
  (inverse : Carrier → Carrier)
  : Set where
  field
    isGroup : IsGroup Carrier identity operation inverse
  open IsGroup isGroup
  field
    order : Carrier → ℕ
    order-identity : ∀ g → power g (order g) ≡ identity
    order-minimal : ∀ g → ∀ n → power g (suc n) ≡ identity → order g ≤ (suc n)
    order-nonzero : ∀ g → order g ≡ 0 → ⊥
    
record PeriodicGroup : Set₁ where
  field
    Carrier : Set
    identity : Carrier
    operation : Carrier → Carrier → Carrier
    inverse : Carrier → Carrier
    isPeriodicGroup : IsPeriodicGroup Carrier identity operation inverse
  open IsPeriodicGroup isPeriodicGroup public
  open IsGroup isGroup public
  asGroup : Group
  asGroup =
    record { Carrier = Carrier
           ; identity = identity
           ; operation = operation
           ; inverse = inverse
           ; isGroup = isGroup
           }
  power-lemma : ∀ g → ∀ n → g ≡ identity → power g n ≡ identity
  power-lemma .(identity) zero refl = refl
  power-lemma .(identity) (suc n) refl = tran (unit-left (power identity n)) inductive-hypothesis where
    inductive-hypothesis : power identity n ≡ identity
    inductive-hypothesis = power-lemma identity n refl

  power-lemma-contrapositive : ∀ g → ∀ n → (power g n ≡ identity → ⊥) → g ≡ identity → ⊥
  power-lemma-contrapositive g n gn-not-identity g-identity = gn-not-identity (power-lemma g n g-identity)


record IsFiniteGroup
  (Carrier : Set)
  (identity : Carrier)
  (operation : Carrier → Carrier → Carrier)
  (inverse : Carrier → Carrier)
  : Set where
  field
    isGroup : IsGroup Carrier identity operation inverse
  open IsGroup isGroup
  field
    isFiniteSet : IsFiniteSet Carrier
    order : Carrier → ℕ
    order-identity : ∀ g → power g (order g) ≡ identity
    order-minimal : ∀ g → ∀ n → power g (suc n) ≡ identity → order g ≤ suc n
    order-nonzero : ∀ g → order g ≡ 0 → ⊥

record FiniteGroup : Set₁ where
  field
    Carrier : Set
    identity : Carrier
    operation : Carrier → Carrier → Carrier
    inverse : Carrier → Carrier
    isFiniteGroup : IsFiniteGroup Carrier identity operation inverse
  open IsFiniteGroup isFiniteGroup public
  open IsGroup isGroup public
  asGroup : Group
  asGroup =
    record { Carrier = Carrier
           ; identity = identity
           ; operation = operation
           ; inverse = inverse
           ; isGroup = isGroup
           }
  power-lemma : ∀ g → ∀ n → g ≡ identity → power g n ≡ identity
  power-lemma .(identity) zero refl = refl
  power-lemma .(identity) (suc n) refl = tran (unit-left (power identity n)) inductive-hypothesis where
    inductive-hypothesis : power identity n ≡ identity
    inductive-hypothesis = power-lemma identity n refl

  power-lemma-contrapositive : ∀ g → ∀ n → (power g n ≡ identity → ⊥) → g ≡ identity → ⊥
  power-lemma-contrapositive g n gn-not-identity g-identity = gn-not-identity (power-lemma g n g-identity)


record IsFiniteSubgroup
  (Source : FiniteGroup)
  (Target : Group)
  (Map : FiniteGroup.Carrier Source → Group.Carrier Target)
  : Set where
  open FiniteGroup Source public
  field
    Map-identity : Map identity ≡ Group.identity Target
    Map-operation : ∀ g h →
      Map (operation g h) ≡ Group.operation Target (Map g) (Map h)
    Map-injective : ∀ g h → Map g ≡ Map h → g ≡ h

record FiniteSubgroup (Target : Group) : Set₁ where
  field
    Source : FiniteGroup
    Map : FiniteGroup.Carrier Source → Group.Carrier Target
    isFiniteSubgroup : IsFiniteSubgroup Source Target Map
  open IsFiniteSubgroup isFiniteSubgroup public
  Map-power : ∀ g → ∀ n → Map (power g n) ≡ Group.power Target (Map g) n
  Map-power g zero = Map-identity
  Map-power g (suc n) = tran (Map-operation g gn) step-1 where
    gn : Carrier
    gn = power g n
    mgn : Group.Carrier Target
    mgn = Group.power Target (Map g) n
    inductive-hypothesis : Map gn ≡ mgn
    inductive-hypothesis = Map-power g n
    step-1 : Group.operation Target (Map g) (Map gn) ≡ Group.operation Target (Map g) mgn
    step-1 = cong (Group.operation Target (Map g)) inductive-hypothesis


record IsPeriodicSubgroup
  (Source : PeriodicGroup)
  (Target : Group)
  (Map : PeriodicGroup.Carrier Source → Group.Carrier Target)
  : Set where
  open PeriodicGroup Source public
  field
    Map-identity : Map identity ≡ Group.identity Target
    Map-operation : ∀ g h →
      Map (operation g h) ≡ Group.operation Target (Map g) (Map h)
    Map-injective : ∀ g h → Map g ≡ Map h → g ≡ h

record PeriodicSubgroup (Target : Group) : Set₁ where
  field
    Source : PeriodicGroup
    Map : PeriodicGroup.Carrier Source → Group.Carrier Target
    isPeriodicSubgroup : IsPeriodicSubgroup Source Target Map
  open IsPeriodicSubgroup isPeriodicSubgroup public
  Map-power : ∀ g → ∀ n → Map (power g n) ≡ Group.power Target (Map g) n
  Map-power g zero = Map-identity
  Map-power g (suc n) = tran (Map-operation g gn) step-1 where
    gn : Carrier
    gn = power g n
    mgn : Group.Carrier Target
    mgn = Group.power Target (Map g) n
    inductive-hypothesis : Map gn ≡ mgn
    inductive-hypothesis = Map-power g n
    step-1 : Group.operation Target (Map g) (Map gn) ≡ Group.operation Target (Map g) mgn
    step-1 = cong (Group.operation Target (Map g)) inductive-hypothesis
