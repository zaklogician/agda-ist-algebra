module IST.Safe.GroupActions where

open import IST.Safe.Base
open import IST.Safe.Naturals
open import IST.Safe.Reals
open import IST.Safe.MetricSpaces
open import IST.Safe.Groups

record IsGroupAction
  (Source : Group)
  (Target : Set)
  (Map : Group.Carrier Source → Target → Target)
  : Set where
  open Group Source
  field
    action-identity : ∀ m → Map identity m ≡ m
    action-operation : ∀ g h → ∀ m → Map g (Map h m) ≡ Map (operation g h) m

record GroupAction (Source : Group) (Target : Set) : Set where
  field
    Map : Group.Carrier Source → Target → Target
    isGroupAction : IsGroupAction Source Target Map
  open IsGroupAction isGroupAction public


record IsDiscreteAction
  (Source : FiniteGroup)
  (Target : MetricSpace)
  (Map : FiniteGroup.Carrier Source →
         MetricSpace.Carrier Target → MetricSpace.Carrier Target)
  : Set where
  open FiniteGroup Source
  open MetricSpace Target
  field
    isGroupAction : IsGroupAction (FiniteGroup.asGroup Source) (MetricSpace.Carrier Target) Map
    continuity : ∀ (g : FiniteGroup.Carrier Source) →
                 ∀ (m : MetricSpace.Carrier Target) →
                 ∀ (ε : ℝ) → 0r < ε → ∃ λ (δ : ℝ) → (0r < δ) ∧ (
                 ∀ (m' : MetricSpace.Carrier Target) →
                 distance m m' < δ →
                 distance (Map g m) (Map g m') < ε)


record DiscreteAction (Source : FiniteGroup) (Target : MetricSpace) : Set where
  field 
    Map : FiniteGroup.Carrier Source →
          MetricSpace.Carrier Target → MetricSpace.Carrier Target
    isDiscreteAction : IsDiscreteAction Source Target Map
  open IsDiscreteAction isDiscreteAction public
  open IsGroupAction isGroupAction public

  power-faithful : ∀ (g : FiniteGroup.Carrier Source) →
                   ∀ (m : MetricSpace.Carrier Target) →
                   ∀ (n : ℕ) → Map g m ≡ m → Map (FiniteGroup.power Source g n) m ≡ m
  power-faithful g m zero gm-equals-m = action-identity m
  power-faithful g m (suc n) gm-equals-m = tran (tran step-1 step-2) gm-equals-m where
    inductive-hypothesis : Map (FiniteGroup.power Source g n) m ≡ m
    inductive-hypothesis = power-faithful g m n gm-equals-m
    step-1 : Map (FiniteGroup.power Source g (suc n)) m ≡
             Map g (Map (FiniteGroup.power Source g n) m)
    step-1 = sym (action-operation g (FiniteGroup.power Source g n) m)
    step-2 : Map g (Map (FiniteGroup.power Source g n) m) ≡
             Map g m
    step-2 = cong (Map g) inductive-hypothesis


record IsPeriodicDiscreteAction
  (Source : PeriodicGroup)
  (Target : MetricSpace)
  (Map : PeriodicGroup.Carrier Source →
         MetricSpace.Carrier Target → MetricSpace.Carrier Target)
  : Set where
  open PeriodicGroup Source
  open MetricSpace Target
  field
    isGroupAction : IsGroupAction (PeriodicGroup.asGroup Source) (MetricSpace.Carrier Target) Map
    continuity : ∀ (g : PeriodicGroup.Carrier Source) →
                 ∀ (m : MetricSpace.Carrier Target) →
                 ∀ (ε : ℝ) → 0r < ε → ∃ λ (δ : ℝ) → (0r < δ) ∧ (
                 ∀ (m' : MetricSpace.Carrier Target) →
                 distance m m' < δ →
                 distance (Map g m) (Map g m') < ε)


record PeriodicDiscreteAction (Source : PeriodicGroup) (Target : MetricSpace) : Set where
  field 
    Map : PeriodicGroup.Carrier Source →
          MetricSpace.Carrier Target → MetricSpace.Carrier Target
    isPeriodicDiscreteAction : IsPeriodicDiscreteAction Source Target Map
  open IsPeriodicDiscreteAction isPeriodicDiscreteAction public
  open IsGroupAction isGroupAction public

  power-faithful : ∀ (g : PeriodicGroup.Carrier Source) →
                   ∀ (m : MetricSpace.Carrier Target) →
                   ∀ (n : ℕ) → Map g m ≡ m → Map (PeriodicGroup.power Source g n) m ≡ m
  power-faithful g m zero gm-equals-m = action-identity m
  power-faithful g m (suc n) gm-equals-m = tran (tran step-1 step-2) gm-equals-m where
    inductive-hypothesis : Map (PeriodicGroup.power Source g n) m ≡ m
    inductive-hypothesis = power-faithful g m n gm-equals-m
    step-1 : Map (PeriodicGroup.power Source g (suc n)) m ≡
             Map g (Map (PeriodicGroup.power Source g n) m)
    step-1 = sym (action-operation g (PeriodicGroup.power Source g n) m)
    step-2 : Map g (Map (PeriodicGroup.power Source g n) m) ≡
             Map g m
    step-2 = cong (Map g) inductive-hypothesis
