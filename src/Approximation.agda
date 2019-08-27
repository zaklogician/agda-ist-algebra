{-# OPTIONS --omega-in-omega --no-pattern-matching #-}

module IST.Approximation where

open import Agda.Primitive
open import IST.Base
open import IST.PredicatedTopologies


record IsApproximation
  (Source : Set)
  (Target : Set)
  (Map : Source → Target → ESet)
  : ESet where
  field
    Target-st : st Target
    Map-exists : ∀ (g : Target) → st g → ∃* λ (h : Source) → Map h g
    Map-unique-Source :
      ∀ (g : Target) → st g →
      ∀ (h₁ : Source) → Map h₁ g → ∀ (h₂ : Source) → Map h₂ g → h₁ ≡ h₂
    Map-unique-Target :
      ∀ (g₁ : Target) → st g₁ → ∀ (g₂ : Target) → st g₂ →
      ∀ (h : Source) → Map h g₁ → Map h g₂ → g₁ ≡ g₂

-- Map-cont :
--   ∀ (h₁ h₂ : Source) → ∀ (g₁ g₂ : Target) → Map h₁ g₁ → Map h₂ g₂ →
--   nearby h₁ h₂ → nearby g₁ g₂
-- -- makes no sense since S-continuity relies on the standardness
-- -- of the first element of the nearness relation.

record Approximation (Source : Set) (Target : Set) : ESet₁ where
  field
    Map : Source → Target → ESet
    isApproximation : IsApproximation Source Target Map
  open IsApproximation isApproximation public


record IsTopApproximation
  (Source : PredicatedSpace)
  (Target : SeparableSpace)
  (Map : PredicatedSpace.Carrier Source → SeparableSpace.Carrier Target → ESet)
  : ESet where
  open SeparableSpace Target renaming
    ( Carrier to G
    ; nearby to G-near
    )
  open PredicatedSpace Source renaming
    ( Carrier to H
    ; nearby to H-near
    )
  field
    Target-st : st G
    Map-exists : ∀ (g : G) → st g → ∃* λ (h : H) → Map h g
    Map-Source :
      ∀ (g : G) → st g →
      ∀ (h₁ : H) → Map h₁ g → ∀ (h₂ : H) → Map h₂ g → H-near h₁ h₂
    Map-Target :
      ∀ (g₁ : G) → st g₁ → ∀ (g₂ : G) → st g₂ →
      ∀ (h : H) → Map h g₁ → Map h g₂ → G-near g₁ g₂


record TopApproximation (Source : PredicatedSpace) (Target : SeparableSpace) : ESet₁ where
  field
    Map : PredicatedSpace.Carrier Source → SeparableSpace.Carrier Target → ESet
    isTopApproximation : IsTopApproximation Source Target Map
  open IsTopApproximation isTopApproximation public
  

open import IST.Groups

record IsFiniteGroupApproximation
  (Source : FiniteGroup)
  (Target : Group)
  (Map : FiniteGroup.Carrier Source → Group.Carrier Target → ESet)
  : ESet where
  field
    isApproximation : IsApproximation (FiniteGroup.Carrier Source) (Group.Carrier Target) Map
    Map-homomorphism :
      ∀ (h₁ h₂ : FiniteGroup.Carrier Source) →
      ∀ (g₁ : Group.Carrier Target) → st g₁ → ∀ (g₂ : Group.Carrier Target) → st g₂ →
      Map h₁ g₁ → Map h₂ g₂ → Map (FiniteGroup.operation Source h₁ h₂) (Group.operation Target g₁ g₂)
  open IsApproximation isApproximation
  open Group Target renaming
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
  open FiniteGroup Source renaming
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
  Map-preserves-unit : st Target → Map 1H 1G
  Map-preserves-unit st-Target = Map-1H-1G where
    st-1G : st 1G
    st-1G = st-fun-d _ _ Group.identity Target st-Group-identity st-Target
    1H-unique : ∀ (h : H) → Map h 1G → h ≡ 1H
    1H-unique h Map-h-1G = step-8 where
      step-1 : Map (xH h h) (xG 1G 1G) 
      step-1 = Map-homomorphism h h 1G st-1G 1G st-1G Map-h-1G Map-h-1G
      step-2 : Map (xH h h) 1G
      step-2 = transport* (G-unit-left 1G) {λ z → Map (xH h h) z} step-1
      step-3 : xH h h ≡ h
      step-3 = Map-unique-Source 1G st-1G (xH h h) step-2 h Map-h-1G
      step-4 : xH (iH h) (xH h h) ≡ xH (iH h) h
      step-4 = cong (λ z → xH (iH h) z) step-3
      step-5 : xH (xH (iH h) h) h ≡ xH (iH h) (xH h h)
      step-5 = H-associative (iH h) h h
      step-6 : xH 1H h ≡ xH (xH (iH h) h) h
      step-6 = sym (cong (λ z → xH z h) (H-inverse-left h))
      step-7 : h ≡ xH (xH (iH h) h) h
      step-7 = tran (sym (H-unit-left h)) step-6
      step-8 : h ≡ 1H
      step-8 = tran (tran (tran step-7 step-5) step-4) (H-inverse-left h)
    1H'-exists : ∃* λ (h : H) → Map h 1G
    1H'-exists = Map-exists 1G st-1G
    1H' : H
    1H' = proj₁ (Map-exists 1G st-1G)
    Map-1H'-1G : Map 1H' 1G
    Map-1H'-1G = proj₂ 1H'-exists
    1H'-equals-1H : 1H' ≡ 1H
    1H'-equals-1H = 1H-unique 1H' Map-1H'-1G
    Map-1H-1G : Map 1H 1G
    Map-1H-1G = transport* 1H'-equals-1H {λ z → Map z 1G} Map-1H'-1G  
  Map-preserves-unit-Target : st Target → ∀ (g : G) → st g → Map 1H g → g ≡ 1G
  Map-preserves-unit-Target st-Target g st-g Map-1H-g =
    Map-unique-Target g st-g 1G st-1G 1H Map-1H-g (Map-preserves-unit st-Target) where
    st-1G : st 1G
    st-1G = st-fun-d _ _ Group.identity Target st-Group-identity st-Target
    
record FiniteGroupApproximation (Source : FiniteGroup) (Target : Group) : ESet₁ where
  field
    Map : FiniteGroup.Carrier Source → Group.Carrier Target → ESet
    isFiniteGroupApproximation : IsFiniteGroupApproximation Source Target Map
  open IsFiniteGroupApproximation isFiniteGroupApproximation public
  open IsApproximation isApproximation public
