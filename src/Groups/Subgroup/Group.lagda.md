---
layout: default
file: "src/Groups/Subgroup/Group.lagda.md"
title: "Groups.Subgroup.Group module"
date: "2026-11-27"
author: "the agda-groups development team"
---

### A subgroup as a finite group

This is the `Groups.Subgroup.Group` module of the agda-groups library.

A subgroup H of a finite group G is a finite group in its own right (ADR
0001, § 6), so that a theorem about finite groups applies to a subgroup:
a Sylow subgroup of a subgroup, or a p-subgroup as a p-group.  Its
carrier is the set of the members of H, each with its proof of
membership, compared as elements of G; its operations and its equations
are G's, closed by the closure of H (the Agda Universal Algebra Library's
`setoidEqsToGroup`).  Its enumeration lists the indices of G whose
elements H's decider accepts, in increasing order, and its index map
reads an element's rank among them off H's table, walking G's index set
once and normalizing no proof (`Groups.Finite.Subset`'s `finite`).  So
the order of H as a finite group is |H|, by definition.

A subgroup of G restricts to a subgroup of H, and a subgroup of H, as a
group, is a subgroup of G (its *image*) of the same order.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Subgroup.Group where

-- Imports from the Agda Standard Library
open import Data.Product.Base                      using ( Σ-syntax ; _,_ ; proj₁ ; proj₂ )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary.Bundles                using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )
open import Relation.Nullary.Decidable             using ( yes ; no ; map′ )
open import Relation.Unary                         using ( Pred ; _∈_ )

-- Imports from the Agda Universal Algebra Library
open import Classical.Structures.Group.Basic       using ( Group ; module Group-Op ; setoidEqsToGroup )
open import Classical.Structures.Group.Subgroups   using ( IsSubgroup ; mkIsSubgroup ; DecSubgroup )

-- Imports from this library
open import Groups.Finite.Group                    using ( FiniteGroup )
open import Groups.Finite.Setoid                   using ( toIrredundant ; inverse⇒≡ )
open import Groups.Finite.Subset                   using ( subsetoid ; module Counting )
open import Groups.Subgroup                        using ( module Subgroups )

private variable α ρ : Level
```
-->

Everything below is about one finite group 𝔾, the parameter of the
module `AsGroup`, and one decidable subgroup H of it.

<!--
```agda
module AsGroup (𝔾 : FiniteGroup α ρ) where
  private
    𝒢 : Group α ρ
    𝒢 = FiniteGroup.group 𝔾

  open FiniteGroup 𝔾  using ( Carrier ; setoid ; finite )
  open Setoid setoid  using ( _≈_ ) renaming ( refl to ≈refl )
  open Group-Op 𝒢     using ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; ⁻¹-cong
                            ; assoc-law ; idˡ-law ; idʳ-law ; invˡ-law ; invʳ-law )
  open Subgroups 𝔾    using ( set ; isSubgroup ; _∈?_ ; subset ; ∣_∣ )
  open Counting finite using () renaming ( finite to finiteˢ )

  private variable ℓ ℓ′ : Level

  module _ (H : DecSubgroup 𝒢 ℓ) where
    open IsSubgroup (isSubgroup H) using ( ∙-closed ; ε-closed ; ⁻¹-closed )
```
-->

#### The group, and its enumeration

```agda
    -- H as a group: its members, compared in G, with G's operations.
    asGroup : Group (α ⊔ ℓ) ρ
    asGroup = setoidEqsToGroup (subsetoid (subset H))
      (λ (x , p) (y , q) → x ∙ y , ∙-closed p q) (ε , ε-closed) (λ (x , p) → x ⁻¹ , ⁻¹-closed p)
      ∙-cong ⁻¹-cong
      (λ a b c → assoc-law (proj₁ a) (proj₁ b) (proj₁ c))
      (λ a → idˡ-law (proj₁ a)) (λ a → idʳ-law (proj₁ a))
      (λ a → invˡ-law (proj₁ a)) (λ a → invʳ-law (proj₁ a))

    -- H as a finite group, enumerated by the indices of G that H's decider accepts.
    asFiniteGroup : FiniteGroup (α ⊔ ℓ) ρ
    asFiniteGroup = record { group = asGroup ; irredundant = toIrredundant (finiteˢ (subset H)) }

    -- Its order is the order of H.
    ∣asFiniteGroup∣≡∣H∣ : FiniteGroup.order asFiniteGroup ≡ ∣ H ∣
    ∣asFiniteGroup∣≡∣H∣ = refl
```

#### Subgroups of the subgroup

A subgroup K of G restricts to the subgroup of H of the members of H
that lie in K, decided by K's decider.  A subgroup K of H, as a group, is
a subgroup of G, its image: the x in H with x, as a member of H, in K.
Their members correspond one to one, so the image has the order of K.

```agda
    -- A subgroup of G, restricted to H.
    restrict : DecSubgroup 𝒢 ℓ′ → DecSubgroup asGroup ℓ′
    restrict K = ( (λ (x , _) → x ∈ set K)
                 , mkIsSubgroup asGroup K.respects K.∙-closed K.ε-closed K.⁻¹-closed )
               , (λ (x , _) → x ∈? K)
      where module K = IsSubgroup (isSubgroup K)

    -- A subgroup of H, as a subgroup of G.
    image : DecSubgroup asGroup ℓ′ → DecSubgroup 𝒢 (ℓ ⊔ ℓ′)
    image K = (P , mkIsSubgroup 𝒢 resp ∙-c ε-c ⁻¹-c) , dec
      where
      module H = IsSubgroup (isSubgroup H)
      module K = IsSubgroup (proj₂ (proj₁ K))
      P : Pred Carrier _
      P x = Σ[ h ∈ x ∈ set H ] ((x , h) ∈ proj₁ (proj₁ K))
      resp : ∀ {x y} → x ≈ y → P x → P y
      resp x≈y (h , k) = H.respects x≈y h , K.respects x≈y k
      ∙-c : ∀ {x y} → P x → P y → P (x ∙ y)
      ∙-c (h , k) (h′ , k′) = ∙-closed h h′ , K.∙-closed k k′
      ε-c : P ε
      ε-c = ε-closed , K.ε-closed
      ⁻¹-c : ∀ {x} → P x → P (x ⁻¹)
      ⁻¹-c (h , k) = ⁻¹-closed h , K.⁻¹-closed k
      dec : ∀ x → _
      dec x with x ∈? H
      ... | yes h  = map′ (h ,_) (λ (_ , k) → K.respects ≈refl k) (proj₂ K (x , h))
      ... | no ¬h  = no (λ (h , _) → ¬h h)

    -- The image of K has the order of K.
    ∣image∣≡∣K∣ : (K : DecSubgroup asGroup ℓ′) → ∣ image K ∣ ≡ Subgroups.∣_∣ asFiniteGroup K
    ∣image∣≡∣K∣ K = inverse⇒≡ (finiteˢ (subset (image K)))
      (Counting.finite (FiniteGroup.finite asFiniteGroup) (Subgroups.subset asFiniteGroup K))
      (record { to = λ (x , h , k) → (x , h) , k ; from = λ ((x , h) , k) → x , h , k
              ; to-cong = λ e → e ; from-cong = λ e → e ; inverse = (λ e → e) , (λ e → e) })
```
