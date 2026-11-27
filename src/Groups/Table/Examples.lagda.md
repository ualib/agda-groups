---
layout: default
file: "src/Groups/Table/Examples.lagda.md"
title: "Groups.Table.Examples module"
date: "2026-11-27"
author: "the agda-groups development team"
---

### Groups on Fin n, evaluated

This is the `Groups.Table.Examples` module of the agda-groups library.

It evaluates the constructions of `Groups.Table` and `Groups.Cyclic`: the
orders of the Agda Universal Algebra Library's example groups as finite
groups (`Groups.Examples.Small`); S₃ built by that library's
`TableGroupBuilder` from its action on three points, with the rotations
A₃ as a Boolean subgroup; the cyclic groups ℤ/n, against that
library's tables of ℤ/3 and ℤ/6; and A₃ inside S₃, re-tabulated, which is
ℤ/3 table for table.  Each check is a named definition proved by `refl`,
so that Agda computes both sides while it checks the module and
`--profile=definitions` reports the time of each; a decision is checked
by its Boolean, `does`.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Table.Examples where

-- Imports from the Agda Standard Library
open import Data.Bool.Base                         using ( Bool ; true ; false )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F )
open import Data.List.Base                         using ( [] ; _∷_ )
open import Data.Nat.Base                          using ( nonZero )
open import Data.Vec.Base                          using ( Vec ; lookup ; tabulate )
                                                   renaming ( [] to []ᵛ ; _∷_ to infixr 5 _∷ᵛ_ )
open import Level                                  using ( 0ℓ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )
open import Relation.Nullary.Decidable             using ( does ; from-yes )

-- Imports from the Agda Universal Algebra Library
open import Classical.Structures.Group.Subgroups   using ( DecSubgroup )
open import Classical.Structures.Group.TableGroup  using ( _⨁_ )
open import Examples.Classical.Groups.AlternatingGroup5
                                                   using ( a5-group )
open import Examples.Classical.Groups.CyclicGroup3 using ( z3-table )
open import Examples.Classical.Groups.CyclicGroup6 using ( z6-table )
open import Examples.Classical.Groups.SymmetricGroup3
                                                   using ( _·_ ; s3-inv )
open import Overture.Operations.Properties         using ( LeftIdentity? ; RightIdentity? ; LeftInverse?
                                                         ; RightInverse? )

-- Imports from this library
open import Groups.Cyclic                          using ( ℤ/_ ; _+ₘ_ ; -ₘ_ ; 1ₘ )
open import Groups.Examples.Small                  using ( v4 ; z2 ; z3 ; z6 ; s3 ; a5 )
open import Groups.Finite.Group                    using ( FiniteGroup )
open import Groups.Subgroup                        using ( module Subgroups )
open import Groups.Subgroup.Generated              using ( module Generated )
open import Groups.Subgroup.Group                  using ( module AsGroup )
open import Groups.Subgroup.Notions                using ( module Notions )
open import Groups.Table                           using ( FinGroup ; module Retabulation ; module TableGroup )

open FiniteGroup using ( order )
```
-->

#### The Agda Universal Algebra Library's examples

Their orders, by definition and as the number of elements of the whole
group, counted by its decider over the enumeration; and A₅'s group is
that library's `a5-group` itself, so its theorems about A₅ apply to the
finite group.

```agda
module Examples where
  -- |V₄| = 4, |ℤ/2| = 2, |ℤ/3| = 3, |ℤ/6| = 6, |S₃| = 6, |A₅| = 60.
  orders : order v4 ∷ order z2 ∷ order z3 ∷ order z6 ∷ order s3 ∷ order a5 ∷ []
         ≡ 4 ∷ 2 ∷ 3 ∷ 6 ∷ 6 ∷ 60 ∷ []
  orders = refl

  -- The same, counted.
  counted : Subgroups.∣_∣ v4 (Subgroups.whole v4 0ℓ) ∷ Subgroups.∣_∣ z6 (Subgroups.whole z6 0ℓ)
            ∷ Subgroups.∣_∣ s3 (Subgroups.whole s3 0ℓ) ∷ Subgroups.∣_∣ a5 (Subgroups.whole a5 0ℓ) ∷ []
          ≡ 4 ∷ 6 ∷ 6 ∷ 60 ∷ []
  counted = refl

  -- A₅'s group is the Agda Universal Algebra Library's.
  a5-same : FiniteGroup.group a5 ≡ a5-group
  a5-same = refl
```

#### S₃ from its action on three points

S₃, in the Agda Universal Algebra Library's encoding e, r, r², s, rs, r²s
on 0 to 5, acts on the points 0, 1 and 2, r as the rotation i ↦ i + 1 and
s as the reflection that fixes 0; each element is the vector of its
images.  So `TableGroupBuilder` builds S₃ from its table: the two
quadratic hypotheses (the action is faithful, and the table computes
composition) and the four linear laws are decided once each, in a named
definition, and the group's associativity follows.  The rotations, A₃,
form a Boolean subgroup, given by their characteristic vector, with its
three closure checks decided once each.  (A₅ built the same way from its
action on five points, `a5-act-table`, decides its two quadratic
hypotheses in about 1.1 s, which would take this module over three
seconds.)

```agda
module S₃-table where
  -- The element i of S₃ as the vector of its images.
  elt : Fin 6 → Vec (Fin 3) 3
  elt = lookup ( (0F ∷ᵛ 1F ∷ᵛ 2F ∷ᵛ []ᵛ) ∷ᵛ (1F ∷ᵛ 2F ∷ᵛ 0F ∷ᵛ []ᵛ) ∷ᵛ (2F ∷ᵛ 0F ∷ᵛ 1F ∷ᵛ []ᵛ)
               ∷ᵛ (0F ∷ᵛ 2F ∷ᵛ 1F ∷ᵛ []ᵛ) ∷ᵛ (1F ∷ᵛ 0F ∷ᵛ 2F ∷ᵛ []ᵛ) ∷ᵛ (2F ∷ᵛ 1F ∷ᵛ 0F ∷ᵛ []ᵛ) ∷ᵛ []ᵛ )

  open TableGroup 6 3 elt _·_ s3-inv 0F using ( elt-inj? ; mul-hom? ; module Build )

  -- The action is faithful ...
  inj : ∀ i j → elt i ≡ elt j → i ≡ j
  inj = from-yes elt-inj?

  -- ... and the table computes composition.
  hom : ∀ i j → elt (i · j) ≡ elt i ⨁ elt j
  hom = from-yes mul-hom?

  -- The identity is an identity on the left ...
  idˡ : ∀ a → 0F · a ≡ a
  idˡ = from-yes (LeftIdentity? _·_ 0F)

  -- ... and on the right.
  idʳ : ∀ a → a · 0F ≡ a
  idʳ = from-yes (RightIdentity? _·_ 0F)

  -- The inverse is an inverse on the left ...
  invˡ : ∀ a → s3-inv a · a ≡ 0F
  invˡ = from-yes (LeftInverse? _·_ 0F s3-inv)

  -- ... and on the right.
  invʳ : ∀ a → a · s3-inv a ≡ 0F
  invʳ = from-yes (RightInverse? _·_ 0F s3-inv)

  open Build inj hom idˡ idʳ invˡ invʳ using ( finiteGroup ; chiPred ; chi-∙? ; chi-ε? ; chi-⁻¹? ; boolSubgroup )
  open Subgroups finiteGroup using ( ∣_∣ )

  -- S₃, built from its action, of order 6.
  order-S₃ : order finiteGroup ≡ 6
  order-S₃ = refl

  -- The characteristic vector of the rotations.
  χ : Vec Bool 6
  χ = true ∷ᵛ true ∷ᵛ true ∷ᵛ false ∷ᵛ false ∷ᵛ false ∷ᵛ []ᵛ

  -- The rotations are closed under products ...
  χ-∙ : ∀ i j → chiPred χ i → chiPred χ j → chiPred χ (i · j)
  χ-∙ = from-yes (chi-∙? χ)

  -- ... hold the identity ...
  χ-ε : chiPred χ 0F
  χ-ε = from-yes (chi-ε? χ)

  -- ... and are closed under inverses.
  χ-⁻¹ : ∀ i → chiPred χ i → chiPred χ (s3-inv i)
  χ-⁻¹ = from-yes (chi-⁻¹? χ)

  -- The rotations A₃, a subgroup of the finite group.
  A₃ : DecSubgroup (FiniteGroup.group finiteGroup) 0ℓ
  A₃ = boolSubgroup χ χ-∙ χ-ε χ-⁻¹

  -- |A₃| = 3.
  order-A₃ : ∣ A₃ ∣ ≡ 3
  order-A₃ = refl
```

#### The cyclic groups

The orders of ℤ/1, ℤ/2 and ℤ/7; the tables of ℤ/3 and ℤ/6 are the Agda
Universal Algebra Library's; in ℤ/7, −3 = 4, and the power 1⁵ is 5, as
`1^ⁿ-toℕ` says of every element; ℤ/6 is abelian, and its subgroups ⟨1⟩,
⟨2⟩ and ⟨3⟩, by generators, have orders 6, 3 and 2.

```agda
module Cyclic where
  -- |ℤ/1| = 1, |ℤ/2| = 2, |ℤ/7| = 7.
  orders : order (ℤ/ 1) ∷ order (ℤ/ 2) ∷ order (ℤ/ 7) ∷ [] ≡ 1 ∷ 2 ∷ 7 ∷ []
  orders = refl

  -- The table of ℤ/3 is agda-algebras' ...
  table₃ : tabulate (λ (a : Fin 3) → tabulate (λ b → a +ₘ b)) ≡ z3-table
  table₃ = refl

  -- ... and so is the table of ℤ/6.
  table₆ : tabulate (λ (a : Fin 6) → tabulate (λ b → a +ₘ b)) ≡ z6-table
  table₆ = refl

  -- In ℤ/7, −3 = 4 ...
  negation : -ₘ_ {7} 3F ≡ 4F
  negation = refl

  -- ... and 1⁵ = 5.
  power : Notions._^ⁿ_ (ℤ/ 7) 1ₘ 5 ≡ 5F
  power = refl

  open Generated (ℤ/ 6) using ( Generators ; mkGenerators ; ⟨_⟩ )
  open Subgroups (ℤ/ 6) using ( ∣_∣ )
  open Notions (ℤ/ 6)   using ( isAbelian? )

  -- ⟨1⟩, ⟨2⟩ and ⟨3⟩ in ℤ/6.
  𝔾₁ 𝔾₂ 𝔾₃ : Generators
  𝔾₁ = mkGenerators (1ₘ ∷ []) _
  𝔾₂ = mkGenerators (2F ∷ []) _
  𝔾₃ = mkGenerators (3F ∷ []) _

  -- Their orders: 6, 3 and 2.
  orders-⟨⟩ : ∣ ⟨ 𝔾₁ ⟩ ∣ ∷ ∣ ⟨ 𝔾₂ ⟩ ∣ ∷ ∣ ⟨ 𝔾₃ ⟩ ∣ ∷ [] ≡ 6 ∷ 3 ∷ 2 ∷ []
  orders-⟨⟩ = refl

  -- ℤ/6 is abelian.
  abelian : does isAbelian? ≡ true
  abelian = refl
```

#### Re-tabulation

A₃ = ⟨r⟩ inside S₃, as a finite group (`Groups.Subgroup.Group`), is
enumerated by the indices 0, 1 and 2 of S₃ that it holds, the elements e,
r and r²; re-tabulated, it is a group on `Fin 3`, and its table is that
of ℤ/3.

```agda
module Retabulated where
  open Generated s3 using ( Generators ; mkGenerators ; ⟨_⟩ )
  open AsGroup s3   using ( asFiniteGroup )

  -- A₃ = ⟨r⟩ in S₃.
  𝔸₃ : Generators
  𝔸₃ = mkGenerators (1F ∷ []) _

  -- A₃ as a finite group.
  A₃ : FiniteGroup 0ℓ 0ℓ
  A₃ = asFiniteGroup ⟨ 𝔸₃ ⟩

  open Retabulation A₃ using ( retabulate )

  -- Re-tabulated, it has the table of ℤ/3.
  table : tabulate (λ a → tabulate (λ b → FinGroup.mul retabulate a b)) ≡ z3-table
  table = refl
```
