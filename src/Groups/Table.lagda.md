---
layout: default
file: "src/Groups/Table.lagda.md"
title: "Groups.Table module"
date: "2026-11-27"
author: "the agda-groups development team"
---

### Groups on Fin n, and groups from tables

This is the `Groups.Table` module of the agda-groups library.

A **group on `Fin n`** is a group whose carrier is `Fin n` under
propositional equality: a multiplication table, an identity and an
inverse map on `Fin n`, with the group laws.  The groups of the Agda
Universal Algebra Library's `Examples.Classical.Groups` (the Klein
four-group, ℤ/2, ℤ/3, ℤ/6, S₃ and A₅) are of this kind, built by that
library's `eqsToGroup`, and so are the groups its `TableGroupBuilder`
builds.  Such a group is a finite group with the **identity
enumeration**, whose index map is the identity, so it normalizes no
proof (ADR 0001, § 1).  `FinGroup` is the record of the data, and
`FinGroup.finiteGroup` the finite group, of order n by definition.

Two constructions, as follows:

+  **Re-tabulation**.  Every finite group G is isomorphic to a group on
   `Fin |G|`, through its enumeration: the product of the indices a and b
   is the index of the product of the elements at a and b.  So the groups
   on `Fin n` are, up to isomorphism, all finite groups: a view and a
   constructor, not the type of a finite group, since a re-tabulated
   product recomputes the original product and its index each time
   (ADR 0001, § 1, and its note, § 2).
+  **Table groups**.  The Agda Universal Algebra Library's
   `TableGroupBuilder` builds a group on `Fin n` from a table whose
   elements are given as permutations of `Fin d` (vectors of images),
   with associativity from the faithful action rather than from a cubic
   sweep of the table.  `TableGroup` wraps it, so that the group it builds
   is a finite group of this library, and its Boolean subgroups
   (`boolSubgroup`, a subgroup given by its characteristic vector) are
   already the library's subgroups, decidable subgroups of the same group.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Table where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from agda-stdlib ----------------------------------------------------
open import Data.Fin.Base            using  ( Fin )
open import Data.Nat.Base            using  ( ℕ )
open import Data.Product.Base        using  ( _,_ ; proj₁ ; proj₂ )
open import Data.Vec.Base            using  ( Vec )
open import Function.Base            using  ( id )
open import Function.Bundles         using  ( Func )
open import Level                    using  ( Level ; 0ℓ )
open import Relation.Binary.Bundles  using  ( Setoid )
open import Relation.Binary.PropositionalEquality
                                     using  ( _≡_ ; refl ; trans )
                                     renaming ( setoid to ≡-setoid )

-- Imports from agda-algebras ----------------------------------------------------
open import Classical.Structures.Group  using  ( Group ; module Group-Op
                                               ; opsToBareGroup ; _⊨ᵍᵖ_
                                               ; eqsToGroup ; _⨁_
                                               ; module TableGroupBuilder )
open import Classical.Theories.Group    using  ( Th-Group )
open import Setoid.Algebras.Basic       using  ( Algebra )
open import Setoid.Algebras.Finite.Irredundant
                                        using  ( IrredundantEnumeration )
open import Setoid.Homomorphisms.Isomorphisms
                                        using  ( _≅_ )

-- Imports from agda-groups ------------------------------------------------------
open import Groups.Finite.Group  using  ( FiniteGroup )
open import Groups.Homomorphism  using  ( module Homomorphisms
                                        ; module Isomorphisms )

private variable α ρ : Level
```
-->

#### Groups on Fin n

A group on `Fin n` is given by its multiplication `mul`, its identity
`unit` and its inverse map `inv`, with the group laws in the form the
Agda Universal Algebra Library states them for its algebra
`opsToBareGroup mul unit inv` (`laws`).  That library's `eqsToGroup` and
its examples build exactly this algebra, so a group they build, as it
stands, gives a `FinGroup` whose group is the same group, and that
library's theorems about it apply unchanged.

```agda
-- A group on Fin n under propositional equality.
record FinGroup : Type where
  field
    n     : ℕ
    mul   : Fin n → Fin n → Fin n
    unit  : Fin n
    inv   : Fin n → Fin n
    laws  : opsToBareGroup mul unit inv ⊨ᵍᵖ Th-Group

  -- The group, as the Agda Universal Algebra Library's Group.
  group : Group 0ℓ 0ℓ
  group = opsToBareGroup mul unit inv , laws

  -- The algebra of the group.
  algebra : Algebra 0ℓ 0ℓ
  algebra = proj₁ group

  -- The identity enumeration of Fin n.
  irredundant : IrredundantEnumeration algebra
  irredundant = record  { icard = n
                        ; ienum[_] = id
                        ; ienum-sur = λ x → x , refl
                        ; ienum-inj = id }

  -- The finite group, with the identity enumeration.
  finiteGroup : FiniteGroup 0ℓ 0ℓ
  finiteGroup = record { group = group ; irredundant = irredundant }

  -- Its order is n, by definition.
  order≡n : FiniteGroup.order finiteGroup ≡ n
  order≡n = refl
```

A group that the Agda Universal Algebra Library builds on `Fin n`, with
`eqsToGroup`, is a finite group by its laws alone: their type names the
operations, so Agda finds them.  `onFin (proj₂ 𝒢)` is the finite group
whose group is 𝒢 itself, up to Agda's own equality of records, so that
library's theorems about 𝒢 apply to it unchanged.

```agda
-- A group built on Fin n, as a finite group with the identity enumeration,
-- from its laws.
onFin : {n : ℕ} {mul : Fin n → Fin n → Fin n} {unit : Fin n}
        {inv : Fin n → Fin n}
  → opsToBareGroup mul unit inv ⊨ᵍᵖ Th-Group → FiniteGroup 0ℓ 0ℓ
onFin {n} {mul} {unit} {inv} laws = FinGroup.finiteGroup record
  { n = n ; mul = mul ; unit = unit ; inv = inv ; laws = laws }
```

A group on `Fin n` is also given by its operations and the five group
laws as equations, the arguments of the Agda Universal Algebra Library's
`eqsToGroup`.

```agda
-- A group on Fin n from its operations and the five group laws.
fromEqs : (n : ℕ) (mul : Fin n → Fin n → Fin n) (unit : Fin n)
          (inv : Fin n → Fin n)
  → (∀ a b c → mul (mul a b) c ≡ mul a (mul b c))
  → (∀ a → mul unit a ≡ a) → (∀ a → mul a unit ≡ a)
  → (∀ a → mul (inv a) a ≡ unit) → (∀ a → mul a (inv a) ≡ unit)
  → FinGroup
fromEqs n mul unit inv assoc idˡ idʳ invˡ invʳ = record
  { n = n ; mul = mul ; unit = unit ; inv = inv
  ; laws = eqsToGroup mul unit inv assoc idˡ idʳ invˡ invʳ .proj₂ }
```

#### Re-tabulation

Every finite group G, with its enumeration e and index map idx, gives a
group on `Fin |G|`: the product of a and b is idx(e(a) e(b)), the
identity idx(1), and the inverse of a is idx(e(a)⁻¹).  The enumeration
is an isomorphism from it onto G, with the index map its inverse, since
e(idx(x)) = x and idx(e(i)) = i.

<!--
```agda
module Retabulation (𝔾 : FiniteGroup α ρ) where
  private
    -- The group of 𝔾.
    𝒢 : Group α ρ
    𝒢 = FiniteGroup.group 𝔾

  open FiniteGroup 𝔾  using  ( setoid ; order ; enum ; idx ; enum-idx ; idx-cong
                             ; idx-enum )
  open Setoid setoid  using  ( _≈_ )
                      renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Group-Op 𝒢     using  ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; assoc-law ; idˡ-law
                             ; idʳ-law ; invˡ-law ; invʳ-law )
```
-->

```agda
  -- The group on Fin |G| through the enumeration.
  retabulate : FinGroup
  retabulate = fromEqs order
    (λ a b → idx (enum a ∙ enum b))
    (idx ε)
    (λ a → idx (enum a ⁻¹))
    (λ _ _ _ → idx-cong (≈trans  (∙-cong (enum-idx _) ≈refl)
                                 (≈trans  (assoc-law _ _ _)
                                          (∙-cong ≈refl (≈sym (enum-idx _))))))
    (λ a → trans  (idx-cong (≈trans  (∙-cong (enum-idx ε) ≈refl)
                                     (idˡ-law (enum a))))
                  (idx-enum a))
    (λ a → trans  (idx-cong (≈trans  (∙-cong ≈refl (enum-idx ε))
                                     (idʳ-law (enum a))))
                  (idx-enum a))
    (λ a → idx-cong (≈trans (∙-cong (enum-idx _) ≈refl) (invˡ-law (enum a))))
    (λ a → idx-cong (≈trans (∙-cong ≈refl (enum-idx _)) (invʳ-law (enum a))))

  -- The enumeration, as a map of setoids.
  enumᶠ : Func (≡-setoid (Fin order)) setoid
  enumᶠ = record { to = enum ; cong = λ { refl → ≈refl } }

  -- The index map, as a map of setoids.
  idxᶠ : Func setoid (≡-setoid (Fin order))
  idxᶠ = record { to = idx ; cong = idx-cong }

  -- The enumeration preserves the product.
  enum-∙ : Homomorphisms.PreservesProduct (FinGroup.group retabulate) 𝒢 enumᶠ
  enum-∙ a b = enum-idx (enum a ∙ enum b)

  -- The re-tabulated group is isomorphic to G, by the enumeration.
  retabulate-≅ : FinGroup.algebra retabulate ≅ FiniteGroup.algebra 𝔾
  retabulate-≅ = Isomorphisms.groupIso  (FinGroup.group retabulate) 𝒢
                                        enumᶠ idxᶠ enum-∙ enum-idx idx-enum
```

#### Table groups

The Agda Universal Algebra Library's `TableGroupBuilder n d elt mul inv
e` takes a table on `Fin n` whose element i is the permutation `elt i` of
`Fin d`, given as its vector of images, and decides two hypotheses: the
action is faithful (`elt-inj?`) and the table computes composition
(`mul-hom?`, `elt (mul i j) ≡ elt i ⨁ elt j`, where `u ⨁ v` applies v
first).  Its `Build` takes them with the four linear laws of the identity
and the inverse, and builds the group `theGroup`, whose associativity
comes from the faithful action.  `TableGroup` takes the same arguments,
re-exports the builder's names, and adds the finite group.  A Boolean
subgroup, `boolSubgroup chi c∙ cε c⁻¹`, is a decidable subgroup of
`theGroup`, and so of `FiniteGroup.group finiteGroup`, the same group.

```agda
-- The Agda Universal Algebra Library's table groups, as finite groups.
module TableGroup
  (n d  : ℕ)
  (elt  : Fin n → Vec (Fin d) d)
  (mul  : Fin n → Fin n → Fin n)
  (inv  : Fin n → Fin n)
  (e    : Fin n)
  where
  open TableGroupBuilder n d elt mul inv e public using ( elt-inj? ; mul-hom? )

  module Build
    (inj   : ∀ i j → elt i ≡ elt j → i ≡ j)
    (hom   : ∀ i j → elt (mul i j) ≡ elt i ⨁ elt j)
    (idˡ   : ∀ a → mul e a ≡ a)
    (idʳ   : ∀ a → mul a e ≡ a)
    (invˡ  : ∀ a → mul (inv a) a ≡ e)
    (invʳ  : ∀ a → mul a (inv a) ≡ e)
    where
    open TableGroupBuilder.Build
      n d elt mul inv e inj hom idˡ idʳ invˡ invʳ public
      using  ( mul-assoc ; theGroup ; theGroup-FiniteAlgebra ; chiPred
             ; chi-∙? ; chi-ε? ; chi-⁻¹? ; boolSubgroup )

    -- The table group on Fin n.
    finGroup : FinGroup
    finGroup = record  { n = n ; mul = mul ; unit = e ; inv = inv
                       ; laws = proj₂ theGroup }

    -- The table group, as a finite group with the identity enumeration.
    finiteGroup : FiniteGroup 0ℓ 0ℓ
    finiteGroup = FinGroup.finiteGroup finGroup
```
