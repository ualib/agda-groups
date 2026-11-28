---
layout: default
file: "src/Groups/Finite/Group.lagda.md"
title: "Groups.Finite.Group module"
date: "2026-11-27"
author: "the agda-groups development team"
---

### Finite groups

This is the `Groups.Finite.Group` module of the agda-groups library.

A **finite group** is a group of the Agda Universal Algebra Library
(`Group α ρ`, an algebra of the signature of groups on a setoid that
satisfies the group equations) together with an *irredundant enumeration*
of its carrier: a size n and a map from `Fin n` that reaches every element,
up to the group's equality, exactly once (that library's
`IrredundantEnumeration`).  The **order** of the group is n.  In the
vocabulary of Mines, Richman and Ruitenburg (*A Course in Constructive
Algebra*, Chapter I, § 2), the carrier is then a finite set: discrete, and
in bijection with {1, ..., n}.

The enumeration is part of the data, not something derived on demand (ADR
0001, § 1).  From it come the carrier as a finite setoid
(`Groups.Finite.Setoid`), with the index map, its laws and decidable
equality, and the Agda Universal Algebra Library's finiteness witness
`FiniteAlgebra`, so that the finite group theory of that library (the
decidable normal closure, the descent to a minimal normal subgroup, the
finite coset space) applies unchanged.  Where a group comes only with a
`FiniteAlgebra` witness, `fromFiniteAlgebra` gives it the enumeration
that library derives by deduplication, which is correct and slow to
compute through.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Finite.Group where

-- Imports from the Agda Standard Library
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Nat.Base                          using ( ℕ )
open import Data.Product.Base                      using ( proj₁ )
open import Level                                  using ( Level ; _⊔_ ) renaming ( suc to lsuc )
open import Relation.Binary.Bundles                using ( Setoid )

-- Imports from the Agda Universal Algebra Library
open import Classical.Signatures.Group             using ( Sig-Group )
open import Classical.Structures.Group.Basic       using ( Group )
open import Setoid.Algebras.Basic                  using ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite                 using ( FiniteAlgebra )
open import Setoid.Algebras.Finite.Irredundant     using ( IrredundantEnumeration
                                                         ; irredundantEnumeration )

-- Imports from this library
open import Groups.Finite.Setoid                   using ( FiniteSetoid ; fromIrredundant )
                                                   renaming ( toFiniteAlgebra to toFiniteAlgebraᶠ )

private variable α ρ : Level
```
-->

#### The record

`FiniteGroup α ρ` holds a group and an irredundant enumeration of its
carrier.  Its record module names the algebra, the setoid and the carrier
of the group, the carrier as a finite setoid (`finite`), the order, and
the derived names of `Groups.Finite.Setoid`: the enumeration `enum`, the
index map `idx` with its laws, the decidable equality `_≟_`, and the
decisions `all?` and `any?` of a predicate that respects `≈` at every
element and at some element.

```agda
record FiniteGroup (α ρ : Level) : Type (lsuc (α ⊔ ρ)) where
  field
    group        : Group α ρ
    irredundant  : IrredundantEnumeration (proj₁ group)

  -- The algebra of the group, its setoid and its carrier.
  algebra : Algebra {𝑆 = Sig-Group} α ρ
  algebra = proj₁ group

  setoid : Setoid α ρ
  setoid = 𝔻[ algebra ]

  Carrier : Type α
  Carrier = 𝕌[ algebra ]

  -- The carrier as a finite setoid, enumerated by the given enumeration.
  finite : FiniteSetoid setoid
  finite = fromIrredundant irredundant

  -- The order of the group: the size of its enumeration.
  order : ℕ
  order = IrredundantEnumeration.icard irredundant

  open FiniteSetoid finite public
    using ( enum ; enum-sur ; enum-inj ; idx ; enum-idx ; idx-cong ; idx-enum ; idx-inj
          ; ↔Fin ; _≟_ ; decSetoid ; all? ; any? )

  -- The Agda Universal Algebra Library's finiteness witness.
  toFiniteAlgebra : FiniteAlgebra algebra
  toFiniteAlgebra = toFiniteAlgebraᶠ finite
```

The order is the size of the finite setoid `finite`, and the cardinality
of `toFiniteAlgebra`, by definition.

#### A finite group from a finiteness witness

A group known only through a `FiniteAlgebra` witness (decidable equality
and an enumeration that may repeat elements) is a finite group with the
enumeration that the Agda Universal Algebra Library derives by
deduplication, `irredundantEnumeration`.  Every theorem about finite
groups holds of it.  Its order alone is cheap to evaluate (A₅'s, 60, in 45
ms), but every lookup of its index map normalizes a proof of membership
in the deduplicated list (141 to 195 ms a lookup on A₅, and 20 to 24 s for
the sixty lookups of one table, against 23 ms through an enumeration given
directly; ADR 0001, § 1).  So a concrete group is given its enumeration
directly, and a computation never looks up the index map of this one.

```agda
-- A finite group from a group and agda-algebras' finiteness witness, by deduplication.
fromFiniteAlgebra : (𝒢 : Group α ρ) → FiniteAlgebra (proj₁ 𝒢) → FiniteGroup α ρ
fromFiniteAlgebra 𝒢 F = record { group = 𝒢 ; irredundant = irredundantEnumeration F }
```
