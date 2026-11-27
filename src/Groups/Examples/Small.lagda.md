---
layout: default
file: "src/Groups/Examples/Small.lagda.md"
title: "Groups.Examples.Small module"
date: "2026-11-27"
author: "the agda-groups development team"
---

### Small groups, as finite groups

This is the `Groups.Examples.Small` module of the agda-groups library.

It makes three groups of the Agda Universal Algebra Library's
`Examples.Classical.Groups` finite groups of this library: the Klein
four-group V₄, the symmetric group S₃ and the alternating group A₅.  Each
is a group on `Fin n` under propositional equality, with 0 the identity,
so each is given the identity enumeration, whose index map is the
identity (ADR 0001, § 1).  M2-4's `Groups.Table` makes every group on
`Fin n` a finite group this way, and extends the list.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Examples.Small where

-- Imports from the Agda Standard Library
open import Data.Fin                               using ( Fin ; #_ )
open import Data.Product.Base                      using ( _,_ )
open import Level                                  using ( 0ℓ )
open import Relation.Binary.PropositionalEquality  using ( refl )

-- Imports from the Agda Universal Algebra Library
open import Examples.Classical.Groups.AlternatingGroup5
                                                   using ( a5-group )
open import Examples.Classical.Groups.AlternatingGroup5.Tables
                                                   using ( a5-gen-s ; a5-gen-t )
open import Examples.Classical.Groups.KleinFourGroup
                                                   using ( v4-group )
open import Examples.Classical.Groups.SymmetricGroup3
                                                   using ( s3-group )

-- Imports from this library
open import Groups.Finite.Group                    using ( FiniteGroup )
```
-->

#### The groups

The Klein four-group is the group of `Fin 4` under the bitwise
exclusive or of the two-bit codes; S₃ is encoded as e, r, r², s, rs, r²s
on 0 to 5; and A₅ is the group of the even permutations of five points,
on `Fin 60`.

```agda
-- The Klein four-group, of order 4.
v4 : FiniteGroup 0ℓ 0ℓ
v4 = record
  { group        = v4-group
  ; irredundant  = record { icard = 4 ; ienum[_] = λ i → i ; ienum-sur = λ x → x , refl ; ienum-inj = λ e → e }
  }

-- The symmetric group S₃, of order 6.
s3 : FiniteGroup 0ℓ 0ℓ
s3 = record
  { group        = s3-group
  ; irredundant  = record { icard = 6 ; ienum[_] = λ i → i ; ienum-sur = λ x → x , refl ; ienum-inj = λ e → e }
  }

-- The alternating group A₅, of order 60.
a5 : FiniteGroup 0ℓ 0ℓ
a5 = record
  { group        = a5-group
  ; irredundant  = record { icard = 60 ; ienum[_] = λ i → i ; ienum-sur = λ x → x , refl ; ienum-inj = λ e → e }
  }
```

#### Elements of A₅

The Agda Universal Algebra Library's generators of A₅, s = (0 1 2 3 4)
and t = (0 1 2), and two double transpositions that fix the point 4,
which with 1 and their product form a Klein four-group in A₅, a Sylow
2-subgroup.

```agda
-- The generators s = (0 1 2 3 4) and t = (0 1 2) of A₅.
a5-s a5-t : Fin 60
a5-s = a5-gen-s
a5-t = a5-gen-t

-- Two double transpositions that fix the point 4.
a5-v₁ a5-v₂ : Fin 60
a5-v₁ = # 13
a5-v₂ = # 30
```
