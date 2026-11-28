---
layout: default
file: "src/Groups/Examples/Small.lagda.md"
title: "Groups.Examples.Small module"
date: "2026-11-27"
author: "the agda-groups development team"
---

### Small groups, as finite groups

This is the `Groups.Examples.Small` module of the agda-groups library.

It makes the groups of the Agda Universal Algebra Library's
`Examples.Classical.Groups` finite groups of this library: the Klein
four-group V₄, the cyclic groups ℤ/2, ℤ/3 and ℤ/6, the symmetric group S₃
and the alternating group A₅.  Each is a group on `Fin n` under
propositional equality, with 0 the identity, built by that library's
`eqsToGroup`, so `Groups.Table`'s `onFin` gives it the identity
enumeration, whose index map is the identity (ADR 0001, § 1), and keeps
the group itself: `FiniteGroup.group a5` is `a5-group`, and that
library's theorems about it (A₅ is simple, say) apply unchanged.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Examples.Small where

-- Imports from agda-stdlib ----------------------------------------------------
open import Data.Fin           using  ( Fin ; #_ )
open import Data.Product.Base  using  ( proj₂ )
open import Level              using  ( 0ℓ )

-- Imports from agda-algebras ----------------------------------------------------
open import Examples.Classical.Groups.AlternatingGroup5
                               using  ( a5-group )
open import Examples.Classical.Groups.AlternatingGroup5.Tables
                               using  ( a5-gen-s ; a5-gen-t )
open import Examples.Classical.Groups.CyclicGroup3
                               using  ( z3-group )
open import Examples.Classical.Groups.CyclicGroup6
                               using  ( z2-group ; z6-group )
open import Examples.Classical.Groups.KleinFourGroup
                               using  ( v4-group )
open import Examples.Classical.Groups.SymmetricGroup3
                               using  ( s3-group )

-- Imports from agda-groups ------------------------------------------------------
open import Groups.Finite.Group  using  ( FiniteGroup )
open import Groups.Table         using  ( onFin )
```
-->

#### The groups

The Klein four-group is the group of `Fin 4` under the bitwise
exclusive or of the two-bit codes; ℤ/2, ℤ/3 and ℤ/6 are `Fin n` under
addition modulo n; S₃ is encoded as e, r, r², s, rs, r²s on 0 to 5; and
A₅ is the group of the even permutations of five points, on `Fin 60`.

```agda
-- The Klein four-group, of order 4.
v4 : FiniteGroup 0ℓ 0ℓ
v4 = onFin (proj₂ v4-group)

-- The cyclic group ℤ/2, of order 2.
z2 : FiniteGroup 0ℓ 0ℓ
z2 = onFin (proj₂ z2-group)

-- The cyclic group ℤ/3, of order 3.
z3 : FiniteGroup 0ℓ 0ℓ
z3 = onFin (proj₂ z3-group)

-- The cyclic group ℤ/6, of order 6.
z6 : FiniteGroup 0ℓ 0ℓ
z6 = onFin (proj₂ z6-group)

-- The symmetric group S₃, of order 6.
s3 : FiniteGroup 0ℓ 0ℓ
s3 = onFin (proj₂ s3-group)

-- The alternating group A₅, of order 60.
a5 : FiniteGroup 0ℓ 0ℓ
a5 = onFin (proj₂ a5-group)
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
