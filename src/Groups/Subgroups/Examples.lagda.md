---
layout: default
file: "src/Groups/Subgroups/Examples.lagda.md"
title: "Groups.Subgroups.Examples module"
date: "2026-11-27"
author: "the agda-groups development team"
---

### Finite groups and their subgroups, evaluated

This is the `Groups.Subgroups.Examples` module of the agda-groups library.

It evaluates the orders of finite groups and of their subgroups, and the
decisions of `Groups.Subgroups.Basic`, `Groups.Subgroups.Generated`,
`Groups.Subgroups.Group` and `Groups.Subgroups.Notions`, on the Klein
four-group V₄, on S₃ and on A₅ (`Groups.Examples.Small`).  Each check is
a named definition proved by `refl`, so that Agda computes both sides
while it checks the module and `--profile=definitions` reports the time
of each; a decision is checked by its Boolean, `does`.  A subgroup given
by generators has its certificate checked where its record is built, so
the time of building it and the time of counting it are reported apart.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Subgroups.Examples where

-- Imports from the Agda Standard Library
open import Data.Bool.Base                         using ( true ; false )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F ; 4F )
open import Data.List.Base                         using ( List ; [] ; _∷_ )
open import Data.Nat.Base                          using ( ℕ )
open import Level                                  using ( 0ℓ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )
open import Relation.Nullary.Decidable             using ( does )

-- Imports from the Agda Universal Algebra Library
open import Examples.Classical.Groups.AlternatingGroup5
                                                   using ( a5-act ; _·_ )

-- Imports from this library
open import Groups.Examples.Small                  using ( v4 ; s3 ; a5 ; a5-s ; a5-t ; a5-v₁ ; a5-v₂ )
open import Groups.Finite.Group                    using ( FiniteGroup )
open import Groups.Finite.Subset                   using ( module Counting )
open import Groups.Subgroups.Basic                 using ( module Subgroups )
open import Groups.Subgroups.Generated             using ( module Generated )
open import Groups.Subgroups.Group                 using ( module AsGroup )
open import Groups.Subgroups.Notions               using ( module Notions )

open FiniteGroup using ( order )
```
-->

#### The acceptance checks

The orders of V₄ and S₃, and of their trivial and whole subgroups.

```agda
module V₄ where
  open Subgroups v4 using ( ∣_∣ ; trivial ; whole )

  -- |V₄| = 4, |1| = 1, |V₄| = 4.
  orders : order v4 ∷ ∣ trivial ∣ ∷ ∣ whole 0ℓ ∣ ∷ [] ≡ 4 ∷ 1 ∷ 4 ∷ []
  orders = refl

module S₃ where
  open Subgroups s3 using ( ∣_∣ ; trivial ; whole )

  -- |S₃| = 6, |1| = 1, |S₃| = 6.
  orders : order s3 ∷ ∣ trivial ∣ ∷ ∣ whole 0ℓ ∣ ∷ [] ≡ 6 ∷ 1 ∷ 6 ∷ []
  orders = refl
```

The orders of four subgroups of A₅ given by generators: a Sylow
5-subgroup ⟨s⟩, a Sylow 3-subgroup ⟨t⟩, a Sylow 2-subgroup V = ⟨v₁, v₂⟩
(the double transpositions that fix the point 4, with 1), and the
stabilizer A₄ of the point 4, ⟨t, v₁⟩.  Building each record checks its
certificate; counting each evaluates its decider at the sixty elements.

```agda
module A₅ where
  open Subgroups a5 using ( ∣_∣ ; trivial ; whole )
  open Generated a5 using ( Generators ; mkGenerators ; ⟨_⟩ )

  -- |A₅| = 60, |1| = 1, |A₅| = 60.
  orders : order a5 ∷ ∣ trivial ∣ ∷ ∣ whole 0ℓ ∣ ∷ [] ≡ 60 ∷ 1 ∷ 60 ∷ []
  orders = refl

  -- v₁ and v₂ fix the point 4 and are involutions.
  v-fix : a5-act a5-v₁ 4F ∷ a5-act a5-v₂ 4F ∷ [] ≡ 4F ∷ 4F ∷ []
  v-fix = refl

  v-involution : a5-v₁ · a5-v₁ ∷ a5-v₂ · a5-v₂ ∷ [] ≡ 0F ∷ 0F ∷ []
  v-involution = refl

  -- The subgroups, each with its certificate checked here.
  𝔾₅ 𝔾₃ 𝕍 𝔸₄ : Generators
  𝔾₅  = mkGenerators (a5-s ∷ []) _
  𝔾₃  = mkGenerators (a5-t ∷ []) _
  𝕍   = mkGenerators (a5-v₁ ∷ a5-v₂ ∷ []) _
  𝔸₄  = mkGenerators (a5-t ∷ a5-v₁ ∷ []) _

  -- Their orders.
  order-⟨s⟩ : ∣ ⟨ 𝔾₅ ⟩ ∣ ≡ 5
  order-⟨s⟩ = refl

  order-⟨t⟩ : ∣ ⟨ 𝔾₃ ⟩ ∣ ≡ 3
  order-⟨t⟩ = refl

  order-V : ∣ ⟨ 𝕍 ⟩ ∣ ≡ 4
  order-V = refl

  order-A₄ : ∣ ⟨ 𝔸₄ ⟩ ∣ ≡ 12
  order-A₄ = refl
```

#### The decisions on S₃

In S₃, encoded as e, r, r², s, rs, r²s on 0 to 5, take A₃ = ⟨r⟩ and ⟨s⟩,
by generators.  A₃ is normal and ⟨s⟩ is not; ⟨s⟩ is its own normalizer
and A₃'s is S₃, by the textbook decider and by the generators; the
conjugate of ⟨s⟩ by r is another subgroup, and A₃'s is A₃; ⟨s⟩ is a
complement to A₃, and A₃ is not one to itself; S₃ is not abelian, and
A₃ is elementary abelian for 3; the centralizer of A₃ is A₃, and the
center, the centralizer of S₃, is trivial; the set A₃⟨s⟩ of products
is S₃; and the generator condition, with B empty (so ⟨B⟩ = 1), holds
between 1 and A₃ and fails between 1 and S₃, where ⟨s⟩ lies between.

```agda
module S₃-decisions where
  open Subgroups s3 using ( ∣_∣ ; trivial ; whole ; subset ; _≐?_ ; conjugateᵈ ; normalizer ; memo
                          ; centralizer ; _∙ᵈ_ )
  open Generated s3 using ( Generators ; mkGenerators ; ⟨_⟩ ; Adjoined ; mkAdjoined ; normalizerGen
                          ; conjGen≐? )
  open Notions s3   using ( normal? ; normalGen? ; isAbelian? ; abelian? ; elementaryAbelian?
                          ; isComplement? ; generates? )
  open AsGroup s3   using ( asFiniteGroup )
  open Counting (FiniteGroup.finite s3) using () renaming ( ∣_∣ to ∣_∣ˢ )

  -- A₃ = ⟨r⟩, ⟨s⟩, and the trivial subgroup ⟨⟩, by generators.
  𝔸₃ 𝕊 𝟙 : Generators
  𝔸₃  = mkGenerators (1F ∷ []) _
  𝕊   = mkGenerators (3F ∷ []) _
  𝟙   = mkGenerators [] _

  generated : ∣ ⟨ 𝔸₃ ⟩ ∣ ∷ ∣ ⟨ 𝕊 ⟩ ∣ ∷ ∣ ⟨ 𝟙 ⟩ ∣ ∷ [] ≡ 3 ∷ 2 ∷ 1 ∷ []
  generated = refl

  -- A₃ is normal, by a sweep and by its generators; ⟨s⟩ is not.
  normality : does (normal? ⟨ 𝔸₃ ⟩) ∷ does (normalGen? 𝔸₃) ∷ does (normalGen? 𝕊) ∷ [] ≡ true ∷ true ∷ false ∷ []
  normality = refl

  -- N(⟨s⟩) = ⟨s⟩ and N(A₃) = S₃, by the textbook decider and by the generators.
  normalizers : ∣ normalizer ⟨ 𝕊 ⟩ ∣ ∷ ∣ normalizerGen 𝕊 ∣ ∷ ∣ normalizerGen 𝔸₃ ∣ ∷ [] ≡ 2 ∷ 2 ∷ 6 ∷ []
  normalizers = refl

  -- The textbook normalizer, remembered as a table, is ⟨s⟩ again.
  memo-normalizer : does (memo (normalizer ⟨ 𝕊 ⟩) ≐? ⟨ 𝕊 ⟩) ≡ true
  memo-normalizer = refl

  -- r ⟨s⟩ r⁻¹ is not ⟨s⟩, by the generators and by the enumeration; r A₃ r⁻¹ is A₃.
  conjugates : does (conjGen≐? 𝕊 0F 1F) ∷ does (conjugateᵈ 1F ⟨ 𝕊 ⟩ ≐? ⟨ 𝕊 ⟩) ∷ does (conjGen≐? 𝔸₃ 0F 1F) ∷ []
             ≡ false ∷ false ∷ true ∷ []
  conjugates = refl

  -- ⟨s⟩ is a complement to A₃, and A₃ is not a complement to itself.
  complements : does (isComplement? ⟨ 𝔸₃ ⟩ ⟨ 𝕊 ⟩) ∷ does (isComplement? ⟨ 𝔸₃ ⟩ ⟨ 𝔸₃ ⟩) ∷ [] ≡ true ∷ false ∷ []
  complements = refl

  -- S₃ is not abelian; A₃ is, and is elementary abelian for 3 but not for 2.
  abelian : does isAbelian? ∷ does (abelian? ⟨ 𝔸₃ ⟩) ∷ does (elementaryAbelian? 3 ⟨ 𝔸₃ ⟩)
            ∷ does (elementaryAbelian? 2 ⟨ 𝔸₃ ⟩) ∷ [] ≡ false ∷ true ∷ true ∷ false ∷ []
  abelian = refl

  -- C(A₃) = A₃, and the center of S₃ is trivial.
  centralizers : ∣ centralizer (subset ⟨ 𝔸₃ ⟩) ∣ ∷ ∣ centralizer (subset (whole 0ℓ)) ∣ ∷ [] ≡ 3 ∷ 1 ∷ []
  centralizers = refl

  -- The set A₃⟨s⟩ of products is S₃.
  product : ∣ ⟨ 𝔸₃ ⟩ ∙ᵈ ⟨ 𝕊 ⟩ ∣ˢ ≡ 6
  product = refl

  -- A₃ as a finite group, of order 3.
  as-group : order (asFiniteGroup ⟨ 𝔸₃ ⟩) ≡ 3
  as-group = refl

  -- The certificates of every ⟨x⟩, x in S₃.
  cyclic : Adjoined []
  cyclic = mkAdjoined [] _

  -- The generator condition holds between 1 and A₃, and fails between 1 and S₃.
  condition : does (generates? 𝟙 cyclic ⟨ 𝔸₃ ⟩) ∷ does (generates? 𝟙 cyclic (whole 0ℓ)) ∷ [] ≡ true ∷ false ∷ []
  condition = refl
```

#### V₄, elementary abelian

```agda
module V₄-decisions where
  open Subgroups v4 using ( whole )
  open Notions v4   using ( isAbelian? ; elementaryAbelian? )

  -- V₄ is abelian, and elementary abelian for 2 but not for 3.
  elementary : does isAbelian? ∷ does (elementaryAbelian? 2 (whole 0ℓ)) ∷ does (elementaryAbelian? 3 (whole 0ℓ)) ∷ []
             ≡ true ∷ true ∷ false ∷ []
  elementary = refl
```

#### The decisions on A₅

The normalizers of the three Sylow subgroups of A₅, of orders 10, 6 and
12, by the generators and by the textbook decider; and the normalizer of
the normalizer of ⟨s⟩, with the inner decider remembered by `memo`
(asked afresh, the same check takes about 2.3 s).

```agda
module A₅-decisions where
  open A₅           using ( 𝔾₅ ; 𝔾₃ ; 𝕍 )
  open Subgroups a5 using ( ∣_∣ ; normalizer ; memo )
  open Generated a5 using ( ⟨_⟩ ; normalizerGen )

  -- N(⟨s⟩), N(⟨t⟩) and N(V), by the generators.
  normalizer₅ : ∣ normalizerGen 𝔾₅ ∣ ≡ 10
  normalizer₅ = refl

  normalizer₃ : ∣ normalizerGen 𝔾₃ ∣ ≡ 6
  normalizer₃ = refl

  normalizer₂ : ∣ normalizerGen 𝕍 ∣ ≡ 12
  normalizer₂ = refl

  -- The same, by the textbook decider.
  normalizer₅ᵗ : ∣ normalizer ⟨ 𝔾₅ ⟩ ∣ ≡ 10
  normalizer₅ᵗ = refl

  normalizer₃ᵗ : ∣ normalizer ⟨ 𝔾₃ ⟩ ∣ ≡ 6
  normalizer₃ᵗ = refl

  normalizer₂ᵗ : ∣ normalizer ⟨ 𝕍 ⟩ ∣ ≡ 12
  normalizer₂ᵗ = refl

  -- N(N(⟨s⟩)) = N(⟨s⟩), with N(⟨s⟩)'s textbook decider remembered.
  normalizer-normalizer₅ : ∣ normalizer (memo (normalizer ⟨ 𝔾₅ ⟩)) ∣ ≡ 10
  normalizer-normalizer₅ = refl
```
