---
layout: default
file: "src/Groups/Symmetric/Examples.lagda.md"
title: "Groups.Symmetric.Examples module"
date: "2026-11-27"
author: "the agda-groups development team"
---

### The symmetric groups and Cayley's theorem, evaluated

This is the `Groups.Symmetric.Examples` module of the agda-groups library.

It evaluates `Groups.Symmetric`: the orders of Sym(3), Sym(4) and
Sym(5), and the factorial numbering, whose index map every count in
Sym(n) walks; and groups of permutations given by generators, in Sym(4)
(Sym(4) itself, A₄, the Klein four-group V, the dihedral group D₄ of
order 8, a Sylow 2-subgroup, and a Sylow 3-subgroup, with their
normalizers) and in Sym(5) (A₅).  Each check is a named definition proved by `refl`, so that Agda computes
both sides while it checks the module and `--profile=definitions`
reports the time of each; a decision is checked by its Boolean, `does`.
A permutation is written by its vector of images, σ(0), σ(1), ..., and in
the comments in cycle notation.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Symmetric.Examples where

-- Imports from the Agda Standard Library
open import Data.Bool.Base                         using ( true ; false )
open import Data.Fin.Base                          using ( Fin ; toℕ )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F ; 4F )
open import Data.List.Base                         using ( [] ; _∷_ ; map ; allFin ; upTo )
open import Data.Nat.Base                          using ( _! )
open import Data.Vec.Base                          using ( tabulate )
                                                   renaming ( [] to []ᵛ ; _∷_ to infixr 5 _∷ᵛ_ )
open import Level                                  using ( 0ℓ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )
open import Relation.Nullary.Decidable             using ( does )

-- Imports from this library
open import Groups.Finite.Group                    using ( FiniteGroup )
open import Groups.Subgroup                        using ( module Subgroups )
open import Groups.Subgroup.Generated              using ( module Generated )
open import Groups.Subgroup.Notions                using ( module Notions )
open import Groups.Symmetric                       using ( Perm ; images ; fromImages ; transposition ; _∘ₚ_
                                                         ; idₚ ; _⁻¹ ; _≟_ ; Sym ; rank ; unrank ; tabulateₚ
                                                         ; lookupₚ )
                                                   renaming ( _≈_ to _≈ₚ_ )

open FiniteGroup using ( order )
```
-->

#### Sym(3), Sym(4) and Sym(5)

Their orders, by definition and, for Sym(3) and Sym(4), as the number of
elements of the whole group, counted over the enumeration; the
numbering, evaluated: the index of the permutation at k is k, for every
k < 4! and every k < 5!, compared as lists of numbers (the same check
written against `tabulate id` takes five times as long in Sym(5), since
Agda first compares the two functions under the binder); and Sym(3)'s
six permutations in the order of the numbering, which is lexicographic
in the images.

```agda
module Orders where
  -- |Sym(3)| = 6, |Sym(4)| = 24, |Sym(5)| = 120.
  orders : order (Sym 3) ∷ order (Sym 4) ∷ order (Sym 5) ∷ [] ≡ 6 ∷ 24 ∷ 120 ∷ []
  orders = refl

  -- The same, counted, for Sym(3) and Sym(4).
  counted : Subgroups.∣_∣ (Sym 3) (Subgroups.whole (Sym 3) 0ℓ) ∷ Subgroups.∣_∣ (Sym 4) (Subgroups.whole (Sym 4) 0ℓ)
            ∷ [] ≡ 6 ∷ 24 ∷ []
  counted = refl

  -- The index of the permutation at k is k, for every k < 4! ...
  numbering₄ : map (λ k → toℕ (rank (unrank {4} k))) (allFin (4 !)) ≡ upTo 24
  numbering₄ = refl

  -- ... and for every k < 5!.
  numbering₅ : map (λ k → toℕ (rank (unrank {5} k))) (allFin (5 !)) ≡ upTo 120
  numbering₅ = refl

  -- Sym(3), in the order of the numbering.
  sym₃ : tabulate (λ k → images (unrank {3} k))
       ≡ (0F ∷ᵛ 1F ∷ᵛ 2F ∷ᵛ []ᵛ) ∷ᵛ (0F ∷ᵛ 2F ∷ᵛ 1F ∷ᵛ []ᵛ) ∷ᵛ (1F ∷ᵛ 0F ∷ᵛ 2F ∷ᵛ []ᵛ)
         ∷ᵛ (1F ∷ᵛ 2F ∷ᵛ 0F ∷ᵛ []ᵛ) ∷ᵛ (2F ∷ᵛ 0F ∷ᵛ 1F ∷ᵛ []ᵛ) ∷ᵛ (2F ∷ᵛ 1F ∷ᵛ 0F ∷ᵛ []ᵛ) ∷ᵛ []ᵛ
  sym₃ = refl
```

#### Groups of permutations in Sym(4)

Six permutations of the points 0 to 3, each given by its images with
the vector of its inverse found by `fromImages`; the product applies its
right factor first, and the transposition (0 1) is agda-stdlib's.  Then
five subgroups by generators: Sym(4) = ⟨(0 1), (0 1 2 3)⟩; A₄ = ⟨(0 1 2),
(0 1)(2 3)⟩; V = ⟨(0 1)(2 3), (0 2)(1 3)⟩, which is normal; D₄ = ⟨(0 1 2
3), (0 2)⟩, of order 8, a Sylow 2-subgroup, its own normalizer, so that
Sym(4) has 24/8 = 3 of them; and ⟨(0 1 2)⟩, a Sylow 3-subgroup, whose
normalizer has order 6, so that Sym(4) has 24/6 = 4 of them (M4-6
counts both).

```agda
module Sym₄ where
  -- (0 1), (0 1 2 3), (0 1 2), (0 1)(2 3), (0 2)(1 3) and (0 2).
  t c₄ c₃ v₁ v₂ r : Perm 4
  t   = fromImages (1F ∷ᵛ 0F ∷ᵛ 2F ∷ᵛ 3F ∷ᵛ []ᵛ) refl refl
  c₄  = fromImages (1F ∷ᵛ 2F ∷ᵛ 3F ∷ᵛ 0F ∷ᵛ []ᵛ) refl refl
  c₃  = fromImages (1F ∷ᵛ 2F ∷ᵛ 0F ∷ᵛ 3F ∷ᵛ []ᵛ) refl refl
  v₁  = fromImages (1F ∷ᵛ 0F ∷ᵛ 3F ∷ᵛ 2F ∷ᵛ []ᵛ) refl refl
  v₂  = fromImages (2F ∷ᵛ 3F ∷ᵛ 0F ∷ᵛ 1F ∷ᵛ []ᵛ) refl refl
  r   = fromImages (2F ∷ᵛ 1F ∷ᵛ 0F ∷ᵛ 3F ∷ᵛ []ᵛ) refl refl

  -- (0 1) is agda-stdlib's transposition of 0 and 1.
  stdlib : transposition 0F 1F ≈ₚ t
  stdlib = refl

  -- (0 1 2 3), read as agda-stdlib's permutation and stored again, is itself.
  round-trip : tabulateₚ (lookupₚ c₄) ≈ₚ c₄
  round-trip = refl

  -- (0 1 2 3)(0 1) applies (0 1) first: it is (0 2 3).
  product : images (c₄ ∘ₚ t) ≡ 2F ∷ᵛ 1F ∷ᵛ 3F ∷ᵛ 0F ∷ᵛ []ᵛ
  product = refl

  -- The inverse of (0 1 2 3) is (0 3 2 1), and their product is the identity.
  inverse : images (c₄ ⁻¹) ∷ᵛ images (c₄ ∘ₚ c₄ ⁻¹) ∷ᵛ []ᵛ ≡ (3F ∷ᵛ 0F ∷ᵛ 1F ∷ᵛ 2F ∷ᵛ []ᵛ) ∷ᵛ images idₚ ∷ᵛ []ᵛ
  inverse = refl

  -- Equality, decided by the vectors: (0 1 2 3)⁴ is the identity, and (0 1) is not (0 1 2 3).
  equality : does (c₄ ∘ₚ c₄ ∘ₚ c₄ ∘ₚ c₄ ≟ idₚ) ∷ᵛ does (t ≟ c₄) ∷ᵛ []ᵛ ≡ true ∷ᵛ false ∷ᵛ []ᵛ
  equality = refl

  open Generated (Sym 4) using ( Generators ; mkGenerators ; ⟨_⟩ ; normalizerGen )
  open Subgroups (Sym 4) using ( ∣_∣ )
  open Notions (Sym 4)   using ( normalGen? )

  -- Sym(4), A₄, V, D₄ and a Sylow 3-subgroup, each with its certificate checked here.
  𝕊₄ 𝔸₄ 𝕍 𝔻₄ ℂ₃ : Generators
  𝕊₄  = mkGenerators (t ∷ c₄ ∷ []) _
  𝔸₄  = mkGenerators (c₃ ∷ v₁ ∷ []) _
  𝕍   = mkGenerators (v₁ ∷ v₂ ∷ []) _
  𝔻₄  = mkGenerators (c₄ ∷ r ∷ []) _
  ℂ₃  = mkGenerators (c₃ ∷ []) _

  -- Their orders: 24, 12, 4, 8 and 3.
  orders : ∣ ⟨ 𝕊₄ ⟩ ∣ ∷ ∣ ⟨ 𝔸₄ ⟩ ∣ ∷ ∣ ⟨ 𝕍 ⟩ ∣ ∷ ∣ ⟨ 𝔻₄ ⟩ ∣ ∷ ∣ ⟨ ℂ₃ ⟩ ∣ ∷ [] ≡ 24 ∷ 12 ∷ 4 ∷ 8 ∷ 3 ∷ []
  orders = refl

  -- V is normal in Sym(4).
  normal-V : does (normalGen? 𝕍) ≡ true
  normal-V = refl

  -- N(D₄) = D₄, of order 8, and N(⟨(0 1 2)⟩) has order 6.
  normalizers : ∣ normalizerGen 𝔻₄ ∣ ∷ ∣ normalizerGen ℂ₃ ∣ ∷ [] ≡ 8 ∷ 6 ∷ []
  normalizers = refl
```

#### A₅ in Sym(5)

A₅ is generated by (0 1 2 3 4) and (0 1 2), the Agda Universal Algebra
Library's generators s and t; as a subgroup of Sym(5) by these
generators, its order is computed by the search of its Schreier vector
over the 120 indices of Sym(5), and counted.

```agda
module A₅-in-Sym₅ where
  open Generated (Sym 5) using ( Generators ; mkGenerators ; ⟨_⟩ )
  open Subgroups (Sym 5) using ( ∣_∣ )

  -- (0 1 2 3 4) and (0 1 2).
  s t : Perm 5
  s = fromImages (1F ∷ᵛ 2F ∷ᵛ 3F ∷ᵛ 4F ∷ᵛ 0F ∷ᵛ []ᵛ) refl refl
  t = fromImages (1F ∷ᵛ 2F ∷ᵛ 0F ∷ᵛ 3F ∷ᵛ 4F ∷ᵛ []ᵛ) refl refl

  -- A₅ = ⟨s, t⟩ in Sym(5), with its certificate checked here.
  𝔸₅ : Generators
  𝔸₅ = mkGenerators (s ∷ t ∷ []) _

  -- |A₅| = 60.
  order-A₅ : ∣ ⟨ 𝔸₅ ⟩ ∣ ≡ 60
  order-A₅ = refl
```
