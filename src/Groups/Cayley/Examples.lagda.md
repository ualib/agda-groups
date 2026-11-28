---
layout: default
file: "src/Groups/Cayley/Examples.lagda.md"
title: "Groups.Cayley.Examples module"
date: "2026-11-27"
author: "the agda-groups development team"
---

### Cayley's theorem, evaluated

This is the `Groups.Cayley.Examples` module of the agda-groups library.

It evaluates the left regular representations of `Groups.Cayley` on V₄,
S₃ and A₅ (`Groups.Examples.Small`), in Sym(4), Sym(6) and Sym(60).  Each
check is a named definition proved by `refl`, so that Agda computes both
sides while it checks the module and `--profile=definitions` reports the
time of each; a decision is checked by its Boolean, `does`.  A
permutation is written by its vector of images, σ(0), σ(1), ..., and in
the comments in cycle notation.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Cayley.Examples where

-- Imports from agda-stdlib ----------------------------------------------------
open import Data.Bool.Base              using  ( true ; false )
open import Data.Fin.Patterns           using  ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F )
open import Data.Product.Base           using  ( proj₁ )
open import Data.Vec.Base               using  ()
                                        renaming ( [] to []ᵛ
                                                 ; _∷_ to infixr 5 _∷ᵛ_ )
open import Relation.Binary.PropositionalEquality
                                        using  ( _≡_ ; refl )
open import Relation.Nullary.Decidable  using  ( does )

-- Imports from agda-algebras ----------------------------------------------------
open import Examples.Classical.Groups.AlternatingGroup5 using ( _·_ )

-- Imports from agda-groups ------------------------------------------------------
open import Groups.Cayley          using  ( module Cayley ; cayley )
open import Groups.Examples.Small  using  ( v4 ; s3 ; a5 ; a5-s ; a5-t )
open import Groups.Subgroup        using  ( module Subgroups )
open import Groups.Symmetric       using  ( Perm ; images ; fromImages ; _∘ₚ_
                                          ; Sym )
```
-->

#### V₄ in Sym(4)

λ(1) is (0 1)(2 3); the image, the subgroup of Sym(4) that `cayley`
gives for V₄, has order 4, counted over Sym(4); and (0 1) is not in it.

```agda
module V₄ where
  open Cayley v4 using ( leftRegular ; inImage? )

  -- λ(1) is (0 1)(2 3).
  λ₁ : images (leftRegular 1F) ≡ 1F ∷ᵛ 0F ∷ᵛ 3F ∷ᵛ 2F ∷ᵛ []ᵛ
  λ₁ = refl

  -- The image, Cayley's subgroup for V₄, has order 4.
  order-image : Subgroups.∣_∣ (Sym 4) (cayley v4 .proj₁) ≡ 4
  order-image = refl

  -- (0 1) is not in the image.
  not-in-image :
    does (inImage? (fromImages (1F ∷ᵛ 0F ∷ᵛ 2F ∷ᵛ 3F ∷ᵛ []ᵛ) refl refl)) ≡ false
  not-in-image = refl
```

#### S₃ in Sym(6)

In the encoding e, r, r², s, rs, r²s on 0 to 5, λ(r) is (0 1 2)(3 4 5)
and λ(s) is (0 3)(1 5)(2 4); λ(r) λ(s) is in the image, and (0 1) is not.
(The order of the image, 6, counted over the 720 elements of Sym(6),
takes about 0.9 s; `∣image∣≡∣G∣` proves it for every finite group.)

```agda
module S₃ where
  open Cayley s3 using ( leftRegular ; inImage? )

  -- λ(r) is (0 1 2)(3 4 5) ...
  λr : images (leftRegular 1F) ≡ 1F ∷ᵛ 2F ∷ᵛ 0F ∷ᵛ 4F ∷ᵛ 5F ∷ᵛ 3F ∷ᵛ []ᵛ
  λr = refl

  -- ... and λ(s) is (0 3)(1 5)(2 4).
  λs : images (leftRegular 3F) ≡ 3F ∷ᵛ 5F ∷ᵛ 4F ∷ᵛ 0F ∷ᵛ 2F ∷ᵛ 1F ∷ᵛ []ᵛ
  λs = refl

  -- (0 1), a permutation of the six indices.
  t : Perm 6
  t = fromImages (1F ∷ᵛ 0F ∷ᵛ 2F ∷ᵛ 3F ∷ᵛ 4F ∷ᵛ 5F ∷ᵛ []ᵛ) refl refl

  -- λ(r) λ(s) is in the image, and (0 1) is not.
  membership :  does (inImage? (leftRegular 1F ∘ₚ leftRegular 3F)) ∷ᵛ
                does (inImage? t) ∷ᵛ []ᵛ
                ≡ true ∷ᵛ false ∷ᵛ []ᵛ
  membership = refl
```

#### A₅ in Sym(60)

λ(s) gives back s at the index of 1; λ(s t) = λ(s) λ(t); and λ(s) λ(t) is
in the image.  None of these computes an index of Sym(60), whose order is
60!.

```agda
module A₅ where
  open Cayley a5 using ( leftRegular ; inImage? ; readOff )

  -- λ(s) gives back s at the index of 1.
  readOff-s : readOff (leftRegular a5-s) ≡ a5-s
  readOff-s = refl

  -- λ(s t) = λ(s) λ(t).
  homomorphism :  images (leftRegular (a5-s · a5-t))
                  ≡ images (leftRegular a5-s ∘ₚ leftRegular a5-t)
  homomorphism = refl

  -- λ(s) λ(t) is in the image.
  in-image : does (inImage? (leftRegular a5-s ∘ₚ leftRegular a5-t)) ≡ true
  in-image = refl
```
