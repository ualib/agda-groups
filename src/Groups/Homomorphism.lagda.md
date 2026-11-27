---
layout: default
file: "src/Groups/Homomorphism.lagda.md"
title: "Groups.Homomorphism module"
date: "2026-11-27"
author: "the agda-groups development team"
---

### Homomorphisms of groups

This is the `Groups.Homomorphism` module of the agda-groups library.

A **homomorphism** of groups is a map h from G to H with h(xy) = h(x)h(y)
for all x and y in G (Aschbacher, § 1); it then sends the identity to
the identity and each inverse to the inverse.  The Agda Universal Algebra
Library has homomorphisms of algebras of any signature (`hom`, in
`Setoid.Homomorphisms.Basic`): a map of the setoids that commutes with
every operation of the signature, here the product, the identity and the
inverse.  This module gives the textbook's definition in that library's
terms: a map of the setoids that preserves the product is a homomorphism
of the algebras (`groupHom`), one that is also one-to-one is a
monomorphism (`groupMon`), and one with an inverse map is an isomorphism
(`groupIso`), whose inverse preserves the product as well.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Homomorphism where

-- Imports from the Agda Standard Library
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Fin.Patterns                      using ( 0F ; 1F )
open import Data.Product.Base                      using ( _,_ ; proj₁ ; proj₂ )
open import Function.Bundles                       using ( Func )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary.Bundles                using ( Setoid )

import Algebra.Properties.Group                    as GroupProperties
import Relation.Binary.Reasoning.Setoid            as SetoidReasoning

-- Imports from the Agda Universal Algebra Library
open import Classical.Bundles.Group                using ( ⟨_⟩ᵍᵖ )
open import Classical.Signatures.Group             using ( ∙-Op ; ε-Op ; ⁻¹-Op )
open import Classical.Structures.Group.Basic       using ( Group ; module Group-Op )
open import Classical.Structures.Group.Subgroups   using ( interp-tuple-∙ ; interp-tuple-ε ; interp-tuple-⁻¹ )
open import Setoid.Algebras.Basic                  using ( Algebra ; 𝔻[_] )
open import Setoid.Functions                       using ( IsInjective )
open import Setoid.Homomorphisms.Basic             using ( hom ; mkhom ; compatible-map ; mon ; IsMon )
open import Setoid.Homomorphisms.Isomorphisms      using ( _≅_ ; mkiso )

open Func using ( cong ) renaming ( to to _⟨$⟩_ )

private variable α β ρ ρ′ : Level
```
-->

#### Maps that preserve the product

Everything in this part is about two groups 𝒢 and ℋ, the parameters of
the module `Homomorphisms`.  A map of their setoids (agda-stdlib's
`Func`: a function that respects `≈`) *preserves the product* when h(x
y) ≈ h(x) h(y); it then preserves the identity, since h(1) is an
idempotent of H, and the inverse, since h(x⁻¹) h(x) ≈ h(1) ≈ 1.  So it
commutes with the three operations of the signature of groups, as the
Agda Universal Algebra Library's homomorphisms do.

<!--
```agda
module Homomorphisms (𝒢 : Group α ρ) (ℋ : Group β ρ′) where
  private
    -- The algebra of 𝒢 ...
    𝑮 : Algebra α ρ
    𝑮 = proj₁ 𝒢

    -- ... and the algebra of ℋ.
    𝑯 : Algebra β ρ′
    𝑯 = proj₁ ℋ

  open Setoid 𝔻[ 𝑯 ]  using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Group-Op 𝒢     using ( _∙_ ; ε ; _⁻¹ ; invˡ-law ; idʳ-law )
  open Group-Op ℋ     using () renaming ( _∙_ to _·_ ; ε to e ; _⁻¹ to _′ ; ∙-cong to ·-cong
                                        ; assoc-law to ·-assoc ; idʳ-law to ·-idʳ ; invʳ-law to ·-invʳ )
  open GroupProperties ⟨ ℋ ⟩ᵍᵖ using ( inverseˡ-unique )
  open SetoidReasoning 𝔻[ 𝑯 ] using ( begin_ ; step-≈-⟩ ; step-≈-⟨ ; _∎ )
```
-->

```agda
  -- A map of the setoids preserves the product.
  PreservesProduct : (Func 𝔻[ 𝑮 ] 𝔻[ 𝑯 ]) → Type (α ⊔ ρ′)
  PreservesProduct h = ∀ x y → h ⟨$⟩ (x ∙ y) ≈ (h ⟨$⟩ x) · (h ⟨$⟩ y)

  module _ (h : Func 𝔻[ 𝑮 ] 𝔻[ 𝑯 ]) (h-∙ : PreservesProduct h) where

    -- It preserves the identity ...
    preserves-ε : h ⟨$⟩ ε ≈ e
    preserves-ε = begin
      h ⟨$⟩ ε                          ≈⟨ ·-idʳ _ ⟨
      h ⟨$⟩ ε · e                      ≈⟨ ·-cong ≈refl (·-invʳ _) ⟨
      h ⟨$⟩ ε · (h ⟨$⟩ ε · h ⟨$⟩ ε ′)  ≈⟨ ·-assoc _ _ _ ⟨
      (h ⟨$⟩ ε · h ⟨$⟩ ε) · h ⟨$⟩ ε ′  ≈⟨ ·-cong (h-∙ ε ε) ≈refl ⟨
      h ⟨$⟩ (ε ∙ ε) · h ⟨$⟩ ε ′        ≈⟨ ·-cong (cong h (idʳ-law ε)) ≈refl ⟩
      h ⟨$⟩ ε · h ⟨$⟩ ε ′              ≈⟨ ·-invʳ _ ⟩
      e                                ∎

    -- ... and inverses.
    preserves-⁻¹ : ∀ x → h ⟨$⟩ (x ⁻¹) ≈ (h ⟨$⟩ x) ′
    preserves-⁻¹ x = inverseˡ-unique (h ⟨$⟩ (x ⁻¹)) (h ⟨$⟩ x)
                       (≈trans (≈sym (h-∙ (x ⁻¹) x)) (≈trans (cong h (invˡ-law x)) preserves-ε))

    -- So it commutes with the three operations of the signature.
    compatible : compatible-map 𝑮 𝑯 h
    compatible {∙-Op}  {a} = ≈trans (cong h (interp-tuple-∙ 𝒢 a))
                               (≈trans (h-∙ (a 0F) (a 1F)) (≈sym (interp-tuple-∙ ℋ (λ i → h ⟨$⟩ a i))))
    compatible {ε-Op}  {a} = ≈trans (cong h (interp-tuple-ε 𝒢 a))
                               (≈trans preserves-ε (≈sym (interp-tuple-ε ℋ (λ i → h ⟨$⟩ a i))))
    compatible {⁻¹-Op} {a} = ≈trans (cong h (interp-tuple-⁻¹ 𝒢 a))
                               (≈trans (preserves-⁻¹ (a 0F)) (≈sym (interp-tuple-⁻¹ ℋ (λ i → h ⟨$⟩ a i))))
```

A map that preserves the product is a homomorphism of the algebras, and
a one-to-one one is a monomorphism, in the Agda Universal Algebra
Library's sense (`mon`).

```agda
  -- A homomorphism, from a map that preserves the product.
  groupHom : (h : Func 𝔻[ 𝑮 ] 𝔻[ 𝑯 ]) → PreservesProduct h → hom 𝑮 𝑯
  groupHom h h-∙ = mkhom 𝑮 𝑯 h (λ {f} {a} → compatible h h-∙ {f} {a})

  -- A monomorphism, from a one-to-one map that preserves the product.
  groupMon : (h : Func 𝔻[ 𝑮 ] 𝔻[ 𝑯 ]) → PreservesProduct h → IsInjective h → mon 𝑮 𝑯
  groupMon h h-∙ inj = h , record { isHom = proj₂ (groupHom h h-∙) ; isInjective = inj }
```

#### Isomorphisms

An isomorphism is a homomorphism with an inverse map; the inverse then
preserves the product as well, so the pair is an isomorphism of the
algebras in the Agda Universal Algebra Library's sense (`_≅_`).

<!--
```agda
module Isomorphisms (𝒢 : Group α ρ) (ℋ : Group β ρ′) where
  private
    -- The algebra of 𝒢 ...
    𝑮 : Algebra α ρ
    𝑮 = proj₁ 𝒢

    -- ... and the algebra of ℋ.
    𝑯 : Algebra β ρ′
    𝑯 = proj₁ ℋ

  open Setoid 𝔻[ 𝑮 ]  using ( _≈_ ) renaming ( sym to ≈sym ; trans to ≈trans )
  open Setoid 𝔻[ 𝑯 ]  using () renaming ( _≈_ to _≈ᴴ_ ; sym to ≈ᴴsym ; trans to ≈ᴴtrans )
  open Group-Op ℋ     using () renaming ( _∙_ to _·_ ; ∙-cong to ·-cong )
  open Homomorphisms 𝒢 ℋ using ( PreservesProduct ; groupHom )
  open Homomorphisms ℋ 𝒢 using () renaming ( PreservesProduct to PreservesProduct′ ; groupHom to groupHom′ )
```
-->

```agda
  module _ (h : Func 𝔻[ 𝑮 ] 𝔻[ 𝑯 ]) (k : Func 𝔻[ 𝑯 ] 𝔻[ 𝑮 ]) (h-∙ : PreservesProduct h)
           (h∘k : ∀ y → h ⟨$⟩ (k ⟨$⟩ y) ≈ᴴ y) (k∘h : ∀ x → k ⟨$⟩ (h ⟨$⟩ x) ≈ x) where

    -- The inverse map preserves the product.
    inverse-∙ : PreservesProduct′ k
    inverse-∙ x y = ≈trans (cong k (·-cong (≈ᴴsym (h∘k x)) (≈ᴴsym (h∘k y))))
                      (≈trans (cong k (≈ᴴsym (h-∙ (k ⟨$⟩ x) (k ⟨$⟩ y)))) (k∘h _))

    -- An isomorphism, from a map that preserves the product and an inverse map.
    groupIso : 𝑮 ≅ 𝑯
    groupIso = mkiso (groupHom h h-∙) (groupHom′ k inverse-∙) h∘k k∘h
```
