---
layout: default
file: "src/Groups/Cayley.lagda.md"
title: "Groups.Cayley module"
date: "2026-11-27"
author: "the agda-groups development team"
---

### Cayley's theorem

This is the `Groups.Cayley` module of the agda-groups library.

**Cayley's theorem** (Gorenstein 1.2.16; Rotman 3.12; Isaacs, p. 2):
every group of order n is isomorphic to a subgroup of the symmetric group
of degree n.  The proof is Rotman's.  For g in G, the *left translation*
λ(g), x ↦ gx, is a permutation of G, and λ(gh) = λ(g) ∘ λ(h), so the
*left regular representation* λ is a homomorphism from G into the
symmetric group on G; it is one-to-one, since λ(g) sends 1 to g; so G is
isomorphic to its image.  (Isaacs and Aschbacher, § 15, act on the right,
by the *regular permutation representation* x ↦ xg, a homomorphism for
their product, which applies its left factor first.  Aschbacher states
no theorem of Cayley's.)

Here G is a finite group with its enumeration e and index map idx, and
the symmetric group is Sym(|G|) of `Groups.Symmetric`, whose product
applies its right factor first, so that the left regular representation
is a homomorphism.  The permutation λ(g) of `Fin |G|` sends the index of
x to the index of g x: it sends i to idx(g e(i)), the operation g of the
Agda Universal Algebra Library's regular action (`Regular` in
`Classical.Structures.Group.RegularAction`, G acting on itself by left
translation) read through the enumeration.  Its image is a subgroup of
Sym(|G|), the set of the λ(g), and it is decided without a search: a
permutation σ is λ(g) for some g exactly when it is λ(e(σ(idx 1))), since
λ(g) sends the index of 1 to the index of g.  The decider compares
vectors of images, |G| points, and computes no index of Sym(|G|), whose
order |G|! is out of reach of evaluation beyond the smallest groups.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Cayley where

-- Imports from agda-stdlib ----------------------------------------------------
open import Data.Fin.Base               using  ( Fin )
open import Data.Product.Base           using  ( Σ-syntax ; _,_ ; proj₁
                                               ; proj₂ )
open import Data.Vec.Base               using  ( lookup ; tabulate )
open import Data.Vec.Properties         using  ( lookup∘tabulate
                                               ; tabulate-cong )
open import Function.Bundles            using  ( Func ; Inverse )
open import Level                       using  ( Level ; 0ℓ )
open import Relation.Binary.Bundles     using  ( Setoid )
open import Relation.Binary.PropositionalEquality
                                        using  ( _≡_ ; refl ; sym ; trans ; cong
                                               ; cong₂ )
open import Relation.Nullary.Decidable  using  ( Dec ; yes ; no )
open import Relation.Unary              using  ( Pred )

-- Imports from agda-algebras ----------------------------------------------------
open import Classical.Structures.Group         using  ( Group ; module Group-Op
                                                      ; module Regular
                                                      ; IsSubgroup ; DecSubgroup
                                                      ; mkIsSubgroup ; _⨁_ )
open import Setoid.Algebras.Basic              using  ( Algebra ; 𝔻[_] ; _^_ )
open import Setoid.Homomorphisms.Basic         using  ( hom ; mon )
open import Setoid.Homomorphisms.Isomorphisms  using  ( _≅_ )

-- Imports from agda-groups ------------------------------------------------------
open import Groups.Finite.Group    using  ( FiniteGroup )
open import Groups.Finite.Setoid   using  ( inverse⇒≡ )
open import Groups.Homomorphism    using  ( module Homomorphisms
                                          ; module Isomorphisms )
open import Groups.Subgroup        using  ( module Subgroups )
open import Groups.Subgroup.Group  using  ( module AsGroup )
open import Groups.Symmetric       using  ( Perm ; perm ; _∘ₚ_ ; idₚ ; ⁻¹-cong
                                          ; symGroup ; Sym ; ι ; _⟨$⟩_ )
                                   renaming ( setoid to permSetoid ; _≈_ to _≈ₚ_
                                            ; _≟_ to _≟ₚ_ )

private variable α ρ : Level
```
-->

Everything below is about one finite group 𝔾, the parameter of the
module `Cayley`.

<!--
```agda
module Cayley (𝔾 : FiniteGroup α ρ) where
  private
    -- The group of 𝔾.
    𝒢 : Group α ρ
    𝒢 = FiniteGroup.group 𝔾

  open FiniteGroup 𝔾  using  ( Carrier ; setoid ; order ; finite ; enum ; idx
                             ; enum-idx ; idx-cong ; idx-enum )
  open Setoid setoid  using  ( _≈_ ; reflexive )
                      renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Group-Op 𝒢     using  ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; assoc-law ; idˡ-law
                             ; idʳ-law ; invˡ-law ; invʳ-law )
  open Regular 𝒢      using  ( cosetAlgebra )
```
-->

#### The left regular representation

λ(g) is stored as a permutation of `Fin |G|`: its images idx(g e(i)), and
the images idx(g⁻¹ e(i)) of its inverse, λ(g⁻¹).  Two left translations by
mutually inverse elements compose to the identity.

```agda
  private
    -- The images of the left translation by b, read back at p, give b e(p).
    lookup-translation : (b : Carrier) (p : Fin order)
      → enum (lookup (tabulate (λ i → idx (b ∙ enum i))) p) ≈ b ∙ enum p
    lookup-translation b p =
      ≈trans  (reflexive (cong enum (lookup∘tabulate _ p))) (enum-idx _)

    -- Left translations by a and b, with a b ≈ 1, compose to the identity.
    cancel : (a b : Carrier) → a ∙ b ≈ ε
      → tabulate (λ i → idx (a ∙ enum i)) ⨁ tabulate (λ i → idx (b ∙ enum i))
        ≡ ι
    cancel a b ab = tabulate-cong λ p → trans
      (lookup∘tabulate (λ i → idx (a ∙ enum i)) _)
      (trans  (idx-cong (≈trans  (∙-cong ≈refl (lookup-translation b p))
                                 (≈trans  (≈sym (assoc-law a b (enum p)))
                                          (≈trans  (∙-cong ab ≈refl)
                                                   (idˡ-law (enum p))))))
              (idx-enum p))

  -- The left translation by g, x ↦ g x, as a permutation of the indices.
  leftRegular : Carrier → Perm order
  leftRegular g = perm  (tabulate (λ i → idx (g ∙ enum i)))
                        (tabulate (λ i → idx (g ⁻¹ ∙ enum i)))
                        (cancel g (g ⁻¹) (invʳ-law g))
                        (cancel (g ⁻¹) g (invˡ-law g))
```

λ(g) sends the index of x to the index of g x, which is the operation g
of the Agda Universal Algebra Library's regular action, applied to x.

```agda
  -- λ(g) sends the index of x to the index of g x ...
  leftRegular-⟨$⟩ : (g x : Carrier) → leftRegular g ⟨$⟩ idx x ≡ idx (g ∙ x)
  leftRegular-⟨$⟩ g x =
    trans  (lookup∘tabulate (λ i → idx (g ∙ enum i)) (idx x))
           (idx-cong (∙-cong ≈refl (enum-idx x)))

  -- ... the image of x under the operation g of agda-algebras' regular
  -- action.
  leftRegular-regular : (g x : Carrier)
    → leftRegular g ⟨$⟩ idx x ≡ idx ((g ^ cosetAlgebra) (λ _ → x))
  leftRegular-regular = leftRegular-⟨$⟩
```

The textbook's three facts: λ respects equality, λ(g h) = λ(g) ∘ λ(h), and
λ is one-to-one, since λ(g) sends the index of 1 to the index of g; also
λ(1) is the identity.

```agda
  -- λ respects equality.
  leftRegular-cong : {g h : Carrier} → g ≈ h → leftRegular g ≈ₚ leftRegular h
  leftRegular-cong g≈h = tabulate-cong λ i → idx-cong (∙-cong g≈h ≈refl)

  -- λ(g h) = λ(g) ∘ λ(h).
  leftRegular-∙ : (g h : Carrier)
    → leftRegular (g ∙ h) ≈ₚ leftRegular g ∘ₚ leftRegular h
  leftRegular-∙ g h = tabulate-cong λ p → sym
    (trans  (lookup∘tabulate (λ i → idx (g ∙ enum i)) _)
            (idx-cong (≈trans  (∙-cong ≈refl (lookup-translation h p))
                               (≈sym (assoc-law g h (enum p))))))

  -- λ(1) is the identity.
  leftRegular-ε : leftRegular ε ≈ₚ idₚ
  leftRegular-ε =
    tabulate-cong λ i → trans (idx-cong (idˡ-law (enum i))) (idx-enum i)

  -- The element read off a permutation at the index of 1.
  readOff : Perm order → Carrier
  readOff σ = enum (σ ⟨$⟩ idx ε)

  private
    -- Equal permutations give back equal elements.
    readOff-cong : (σ τ : Perm order) → σ ≈ₚ τ → readOff σ ≈ readOff τ
    readOff-cong _ _ σ≈τ = reflexive (cong (λ v → enum (lookup v (idx ε))) σ≈τ)

  -- λ(g) gives back g at the index of 1 ...
  readOff-leftRegular : (g : Carrier) → readOff (leftRegular g) ≈ g
  readOff-leftRegular g =
    ≈trans  (reflexive (cong enum (leftRegular-⟨$⟩ g ε)))
            (≈trans (enum-idx (g ∙ ε)) (idʳ-law g))

  -- ... so λ is one-to-one.
  leftRegular-injective : {g h : Carrier}
    → leftRegular g ≈ₚ leftRegular h → g ≈ h
  leftRegular-injective {g} {h} λg≈λh =
    ≈trans  (≈sym (readOff-leftRegular g))
            (≈trans  (readOff-cong (leftRegular g) (leftRegular h) λg≈λh)
                     (readOff-leftRegular h))
```

So λ is a homomorphism, and a monomorphism, of G into Sym(|G|), in the
Agda Universal Algebra Library's sense.

```agda
  -- λ as a map of setoids.
  leftRegularᶠ : Func setoid (permSetoid {order})
  leftRegularᶠ = record { to = leftRegular ; cong = leftRegular-cong }

  -- The left regular representation is a homomorphism into Sym(|G|) ...
  regularHom : hom (FiniteGroup.algebra 𝔾) (proj₁ (symGroup order))
  regularHom =
    Homomorphisms.groupHom 𝒢 (symGroup order) leftRegularᶠ leftRegular-∙

  -- ... and a monomorphism.
  regularMon : mon (FiniteGroup.algebra 𝔾) (proj₁ (symGroup order))
  regularMon = Homomorphisms.groupMon  𝒢 (symGroup order) leftRegularᶠ
                                       leftRegular-∙ leftRegular-injective
```

#### The image

The image of λ is the set of the permutations λ(g), g in G: the
textbook's predicate.  It is a subgroup of Sym(|G|), since λ preserves
products, the identity and inverses (λ(g⁻¹) is λ(g)⁻¹, the inverse vector
λ(g) carries).  Its decider reads g off σ at the index of 1 and compares
λ(g) with σ.

```agda
  -- The image of λ: the permutations λ(g).
  InImage : Pred (Perm order) α
  InImage σ = Σ[ g ∈ Carrier ] (leftRegular g ≈ₚ σ)

  -- It is a subgroup of Sym(|G|).
  inImage-isSubgroup : IsSubgroup (symGroup order) InImage
  inImage-isSubgroup = mkIsSubgroup (symGroup order)
    (λ σ≈τ (g , p) → g , trans p σ≈τ)
    (λ (g , p) (h , q) → g ∙ h , trans (leftRegular-∙ g h) (cong₂ _⨁_ p q))
    (ε , leftRegular-ε)
    (λ {σ} (g , p) → g ⁻¹ , ⁻¹-cong (leftRegular g) σ p)

  -- Membership in the image, decided at the index of 1.
  inImage? : (σ : Perm order) → Dec (InImage σ)
  inImage? σ with leftRegular (readOff σ) ≟ₚ σ
  ... | yes p  = yes (readOff σ , p)
  ... | no ¬p  = no λ (h , q) →
    ¬p (trans  (leftRegular-cong
                 (≈trans  (readOff-cong σ (leftRegular h) (sym q))
                          (readOff-leftRegular h)))
               q)

  -- The image of λ, a decidable subgroup of Sym(|G|).
  image : DecSubgroup (symGroup order) α
  image = (InImage , inImage-isSubgroup) , inImage?
```

#### G is isomorphic to the image

G is isomorphic to the image as a group (`Groups.Subgroup.Group`): g goes
to λ(g), and an element (σ, g, p) of the image back to g.  So the image
has the order of G.

<!--
```agda
  open AsGroup (Sym order) using ( asGroup ; asFiniteGroup )
  open Subgroups (Sym order) using ( ∣_∣ )
```
-->

```agda
  private
    -- The algebra of the image, as a group.
    𝑰 : Algebra α 0ℓ
    𝑰 = proj₁ (asGroup image)

  -- g goes to λ(g), an element of the image ...
  toImage : Func setoid 𝔻[ 𝑰 ]
  toImage = record  { to = λ g → leftRegular g , g , refl
                    ; cong = leftRegular-cong }

  -- ... and an element of the image back to the element it is the image of.
  fromImage : Func 𝔻[ 𝑰 ] setoid
  fromImage = record
    { to    = λ (_ , g , _) → g
    ; cong  = λ {x} {y} x≈y → leftRegular-injective
                (trans (x .proj₂ .proj₂) (trans x≈y (sym (y .proj₂ .proj₂)))) }

  -- G is isomorphic to the image of λ.
  cayley-≅ : FiniteGroup.algebra 𝔾 ≅ 𝑰
  cayley-≅ = Isomorphisms.groupIso  𝒢 (asGroup image) toImage fromImage
                                    leftRegular-∙
                                    (λ (_ , _ , p) → p)
                                    (λ _ → ≈refl)

  -- G and the image, as setoids, are in bijection ...
  ↔image : Inverse setoid 𝔻[ 𝑰 ]
  ↔image = record
    { to         = Func.to toImage
    ; from       = Func.to fromImage
    ; to-cong    = leftRegular-cong
    ; from-cong  = λ {x} {y} → Func.cong fromImage {x} {y}
    ; inverse    =
        (λ {x} y≈ → trans (leftRegular-cong y≈) (x .proj₂ .proj₂)) ,
        (λ {_} {y} y≈ → leftRegular-injective (trans (y .proj₂ .proj₂) y≈))
    }

  -- ... so the image has the order of G.
  ∣image∣≡∣G∣ : ∣ image ∣ ≡ order
  ∣image∣≡∣G∣ =
    sym (inverse⇒≡ finite (FiniteGroup.finite (asFiniteGroup image)) ↔image)
```

#### The theorem

```agda
-- Cayley's theorem: a finite group G is isomorphic to a subgroup of Sym(|G|).
cayley : (𝔾 : FiniteGroup α ρ)
  → Σ[ H ∈ DecSubgroup (symGroup (FiniteGroup.order 𝔾)) α ]
      (FiniteGroup.algebra 𝔾
        ≅ proj₁ (AsGroup.asGroup (Sym (FiniteGroup.order 𝔾)) H))
cayley 𝔾 = Cayley.image 𝔾 , Cayley.cayley-≅ 𝔾
```
