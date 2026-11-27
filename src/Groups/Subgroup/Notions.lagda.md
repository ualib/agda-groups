---
layout: default
file: "src/Groups/Subgroup/Notions.lagda.md"
title: "Groups.Subgroup.Notions module"
date: "2026-11-27"
author: "the agda-groups development team"
---

### Notions about subgroups

This is the `Groups.Subgroup.Notions` module of the agda-groups library.

It states the notions that later modules use, each decided over a finite
group: normal subgroups; abelian groups and subgroups; powers xⁿ and
elementary abelian p-groups; the subgroups between two subgroups;
complements; and minimal normal subgroups, with the theorem that every
nontrivial normal subgroup of a finite group contains a minimal normal
one.

#### Two forms of a statement about every subgroup

A statement about *every* subgroup between H and K can take two forms
(ADR 0001, § 3).  Over the library's decidable subgroups it may end in a
disjunction: every decidable subgroup L between H and K is H or K
(`OnlyEnds`).  Over subgroups that are only predicates it carries a
witness instead: every subgroup L between H and K that holds an element
outside H contains K (`OnlyEndsʷ`).  The reason is the second rule of
the plan.  For any proposition P, the predicate "x is 1, or P holds and x
is in K" is a subgroup between 1 and K, so the disjunction about every
predicate subgroup would prove P or not P; that subgroup is decidable
only when P is, so the disjunction about every decidable subgroup decides
nothing new.  The witnessed form gives the disjunction for decidable
subgroups, by a search for the witness (`ʷ⇒OnlyEnds`), and the
*generator condition* of ADR 0001's § 3, which a search decides for a
concrete group, gives the witnessed form (`betweenʷ`) and so the
disjunction (`between`); conversely, the disjunction gives the condition
(`generates`).  The Agda Universal Algebra Library's interval of
subuniverses, `SubInterval`, is an interval of predicates, so over it
only the witnessed form is stated (`OnlyEndsᴵ`).

Minimal normal subgroups take the witnessed form for the same reason, as
that library's `MinimalNormalDescent` explains: minimality against every
normal subgroup, with nontriviality in the negative form, proves
double-negation elimination.  The descent theorem is that library's, stated here for the
library's finite groups and decidable subgroups.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Subgroup.Notions where

-- Imports from the Agda Standard Library
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Base                          using ( zero ; suc )
open import Data.List.Base                         using ( List ; _∷_ ; lookup )
open import Data.Nat.Base                          using ( ℕ ; _+_ ; _*_ )
open import Data.Nat.Primality                     using ( Prime ; prime? )
open import Data.Product.Base                      using ( _,_ ; proj₁ ; proj₂ ; _×_ ; ∃-syntax ; Σ-syntax )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Function.Base                          using ( _∘_ )
open import Level                                  using ( Level ; _⊔_ ) renaming ( suc to lsuc )
open import Relation.Binary.Bundles                using ( Setoid )
open import Relation.Binary.Definitions            using ( _Respects_ )
open import Relation.Nullary.Decidable             using ( Dec ; yes ; no ; map′ ; _×?_ ; _→?_ ; ¬? )
open import Relation.Nullary.Negation              using ( ¬_ )
open import Relation.Unary                         using ( Pred ; _∈_ ; _∉_ ; _⊆_ ; _≐_ ; _∩_ )

import Algebra.Bundles                             as Std
import Algebra.Properties.Monoid.Mult              as Mult
import Data.Fin.Properties                         as Fin

-- Imports from the Agda Universal Algebra Library
open import Classical.Bundles.Group                using ( ⟨_⟩ᵍᵖ )
open import Classical.Structures.Group.Basic       using ( Group ; module Group-Op )
open import Classical.Structures.Group.Complements using ( module Complements )
open import Classical.Structures.Group.Conjugation using ( module Conjugate )
open import Classical.Structures.Group.MinimalNormalDescent
                                                   using ( module MinimalNormalDescent )
open import Classical.Structures.Group.SubgroupLattice
                                                   using ( module GroupSublattice )
open import Classical.Structures.Group.Subgroups   using ( IsSubgroup ; DecSubgroup )

-- Imports from this library
open import Groups.Finite.Group                    using ( FiniteGroup )
open import Groups.Finite.Subset                   using ( DecSubset )
open import Groups.Subgroup                        using ( module Subgroups )
open import Groups.Subgroup.Generated              using ( module Generated )

private variable α ρ : Level
```
-->

Everything below is about one finite group 𝔾, the parameter of the
module `Notions`.

<!--
```agda
module Notions (𝔾 : FiniteGroup α ρ) where
  private
    𝒢 : Group α ρ
    𝒢 = FiniteGroup.group 𝔾

  open FiniteGroup 𝔾  using ( Carrier ; setoid ; order ; enum ; idx ; enum-idx ; toFiniteAlgebra ; _≟_
                            ; all? )
  open Setoid setoid  using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Group-Op 𝒢     using ( _∙_ ; ε ; ∙-cong )
  open Conjugate 𝒢    using ( conj-syntax ; conj-cong ; conj-congᵍ )
  open Complements 𝒢  using ( Factors )
  open Subgroups 𝔾    using ( set ; isSubgroup ; _∈?_ ; _⊆?_ ; ⊈⇒∃ ; trivial ; _∩ᵈ_ ; _∙ᵈ_ ; preimage )
  open Generated 𝔾    using ( InGen ; gens∈ ; gen⊆ ; inGen-isSubgroup ; InGen-∷ ; InGen-∷-cong
                            ; Generators ; gens ; Adjoined ; adjoin ; ⟨_⟩ )
  open Mult (Std.Group.monoid ⟨ 𝒢 ⟩ᵍᵖ) using ( ×-congʳ ; ×-homo-+ ; ×-assocˡ ) renaming ( _×_ to _×ⁿ_ )
  open MinimalNormalDescent 𝒢 toFiniteAlgebra
                      using ( IsNormalSubgroup ; minimal-normal-descentᵈ ; minimalʷ→minimalᵈ )

  private variable ℓ ℓ′ ℓ₁ ℓ₂ : Level
```
-->

#### Normal subgroups

H is **normal** in G when x ^ g = g x g⁻¹ lies in H for every x in H and
every g (the Agda Universal Algebra Library's `IsNormal`).  It is decided
by a sweep of the enumeration, over g and over x; and for H = ⟨A⟩, by
the generators alone: ⟨A⟩ is normal exactly when a ^ g lies in ⟨A⟩ for
every generator a and every g, by the universal property applied to the
preimage of ⟨A⟩ under conjugation by g.  The module re-exports
`IsNormal`, so that a statement about normal subgroups needs only this
module.

```agda
  -- Normality: closure under conjugation.
  open Conjugate 𝒢 public using ( IsNormal )

  -- Normality, decided by a sweep.
  normal? : (H : DecSubgroup 𝒢 ℓ) → Dec (IsNormal (set H))
  normal? H = map′ (λ t g {x} → t g x) (λ N g x → N g {x})
    (all? respᵍ (λ g → all? (respˣ g) (λ x → (x ∈? H) →? (x ^ g ∈? H))))
    where
    open IsSubgroup (isSubgroup H) using ( respects )
    respˣ : ∀ g → (λ x → x ∈ set H → x ^ g ∈ set H) Respects _≈_
    respˣ g x≈y t y∈H = respects (conj-cong g x≈y) (t (respects (≈sym x≈y) y∈H))
    respᵍ : (λ g → ∀ x → x ∈ set H → x ^ g ∈ set H) Respects _≈_
    respᵍ g≈h t x x∈H = respects (conj-congᵍ x g≈h) (t x x∈H)

  -- Normality of ⟨A⟩, decided by the generators.
  normalGen? : (𝔸 : Generators) → Dec (IsNormal (set ⟨ 𝔸 ⟩))
  normalGen? 𝔸 = map′ to (λ N g k → N g (gens∈ A k)) (all? resp (λ g → Fin.all? (λ k → lookup A k ^ g ∈? ⟨ 𝔸 ⟩)))
    where
    A : List Carrier
    A = gens 𝔸
    to : (∀ g k → lookup A k ^ g ∈ InGen A) → IsNormal (InGen A)
    to t g = gen⊆ A (set (preimage g ⟨ 𝔸 ⟩)) (isSubgroup (preimage g ⟨ 𝔸 ⟩)) (t g)
    resp : (λ g → ∀ k → lookup A k ^ g ∈ InGen A) Respects _≈_
    resp g≈h t k = IsSubgroup.respects (inGen-isSubgroup A) (conj-congᵍ (lookup A k) g≈h) (t k)
```

#### Abelian groups

A group is **abelian** when its operation is commutative (Aschbacher, §
1), and so is a subgroup when any two of its elements commute.  Each is
decided by a sweep of the enumeration, over pairs.

```agda
  private
    -- Commuting respects ≈ in both elements.
    commute-resp : ∀ {x x′ y y′} → x ≈ x′ → y ≈ y′ → x ∙ y ≈ y ∙ x → x′ ∙ y′ ≈ y′ ∙ x′
    commute-resp x≈x′ y≈y′ c = ≈trans (∙-cong (≈sym x≈x′) (≈sym y≈y′)) (≈trans c (∙-cong y≈y′ x≈x′))

  -- The group is abelian ...
  IsAbelian : Type (α ⊔ ρ)
  IsAbelian = ∀ x y → x ∙ y ≈ y ∙ x

  -- ... decided.
  isAbelian? : Dec IsAbelian
  isAbelian? = all? (λ x≈x′ t y → commute-resp x≈x′ ≈refl (t y))
                    (λ x → all? (λ y≈y′ → commute-resp ≈refl y≈y′) (λ y → x ∙ y ≟ y ∙ x))

  -- A subgroup is abelian ...
  Abelian : DecSubgroup 𝒢 ℓ → Type (α ⊔ ρ ⊔ ℓ)
  Abelian H = ∀ {x y} → x ∈ set H → y ∈ set H → x ∙ y ≈ y ∙ x

  -- ... decided.
  abelian? : (H : DecSubgroup 𝒢 ℓ) → Dec (Abelian H)
  abelian? H = map′ (λ t {x} {y} x∈H y∈H → t x x∈H y y∈H) (λ A x x∈H y y∈H → A x∈H y∈H)
    (all? respˣ (λ x → (x ∈? H) →? all? (respʸ x) (λ y → (y ∈? H) →? (x ∙ y ≟ y ∙ x))))
    where
    open IsSubgroup (isSubgroup H) using ( respects )
    respʸ : ∀ x → (λ y → y ∈ set H → x ∙ y ≈ y ∙ x) Respects _≈_
    respʸ x y≈y′ t y′∈H = commute-resp ≈refl y≈y′ (t (respects (≈sym y≈y′) y′∈H))
    respˣ : (λ x → x ∈ set H → ∀ y → y ∈ set H → x ∙ y ≈ y ∙ x) Respects _≈_
    respˣ x≈x′ t x′∈H y y∈H = commute-resp x≈x′ ≈refl (t (respects (≈sym x≈x′) x′∈H) y y∈H)
```

#### Powers and elementary abelian p-groups

The power xⁿ is the product of n copies of x (Aschbacher, § 1), here
agda-stdlib's multiple `n × x` in the group's monoid, written
multiplicatively, with that library's laws: it respects `≈`, xᵐ⁺ⁿ = xᵐ
xⁿ, and (xⁿ)ᵐ = xᵐⁿ.

```agda
  infixr 8 _^ⁿ_

  -- The power xⁿ.
  _^ⁿ_ : Carrier → ℕ → Carrier
  x ^ⁿ n = n ×ⁿ x

  -- Powers respect ≈ ...
  ^ⁿ-cong : (n : ℕ) {x y : Carrier} → x ≈ y → x ^ⁿ n ≈ y ^ⁿ n
  ^ⁿ-cong n = ×-congʳ n

  -- ... and add and multiply their exponents.
  ^ⁿ-+ : (x : Carrier) (m n : ℕ) → x ^ⁿ (m + n) ≈ x ^ⁿ m ∙ x ^ⁿ n
  ^ⁿ-+ = ×-homo-+

  ^ⁿ-* : (x : Carrier) (m n : ℕ) → (x ^ⁿ n) ^ⁿ m ≈ x ^ⁿ (m * n)
  ^ⁿ-* = ×-assocˡ
```

For a prime p, a group is **elementary abelian** when it is abelian and
xᵖ = 1 for every x.  Aschbacher (§ 1) defines an elementary abelian
p-group as an abelian p-group of exponent p; with p prime, xᵖ = 1 for
every x makes the order of each element 1 or p, so the group is a p-group
by Cauchy's theorem (M4-2), and the two definitions agree.  A subgroup is
elementary abelian when it is so as a group, stated on its elements.

```agda
  -- H is elementary abelian for the prime p.
  record ElementaryAbelian (p : ℕ) (H : DecSubgroup 𝒢 ℓ) : Type (α ⊔ ρ ⊔ ℓ) where
    field
      prime     : Prime p
      abelian   : Abelian H
      exponent  : ∀ {x} → x ∈ set H → x ^ⁿ p ≈ ε

  -- It is decidable.
  elementaryAbelian? : (p : ℕ) (H : DecSubgroup 𝒢 ℓ) → Dec (ElementaryAbelian p H)
  elementaryAbelian? p H = map′
    (λ (pr , ab , ex) → record { prime = pr ; abelian = λ {x} {y} → ab {x} {y} ; exponent = λ {x} → ex x })
    (λ E → ElementaryAbelian.prime E , (λ {x} {y} → ElementaryAbelian.abelian E {x} {y})
         , λ x → ElementaryAbelian.exponent E {x})
    (prime? p ×? abelian? H ×? all? resp (λ x → (x ∈? H) →? (x ^ⁿ p ≟ ε)))
    where
    open IsSubgroup (isSubgroup H) using ( respects )
    resp : (λ x → x ∈ set H → x ^ⁿ p ≈ ε) Respects _≈_
    resp x≈y t y∈H = ≈trans (^ⁿ-cong p (≈sym x≈y)) (t (respects (≈sym x≈y) y∈H))
```

#### The subgroups between two subgroups

L lies between H and K when H ⊆ L ⊆ K.  `OnlyEnds ℓ′ H K` is the
disjunctive form: every decidable subgroup at level ℓ′ between H and K
is H or K, up to `≐`.  `OnlyEndsʷ ℓ′ H K` is the witnessed form, over
subgroups that are predicates: each between H and K that holds an
element outside H contains K.  The witnessed form gives the disjunctive
one for decidable subgroups, since L ⊆ H is decided and a failed
inclusion has a witness.

```agda
  -- Every decidable subgroup between H and K is H or K.
  OnlyEnds : (ℓ′ : Level) → DecSubgroup 𝒢 ℓ₁ → DecSubgroup 𝒢 ℓ₂ → Type (α ⊔ ρ ⊔ lsuc ℓ′ ⊔ ℓ₁ ⊔ ℓ₂)
  OnlyEnds ℓ′ H K = (L : DecSubgroup 𝒢 ℓ′) → set H ⊆ set L → set L ⊆ set K
    → (set L ≐ set H) ⊎ (set L ≐ set K)

  -- Every subgroup between H and K that holds an element outside H contains K.
  OnlyEndsʷ : (ℓ′ : Level) → Pred Carrier ℓ₁ → Pred Carrier ℓ₂ → Type (α ⊔ ρ ⊔ lsuc ℓ′ ⊔ ℓ₁ ⊔ ℓ₂)
  OnlyEndsʷ ℓ′ H K = (L : Pred Carrier ℓ′) → IsSubgroup 𝒢 L → H ⊆ L → L ⊆ K
    → ∃[ x ] (x ∈ L × x ∉ H) → K ⊆ L

  -- The witnessed form gives the disjunctive one.
  ʷ⇒OnlyEnds : (H : DecSubgroup 𝒢 ℓ₁) (K : DecSubgroup 𝒢 ℓ₂) → OnlyEndsʷ ℓ′ (set H) (set K) → OnlyEnds ℓ′ H K
  ʷ⇒OnlyEnds H K w L H⊆L L⊆K with L ⊆? H
  ... | yes L⊆H  = inj₁ (L⊆H , H⊆L)
  ... | no L⊈H   = inj₂ (L⊆K , w (set L) (isSubgroup L) H⊆L L⊆K (⊈⇒∃ L H L⊈H))
```

The **generator condition**, for H = ⟨B⟩ and a decidable K: every
element x of K outside H generates K together with B, K ⊆ ⟨x, B⟩.  It is
stated at the enumerated elements, where a search decides it with the
certificates of the ⟨x, B⟩ that `Adjoined B` holds, and it holds then at
every element, since ⟨x, B⟩ depends on x only up to `≈`.

```agda
  -- Each enumerated element of K outside ⟨B⟩ generates K together with B.
  Generates : List Carrier → DecSubgroup 𝒢 ℓ → Type (α ⊔ ρ ⊔ ℓ)
  Generates B K = ∀ i → enum i ∈ set K → enum i ∉ InGen B → set K ⊆ InGen (enum i ∷ B)

  -- It holds at every element of K outside ⟨B⟩.
  generates-at : {B : List Carrier} (K : DecSubgroup 𝒢 ℓ) → Generates B K
    → ∀ {x} → x ∈ set K → x ∉ InGen B → set K ⊆ InGen (x ∷ B)
  generates-at {B = B} K gen {x} x∈K x∉H y∈K =
    InGen-∷-cong B (enum-idx x)
      (gen (idx x) (IsSubgroup.respects (isSubgroup K) (≈sym (enum-idx x)) x∈K)
                   (λ e → x∉H (IsSubgroup.respects (inGen-isSubgroup B) (enum-idx x) e)) y∈K)

  -- The condition, decided by a search, with the certificates of every ⟨x, B⟩.
  generates? : (𝔹 : Generators) → Adjoined (gens 𝔹) → (K : DecSubgroup 𝒢 ℓ) → Dec (Generates (gens 𝔹) K)
  generates? 𝔹 cs K = Fin.all? (λ i → (enum i ∈? K) →? (¬? (enum i ∈? ⟨ 𝔹 ⟩) →? (K ⊆? ⟨ adjoin cs i ⟩)))
```

From the condition, the witnessed form holds: a subgroup L between ⟨B⟩
and K holding an element x outside ⟨B⟩ holds x and B, so it holds ⟨x,
B⟩ by the universal property, and so K.  The disjunctive form follows.
Conversely, when ⟨B⟩ ⊆ K, the disjunction for the decidable subgroups
⟨x, B⟩ gives the condition, since ⟨x, B⟩ is not ⟨B⟩ when x lies outside
⟨B⟩.

```agda
  -- The generator condition gives the witnessed form ...
  betweenʷ : {B : List Carrier} (K : DecSubgroup 𝒢 ℓ) → Generates B K → OnlyEndsʷ ℓ′ (InGen B) (set K)
  betweenʷ {B = B} K gen L L-sg H⊆L L⊆K (x , x∈L , x∉H) =
    gen⊆ (x ∷ B) L L-sg gens⊆L ∘ generates-at K gen (L⊆K x∈L) x∉H
    where
    gens⊆L : ∀ k → lookup (x ∷ B) k ∈ L
    gens⊆L zero     = x∈L
    gens⊆L (suc k)  = H⊆L (gens∈ B k)

  -- ... and so every decidable subgroup between ⟨B⟩ and K is ⟨B⟩ or K.
  between : (𝔹 : Generators) (K : DecSubgroup 𝒢 ℓ) → Generates (gens 𝔹) K → OnlyEnds ℓ′ ⟨ 𝔹 ⟩ K
  between 𝔹 K gen = ʷ⇒OnlyEnds ⟨ 𝔹 ⟩ K (betweenʷ K gen)

  -- Conversely, the disjunction gives the condition.
  generates : (𝔹 : Generators) → Adjoined (gens 𝔹) → (K : DecSubgroup 𝒢 ℓ) → set ⟨ 𝔹 ⟩ ⊆ set K
    → OnlyEnds ρ ⟨ 𝔹 ⟩ K → Generates (gens 𝔹) K
  generates 𝔹 cs K H⊆K b i x∈K x∉H =
    choose (b ⟨ adjoin cs i ⟩ (InGen-∷ (enum i) B) (gen⊆ (enum i ∷ B) (set K) (isSubgroup K) gens⊆K))
    where
    B : List Carrier
    B = gens 𝔹
    gens⊆K : ∀ k → lookup (enum i ∷ B) k ∈ set K
    gens⊆K zero     = x∈K
    gens⊆K (suc k)  = H⊆K (gens∈ B k)
    choose : (InGen (enum i ∷ B) ≐ InGen B) ⊎ (InGen (enum i ∷ B) ≐ set K) → set K ⊆ InGen (enum i ∷ B)
    choose (inj₁ (L⊆H , _))  = ⊥-elim (x∉H (L⊆H (gens∈ (enum i ∷ B) zero)))
    choose (inj₂ (_ , K⊆L))  = K⊆L
```

The Agda Universal Algebra Library's `SubInterval B C` is the interval
[B, C] of its lattice of subuniverses, at the level L of
`GroupSublattice 𝒢 ℓ₀`: predicates closed under the operations, which
need not respect `≈`.  Its members that respect `≈` are subgroups, and
over them the witnessed form reads as `OnlyEndsᴵ`; `OnlyEndsʷ` at the
level L gives it.

```agda
  module _ (ℓ₀ : Level) where
    open GroupSublattice 𝒢 ℓ₀ using ( Subᴸ ; _≤_ ; module SubInterval ) renaming ( L to Lᴵ )

    -- Every member of [B, C] that respects ≈ and holds an element outside B contains C.
    OnlyEndsᴵ : (B C : Subᴸ) → B ≤ C → Type (α ⊔ ρ ⊔ lsuc Lᴵ)
    OnlyEndsᴵ B C B≤C = (X : SubInterval.Interval B C B≤C) → proj₁ (proj₁ X) Respects _≈_
      → ∃[ x ] (x ∈ proj₁ (proj₁ X) × x ∉ proj₁ B) → C ≤ proj₁ X

    -- The witnessed form over predicates gives it.
    ʷ⇒OnlyEndsᴵ : (B C : Subᴸ) (B≤C : B ≤ C) → OnlyEndsʷ Lᴵ (proj₁ B) (proj₁ C) → OnlyEndsᴵ B C B≤C
    ʷ⇒OnlyEndsᴵ B C B≤C w ((X , X-sub) , B≤X , X≤C) resp =
      w X (record { respects = resp ; isSubuniverse = X-sub }) B≤X X≤C
```

#### Complements

A subgroup K is a **complement** to N in G when N ∩ K = 1 and NK = G
(Aschbacher, § 10, where N is normal; the definition does not use it).
N ∩ K = 1 is stated as an inclusion in the trivial subgroup, the other
inclusion being automatic, and NK = G as the Agda Universal Algebra
Library's `Factors`, every element a product.  Both are decided: the
first by an inclusion, the second by the decider of the set NK of
products (`Groups.Subgroup`).  That library's `Complements` module treats
complements in an interval of subgroups, which is not this notion.

```agda
  -- K is a complement to N.
  record IsComplement (N : DecSubgroup 𝒢 ℓ) (K : DecSubgroup 𝒢 ℓ′) : Type (α ⊔ ρ ⊔ ℓ ⊔ ℓ′) where
    field
      meet     : set N ∩ set K ⊆ set trivial
      factors  : Factors (set N) (set K)

  -- It is decidable.
  isComplement? : (N : DecSubgroup 𝒢 ℓ) (K : DecSubgroup 𝒢 ℓ′) → Dec (IsComplement N K)
  isComplement? N K = map′ (λ (m , f) → record { meet = λ {x} → m {x} ; factors = f })
                           (λ C → (λ {x} → IsComplement.meet C {x}) , IsComplement.factors C)
    (((N ∩ᵈ K) ⊆? trivial) ×? all? (DecSubset.respects (N ∙ᵈ K)) (DecSubset.decide (N ∙ᵈ K)))
```

#### Minimal normal subgroups

A **minimal normal** subgroup of G is a minimal member of the set of
nontrivial normal subgroups (Aschbacher, § 8).  The library's notion is
the Agda Universal Algebra Library's witnessed form,
`IsMinimalNormalʷ M`: M is normal, holds an element other than 1, and
lies in every normal subgroup inside it that holds an element other than
1.  Its minimality quantifies over every normal subgroup that is a
predicate, so its nontriviality carries a witness (the second rule; that
library's `minimal→DNE` shows that the negative form there proves
double-negation elimination).  Against a decidable normal subgroup, the negative form of
nontriviality suffices, since a search finds the witness
(`minimal⇒minimalᵈ`).

That library's descent theorem works at the level α ⊔ ρ of its normal
closures; a decidable normal subgroup passes to its `Normalᵈ` there and
back.  The module re-exports the names these statements use.

```agda
  -- The witnessed notions of minimal normality and of nontriviality, and Normalᵈ.
  open MinimalNormalDescent 𝒢 toFiniteAlgebra public
    using ( IsMinimalNormalʷ ; module IsMinimalNormalʷ ; HasNontrivialWitness ; Normalᵈ )

  -- A decidable normal subgroup, as agda-algebras' Normalᵈ ...
  toNormalᵈ : (N : DecSubgroup 𝒢 (α ⊔ ρ)) → IsNormal (set N) → Normalᵈ
  toNormalᵈ N nrm = set N , record { isSubgroup = isSubgroup N ; isNormal = nrm } , proj₂ N

  -- ... and back.
  fromNormalᵈ : Normalᵈ → DecSubgroup 𝒢 (α ⊔ ρ)
  fromNormalᵈ (N , nsg , N?) = (N , IsNormalSubgroup.isSubgroup nsg) , N?

  -- Minimality against a decidable normal subgroup, with nontriviality in the negative form.
  minimal⇒minimalᵈ : {M : Pred Carrier (α ⊔ ρ)} → IsMinimalNormalʷ M
    → (N : DecSubgroup 𝒢 (α ⊔ ρ)) → IsNormal (set N) → set N ⊆ M → ¬ (set N ⊆ set trivial) → M ⊆ set N
  minimal⇒minimalᵈ M-min N nrm = minimalʷ→minimalᵈ M-min (toNormalᵈ N nrm)
```

The descent theorem: every nontrivial normal subgroup N of a finite group
contains a minimal normal subgroup.  N is a decidable subgroup, and its
nontriviality is the textbook's N ≠ 1, the negative form, since a search
of N finds an element other than 1.

```agda
  -- Every nontrivial normal subgroup contains a minimal normal subgroup.
  minimal-normal-descent : (N : DecSubgroup 𝒢 (α ⊔ ρ)) → IsNormal (set N) → ¬ (set N ⊆ set trivial)
    → Σ[ M ∈ DecSubgroup 𝒢 (α ⊔ ρ) ] (IsMinimalNormalʷ (set M) × set M ⊆ set N)
  minimal-normal-descent N nrm N≠1 = fromNormalᵈ M , proj₁ (proj₂ d) , proj₂ (proj₂ d)
    where
    d = minimal-normal-descentᵈ (toNormalᵈ N nrm) N≠1
    M = proj₁ d
```
