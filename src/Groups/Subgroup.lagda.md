---
layout: default
file: "src/Groups/Subgroup.lagda.md"
title: "Groups.Subgroup module"
date: "2026-11-27"
author: "the agda-groups development team"
---

### Subgroups of a finite group

This is the `Groups.Subgroup` module of the agda-groups library.

A **subgroup** of a finite group G is the Agda Universal Algebra
Library's decidable subgroup, `DecSubgroup`: a predicate on the carrier,
a proof that it is a subgroup (it respects `≈` and is closed under the
operations), and a decision procedure for membership, its *decider*
(ADR 0001, § 2).  Two subgroups are equal when they have the same
elements, `H ≐ K`, the pair of inclusions H ⊆ K and K ⊆ H; never `≡`,
since two subgroups with the same elements are not propositionally equal
under `--without-K --safe` (ADR 0001, § 3).

Over a finite group a decidable subgroup is a decidable subset of the
carrier (`Groups.Finite.Subset`), so its **order** |H| is the size of
that subset, the number of enumerated elements its decider accepts, and
inclusion and `≐` are decided at the enumerated elements, with a witness
when an inclusion fails.  The module then gives the subgroups that later
modules build, each with its decider: the trivial subgroup, of order 1,
and the whole group, of order |G|; intersections; conjugates and
normalizers; the decider remembered as a table (`memo`); and the
subgroups that the Agda Universal Algebra Library defines, decided over
a finite group: the centralizer of a decidable subset, the normal
closure of an element, and the set HK of products of two subgroups.

Where a notion has a textbook definition and a computed one, both are
given, the textbook's first, with the theorem that they agree (ADR 0001,
§ 5): the conjugate g H g⁻¹ is the set of the g h g⁻¹ for h in H, and is
decided as the set of the x with g⁻¹ x g in H; the normalizer is the set
of the g with g H g⁻¹ = H, and is decided as the set of the g for which
conjugation by g and by g⁻¹ maps H into H.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Subgroup where

-- Imports from the Agda Standard Library
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Fin.Base                          using ( zero )
open import Data.Nat.Base                          using ( ℕ ; _≤_ )
open import Data.Nat.Properties                    using ( ≤-antisym )
open import Data.Product.Base                      using ( _,_ ; proj₁ ; proj₂ ; _×_ ; ∃-syntax )
open import Data.Unit.Base                         using ( tt )
open import Function.Bundles                       using ( _⇔_ ; mk⇔ )
open import Level                                  using ( Level ; _⊔_ ; 0ℓ ; Lift ; lift ; lower )
open import Relation.Binary.Bundles                using ( Setoid )
open import Relation.Binary.Definitions            using ( _Respects_ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; trans )
open import Relation.Nullary.Decidable             using ( Dec ; yes ; map′ ; _×?_ ; _→?_ )
open import Relation.Unary                         using ( Pred ; _∈_ ; _∉_ ; _⊆_ ; _⊈_ ; _≐_ ; _∩_ )

import Algebra.Properties.Group                    as GroupProperties

-- Imports from the Agda Universal Algebra Library
open import Classical.Bundles.Group                using ( ⟨_⟩ᵍᵖ )
open import Classical.Structures.Group.Basic       using ( Group ; module Group-Op )
open import Classical.Structures.Group.Centralizer using ( module Centralizer )
open import Classical.Structures.Group.Complexes   using ( module Complex )
open import Classical.Structures.Group.Congruences using ( module GroupCongruences )
open import Classical.Structures.Group.Conjugation using ( module Conjugate )
open import Classical.Structures.Group.NormalClosure
                                                   using ( module NormalClosureᵈ )
open import Classical.Structures.Group.Subgroups   using ( IsSubgroup ; mkIsSubgroup ; DecSubgroup
                                                         ; trivialSubgroup ; fullSubgroup )

-- Imports from this library
open import Groups.Finite.Group                    using ( FiniteGroup )
open import Groups.Finite.Setoid                   using ( Finᶠ ; injective⇒≤ )
open import Groups.Finite.Subset                   using ( DecSubset ; full ; module Counting )

private variable α ρ : Level
```
-->

Everything below is about one finite group 𝔾, the parameter of the
module `Subgroups`; a later module opens `Subgroups 𝔾`.

<!--
```agda
module Subgroups (𝔾 : FiniteGroup α ρ) where
  private
    𝒢 : Group α ρ
    𝒢 = FiniteGroup.group 𝔾

  open FiniteGroup 𝔾  using ( Carrier ; setoid ; finite ; order ; toFiniteAlgebra ; _≟_ ; all? ; any? )
  open Setoid setoid  using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Group-Op 𝒢     using ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; ⁻¹-cong )
  open Conjugate 𝒢    using ( conj-syntax ; conjugate-syntax ; IsNormal ; conj-cong ; conj-congᵍ ; conj-ε
                            ; conj-∙-hom ; conj-⁻¹ ; conj-action-∙ ; conj-action-ε ; conj-conj⁻¹
                            ; conj⁻¹-conj ; mem-conjugate )
  open Centralizer 𝒢  using ( C[_] ; C-isSubgroup )
  open Complex 𝒢      using ( _∙ᶜ_ ; ∙ᶜ-respects )
  open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ
                      using ( ε⁻¹≈ε ; ⁻¹-involutive ; ⁻¹-anti-homo-∙ ; \\-leftDividesˡ ; \\-leftDividesʳ )
  open Counting finite
                      using ( table ; fromTable ; fromTable-table ; P≐Q⇒∣P∣≡∣Q∣ ; P⊆Q⇒∣P∣≤∣Q∣ ; ∣P∣≤n
                            ; P⊆Q∧∣P∣≡∣Q∣⇒P≐Q ; ∣full∣≡n ; ∈⇒0<∣P∣ )
                      renaming ( ∣_∣ to ∣_∣ˢ ; _⊆?_ to _⊆?ˢ_ ; _≐?_ to _≐?ˢ_ ; ⊈⇒∃ to ⊈⇒∃ˢ
                               ; finite to finiteˢ )

  private variable ℓ ℓ′ p : Level
```
-->

#### The parts of a subgroup, and its order

A decidable subgroup H is a triple: its predicate `set H`, the proof
`isSubgroup H`, and its decider, `x ∈? H`.  Its subset is the decidable
subset of the carrier with the same predicate, and its order `∣ H ∣` is
that subset's size.

```agda
  -- The predicate of a subgroup ...
  set : DecSubgroup 𝒢 ℓ → Pred Carrier ℓ
  set H = proj₁ (proj₁ H)

  -- ... the proof that it is a subgroup ...
  isSubgroup : (H : DecSubgroup 𝒢 ℓ) → IsSubgroup 𝒢 (set H)
  isSubgroup H = proj₂ (proj₁ H)

  -- ... and its decider.
  infix 4 _∈?_
  _∈?_ : (x : Carrier) (H : DecSubgroup 𝒢 ℓ) → Dec (x ∈ set H)
  x ∈? H = proj₂ H x

  -- A subgroup as a decidable subset of the carrier.
  subset : DecSubgroup 𝒢 ℓ → DecSubset setoid ℓ
  subset H = record { set = set H ; respects = IsSubgroup.respects (isSubgroup H) ; decide = proj₂ H }

  -- The order of a subgroup: the number of enumerated elements it holds.
  ∣_∣ : DecSubgroup 𝒢 ℓ → ℕ
  ∣ H ∣ = ∣ subset H ∣ˢ
```

The orders, from the sizes of `Groups.Finite.Subset`: equal subgroups
have equal orders, a subgroup of a subgroup has no larger order, no
subgroup is larger than the group, and a subgroup of a subgroup of the
same order is equal to it.

```agda
  -- Equal subgroups have equal orders.
  H≐K⇒∣H∣≡∣K∣ : (H : DecSubgroup 𝒢 ℓ) (K : DecSubgroup 𝒢 ℓ′) → set H ≐ set K → ∣ H ∣ ≡ ∣ K ∣
  H≐K⇒∣H∣≡∣K∣ H K = P≐Q⇒∣P∣≡∣Q∣ (subset H) (subset K)

  -- A subgroup of a subgroup has no larger order.
  H⊆K⇒∣H∣≤∣K∣ : (H : DecSubgroup 𝒢 ℓ) (K : DecSubgroup 𝒢 ℓ′) → set H ⊆ set K → ∣ H ∣ ≤ ∣ K ∣
  H⊆K⇒∣H∣≤∣K∣ H K = P⊆Q⇒∣P∣≤∣Q∣ (subset H) (subset K)

  -- No subgroup is larger than the group.
  ∣H∣≤∣G∣ : (H : DecSubgroup 𝒢 ℓ) → ∣ H ∣ ≤ order
  ∣H∣≤∣G∣ H = ∣P∣≤n (subset H)

  -- A subgroup of a subgroup with the same order is equal to it.
  H⊆K∧∣H∣≡∣K∣⇒H≐K : (H : DecSubgroup 𝒢 ℓ) (K : DecSubgroup 𝒢 ℓ′) → set H ⊆ set K → ∣ H ∣ ≡ ∣ K ∣
    → set H ≐ set K
  H⊆K∧∣H∣≡∣K∣⇒H≐K H K = P⊆Q∧∣P∣≡∣Q∣⇒P≐Q (subset H) (subset K)
```

#### Inclusion and equality, decided

Inclusion is decided at the enumerated elements and carried to every
element by the respect of `≈`; equality, `≐`, is decided as two
inclusions; and a failed inclusion has a witness, an element of H outside
K, found by a search of the enumeration.  So the decidable subgroups of a
finite group form a discrete setoid under `≐`.  (The Agda Universal
Algebra Library's `Classify.sub⊆-dec` and `sub⊈-witness` decide the same
for two subgroups at one level; these take any two levels.)

```agda
  infix 4 _⊆?_ _≐?_

  -- Inclusion of subgroups is decidable ...
  _⊆?_ : (H : DecSubgroup 𝒢 ℓ) (K : DecSubgroup 𝒢 ℓ′) → Dec (set H ⊆ set K)
  H ⊆? K = subset H ⊆?ˢ subset K

  -- ... and so is their equality.
  _≐?_ : (H : DecSubgroup 𝒢 ℓ) (K : DecSubgroup 𝒢 ℓ′) → Dec (set H ≐ set K)
  H ≐? K = subset H ≐?ˢ subset K

  -- A failed inclusion has a witness.
  ⊈⇒∃ : (H : DecSubgroup 𝒢 ℓ) (K : DecSubgroup 𝒢 ℓ′) → set H ⊈ set K → ∃[ x ] (x ∈ set H × x ∉ set K)
  ⊈⇒∃ H K = ⊈⇒∃ˢ (subset H) (subset K)
```

A predicate with the same elements as a subgroup is a subgroup, and a
subgroup carried to a higher level is the same subgroup.

```agda
  -- A predicate with the elements of a subgroup is a subgroup.
  ≐-isSubgroup : {P : Pred Carrier ℓ′} (H : DecSubgroup 𝒢 ℓ) → P ≐ set H → IsSubgroup 𝒢 P
  ≐-isSubgroup H (P⊆H , H⊆P) = mkIsSubgroup 𝒢
    (λ x≈y px → H⊆P (respects x≈y (P⊆H px)))
    (λ px py → H⊆P (∙-closed (P⊆H px) (P⊆H py)))
    (H⊆P ε-closed)
    (λ px → H⊆P (⁻¹-closed (P⊆H px)))
    where open IsSubgroup (isSubgroup H) using ( respects ; ∙-closed ; ε-closed ; ⁻¹-closed )

  -- A subgroup at a higher level ...
  liftᵈ : (ℓ′ : Level) → DecSubgroup 𝒢 ℓ → DecSubgroup 𝒢 (ℓ ⊔ ℓ′)
  liftᵈ ℓ′ H = ((λ x → Lift ℓ′ (x ∈ set H)) , ≐-isSubgroup H (lower , lift))
             , (λ x → map′ lift lower (x ∈? H))

  -- ... is the same subgroup.
  liftᵈ-≐ : (ℓ′ : Level) (H : DecSubgroup 𝒢 ℓ) → set (liftᵈ ℓ′ H) ≐ set H
  liftᵈ-≐ ℓ′ H = lower , lift
```

#### The trivial subgroup and the whole group

The trivial subgroup {1} and the whole group are the Agda Universal
Algebra Library's `trivialSubgroup` and `fullSubgroup`, each with a
decider: membership in {1} is decided by the enumeration's equality, and
every element is in the whole group.  Their orders are 1 and |G|: the
trivial subgroup holds 1, and any two of its elements are equal, so its
members map one-to-one into a set with one element.

```agda
  -- The trivial subgroup {1}.
  trivial : DecSubgroup 𝒢 ρ
  trivial = trivialSubgroup 𝒢 , (λ x → x ≟ ε)

  -- The whole group, as a subgroup at any level.
  whole : (ℓ : Level) → DecSubgroup 𝒢 ℓ
  whole ℓ = fullSubgroup 𝒢 ℓ , (λ _ → yes (lift tt))

  -- The trivial subgroup has order 1 ...
  ∣trivial∣≡1 : ∣ trivial ∣ ≡ 1
  ∣trivial∣≡1 = ≤-antisym
    (injective⇒≤ (finiteˢ (subset trivial)) (Finᶠ 1) (λ _ → zero)
                 (λ {x} {y} _ → ≈trans (proj₂ x) (≈sym (proj₂ y))))
    (∈⇒0<∣P∣ (subset trivial) {ε} ≈refl)

  -- ... and the whole group has the order of the group.
  ∣whole∣≡∣G∣ : (ℓ : Level) → ∣ whole ℓ ∣ ≡ order
  ∣whole∣≡∣G∣ ℓ = trans (P≐Q⇒∣P∣≡∣Q∣ (subset (whole ℓ)) full ((λ _ → tt) , (λ _ → lift tt))) ∣full∣≡n
```

#### Intersections

The intersection of two subgroups is a subgroup, decided by the two
deciders.

```agda
  infixl 7 _∩ᵈ_

  -- The intersection H ∩ K.
  _∩ᵈ_ : DecSubgroup 𝒢 ℓ → DecSubgroup 𝒢 ℓ′ → DecSubgroup 𝒢 (ℓ ⊔ ℓ′)
  H ∩ᵈ K = ( set H ∩ set K
           , mkIsSubgroup 𝒢 (λ x≈y (h , k) → H.respects x≈y h , K.respects x≈y k)
                            (λ (h , k) (h′ , k′) → H.∙-closed h h′ , K.∙-closed k k′)
                            (H.ε-closed , K.ε-closed)
                            (λ (h , k) → H.⁻¹-closed h , K.⁻¹-closed k) )
         , (λ x → (x ∈? H) ×? (x ∈? K))
    where
    module H = IsSubgroup (isSubgroup H)
    module K = IsSubgroup (isSubgroup K)
```

#### Conjugates

Write x ^ g for g x g⁻¹, the Agda Universal Algebra Library's
conjugation.  The *preimage* of H under conjugation by g, the set of the
x with g x g⁻¹ in H, is a subgroup for every H, since conjugation by g is
an endomorphism of the group, and its decider asks H's at g x g⁻¹.  The
conjugate g H g⁻¹ is the preimage under conjugation by g⁻¹, the x with
g⁻¹ x g in H.  The textbook's conjugate is the set of the h ^ g for h in
H, that library's `[ H ]^ g`; the theorem `conjugateᵈ-≐` says that the
two have the same elements.

```agda
  -- The preimage of H under conjugation by g: the x with x ^ g in H, that is, g⁻¹ H g.
  preimage : Carrier → DecSubgroup 𝒢 ℓ → DecSubgroup 𝒢 ℓ
  preimage g H = (P , mkIsSubgroup 𝒢 resp ∙-c ε-c ⁻¹-c) , (λ x → x ^ g ∈? H)
    where
    open IsSubgroup (isSubgroup H) using ( respects ; ∙-closed ; ε-closed ; ⁻¹-closed )
    P : Pred Carrier _
    P x = x ^ g ∈ set H
    resp : P Respects _≈_
    resp x≈y = respects (conj-cong g x≈y)
    ∙-c : ∀ {x y} → P x → P y → P (x ∙ y)
    ∙-c {x} {y} px py = respects (≈sym (conj-∙-hom g x y)) (∙-closed px py)
    ε-c : P ε
    ε-c = respects (≈sym (conj-ε g)) ε-closed
    ⁻¹-c : ∀ {x} → P x → P (x ⁻¹)
    ⁻¹-c {x} px = respects (≈sym (conj-⁻¹ g x)) (⁻¹-closed px)

  -- The conjugate g H g⁻¹, decided: the x with g⁻¹ x g in H.
  conjugateᵈ : Carrier → DecSubgroup 𝒢 ℓ → DecSubgroup 𝒢 ℓ
  conjugateᵈ g = preimage (g ⁻¹)

  -- It is the textbook's g H g⁻¹, the set of the h ^ g for h in H.
  conjugateᵈ-≐ : (g : Carrier) (H : DecSubgroup 𝒢 ℓ) → set (conjugateᵈ g H) ≐ [ set H ]^ g
  conjugateᵈ-≐ g H = (λ {x} p → x ^ (g ⁻¹) , p , ≈sym (conj-conj⁻¹ g x))
                   , (λ (h , h∈H , x≈hᵍ) →
                        respects (≈trans (≈sym (conj⁻¹-conj g h)) (conj-cong (g ⁻¹) (≈sym x≈hᵍ))) h∈H)
    where open IsSubgroup (isSubgroup H) using ( respects )
```

#### Normalizers

g *normalizes* H when conjugation by g and by g⁻¹ maps H into H, that
is, g H g⁻¹ ⊆ H and g⁻¹ H g ⊆ H.  For every H this is a subgroup, by one
proof, and its textbook decider tests every enumerated element of H.  The
textbook's normalizer N_G(H) is the set of the g with g H g⁻¹ = H
(Aschbacher, § 1, defines it by g⁻¹ H g = H, the same condition); the
theorem `Normalizes⇔` says that the two predicates agree, for every
group.

```agda
  -- g normalizes H: conjugation by g and by g⁻¹ maps H into H.
  Normalizes : DecSubgroup 𝒢 ℓ → Pred Carrier (α ⊔ ℓ)
  Normalizes H g = ∀ {x} → x ∈ set H → (x ^ g ∈ set H) × (x ^ (g ⁻¹) ∈ set H)

  -- The elements that normalize H form a subgroup.
  normalizes-isSubgroup : (H : DecSubgroup 𝒢 ℓ) → IsSubgroup 𝒢 (Normalizes H)
  normalizes-isSubgroup H = mkIsSubgroup 𝒢 resp ∙-c ε-c ⁻¹-c
    where
    open IsSubgroup (isSubgroup H) using ( respects )
    resp : Normalizes H Respects _≈_
    resp {g} {h} g≈h N x∈H =  respects (conj-congᵍ _ g≈h) (proj₁ (N x∈H))
                           ,  respects (conj-congᵍ _ (⁻¹-cong g≈h)) (proj₂ (N x∈H))
    ∙-c : ∀ {g h} → Normalizes H g → Normalizes H h → Normalizes H (g ∙ h)
    ∙-c {g} {h} Ng Nh {x} x∈H =
         respects (≈sym (conj-action-∙ g h x)) (proj₁ (Ng (proj₁ (Nh x∈H))))
      ,  respects (≈sym (≈trans (conj-congᵍ x (⁻¹-anti-homo-∙ g h)) (conj-action-∙ (h ⁻¹) (g ⁻¹) x)))
                  (proj₂ (Nh (proj₂ (Ng x∈H))))
    ε-c : Normalizes H ε
    ε-c {x} x∈H =  respects (≈sym (conj-action-ε x)) x∈H
                ,  respects (≈sym (≈trans (conj-congᵍ x ε⁻¹≈ε) (conj-action-ε x))) x∈H
    ⁻¹-c : ∀ {g} → Normalizes H g → Normalizes H (g ⁻¹)
    ⁻¹-c {g} Ng {x} x∈H =  proj₂ (Ng x∈H)
                        ,  respects (≈sym (conj-congᵍ x (⁻¹-involutive g))) (proj₁ (Ng x∈H))

  -- g normalizes H exactly when g H g⁻¹ = H, the textbook's condition.
  Normalizes⇔ : (H : DecSubgroup 𝒢 ℓ) (g : Carrier) → Normalizes H g ⇔ ([ set H ]^ g ≐ set H)
  Normalizes⇔ H g = mk⇔ to from
    where
    open IsSubgroup (isSubgroup H) using ( respects )
    to : Normalizes H g → [ set H ]^ g ≐ set H
    to N = (λ (h , h∈H , x≈hᵍ) → respects (≈sym x≈hᵍ) (proj₁ (N h∈H)))
         , (λ x∈H → proj₁ (conjugateᵈ-≐ g H) (proj₂ (N x∈H)))
    from : [ set H ]^ g ≐ set H → Normalizes H g
    from (Hᵍ⊆H , H⊆Hᵍ) x∈H = Hᵍ⊆H (mem-conjugate g x∈H) , proj₂ (conjugateᵈ-≐ g H) (H⊆Hᵍ x∈H)

  -- The textbook decider: test every enumerated element of H.
  normalizes? : (H : DecSubgroup 𝒢 ℓ) (g : Carrier) → Dec (Normalizes H g)
  normalizes? H g = map′ (λ t {x} → t x) (λ N x → N {x})
    (all? resp (λ x → (x ∈? H) →? ((x ^ g ∈? H) ×? (x ^ (g ⁻¹) ∈? H))))
    where
    open IsSubgroup (isSubgroup H) using ( respects )
    resp : (λ x → x ∈ set H → (x ^ g ∈ set H) × (x ^ (g ⁻¹) ∈ set H)) Respects _≈_
    resp x≈y t y∈H with t (respects (≈sym x≈y) y∈H)
    ... | p , q = respects (conj-cong g x≈y) p , respects (conj-cong (g ⁻¹) x≈y) q

  -- The normalizer N_G(H), with the textbook decider.
  normalizer : DecSubgroup 𝒢 ℓ → DecSubgroup 𝒢 (α ⊔ ℓ)
  normalizer H = (Normalizes H , normalizes-isSubgroup H) , normalizes? H
```

#### A decider remembered as a table

A decider is a function, and Agda does not remember what a function has
answered, so a computation that asks one decider about every element many
times asks it again each time.  `memo H` is H with its decider remembered
as its table over the enumeration (`Groups.Finite.Subset`'s `fromTable`),
the same subgroup up to `≐`.  The table reaches the decider as an
argument, so that one evaluation computes each of its entries once.  On
A₅, the order of N(N(P)) for a Sylow 5-subgroup P, whose decider asks
N(P)'s about each element of N(P) for each element of the group, took
2,332 ms with N(P)'s textbook decider asked afresh and 148 ms with it
remembered (2026-11-27, by `--profile=definitions`).

```agda
  private
    -- A decidable subset with the elements of H, as a subgroup.
    tabled : (H : DecSubgroup 𝒢 ℓ) (M : DecSubset setoid 0ℓ) → DecSubset.set M ≐ set H → DecSubgroup 𝒢 0ℓ
    tabled H M eq = (DecSubset.set M , ≐-isSubgroup H eq) , DecSubset.decide M

  -- H with its decider remembered as a table ...
  memo : DecSubgroup 𝒢 ℓ → DecSubgroup 𝒢 0ℓ
  memo H = tabled H (fromTable (table (subset H))) (fromTable-table (subset H))

  -- ... is the same subgroup.
  memo-≐ : (H : DecSubgroup 𝒢 ℓ) → set (memo H) ≐ set H
  memo-≐ H = fromTable-table (subset H)
```

#### Centralizers, normal closures and products

The Agda Universal Algebra Library defines the centralizer C[ S ] of a
predicate S, the g with g x = x g for every x in S (Aschbacher's C_G(S),
§ 1), and proves it a subgroup (`Centralizer`).  Over a finite group,
when S is a decidable subset (so it respects `≈`), the centralizer is
decided by testing every enumerated element of S.

```agda
  -- The centralizer of a decidable subset S.
  centralizer : DecSubset setoid p → DecSubgroup 𝒢 (α ⊔ ρ ⊔ p)
  centralizer S = (C[ DecSubset.set S ] , C-isSubgroup (DecSubset.set S))
                , (λ g → all? (resp g) (λ x → DecSubset.decide S x →? (g ∙ x ≟ x ∙ g)))
    where
    resp : ∀ g → (λ x → x ∈ DecSubset.set S → g ∙ x ≈ x ∙ g) Respects _≈_
    resp g x≈y c y∈S = ≈trans (∙-cong ≈refl (≈sym x≈y))
                         (≈trans (c (DecSubset.respects S (≈sym x≈y) y∈S)) (∙-cong x≈y ≈refl))
```

The normal closure of an element y, the least normal subgroup that holds
y, is that library's `NormalClosureᵈ`: the identity class of the
congruence generated by the pair (y, 1), with a decider computed over the
library's finiteness witness, which `toFiniteAlgebra` supplies.  Its
decider is sealed there (`abstract`), so a check by evaluation does not
run it.

```agda
  open NormalClosureᵈ 𝒢 toFiniteAlgebra using ( ⟪_⟫ ; ⟪⟫-dec ; ⟪⟫-mem ; ⟪⟫-least )
  open GroupCongruences 𝒢 using () renaming ( set to setᴺ ; set-isSubgroup to setᴺ-isSubgroup
                                            ; set-normal to setᴺ-normal )

  -- The normal closure of y.
  normalClosure : Carrier → DecSubgroup 𝒢 (α ⊔ ρ)
  normalClosure y = (setᴺ ⟪ y ⟫ , setᴺ-isSubgroup ⟪ y ⟫) , ⟪⟫-dec y

  -- It is normal ...
  normalClosure-normal : (y : Carrier) → IsNormal (set (normalClosure y))
  normalClosure-normal y = setᴺ-normal ⟪ y ⟫

  -- ... it holds y ...
  normalClosure-∋ : (y : Carrier) → y ∈ set (normalClosure y)
  normalClosure-∋ = ⟪⟫-mem

  -- ... and it lies in every normal subgroup that holds y.
  normalClosure-least : (y : Carrier) (N : DecSubgroup 𝒢 (α ⊔ ρ)) → IsNormal (set N) → y ∈ set N
    → set (normalClosure y) ⊆ set N
  normalClosure-least y N nrm = ⟪⟫-least y (set N , isSubgroup N , nrm)
```

The set HK of the products h k, h in H and k in K, is that library's
complex product `set H ∙ᶜ set K`.  It is a decidable subset: x is in HK
exactly when some h in H has h⁻¹ x in K, which a search of the
enumeration decides.  It is a subgroup only when H and K permute, so it
is given as a subset.

```agda
  infixl 7 _∙ᵈ_

  -- The set HK of products, as a decidable subset.
  _∙ᵈ_ : DecSubgroup 𝒢 ℓ → DecSubgroup 𝒢 ℓ′ → DecSubset setoid (α ⊔ ρ ⊔ ℓ ⊔ ℓ′)
  H ∙ᵈ K = record
    { set       = set H ∙ᶜ set K
    ; respects  = ∙ᶜ-respects (set H) (set K)
    ; decide    = λ x → map′ (to x) (from x) (any? (resp x) (λ h → (h ∈? H) ×? (h ⁻¹ ∙ x ∈? K)))
    }
    where
    module H = IsSubgroup (isSubgroup H)
    module K = IsSubgroup (isSubgroup K)
    to : ∀ x → ∃[ h ] (h ∈ set H × h ⁻¹ ∙ x ∈ set K) → x ∈ (set H ∙ᶜ set K)
    to x (h , h∈H , k∈K) = h , h ⁻¹ ∙ x , h∈H , k∈K , ≈sym (\\-leftDividesˡ h x)
    from : ∀ x → x ∈ (set H ∙ᶜ set K) → ∃[ h ] (h ∈ set H × h ⁻¹ ∙ x ∈ set K)
    from x (h , k , h∈H , k∈K , x≈hk) =
      h , h∈H , K.respects (≈sym (≈trans (∙-cong ≈refl x≈hk) (\\-leftDividesʳ h k))) k∈K
    resp : ∀ x → (λ h → h ∈ set H × h ⁻¹ ∙ x ∈ set K) Respects _≈_
    resp x h≈h′ (h∈H , k∈K) = H.respects h≈h′ h∈H , K.respects (∙-cong (⁻¹-cong h≈h′) ≈refl) k∈K
```
