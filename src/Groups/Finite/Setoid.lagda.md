---
layout: default
file: "src/Groups/Finite/Setoid.lagda.md"
title: "Groups.Finite.Setoid module"
date: "2026-11-26"
author: "the agda-groups development team"
---

### Finite setoids

This is the `Groups.Finite.Setoid` module of the agda-groups library.

A setoid is a type with an equivalence relation `_≈_` that plays the part of
equality.  In the vocabulary of Mines, Richman and Ruitenburg
(*A Course in Constructive Algebra*, Chapter I, § 2), a set is *discrete* when its
equality is decidable, and *finite* when it is discrete and in bijection with
`{1, ..., n}` for some `n`, its *cardinality*.  A **finite setoid** here is a
setoid with an *irredundant enumeration*: a size `n` and a map from `Fin n` that
reaches every element up to `≈` and no element twice.  That is the bijection with
`Fin n` the definition asks for, and the setoid is discrete, since `x ≈ y` exactly
when the positions of `x` and `y` are equal.

The record has the four fields of `IrredundantEnumeration`{.AgdaRecord}, for a
setoid that need not be the carrier of an algebra, and it is taken at any universe
level: the setoid of the subgroups of a group lies a universe above the group, and
it is counted too.  The module gives the index map and its laws, decidable equality,
the passage to and from that library's enumerations, the size's invariance under
bijections, and the pigeonhole principle in agda-stdlib's form, with its corollary
that a one-to-one map between finite setoids of the same size is onto.  Each
counting fact is agda-stdlib's fact about `Fin`, transported along the enumeration.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Finite.Setoid where

-- Imports from the Agda Standard Library
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Fin.Base                          using ( Fin ; suc ; _<_ ; punchOut )
open import Data.Nat.Base                          using ( ℕ ; suc ; _≤_ )
                                                   renaming ( _<_ to _<ℕ_ )
open import Data.Nat.Properties                    using ( ≤-antisym ; n<1+n )
open import Data.Product.Base                      using ( _,_ ; proj₁ ; proj₂ ; _×_
                                                         ; ∃ ; ∃-syntax ; ∃₂ )
open import Function.Base                          using ( _∘_ ; id )
open import Function.Bundles                       using ( Inverse ; Bijection )
open import Function.Definitions                   using ( Injective ; StrictlySurjective )
open import Function.Properties.Inverse            using ( Inverse⇒Bijection )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary.Bundles                using ( Setoid ; DecSetoid )
open import Relation.Binary.Definitions            using ( Decidable ; _Respects_ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong )
open import Relation.Nullary.Decidable             using ( Dec ; yes ; no ; map′ )
open import Relation.Nullary.Negation              using ( ¬_ ; contradiction )
open import Relation.Unary                         using ( Pred )

import Data.Fin.Properties                         as Fin
import Relation.Binary.PropositionalEquality       as ≡

-- Imports from the agda-algebras ---------------------------------------------------------
open import Overture                               using ( 𝓞 ; 𝓥 ; Signature )
open import Setoid.Algebras.Basic                  using ( Algebra ; 𝔻[_] )
open import Setoid.Algebras.Finite                 using ( FiniteAlgebra )
open import Setoid.Algebras.Finite.Irredundant     using ( IrredundantEnumeration )

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private variable a b ℓ ℓ′ p α ρ : Level
```
-->

#### The record

`FiniteSetoid S` is the structure of a finite setoid on the setoid `S`:
its size, its enumeration, and the two laws that make the enumeration a
bijection up to `≈`.  The *index map* `idx` sends an element to its
position, the index of the enumerated element it is equal to.

```agda
record FiniteSetoid (S : Setoid a ℓ) : Type (a ⊔ ℓ) where
  open Setoid S  using ( Carrier ; _≈_ ; reflexive )
                 renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open ≈-Reasoning S

  field
    size      : ℕ
    enum      : Fin size → Carrier
    enum-sur  : ∀ x → ∃[ i ] enum i ≈ x              -- every element is reached,
    enum-inj  : ∀ {i j} → enum i ≈ enum j → i ≡ j    -- and none twice

  -- The index map: the position of an element in the enumeration.
  idx : Carrier → Fin size
  idx x = enum-sur x .proj₁

  -- The element at the position of x is x.
  enum-idx : ∀ x → enum (idx x) ≈ x
  enum-idx x = enum-sur x .proj₂

  -- Equal elements have the same position.
  idx-cong : ∀ {x y} → x ≈ y → idx x ≡ idx y
  idx-cong {x} {y} x≈y = enum-inj (≈trans  (enum-idx x)
                                           (≈trans x≈y (≈sym (enum-idx y))))

  -- The position of the i-th element is i.
  idx-enum : ∀ i → idx (enum i) ≡ i
  idx-enum = enum-inj ∘ enum-idx ∘ enum

  -- Elements with the same position are equal.
  idx-inj : ∀ {x y} → idx x ≡ idx y → x ≈ y
  idx-inj {x} {y} eq = begin
    x             ≈⟨ enum-idx x ⟨
    enum (idx x)  ≈⟨ reflexive (cong enum eq) ⟩
    enum (idx y)  ≈⟨ enum-idx y ⟩
    y             ∎
```

The index map and the enumeration are inverse to each other, so the
setoid is in bijection with `Fin size`, and its equality is decidable,
read off the positions: the setoid is discrete.

```agda
  -- The bijection between the setoid and Fin size.
  ↔Fin : Inverse S (≡.setoid (Fin size))
  ↔Fin = record
    { to         = idx
    ; from       = enum
    ; to-cong    = idx-cong
    ; from-cong  = λ eq → reflexive (cong enum eq)
    ; inverse    = (λ y≈ei → trans (idx-cong y≈ei) (idx-enum _))
                   , λ { {x} refl → enum-idx x }
    }

  -- Equality is decidable: x ≈ y exactly when idx x ≡ idx y.
  infix 4 _≟_
  _≟_ : Decidable _≈_
  x ≟ y = map′ idx-inj idx-cong (idx x Fin.≟ idx y)

  -- The setoid with its decided equality.
  decSetoid : DecSetoid a ℓ
  decSetoid = record
    { isDecEquivalence = record
      { isEquivalence = Setoid.isEquivalence S ; _≟_ = _≟_ } }
```

A predicate that respects `≈` holds everywhere exactly when it holds at
every enumerated element, and somewhere exactly when it holds at one, so
both are decidable when the predicate is: agda-stdlib's `all?` and `any?`
for `Fin`, carried along the enumeration.

```agda
  -- A decidable predicate that respects ≈ is decided everywhere ...
  all? : {P : Pred Carrier p} → P Respects _≈_ → (∀ x → Dec (P x)) → Dec (∀ x → P x)
  all? resp P? = map′  (λ h x → resp (enum-idx x) (h (idx x))) (λ h i → h (enum i))
                       (Fin.all? (P? ∘ enum))

  -- ... and somewhere.
  any? : {P : Pred Carrier p} → P Respects _≈_ → (∀ x → Dec (P x)) → Dec (∃ P)
  any? resp P? = map′  (λ (i , pi) → enum i , pi)
                       (λ (x , px) → idx x , resp (≈sym (enum-idx x)) px)
                       (Fin.any? (P? ∘ enum))

open FiniteSetoid using  ( size ; enum ; enum-inj ; idx ; enum-idx
                         ; idx-cong ; idx-enum ; idx-inj )
```

#### Finite setoids from bijections

A bijection with `Fin n` makes a finite setoid of size n, and a finite
setoid carries its structure along a bijection to another setoid, with
the same size.  `Fin n` itself, under propositional equality, is a finite
setoid of size n, enumerated by the identity.

```agda
module _ {S : Setoid a ℓ} where
  open Setoid S using ( Carrier ; _≈_ ) renaming ( trans to ≈trans )

  -- A bijection with Fin n is a finite structure of size n.
  fromInverse : ∀ {n} → Inverse S (≡.setoid (Fin n)) → FiniteSetoid S
  fromInverse {n} I = record
    { size      = n
    ; enum      = from
    ; enum-sur  = λ x → to x , strictlyInverseʳ x
    ; enum-inj  =  λ {i} {j} e
                   → trans  (sym (strictlyInverseˡ i))
                            (trans (to-cong e) (strictlyInverseˡ j))
    }
    where open Inverse I

-- Fin n, enumerated by the identity.
Finᶠ : ∀ n → FiniteSetoid (≡.setoid (Fin n))
Finᶠ n = record
  { size      = n
  ; enum      = λ i → i
  ; enum-sur  = λ i → i , refl
  ; enum-inj  = λ e → e
  }

module _ {S : Setoid a ℓ} {T : Setoid b ℓ′} where
  open Setoid S using () renaming ( _≈_ to _≈₁_ ; trans to ≈trans₁ ; sym to ≈sym₁)
  open Setoid T using () renaming ( _≈_ to _≈₂_ ; trans to ≈trans₂ )

  -- A finite structure carried along a bijection, with the same size.
  transport : Inverse S T → FiniteSetoid S → FiniteSetoid T
  transport I F = record
    { size      = size F
    ; enum      = to ∘ enum F
    ; enum-sur  = λ y → idx F (from y) , ≈trans₂  (to-cong (enum-idx F (from y)))
                                                  (strictlyInverseˡ y)
    ; enum-inj  = λ e → enum-inj F (≈trans₁  (≈sym₁ (strictlyInverseʳ _))
                                             (≈trans₁  (from-cong e)
                                                       (strictlyInverseʳ _)))
    }
    where open Inverse I
```

#### The agda-algebras enumerations

An irredundant enumeration of the carrier of an algebra, in the sense of
the Agda Universal Algebra Library's `Setoid.Algebras.Finite.Irredundant`,
is a finite structure on its domain, field for field, and conversely; and
a finite structure gives that library's `FiniteAlgebra` witness, with the
derived decidable equality.  The library's finite groups carry the first
(ADR 0001, § 1), and the second feeds that library's finite group theory.

```agda
module _ {𝑆 : Signature 𝓞 𝓥} {𝑨 : Algebra {𝑆 = 𝑆} α ρ} where

  -- An irredundant enumeration of an algebra's carrier is a finite structure on its domain ...
  fromIrredundant : IrredundantEnumeration 𝑨 → FiniteSetoid 𝔻[ 𝑨 ]
  fromIrredundant I = record
    { size = icard ; enum = ienum[_] ; enum-sur = ienum-sur ; enum-inj = ienum-inj }
    where open IrredundantEnumeration I

  -- ... and conversely.
  toIrredundant : FiniteSetoid 𝔻[ 𝑨 ] → IrredundantEnumeration 𝑨
  toIrredundant F = record
    { icard = size F
    ; ienum[_] = enum F
    ; ienum-sur = FiniteSetoid.enum-sur F
    ; ienum-inj = enum-inj F }

  -- A finite structure gives agda-algebras' finiteness witness.
  toFiniteAlgebra : FiniteSetoid 𝔻[ 𝑨 ] → FiniteAlgebra 𝑨
  toFiniteAlgebra F = record
    { _≟_ = FiniteSetoid._≟_ F
    ; card = size F
    ; enum = enum F
    ; enum-sur = FiniteSetoid.enum-sur F }
```

#### Sizes under injections and bijections

A one-to-one map from a finite setoid S into a finite setoid T gives |S| ≤
|T|: its positions form a one-to-one map from `Fin |S|` into `Fin |T|`,
and agda-stdlib's `injective⇒≤` is that statement for `Fin`.  The map need
not respect `≈`.  A bijection, a map that respects `≈` and is one-to-one
and onto, gives one-to-one maps both ways, the map and a section of it, so
two setoids in bijection have the same size; in particular the size of a
finite setoid does not depend on its enumeration.

```agda
module _
  {S : Setoid a ℓ}
  {T : Setoid b ℓ′}
  (F : FiniteSetoid S)
  (G : FiniteSetoid T)
  where
  open Setoid S using () renaming ( Carrier to A ; _≈_ to _≈₁_ )
  open Setoid T using () renaming ( Carrier to B ; _≈_ to _≈₂_ )

  -- A one-to-one map from S into T: |S| ≤ |T|.
  injective⇒≤ : (f : A → B) → Injective _≈₁_ _≈₂_ f → size F ≤ size G
  injective⇒≤ f inj = Fin.injective⇒≤ (λ e → enum-inj F (inj (idx-inj G e)))

module _
  {S : Setoid a ℓ}
  {T : Setoid b ℓ′}
  (F : FiniteSetoid S)
  (G : FiniteSetoid T)
  where
  open Setoid S using () renaming ( sym to ≈sym₁ ; trans to ≈trans₁ ; _≈_ to _≈₁_ )
  open Setoid T using () renaming ( sym to ≈sym₂ ; trans to ≈trans₂ ; _≈_ to _≈₂_ )

  -- Setoids in bijection have the same size.
  bijection⇒≡ : Bijection S T → size F ≡ size G
  bijection⇒≡ β = ≤-antisym (injective⇒≤ F G to injective) (injective⇒≤ G F to⁻ to⁻-inj)
    where
    open Bijection β  using ( to ; injective ; to⁻ ; strictlySurjective )
                      renaming ( cong to to-cong )

    to⁻-inj : ∀ {x y} → (to⁻ x) ≈₁ (to⁻ y) → x ≈₂ y
    to⁻-inj {x} {y} e = ≈trans₂  (≈sym₂ (strictlySurjective x .proj₂))
                                 (≈trans₂ (to-cong e) (strictlySurjective y .proj₂))

  -- In particular, setoids related by an inverse pair have the same size.
  inverse⇒≡ : Inverse S T → size F ≡ size G
  inverse⇒≡ I = bijection⇒≡ (Inverse⇒Bijection I)

-- The size of a finite setoid does not depend on its enumeration.
size-unique : {S : Setoid a ℓ} (F G : FiniteSetoid S) → size F ≡ size G
size-unique F G = ≤-antisym  (injective⇒≤ F G id id) (injective⇒≤ G F id id)
```

#### The pigeonhole principle

The principle for `Fin` is agda-stdlib's `pigeonhole`: a map from `Fin m`
into `Fin n` with n < m sends two indices i < j to the same place.
Transported along the enumeration of T, it holds for maps from `Fin m`
into a finite setoid T of size n < m.  With m = n + 1 it says that T *has
at most n elements* in the sense of Mines, Richman and Ruitenburg (Chapter
I, § 2): among any a₀, ..., aₙ in T there are i < j with aᵢ ≈ aⱼ.  That is
the form that bounds the order of an element and the closing of a
generated subgroup.  For a map between finite setoids, with |T| < |S|, it
gives two distinct elements with equal images.

```agda
module _ {T : Setoid b ℓ′} (G : FiniteSetoid T) where
  open Setoid T using ( Carrier ; _≈_ )

  -- The pigeonhole principle, for a map from Fin m with |T| < m.
  pigeonhole : ∀ {m} → size G <ℕ m → (f : Fin m → Carrier)
    → ∃[ i ] ∃[ j ] i < j × f i ≈ f j
  pigeonhole lt f with Fin.pigeonhole lt (idx G ∘ f)
  ... | i , j , i<j , e = i , j , i<j , idx-inj G e

module _
  {S : Setoid a ℓ}
  {T : Setoid b ℓ′}
  (F : FiniteSetoid S)
  (G : FiniteSetoid T) where
  open Setoid S using () renaming ( Carrier to A ; _≈_ to _≈₁_ )
  open Setoid T using () renaming ( Carrier to B ; _≈_ to _≈₂_ )

  -- The pigeonhole principle, for a map between finite setoids with |T| < |S|.
  pigeonholeˢ : size G <ℕ size F → (f : A → B) → ∃[ x ] ∃[ y ] ¬ (x ≈₁ y) × f x ≈₂ f y
  pigeonholeˢ lt f with pigeonhole G lt (f ∘ enum F)
  ... | i , j , i<j , e = enum F i , enum F j , (λ eq → Fin.<-irrefl (enum-inj F eq) i<j) , e
```

Its corollary: a one-to-one map from a finite setoid into one of the same
size is onto.  agda-stdlib 2.4.1 has no such lemma for `Fin`, so it is
proved there first, from `pigeonhole`: if a one-to-one map of `Fin (suc
n)` into itself missed some j, then removing j from its codomain
(agda-stdlib's `punchOut`) would map `Fin (suc n)` one-to-one into `Fin
n`.

```agda
private
  -- A map of Fin (suc n) into itself that misses j has two indices with one image.
  collision : ∀ {n} (g : Fin (suc n) → Fin (suc n)) (j : Fin (suc n))
    → (∀ i → ¬ (g i ≡ j)) → ∃[ i ] ∃[ i′ ] i < i′ × g i ≡ g i′
  collision {n} g j miss with Fin.pigeonhole (n<1+n n) (λ i → punchOut (miss i ∘ sym))
  ... | i , i′ , i<i′ , e = i , i′ , i<i′ ,
        Fin.punchOut-injective (miss i ∘ sym) (miss i′ ∘ sym) e

-- A one-to-one map from Fin n into itself is onto.
injective⇒onto-Fin : ∀ {n} (g : Fin n → Fin n)
  → Injective _≡_ _≡_ g → ∀ j → ∃[ i ] g i ≡ j
injective⇒onto-Fin {suc n} g inj j with Fin.any? (λ i → g i Fin.≟ j)
... | yes found = found
... | no  none  with collision g j (λ i e → none (i , e))
...   | i , i′ , i<i′ , e = contradiction (inj e) (Fin.<⇒≢ i<i′)

private
  -- The same, for a map between Fin m and Fin n with m ≡ n.
  injective⇒onto-Fin′ : ∀ {m n} → m ≡ n → (g : Fin m → Fin n)
    → Injective _≡_ _≡_ g → ∀ j → ∃[ i ] g i ≡ j
  injective⇒onto-Fin′ refl = injective⇒onto-Fin

module _
  {S : Setoid a ℓ}
  {T : Setoid b ℓ′}
  (F : FiniteSetoid S)
  (G : FiniteSetoid T)
  where
  open Setoid S using () renaming ( Carrier to A ; _≈_ to _≈₁_ )
  open Setoid T using () renaming ( Carrier to B ; _≈_ to _≈₂_ )

  -- A one-to-one map between finite setoids of the same size is onto.
  injective⇒onto : size F ≡ size G → (f : A → B)
    → Injective _≈₁_ _≈₂_ f → StrictlySurjective _≈₂_ f
  injective⇒onto eq f inj y with injective⇒onto-Fin′ eq (idx G ∘ f ∘ enum F)
                                   (λ e → enum-inj F (inj (idx-inj G e))) (idx G y)
  ... | i , e = enum F i , idx-inj G e
```
