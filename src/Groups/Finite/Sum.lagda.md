---
layout: default
file: "src/Groups/Finite/Sum.lagda.md"
title: "Groups.Finite.Sum module"
date: "2026-11-26"
author: "the agda-groups development team"
---

### Sums, products and partitions of finite setoids

This is the `Groups.Finite.Sum` module of the agda-groups library.

It counts the finite setoids that later modules build: the disjoint union
and the product of two finite setoids, of sizes m + n and mn; the
functions from `Fin k` to a finite setoid of size n, under pointwise
equality, of size nᵏ (the p-tuples of Cauchy's theorem); and the classes
of a decidable equivalence relation.  The last is the step that
Lagrange's theorem, the orbit-stabilizer theorem and the class equation
share: the classes form a finite setoid, counted by their first members,
and the size of the setoid is the sum of the sizes of its classes, or k
times the number of classes when each has k elements.  It ends with sums
modulo p: a sum whose terms outside a decidable set of indices are each
divisible by p is congruent modulo p to the sum of the terms in the set,
the step of the count of fixed points.

The sums are agda-stdlib's sums over `Fin n`, from
`Algebra.Properties.CommutativeMonoid.Sum` on the natural numbers under
addition, with their lemmas (`∑-comm` exchanges two sums); the bijections
are agda-stdlib's `+↔⊎` and `*↔×`, unfolded into the enumerations.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Finite.Sum where

-- Imports from the Agda Standard Library
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Bool.Base                         using ( Bool ; true ; false ; not ; if_then_else_ )
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Base                          using ( Fin ; zero ; suc ; splitAt ; join
                                                         ; remQuot ; combine )
open import Data.Fin.Properties                    using ( splitAt-join ; join-splitAt
                                                         ; remQuot-combine ; combine-remQuot
                                                         ; search-least⟨_⟩ ; Least⟨_⟩ ; <-cmp )
                                                   renaming ( _≟_ to _≟ᶠ_ )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _+_ ; _*_ ; _^_ ; _%_
                                                         ; NonZero )
open import Data.Nat.Divisibility                  using ( _∣_ ; divides ; _∣0 ; ∣m∣n⇒∣m+n
                                                         ; ∣m+n∣m⇒∣n )
open import Data.Nat.DivMod                        using ( [m+kn]%n≡m%n )
open import Data.Nat.Properties                    using ( +-identityʳ ; *-identityʳ ; *-zeroʳ
                                                         ; +-0-commutativeMonoid ; +-comm )
open import Data.Product.Base                      using ( _,_ ; proj₁ ; proj₂ ; _×_ ; ∃-syntax )
                                                   renaming ( map to map× )
open import Data.Product.Relation.Binary.Pointwise.NonDependent using ( _×ₛ_ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
                                                   renaming ( map to map⊎ )
open import Data.Sum.Relation.Binary.Pointwise     using ( _⊎ₛ_ ; Pointwise ; inj₁ ; inj₂ )
open import Data.Vec.Functional                    using ( [] ; _∷_ ; head ; tail )
open import Function.Base                          using ( _∘_ ; id )
open import Function.Bundles                       using ( Inverse ; _⇔_ ; mk⇔ )
open import Level                                  using ( Level ; 0ℓ )
open import Relation.Binary.Bundles                using ( Setoid )
open import Relation.Binary.Definitions            using ( Decidable ; tri< ; tri≈ ; tri> )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong ; cong₂
                                                         ; subst )
open import Relation.Binary.Structures             using ( IsEquivalence )
open import Relation.Nullary.Decidable             using ( Dec ; yes ; no ; does ; ¬? )
open import Relation.Nullary.Negation              using ( ¬_ ; contradiction )
open import Relation.Unary                         using ( Pred )

import Data.Fin.Subset                             as Sub
import Data.Vec.Base                               as Vec
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as PW
import Relation.Binary.PropositionalEquality       as ≡
import Relation.Unary                              as U

open import Algebra.Properties.CommutativeMonoid.Sum +-0-commutativeMonoid
                                                   using ( sum ; sum-syntax ; sum-cong-≗ ; ∑-comm
                                                         ; ∑-distrib-+ )

-- Imports from the Agda Universal Algebra Library
open import Overture                               using ( Equivalence )
open import Setoid.Relations.Quotients             using ( _/_ )

-- Imports from this library
open import Groups.Finite.Setoid                   using ( FiniteSetoid ; Finᶠ ; transport )
open import Groups.Finite.Subset                   using ( DecSubset ; set ; respects ; decide
                                                         ; subsetoid ; module Counting )

private variable a b ℓ ℓ′ d : Level

open FiniteSetoid using ( size ; enum ; enum-sur ; enum-inj ; idx ; enum-idx ; idx-cong ; idx-enum
                        ; idx-inj )
```
-->

#### Disjoint unions and products

The disjoint union of finite setoids of sizes m and n is enumerated by
`Fin (m + n)`, through agda-stdlib's `splitAt` and `join` (the bijection
`+↔⊎`); the product, by `Fin (m * n)`, through `remQuot` and `combine`
(the bijection `*↔×`).  The sizes are m + n and m * n by definition.

```agda
module _ {S : Setoid a ℓ} {T : Setoid b ℓ′} where
  open Setoid S using () renaming ( Carrier to A ; _≈_ to _≈₁_ ; reflexive to reflexive₁
                                  ; trans to ≈trans₁ )
  open Setoid T using () renaming ( Carrier to B ; _≈_ to _≈₂_ ; reflexive to reflexive₂
                                  ; trans to ≈trans₂ )

  -- The disjoint union of two finite setoids: |S ⊎ T| = |S| + |T|.
  infixr 1 _⊎ᶠ_
  _⊎ᶠ_ : FiniteSetoid S → FiniteSetoid T → FiniteSetoid (S ⊎ₛ T)
  F ⊎ᶠ G = record
    { size      = m + n
    ; enum      = e
    ; enum-sur  = sur
    ; enum-inj  = λ {k} {k′} eq → trans (sym (join-splitAt m n k))
                                    (trans (cong (join m n) (map-inj (splitAt m k) (splitAt m k′) eq))
                                           (join-splitAt m n k′))
    }
    where
    m = size F
    n = size G
    e : Fin (m + n) → A ⊎ B
    e k = map⊎ (enum F) (enum G) (splitAt m k)
    sur : ∀ u → ∃[ k ] Pointwise _≈₁_ _≈₂_ (e k) u
    sur (inj₁ x) = join m n (inj₁ (idx F x))
                 , subst (λ s → Pointwise _≈₁_ _≈₂_ (map⊎ (enum F) (enum G) s) (inj₁ x))
                         (sym (splitAt-join m n (inj₁ (idx F x)))) (inj₁ (enum-idx F x))
    sur (inj₂ y) = join m n (inj₂ (idx G y))
                 , subst (λ s → Pointwise _≈₁_ _≈₂_ (map⊎ (enum F) (enum G) s) (inj₂ y))
                         (sym (splitAt-join m n (inj₂ (idx G y)))) (inj₂ (enum-idx G y))
    map-inj : ∀ s s′ → Pointwise _≈₁_ _≈₂_ (map⊎ (enum F) (enum G) s) (map⊎ (enum F) (enum G) s′) → s ≡ s′
    map-inj (inj₁ i) (inj₁ i′) (inj₁ eq) = cong inj₁ (enum-inj F eq)
    map-inj (inj₂ j) (inj₂ j′) (inj₂ eq) = cong inj₂ (enum-inj G eq)
    map-inj (inj₁ i) (inj₂ j′) ()
    map-inj (inj₂ j) (inj₁ i′) ()

  -- The product of two finite setoids: |S × T| = |S| |T|.
  infixr 2 _×ᶠ_
  _×ᶠ_ : FiniteSetoid S → FiniteSetoid T → FiniteSetoid (S ×ₛ T)
  F ×ᶠ G = record
    { size      = m * n
    ; enum      = e
    ; enum-sur  = λ (x , y) → combine {m} {n} (idx F x) (idx G y) , sur x y
    ; enum-inj  = λ {k} {k′} (eq₁ , eq₂) →
                    trans (sym (combine-remQuot {m} n k))
                          (trans (cong₂ combine (enum-inj F eq₁) (enum-inj G eq₂)) (combine-remQuot {m} n k′))
    }
    where
    m = size F
    n = size G
    e : Fin (m * n) → A × B
    e k = map× (enum F) (enum G) (remQuot {m} n k)
    sur : ∀ x y → (enum F (proj₁ (remQuot {m} n (combine {m} {n} (idx F x) (idx G y)))) ≈₁ x)
                × (enum G (proj₂ (remQuot {m} n (combine {m} {n} (idx F x) (idx G y)))) ≈₂ y)
    sur x y = ≈trans₁ (reflexive₁ (cong (enum F ∘ proj₁) rq)) (enum-idx F x)
            , ≈trans₂ (reflexive₂ (cong (enum G ∘ proj₂) rq)) (enum-idx G y)
      where
      rq = remQuot-combine {m} {n} (idx F x) (idx G y)
```

#### Functions from `Fin k`

The functions from `Fin k` to a setoid S, compared pointwise, form a
setoid (agda-stdlib's `Data.Vec.Functional`, whose vectors are such
functions).  For S finite of size n it is finite of size nᵏ: there is one
function from `Fin 0`, and a function from `Fin (suc k)` is its value at
`zero` together with a function from `Fin k` (`head` and `tail`, inverse
to `_∷_`), so the structure is the product's, carried along that
bijection.  The functions are compared pointwise, so no extensionality is
needed (agda-stdlib's `^↔→`, for propositional equality of functions,
takes it as a hypothesis).

```agda
module _ {S : Setoid a ℓ} where
  open Setoid S using ( Carrier ; _≈_ )

  -- A function from Fin (suc k) is its head and its tail.
  ∷-inverse : ∀ k → Inverse (S ×ₛ PW.setoid S k) (PW.setoid S (suc k))
  ∷-inverse k = record
    { to         = λ (x , v) → x ∷ v
    ; from       = λ w → head w , tail w
    ; to-cong    = λ (e , es) → λ { zero → e ; (suc i) → es i }
    ; from-cong  = λ es → es zero , es ∘ suc
    ; inverse    = (λ (e , es) → λ { zero → e ; (suc i) → es i }) , (λ es → es zero , es ∘ suc)
    }

  -- The functions from Fin k to a finite setoid: |Sᵏ| = |S|ᵏ.
  infixr 8 _^ᶠ_
  _^ᶠ_ : FiniteSetoid S → ∀ k → FiniteSetoid (PW.setoid S k)
  F ^ᶠ zero   = record
    { size = 1 ; enum = λ _ → [] ; enum-sur = λ _ → zero , λ () ; enum-inj = λ { {zero} {zero} _ → refl } }
  F ^ᶠ suc k  = transport (∷-inverse k) (F ×ᶠ (F ^ᶠ k))

  -- Its size is |S|ᵏ.
  size-^ᶠ : (F : FiniteSetoid S) → ∀ k → size (F ^ᶠ k) ≡ size F ^ k
  size-^ᶠ F zero     = refl
  size-^ᶠ F (suc k)  = cong (size F *_) (size-^ᶠ F k)
```

#### Sizes as sums

The size of a decidable subset is the sum, over the positions, of 1 where
the subset holds the element and 0 elsewhere.  The two sides are
recursions on n, agda-stdlib's `count`, by which `Data.Fin.Subset`
measures a table, and its `sum`, so their agreement is an induction on
the table.

```agda
-- 1 for true, 0 for false.
𝟙 : Bool → ℕ
𝟙 b = if b then 1 else 0

-- The size of a table is the sum of its entries.
∣tabulate∣≡∑ : ∀ {n} (t : Fin n → Bool) → Sub.∣ Vec.tabulate t ∣ ≡ ∑[ i < n ] 𝟙 (t i)
∣tabulate∣≡∑ {zero}  t = refl
∣tabulate∣≡∑ {suc n} t with t zero
... | true   = cong suc (∣tabulate∣≡∑ (t ∘ suc))
... | false  = ∣tabulate∣≡∑ (t ∘ suc)

-- A sum of a constant.
∑-const : ∀ n m → ∑[ i < n ] m ≡ n * m
∑-const zero     m = refl
∑-const (suc n)  m = cong (m +_) (∑-const n m)

-- The sum of the indicator of one index is 1.
∑-δ : ∀ {n} (j : Fin n) → ∑[ i < n ] 𝟙 (does (i ≟ᶠ j)) ≡ 1
∑-δ {suc n} zero     = cong suc (trans (∑-const n 0) (*-zeroʳ n))
∑-δ {suc n} (suc j)  = ∑-δ j

module _ {S : Setoid a ℓ} (F : FiniteSetoid S) where
  open Setoid S using ( Carrier ; _≈_ ; reflexive ) renaming ( trans to ≈trans )
  open Counting F using ( ∣_∣ )

  -- The size of P is the number of positions whose elements P holds.
  ∣P∣≡∑ : ∀ {p} (P : DecSubset S p) → ∣ P ∣ ≡ ∑[ i < size F ] 𝟙 (does (decide P (enum F i)))
  ∣P∣≡∑ P = ∣tabulate∣≡∑ (λ i → does (decide P (enum F i)))

  -- Each element is enumerated exactly once: the indicator of its positions sums to 1.
  ∑-unique : (y : Carrier) (d : ∀ i → Dec (enum F i ≈ y)) → ∑[ i < size F ] 𝟙 (does (d i)) ≡ 1
  ∑-unique y d = trans (sum-cong-≗ (λ i → cong 𝟙 (same i))) (∑-δ (idx F y))
    where
    same : ∀ i → does (d i) ≡ does (i ≟ᶠ idx F y)
    same i with d i | i ≟ᶠ idx F y
    ... | yes _  | yes _  = refl
    ... | no  _  | no  _  = refl
    ... | yes e  | no ne  = ⊥-elim (ne (trans (sym (idx-enum F i)) (idx-cong F e)))
    ... | no ne  | yes e  = ⊥-elim (ne (≈trans (reflexive (cong (enum F) e)) (enum-idx F y)))
```

#### Sums over a partition

A decidable equivalence relation ∼ on a finite setoid, coarser than `≈`
(x ≈ y gives x ∼ y, as agda-algebras' `≈⇒∼` gives it for the coset
relation), partitions it into classes.  Its classes form the setoid of
the same carrier under ∼ (agda-algebras' quotient `_/_`, of which its
coset space `cosetSetoid` is an instance), and the class of x is the
decidable subset of the y with x ∼ y.  The module `Partition` holds them,
with two theorems, as follows:

+  **the classes are a finite setoid**, counted by their first members:
   the indices i such that no smaller index j has `enum j ∼ enum i`.  The
   least index in the class of x is found by agda-stdlib's
   `search-least⟨_⟩`, the first members are the indices that are least in
   their classes (as a transversal of cosets chooses the first element of
   each), and they form a decidable subset of `Fin n`, enumerated as a
   finite setoid by `Groups.Finite.Subset`;
+  **the size of the setoid is the sum of the sizes of its classes**, for
   any finite structure on the classes, and k times the number of classes
   when every class has k elements.  Each element lies in exactly one
   class, so the sum of the class sizes counts each element once: the two
   sums of the indicator of "x is in the c-th class" agree (agda-stdlib's
   `∑-comm`).

```agda
module Partition {S : Setoid a ℓ} (F : FiniteSetoid S) (R : Equivalence (Setoid.Carrier S) {ℓ′})
                 (R? : Decidable (proj₁ R)) (≈⇒R : ∀ {x y} → Setoid._≈_ S x y → proj₁ R x y) where
  open Setoid S using ( Carrier ; _≈_ ) renaming ( sym to ≈sym )
  open IsEquivalence (proj₂ R) using () renaming ( refl to ∼refl ; sym to ∼sym ; trans to ∼trans )
  open Counting F using ( ∣_∣ )

  private
    _∼_ : Carrier → Carrier → Type ℓ′
    _∼_ = proj₁ R
    n = size F

  -- The setoid of the classes: the carrier of S under ∼.
  classSetoid : Setoid a ℓ′
  classSetoid = Carrier / R

  -- The class of x: the y with x ∼ y.
  class : Carrier → DecSubset S ℓ′
  class x = record
    { set       = x ∼_
    ; respects  = λ y≈z x∼y → ∼trans x∼y (≈⇒R y≈z)
    ; decide    = R? x
    }
```

The least index in the class of x, and its laws: it lies in the class, no
smaller index does, and two elements of one class have the same least
index.

```agda
  -- The least index in the class of x, found by a search from 0.
  least⟨_⟩ : (x : Carrier) → Least⟨ (λ j → enum F j ∼ x) ⟩
  least⟨ x ⟩ = [ (λ none → ⊥-elim (none (idx F x) (≈⇒R (enum-idx F x)))) , id ]′
               (search-least⟨ (λ j → R? (enum F j) x) ⟩)

  least : Carrier → Fin n
  least x = Least⟨_⟩.witness least⟨ x ⟩

  -- It lies in the class of x ...
  least-∼ : ∀ x → enum F (least x) ∼ x
  least-∼ x = Least⟨_⟩.example least⟨ x ⟩

  -- ... and elements of one class have the same least index.
  least-cong : ∀ {x y} → x ∼ y → least x ≡ least y
  least-cong {x} {y} x∼y with <-cmp (least x) (least y)
  ... | tri< lt _ _  = contradiction (∼trans (least-∼ x) x∼y) (Least⟨_⟩.minimal least⟨ y ⟩ lt)
  ... | tri≈ _ eq _  = eq
  ... | tri> _ _ gt  = contradiction (∼trans (least-∼ y) (∼sym x∼y)) (Least⟨_⟩.minimal least⟨ x ⟩ gt)
```

The first members, as a decidable subset of the positions, and the
classes enumerated by them.

```agda
  -- The first members: the indices least in their classes.
  first : DecSubset (≡.setoid (Fin n)) 0ℓ
  first = record
    { set       = λ i → least (enum F i) ≡ i
    ; respects  = λ { refl e → e }
    ; decide    = λ i → least (enum F i) ≟ᶠ i
    }

  private
    -- The first members, as a finite setoid.
    firsts : FiniteSetoid (subsetoid first)
    firsts = Counting.finite (Finᶠ n) first

    -- The least index of a class is a first member ...
    least-first : ∀ x → least (enum F (least x)) ≡ least x
    least-first x = least-cong (least-∼ x)

    -- ... and two first members of one class are equal.
    first-unique : ∀ {i j} → least (enum F i) ≡ i → least (enum F j) ≡ j → enum F i ∼ enum F j → i ≡ j
    first-unique fi fj e = trans (sym fi) (trans (least-cong e) fj)

  -- The classes, a finite setoid enumerated by their first members.
  classes : FiniteSetoid classSetoid
  classes = record
    { size      = size firsts
    ; enum      = λ c → enum F (proj₁ (enum firsts c))
    ; enum-sur  = λ x → idx firsts (least x , least-first x)
                      , subst (λ i → enum F i ∼ x) (sym (enum-idx firsts (least x , least-first x))) (least-∼ x)
    ; enum-inj  = λ {c} {c′} e → enum-inj firsts (first-unique (proj₂ (enum firsts c)) (proj₂ (enum firsts c′)) e)
    }

  -- The number of classes is the number of first members.
  size-classes : size classes ≡ Counting.∣_∣ (Finᶠ n) first
  size-classes = refl
```

The size of the setoid is the sum of the sizes of the classes, for any
finite structure C on the classes (the first members, or agda-algebras'
coset space with its own enumeration), and k times the number of classes
when every class has k elements.

```agda
  module _ (C : FiniteSetoid classSetoid) where

    -- The size of S is the sum of the sizes of its classes.
    size≡∑∣class∣ : size F ≡ ∑[ c < size C ] ∣ class (enum C c) ∣
    size≡∑∣class∣ = begin
      n                                                            ≡⟨ sym (trans (∑-const n 1) (*-identityʳ n)) ⟩
      ∑[ i < n ] 1                                                 ≡⟨ sum-cong-≗ (λ i → sym (one i)) ⟩
      ∑[ i < n ] ∑[ c < size C ] 𝟙 (does (R? (enum C c) (enum F i)))  ≡⟨ ∑-comm (λ i c → 𝟙 (does (R? (enum C c) (enum F i)))) ⟩
      ∑[ c < size C ] ∑[ i < n ] 𝟙 (does (R? (enum C c) (enum F i)))  ≡⟨ sum-cong-≗ (λ c → sym (∣P∣≡∑ F (class (enum C c)))) ⟩
      ∑[ c < size C ] ∣ class (enum C c) ∣                         ∎
      where
      open ≡.≡-Reasoning
      one : ∀ i → ∑[ c < size C ] 𝟙 (does (R? (enum C c) (enum F i))) ≡ 1
      one i = ∑-unique C (enum F i) (λ c → R? (enum C c) (enum F i))

    -- When every class has k elements, |S| = (the number of classes) k.
    size≡#classes*k : ∀ {k} → (∀ x → ∣ class x ∣ ≡ k) → size F ≡ size C * k
    size≡#classes*k {k} h = trans size≡∑∣class∣ (trans (sum-cong-≗ (λ c → h (enum C c))) (∑-const (size C) k))
```

A setoid is *finitely enumerable* when some map from `Fin m` reaches every
element up to `≈`, perhaps more than once.  Mines, Richman and Ruitenburg
note that a finitely enumerable set is discrete if and only if it is
finite (Chapter I, § 2), and leave one direction as an exercise ("Show
that a finitely enumerable discrete set is finite", § 2, Exercise 7).
Here it is a corollary of the partition: two indices are related when
they reach equal elements, a decidable equivalence on `Fin m` when `≈` is
decidable, and the map is a bijection from its classes onto the setoid.
So the setoid is finite, counted by the first index that reaches each
element.  This is how a setoid enumerated with repetitions (the
conjugates of a subgroup, by the elements of the group) becomes a finite
setoid, with an index map that searches the indices rather than
normalizing a proof.

```agda
module _ {T : Setoid b ℓ′} where
  open Setoid T using ( Carrier ; _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )

  -- A finitely enumerable discrete setoid is finite.
  enumerable⇒finite : ∀ {m} (f : Fin m → Carrier) → (∀ y → ∃[ i ] f i ≈ y) → Decidable _≈_ → FiniteSetoid T
  enumerable⇒finite {m} f sur _≟_ = transport I K.classes
    where
    R : Equivalence (Fin m) {ℓ′}
    R = (λ i j → f i ≈ f j) , record { refl = ≈refl ; sym = ≈sym ; trans = ≈trans }
    module K = Partition (Finᶠ m) R (λ i j → f i ≟ f j) (λ { refl → ≈refl })
    I : Inverse K.classSetoid T
    I = record
      { to         = f
      ; from       = λ y → proj₁ (sur y)
      ; to-cong    = λ e → e
      ; from-cong  = λ {y} {y′} e → ≈trans (proj₂ (sur y)) (≈trans e (≈sym (proj₂ (sur y′))))
      ; inverse    = (λ {y} e → ≈trans e (proj₂ (sur y))) , (λ {_} {y} e → ≈trans (proj₂ (sur y)) e)
      }
```

#### Sums modulo p

`sumOn D? f` is the sum of the terms of f at the indices in the decidable
set D.  A sum splits into the terms in D and the terms outside it; when
p divides each term outside D, p divides their sum, so the whole sum is
the sum over D plus a multiple of p, congruent to it modulo p, and p
divides the one exactly when it divides the other.  With f the sizes of
the orbits of a p-group acting on a finite set and D the orbits of size
1, it is the count of fixed points; and the sum over D of 1 is the number
of indices in D.

```agda
-- The sum of the terms of f at the indices in a decidable set D.
sumOn : ∀ {n} {D : Pred (Fin n) d} → U.Decidable D → (Fin n → ℕ) → ℕ
sumOn {n = n} D? f = ∑[ i < n ] (if does (D? i) then f i else 0)

-- p divides a sum whose terms it divides.
∣-sum : ∀ {p n} (g : Fin n → ℕ) → (∀ i → p ∣ g i) → p ∣ sum g
∣-sum {p} {zero}  g h = p ∣0
∣-sum {p} {suc n} g h = ∣m∣n⇒∣m+n (h zero) (∣-sum (g ∘ suc) (h ∘ suc))

module _ {n} {D : Pred (Fin n) d} (D? : U.Decidable D) where

  -- The sum over D of 1 is the number of indices in D.
  sumOn-1 : sumOn D? (λ _ → 1) ≡ Sub.∣ Vec.tabulate (λ i → does (D? i)) ∣
  sumOn-1 = sym (∣tabulate∣≡∑ (λ i → does (D? i)))

  -- Functions that agree on D have the same sum over D.
  sumOn-cong : {f g : Fin n → ℕ} → (∀ i → D i → f i ≡ g i) → sumOn D? f ≡ sumOn D? g
  sumOn-cong {f} {g} h = sum-cong-≗ guard
    where
    guard : ∀ i → (if does (D? i) then f i else 0) ≡ (if does (D? i) then g i else 0)
    guard i with D? i
    ... | yes di  = h i di
    ... | no  _   = refl

  -- A sum is the sum of its terms in D and of its terms outside D.
  sum≡sumOn+sumOn∁ : (f : Fin n → ℕ) → sum f ≡ sumOn D? f + sumOn (¬? ∘ D?) f
  sum≡sumOn+sumOn∁ f = trans (sum-cong-≗ (λ i → split (does (D? i)) (f i)))
                             (∑-distrib-+ (λ i → if does (D? i) then f i else 0)
                                          (λ i → if not (does (D? i)) then f i else 0))
    where
    split : ∀ b x → x ≡ (if b then x else 0) + (if not b then x else 0)
    split true   x = sym (+-identityʳ x)
    split false  x = refl

  module _ {p} (f : Fin n → ℕ) (p∣ : ∀ i → ¬ D i → p ∣ f i) where

    -- p divides the sum of the terms outside D.
    p∣sumOn∁ : p ∣ sumOn (¬? ∘ D?) f
    p∣sumOn∁ = ∣-sum _ guarded
      where
      guarded : ∀ i → p ∣ (if does (¬? (D? i)) then f i else 0)
      guarded i with D? i
      ... | yes _   = p ∣0
      ... | no  ¬d  = p∣ i ¬d

    -- Sums modulo p: the sum is the sum over D plus a multiple of p, ...
    sum≡sumOn+q*p : ∃[ q ] sum f ≡ sumOn D? f + q * p
    sum≡sumOn+q*p = _∣_.quotient p∣sumOn∁
                  , trans (sum≡sumOn+sumOn∁ f) (cong (sumOn D? f +_) (_∣_.equality p∣sumOn∁))

    -- ... so the two are congruent modulo p, ...
    sum%p≡sumOn%p : .{{_ : NonZero p}} → sum f % p ≡ sumOn D? f % p
    sum%p≡sumOn%p with sum≡sumOn+q*p
    ... | q , e = trans (cong (_% p) e) ([m+kn]%n≡m%n (sumOn D? f) q p)

    -- ... and p divides the one exactly when it divides the other.
    p∣sum⇔p∣sumOn : p ∣ sum f ⇔ p ∣ sumOn D? f
    p∣sum⇔p∣sumOn = mk⇔ to from
      where
      to : p ∣ sum f → p ∣ sumOn D? f
      to h = ∣m+n∣m⇒∣n (subst (p ∣_) (trans (sum≡sumOn+sumOn∁ f) (+-comm (sumOn D? f) _)) h) p∣sumOn∁
      from : p ∣ sumOn D? f → p ∣ sum f
      from h = subst (p ∣_) (sym (sum≡sumOn+sumOn∁ f)) (∣m∣n⇒∣m+n h p∣sumOn∁)
```
