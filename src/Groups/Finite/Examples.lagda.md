---
layout: default
file: "src/Groups/Finite/Examples.lagda.md"
title: "Groups.Finite.Examples module"
date: "2026-11-26"
author: "the agda-groups development team"
---

### Finite setoids and counting, evaluated

This is the `Groups.Finite.Examples` module of the agda-groups library.

It applies each public lemma of `Groups.Finite.Setoid`,
`Groups.Finite.Subset` and `Groups.Finite.Sum` to small finite setoids,
and checks by `refl` what the lemma states there: Agda computes both sides
of each equation while it checks the module, and a lemma that returns a
witness (a pair of colliding indices, a preimage, an element outside a
subset, a quotient) has the witness computed.  The setoids are `Fin 6`,
under propositional equality, and its quotient by congruence modulo 3,
the finite setoid Z₃ of its three classes, counted by their first
members 0, 1 and 2.  Each evaluation is a named definition, so that
`--profile=definitions` can report its time.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Finite.Examples where

-- Imports from the Agda Standard Library
open import Data.Bool.Base                         using ( Bool ; true ; false ; T )
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Base                          using ( Fin ; toℕ ; _↑ˡ_ )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F )
open import Data.Nat.Base                          using ( ℕ ; _%_ ; _<_ ; _≤_ ; _+_ ; _*_ ; _^_ ; _∸_ )
open import Data.Nat.Divisibility                  using ( _∣_ ; divides )
open import Data.Nat.Properties                    using ( n<1+n ; _<?_ ; ≤-refl ) renaming ( _≟_ to _≟ℕ_ )
import Data.Nat.Properties
open import Data.Product.Base                      using ( _,_ ; proj₁ ; proj₂ ; _×_ )
open import Data.Sum.Base                          using ( inj₂ )
open import Data.Unit.Base                         using ( ⊤ ; tt )
open import Data.Vec.Base                          using ( [] ; _∷_ ; lookup )
open import Function.Base                          using ( _∘_ )
open import Data.Vec.Functional                    using () renaming ( [] to []ᶠ ; _∷_ to _∷ᶠ_ )
open import Function.Bundles                       using ( Equivalence ; Inverse )
open import Function.Properties.Inverse            using ( Inverse⇒Bijection )
open import Level                                  using ( 0ℓ )
open import Relation.Binary.Bundles                using ( Setoid ; DecSetoid )
open import Relation.Binary.Definitions            using ( Decidable ; _Respects_ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong )
open import Relation.Nullary.Decidable             using ( Dec ; does ; _→?_ ; ¬? ; toWitness ; toWitnessFalse )
open import Relation.Nullary.Negation              using ( ¬_ )
open import Relation.Unary                         using ( _∈_ ; _⊆_ ; _≐_ )

import Data.Bool.Properties                        as Bool
import Data.Fin.Properties                         as Fin
import Data.Fin.Subset                             as Sub
import Data.Vec.Base                               as Vec
import Relation.Binary.PropositionalEquality       as ≡

open import Algebra.Properties.CommutativeMonoid.Sum Data.Nat.Properties.+-0-commutativeMonoid
                                                   using ( sum ; sum-syntax )

-- Imports from the Agda Universal Algebra Library
open import Classical.Signatures.Group             using ( Sig-Group )
open import Setoid.Algebras.Basic                  using ( 𝔻[_] )
open import Setoid.Algebras.Finite                 using ( FiniteAlgebra ; 𝟏 ; 𝟏-FiniteAlgebra )
open import Setoid.Algebras.Finite.Irredundant     using ( IrredundantEnumeration
                                                         ; irredundantEnumeration )

import Overture

-- Imports from this library
open import Groups.Finite.Setoid
open import Groups.Finite.Subset
open import Groups.Finite.Sum

open FiniteSetoid using ( size ; enum ; idx )
```
-->

#### The setoids

`Fin 6` under propositional equality, enumerated by the identity, and
congruence modulo 3 on it, a decidable equivalence coarser than
equality.  Its classes are Z₃.

```agda
-- Fin 6, enumerated by the identity.
F₆ : FiniteSetoid (≡.setoid (Fin 6))
F₆ = Finᶠ 6

-- Congruence modulo 3.
_≡₃_ : Fin 6 → Fin 6 → Set
i ≡₃ j = toℕ i % 3 ≡ toℕ j % 3

≡₃-equivalence : Overture.Equivalence (Fin 6) {0ℓ}
≡₃-equivalence = _≡₃_ , record { refl = refl ; sym = sym ; trans = trans }

_≡₃?_ : Decidable _≡₃_
i ≡₃? j = toℕ i % 3 ≟ℕ toℕ j % 3

module Mod3 = Partition F₆ ≡₃-equivalence _≡₃?_ (cong (λ i → toℕ i % 3))
open Mod3 using ( classSetoid ; classes ; class ; least⟨_⟩ ; least ; least-∼ ; least-cong ; first
                ; size-classes ; size≡∑∣class∣ ; size≡#classes*k )

-- Z₃: the classes of congruence modulo 3, counted by their first members.
Z₃ : FiniteSetoid classSetoid
Z₃ = classes
```

#### `Groups.Finite.Setoid`

The size, the enumeration and the index map of Z₃; decidable equality
and the searches; the passages; sizes under maps; and the pigeonhole
principle with its corollary.

```agda
-- Z₃ has three elements, its first members 0, 1 and 2.
size-Z₃ : size Z₃ ≡ 3
size-Z₃ = refl

enum-Z₃ : enum Z₃ 0F ≡ 0F × enum Z₃ 1F ≡ 1F × enum Z₃ 2F ≡ 2F
enum-Z₃ = refl , refl , refl

-- The index of 4 is the index of its class, that of 1.
idx-Z₃ : idx Z₃ 4F ≡ 1F × idx Z₃ 5F ≡ 2F
idx-Z₃ = refl , refl

-- Decidable equality: 1 and 4 are equal in Z₃, 1 and 5 are not.
≟-Z₃ : does (FiniteSetoid._≟_ Z₃ 1F 4F) ≡ true × does (FiniteSetoid._≟_ Z₃ 1F 5F) ≡ false
≟-Z₃ = refl , refl

-- The searches: some element is congruent to 5, found at 2; not every one is congruent to 0.
≡₃-resp : (j : Fin 6) → (_≡₃ j) Respects _≡₃_
≡₃-resp j {x} {y} x∼y x∼j = trans (sym x∼y) x∼j

any?-Z₃ : proj₁ (toWitness {a? = FiniteSetoid.any? Z₃ (λ {x} {y} → ≡₃-resp 5F {x} {y}) (λ x → x ≡₃? 5F)} tt) ≡ 2F
any?-Z₃ = refl

all?-Z₃ : does (FiniteSetoid.all? Z₃ (λ {x} {y} → ≡₃-resp 0F {x} {y}) (λ x → x ≡₃? 0F)) ≡ false
all?-Z₃ = refl

-- The bijection with Fin 3, as a finite structure, and carried to Fin 3.
fromInverse-Z₃ : size (fromInverse (FiniteSetoid.↔Fin Z₃)) ≡ 3 × enum (fromInverse (FiniteSetoid.↔Fin Z₃)) 2F ≡ 2F
fromInverse-Z₃ = refl , refl

transport-Z₃ : size (transport (FiniteSetoid.↔Fin Z₃) Z₃) ≡ 3 × idx (transport (FiniteSetoid.↔Fin Z₃) Z₃) 1F ≡ 1F
transport-Z₃ = refl , refl

-- The passages, on agda-algebras' one-element algebra of the signature of groups.
𝟏ᶠ : FiniteSetoid 𝔻[ 𝟏 {𝑆 = Sig-Group} ]
𝟏ᶠ = fromIrredundant (irredundantEnumeration (𝟏-FiniteAlgebra {𝑆 = Sig-Group}))

passages-𝟏 : size 𝟏ᶠ ≡ 1 × IrredundantEnumeration.icard (toIrredundant {𝑨 = 𝟏 {𝑆 = Sig-Group}} 𝟏ᶠ) ≡ 1
           × FiniteAlgebra.card (toFiniteAlgebra {𝑨 = 𝟏 {𝑆 = Sig-Group}} 𝟏ᶠ) ≡ 1
passages-𝟏 = refl , refl , refl

-- A one-to-one map from Z₃ into Fin 6, the least member of each class: 3 ≤ 6.
least-inj : ∀ {x y} → least x ≡ least y → x ≡₃ y
least-inj {x} {y} e = trans (sym (least-∼ x)) (trans (cong (λ i → toℕ i % 3) e) (least-∼ y))

injective⇒≤-Z₃ : size Z₃ ≤ size F₆
injective⇒≤-Z₃ = injective⇒≤ Z₃ F₆ least (λ {x} {y} → least-inj {x} {y})

-- Setoids in bijection have one size: Z₃ and Fin 3.
inverse⇒≡-Z₃ : size Z₃ ≡ size (Finᶠ 3)
inverse⇒≡-Z₃ = inverse⇒≡ Z₃ (Finᶠ 3) (FiniteSetoid.↔Fin Z₃)

size-unique-Z₃ : size Z₃ ≡ size (fromInverse (FiniteSetoid.↔Fin Z₃))
size-unique-Z₃ = size-unique Z₃ (fromInverse (FiniteSetoid.↔Fin Z₃))

-- The pigeonhole principle: 0, 1, 2, 3 into Z₃; 0 and 3 collide.
pigeonhole-Z₃ : proj₁ (pigeonhole Z₃ (n<1+n 3) (λ i → i ↑ˡ 2)) ≡ 0F
              × proj₁ (proj₂ (pigeonhole Z₃ (n<1+n 3) (λ i → i ↑ˡ 2))) ≡ 3F
pigeonhole-Z₃ = refl , refl

pigeonholeˢ-Z₃ : proj₁ (pigeonholeˢ F₆ Z₃ (toWitness {a? = 3 <? 6} tt) (λ i → i)) ≡ 0F
               × proj₁ (proj₂ (pigeonholeˢ F₆ Z₃ (toWitness {a? = 3 <? 6} tt) (λ i → i))) ≡ 3F
pigeonholeˢ-Z₃ = refl , refl
```

A one-to-one map from Z₃ to itself, x ↦ x + 1 within each half of
`Fin 6` (so 2 and 5 go to the class of 0), is onto: the preimage of the
class of 0 that the corollary finds is the first member 2.  Its
injectivity is decided over the 36 pairs.

```agda
-- x ↦ x + 1 modulo 3, on representatives.
σ : Fin 6 → Fin 6
σ 0F = 1F
σ 1F = 2F
σ 2F = 0F
σ 3F = 4F
σ 4F = 5F
σ 5F = 3F

σ-inj : ∀ {x y} → σ x ≡₃ σ y → x ≡₃ y
σ-inj {x} {y} = toWitness {a? = Fin.all? λ x → Fin.all? λ y → (σ x ≡₃? σ y) →? (x ≡₃? y)} tt x y

injective⇒onto-Z₃ : proj₁ (injective⇒onto Z₃ Z₃ refl σ (λ {x} {y} → σ-inj {x} {y}) 0F) ≡ 2F
injective⇒onto-Z₃ = refl
```

The laws of the index map at 1, 2, 4 and 5; the decidable setoid; the
size under a bijection; and the corollary for `Fin 3`, where the
rotation 0 ↦ 1 ↦ 2 ↦ 0 sends 2 to 0.

```agda
-- The element at the position of 4 is congruent to 4; 1 and 4 have one position.
enum-idx-Z₃ : enum Z₃ (idx Z₃ 4F) ≡₃ 4F
enum-idx-Z₃ = FiniteSetoid.enum-idx Z₃ 4F

idx-cong-Z₃ : idx Z₃ 1F ≡ idx Z₃ 4F
idx-cong-Z₃ = FiniteSetoid.idx-cong Z₃ {1F} {4F} refl

-- The position of the third element is 2; 2 and 5, of one position, are congruent.
idx-enum-Z₃ : idx Z₃ (enum Z₃ 2F) ≡ 2F
idx-enum-Z₃ = FiniteSetoid.idx-enum Z₃ 2F

idx-inj-Z₃ : 2F ≡₃ 5F
idx-inj-Z₃ = FiniteSetoid.idx-inj Z₃ {2F} {5F} refl

-- The decidable setoid decides 0 and 3 equal.
decSetoid-Z₃ : does (DecSetoid._≟_ (FiniteSetoid.decSetoid Z₃) 0F 3F) ≡ true
decSetoid-Z₃ = refl

-- Z₃ and Fin 3, through the bijection of the inverse pair.
bijection⇒≡-Z₃ : size Z₃ ≡ size (Finᶠ 3)
bijection⇒≡-Z₃ = bijection⇒≡ Z₃ (Finᶠ 3) (Inverse⇒Bijection (FiniteSetoid.↔Fin Z₃))

-- The rotation of Fin 3, one-to-one, is onto: 2 goes to 0.
rot : Fin 3 → Fin 3
rot 0F = 1F
rot 1F = 2F
rot 2F = 0F

rot-inj : ∀ {i j} → rot i ≡ rot j → i ≡ j
rot-inj {i} {j} = toWitness {a? = Fin.all? λ i → Fin.all? λ j → (rot i Fin.≟ rot j) →? (i Fin.≟ j)} tt i j

injective⇒onto-Fin-rot : proj₁ (injective⇒onto-Fin rot (λ {i} {j} → rot-inj {i} {j}) 0F) ≡ 2F
injective⇒onto-Fin-rot = refl
```

#### `Groups.Finite.Subset`

On `Fin 6`: the multiples of 3, {0, 3}, inside the indices below 4,
{0, 1, 2, 3}; their tables, sizes and complements; the decided
inclusions and the witness of the failed one; the size lemmas; the
multiples of 3 as a finite setoid; and a table read back as a subset.

```agda
open Counting F₆

-- The multiples of 3.
M₃ : DecSubset (≡.setoid (Fin 6)) 0ℓ
M₃ = record { set = λ i → toℕ i % 3 ≡ 0 ; respects = λ { refl m → m } ; decide = λ i → toℕ i % 3 ≟ℕ 0 }

-- The indices below 4.
B₄ : DecSubset (≡.setoid (Fin 6)) 0ℓ
B₄ = record { set = λ i → toℕ i < 4 ; respects = λ { refl b → b } ; decide = λ i → toℕ i <? 4 }

M₃⊆B₄ : set M₃ ⊆ set B₄
M₃⊆B₄ {i} = toWitness {a? = Fin.all? λ i → decide M₃ i →? decide B₄ i} tt i

-- Their tables and sizes.
table-M₃ : table M₃ ≡ true ∷ false ∷ false ∷ true ∷ false ∷ false ∷ []
table-M₃ = refl

sizes : ∣ M₃ ∣ ≡ 2 × ∣ B₄ ∣ ≡ 4 × ∣ ∁ M₃ ∣ ≡ 4 × ∣ full ∣ ≡ 6 × ∣ empty ∣ ≡ 0
sizes = refl , refl , refl , refl , refl

-- The decided inclusions, and the witness of the failed one, 1.
⊆?-M₃-B₄ : does (M₃ ⊆? B₄) ≡ true × does (B₄ ⊆? M₃) ≡ false × does (M₃ ≐? M₃) ≡ true
⊆?-M₃-B₄ = refl , refl , refl

B₄⊈M₃ = toWitnessFalse {a? = B₄ ⊆? M₃} tt

⊈⇒∃-B₄-M₃ : proj₁ (⊈⇒∃ B₄ M₃ B₄⊈M₃) ≡ 1F
⊈⇒∃-B₄-M₃ = refl

-- The size lemmas, instantiated: each states what the sizes above compute.
P⊆Q⇒∣P∣≤∣Q∣-M₃ : ∣ M₃ ∣ ≤ ∣ B₄ ∣
P⊆Q⇒∣P∣≤∣Q∣-M₃ = P⊆Q⇒∣P∣≤∣Q∣ M₃ B₄ M₃⊆B₄

P⊂Q⇒∣P∣<∣Q∣-M₃ : ∣ M₃ ∣ < ∣ B₄ ∣
P⊂Q⇒∣P∣<∣Q∣-M₃ = P⊂Q⇒∣P∣<∣Q∣ M₃ B₄ (M₃⊆B₄ , B₄⊈M₃)

P⊆Q∧x∈Q∖P⇒∣P∣<∣Q∣-M₃ : ∣ M₃ ∣ < ∣ B₄ ∣
P⊆Q∧x∈Q∖P⇒∣P∣<∣Q∣-M₃ = P⊆Q∧x∈Q∖P⇒∣P∣<∣Q∣ M₃ B₄ M₃⊆B₄ {1F} (toWitness {a? = 1 <? 4} tt) (λ ())

∣P∣+∣∁P∣≡n-M₃ : ∣ M₃ ∣ + ∣ ∁ M₃ ∣ ≡ 6
∣P∣+∣∁P∣≡n-M₃ = ∣P∣+∣∁P∣≡n M₃

-- The multiples of 3 again, as the i with 2i ≡ 0 modulo 6: one inclusion and the
-- sizes give the other.
M₃′ : DecSubset (≡.setoid (Fin 6)) 0ℓ
M₃′ = record { set = λ i → (2 * toℕ i) % 6 ≡ 0 ; respects = λ { refl m → m } ; decide = λ i → (2 * toℕ i) % 6 ≟ℕ 0 }

M₃⊆M₃′ : ∀ {i} → i ∈ set M₃ → i ∈ set M₃′
M₃⊆M₃′ {i} = toWitness {a? = Fin.all? λ i → decide M₃ i →? decide M₃′ i} tt i

P⊆Q∧∣P∣≡∣Q∣⇒P≐Q-M₃ : 3F ∈ set M₃′ → 3F ∈ set M₃
P⊆Q∧∣P∣≡∣Q∣⇒P≐Q-M₃ = proj₂ (P⊆Q∧∣P∣≡∣Q∣⇒P≐Q M₃ M₃′ (λ {i} → M₃⊆M₃′ {i}) refl) {3F}

-- A subset with six elements holds 5; a subset with two has a member, 0.
∅ᶜ : DecSubset (≡.setoid (Fin 6)) 0ℓ
∅ᶜ = ∁ empty

∣P∣≡n⇒∈P-5 : 5F ∈ set ∅ᶜ
∣P∣≡n⇒∈P-5 = ∣P∣≡n⇒∈P ∅ᶜ refl 5F

0<∣P∣⇒∃-M₃ : proj₁ (0<∣P∣⇒∃ M₃ (∈⇒0<∣P∣ M₃ {3F} refl)) ≡ 0F
0<∣P∣⇒∃-M₃ = refl

-- The multiples of 3 as a finite setoid: its second element is 3, at position 1.
finite-M₃ : size (finite M₃) ≡ 2 × proj₁ (enum (finite M₃) 1F) ≡ 3F × idx (finite M₃) (3F , refl) ≡ 1F
finite-M₃ = refl , refl , refl

-- A table read back as a subset, and the subset of a table.
table-fromTable-M₃ : table (fromTable (table M₃)) ≡ table M₃
table-fromTable-M₃ = refl

fromTable-table-M₃ : does (decide (fromTable (table M₃)) 3F) ≡ true × does (decide (fromTable (table M₃)) 4F) ≡ false
fromTable-table-M₃ = refl , refl
```

The remaining lemmas, each applied to these subsets: the entries of a
table, the two readings of membership in it, equal subsets and their
tables and sizes, the bounds, the inclusion of tables, the complement's
table and size, the stronger form of "same size contains", and the two
round trips.

```agda
-- An element of the subsetoid of the multiples of 3.
subsetoid-M₃ : Setoid.Carrier (subsetoid M₃)
subsetoid-M₃ = 3F , refl

-- The entry at 3 is the decision at 3, which holds.
lookup-table-M₃ : lookup (table M₃) 3F ≡ does (decide M₃ 3F)
lookup-table-M₃ = lookup-table M₃ 3F

-- Membership in the table and in the subset, both ways, at 3 and at 0.
T-table⇒∈-M₃ : 3F ∈ set M₃
T-table⇒∈-M₃ = T-table⇒∈ M₃ {3F} tt

∈⇒T-table-M₃ : T (lookup (table M₃) 3F)
∈⇒T-table-M₃ = ∈⇒T-table M₃ {3F} refl

∈table⇒∈-M₃ : 0F ∈ set M₃
∈table⇒∈-M₃ = ∈table⇒∈ M₃ {0F} (∈⇒∈table M₃ {0F} refl)

-- M₃ and M₃′ are equal, so their tables and sizes are.
M₃≐M₃′ : set M₃ ≐ set M₃′
M₃≐M₃′ = P⊆Q∧∣P∣≡∣Q∣⇒P≐Q M₃ M₃′ (λ {i} → M₃⊆M₃′ {i}) refl

table-cong-M₃ : table M₃ ≡ table M₃′
table-cong-M₃ = table-cong M₃ M₃′ M₃≐M₃′

P≐Q⇒∣P∣≡∣Q∣-M₃ : ∣ M₃ ∣ ≡ ∣ M₃′ ∣
P≐Q⇒∣P∣≡∣Q∣-M₃ = P≐Q⇒∣P∣≡∣Q∣ M₃ M₃′ M₃≐M₃′

-- The bounds: 4 ≤ 6, and the sizes of the whole and the empty subset.
∣P∣≤n-B₄ : ∣ B₄ ∣ ≤ 6
∣P∣≤n-B₄ = ∣P∣≤n B₄

∣full∣≡n-F₆ : ∣ full ∣ ≡ 6
∣full∣≡n-F₆ = ∣full∣≡n

∣empty∣≡0-F₆ : ∣ empty ∣ ≡ 0
∣empty∣≡0-F₆ = ∣empty∣≡0

-- The inclusion of the tables of M₃ and B₄.
table-mono-M₃ : table M₃ Sub.⊆ table B₄
table-mono-M₃ = table-mono M₃ B₄ (λ {i} → M₃⊆B₄ {i})

-- The complement's table, and its size 6 ∸ 2.
table-∁-M₃ : table (∁ M₃) ≡ Sub.∁ (table M₃) × table (∁ M₃) ≡ false ∷ true ∷ true ∷ false ∷ true ∷ true ∷ []
table-∁-M₃ = table-∁ M₃ , refl

∣∁P∣≡n∸∣P∣-M₃ : ∣ ∁ M₃ ∣ ≡ 6 ∸ ∣ M₃ ∣
∣∁P∣≡n∸∣P∣-M₃ = ∣∁P∣≡n∸∣P∣ M₃

-- M₃ inside M₃′, and M₃′ no larger: M₃′ lies in M₃.
P⊆Q∧∣Q∣≤∣P∣⇒Q⊆P-M₃ : 3F ∈ set M₃′ → 3F ∈ set M₃
P⊆Q∧∣Q∣≤∣P∣⇒Q⊆P-M₃ = P⊆Q∧∣Q∣≤∣P∣⇒Q⊆P M₃ M₃′ (λ {i} → M₃⊆M₃′ {i}) ≤-refl {3F}

-- The two round trips, applied.
table-fromTable-t : table (fromTable (table M₃)) ≡ table M₃
table-fromTable-t = table-fromTable (table M₃)

fromTable-table-3 : 3F ∈ set (fromTable (table M₃)) → 3F ∈ set M₃
fromTable-table-3 = proj₁ (fromTable-table M₃) {3F}
```

The respect of `≈` is needed for "a subset of a subset with the same size
contains it".  On `Bool` with `≈` total, enumerated by `true` alone, the
predicate "is `true`" does not respect `≈`, so it is not a `DecSubset`;
its decisions at the enumeration and those of the whole setoid have the
same size 1, yet `false` lies in the whole setoid and not in it.

```agda
-- Bool with every two elements equal, enumerated by true alone.
Bool⊤ : Setoid 0ℓ 0ℓ
Bool⊤ = record { Carrier = Bool ; _≈_ = λ _ _ → ⊤
               ; isEquivalence = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt } }

Bool⊤ᶠ : FiniteSetoid Bool⊤
Bool⊤ᶠ = record { size = 1 ; enum = λ _ → true ; enum-sur = λ _ → 0F , tt ; enum-inj = λ { {0F} {0F} _ → refl } }

-- "is true" does not respect ≈ ...
is-true-disrespects : ¬ ((_≡ true) Respects (Setoid._≈_ Bool⊤))
is-true-disrespects resp with resp {true} {false} tt refl
... | ()

-- ... and its decisions at the enumeration count 1, as the whole setoid's do.
respect-needed : Sub.∣ Vec.tabulate (λ i → does (enum Bool⊤ᶠ i Bool.≟ true)) ∣ ≡ Counting.∣_∣ Bool⊤ᶠ full
respect-needed = refl
```

#### `Groups.Finite.Sum`

The disjoint union and the product of `Fin 2` and Z₃, the functions from
`Fin 2` to Z₃, sizes as sums, the partition of `Fin 6` into the classes
modulo 3 (each of size 2) and into {0, 1, 2, 3} and {4, 5}, and a sum
modulo 3.

```agda
-- Fin 2 ⊎ Z₃: five elements; the fourth is the class of 1, and 5 sits at 4.
⊎ᶠ-2-Z₃ : size (Finᶠ 2 ⊎ᶠ Z₃) ≡ 5 × enum (Finᶠ 2 ⊎ᶠ Z₃) 3F ≡ inj₂ 1F × idx (Finᶠ 2 ⊎ᶠ Z₃) (inj₂ 5F) ≡ 4F
⊎ᶠ-2-Z₃ = refl , refl , refl

-- Fin 2 × Z₃: six elements; (1, 4) sits at 1·3 + 1 = 4, and 5 is (1, 2).
×ᶠ-2-Z₃ : size (Finᶠ 2 ×ᶠ Z₃) ≡ 6 × idx (Finᶠ 2 ×ᶠ Z₃) (1F , 4F) ≡ 4F × enum (Finᶠ 2 ×ᶠ Z₃) 5F ≡ (1F , 2F)
×ᶠ-2-Z₃ = refl , refl , refl

-- The functions from Fin 2 to Z₃: 3² = 9 of them; 0 ↦ 4, 1 ↦ 2 sits at 1·3 + 2 = 5.
^ᶠ-Z₃-2 : size (Z₃ ^ᶠ 2) ≡ 9 × idx (Z₃ ^ᶠ 2) (4F ∷ᶠ (2F ∷ᶠ []ᶠ)) ≡ 5F
^ᶠ-Z₃-2 = refl , refl

size-^ᶠ-Z₃-2 : size (Z₃ ^ᶠ 2) ≡ 3 ^ 2
size-^ᶠ-Z₃-2 = size-^ᶠ Z₃ 2

-- Sizes as sums.
∣P∣≡∑-M₃ : ∣ M₃ ∣ ≡ ∑[ i < 6 ] 𝟙 (does (decide M₃ i))
∣P∣≡∑-M₃ = ∣P∣≡∑ F₆ M₃

∑-unique-4 : ∑[ c < 3 ] 𝟙 (does (enum Z₃ c ≡₃? 4F)) ≡ 1
∑-unique-4 = refl

-- The partition modulo 3: three classes of two elements, and 6 = 2 + 2 + 2 = 3 · 2.
classes-mod-3 : ∣ class 0F ∣ ≡ 2 × ∣ class 4F ∣ ≡ 2 × ∑[ c < size Z₃ ] ∣ class (enum Z₃ c) ∣ ≡ 6
classes-mod-3 = refl , refl , refl

size≡∑∣class∣-mod-3 : size F₆ ≡ ∑[ c < size Z₃ ] ∣ class (enum Z₃ c) ∣
size≡∑∣class∣-mod-3 = size≡∑∣class∣ Z₃

every-class-2 : ∀ x → ∣ class x ∣ ≡ 2
every-class-2 = toWitness {a? = Fin.all? λ x → ∣ class x ∣ ≟ℕ 2} tt

size≡#classes*k-mod-3 : size F₆ ≡ size Z₃ * 2
size≡#classes*k-mod-3 = size≡#classes*k Z₃ every-class-2

-- A partition with classes of different sizes: below 4, and not.
_~₄_ : Fin 6 → Fin 6 → Set
i ~₄ j = does (toℕ i <? 4) ≡ does (toℕ j <? 4)

module Below4 = Partition F₆ (_~₄_ , record { refl = refl ; sym = sym ; trans = trans })
                              (λ i j → does (toℕ i <? 4) Bool.≟ does (toℕ j <? 4)) (cong (λ i → does (toℕ i <? 4)))

below-4 : size Below4.classes ≡ 2 × enum Below4.classes 0F ≡ 0F × enum Below4.classes 1F ≡ 4F
        × ∣ Below4.class 0F ∣ ≡ 4 × ∣ Below4.class 5F ∣ ≡ 2
below-4 = refl , refl , refl , refl , refl

size≡∑∣class∣-below-4 : size F₆ ≡ ∑[ c < size Below4.classes ] ∣ Below4.class (enum Below4.classes c) ∣
size≡∑∣class∣-below-4 = Below4.size≡∑∣class∣ Below4.classes

-- The classes modulo 3, enumerated with repetitions by Fin 6 itself: a finite setoid of size 3.
enumerable⇒finite-mod-3 : size (enumerable⇒finite {T = classSetoid} (λ i → i) (λ y → y , refl) _≡₃?_) ≡ 3
enumerable⇒finite-mod-3 = refl

-- A sum modulo 3: the terms 1, 3, 1, 6, 9, 1; those other than 1 are multiples of 3.
f₆ : Fin 6 → ℕ
f₆ 0F = 1
f₆ 1F = 3
f₆ 2F = 1
f₆ 3F = 6
f₆ 4F = 9
f₆ 5F = 1

One : Fin 6 → Set
One i = f₆ i ≡ 1

One? : ∀ i → Dec (One i)
One? i = f₆ i ≟ℕ 1

3∣f₆ : ∀ i → ¬ One i → 3 ∣ f₆ i
3∣f₆ 0F ¬o = ⊥-elim (¬o refl)
3∣f₆ 1F _  = divides 1 refl
3∣f₆ 2F ¬o = ⊥-elim (¬o refl)
3∣f₆ 3F _  = divides 2 refl
3∣f₆ 4F _  = divides 3 refl
3∣f₆ 5F ¬o = ⊥-elim (¬o refl)

-- The sum is 21, the sum of the ones 3, and 21 = 3 + 6 · 3.
sums-mod-3 : sum f₆ ≡ 21 × sumOn One? f₆ ≡ 3 × proj₁ (sum≡sumOn+q*p One? f₆ 3∣f₆) ≡ 6
           × sumOn One? (λ _ → 1) ≡ 3
sums-mod-3 = refl , refl , refl , refl

-- On the ones, f₆ agrees with 1.
sumOn-cong-f₆ : sumOn One? f₆ ≡ sumOn One? (λ _ → 1)
sumOn-cong-f₆ = sumOn-cong One? (λ _ o → o)

sum%p≡sumOn%p-f₆ : sum f₆ % 3 ≡ sumOn One? f₆ % 3
sum%p≡sumOn%p-f₆ = sum%p≡sumOn%p One? f₆ 3∣f₆

-- 3 divides 21, so 3 divides the sum of the ones, with quotient 1.
p∣sum⇔p∣sumOn-f₆ : _∣_.quotient (Equivalence.to (p∣sum⇔p∣sumOn One? f₆ 3∣f₆) (divides 7 refl)) ≡ 1
p∣sum⇔p∣sumOn-f₆ = refl
```

The remaining lemmas of `Groups.Finite.Sum`, applied: the bijection
behind the functions from `Fin (suc k)`, the sums behind the sizes, the
least index of a class and its congruence, the number of classes, and
the two steps of the sums modulo p.

```agda
-- A function from Fin 2 is its head and its tail.
∷-inverse-Z₃ : proj₁ (Inverse.from (∷-inverse {S = classSetoid} 1) (4F ∷ᶠ (2F ∷ᶠ []ᶠ))) ≡ 4F
             × Inverse.to (∷-inverse {S = classSetoid} 1) (4F , (2F ∷ᶠ []ᶠ)) 1F ≡ 2F
∷-inverse-Z₃ = refl , refl

-- The size of a table as a sum, a constant sum, and the indicator of 4.
∣tabulate∣≡∑-M₃ : Sub.∣ Vec.tabulate (λ i → does (decide M₃ i)) ∣ ≡ ∑[ i < 6 ] 𝟙 (does (decide M₃ i))
∣tabulate∣≡∑-M₃ = ∣tabulate∣≡∑ (λ i → does (decide M₃ i))

∑-const-6-2 : ∑[ i < 6 ] 2 ≡ 6 * 2 × ∑[ i < 6 ] 2 ≡ 12
∑-const-6-2 = ∑-const 6 2 , refl

∑-δ-4 : ∑[ i < 6 ] 𝟙 (does (i Fin.≟ 4F)) ≡ 1
∑-δ-4 = ∑-δ {6} 4F

-- Exactly one class of Z₃ holds 4.
∑-unique-Z₃ : ∑[ c < 3 ] 𝟙 (does (enum Z₃ c ≡₃? 4F)) ≡ 1
∑-unique-Z₃ = ∑-unique Z₃ 4F (λ c → enum Z₃ c ≡₃? 4F)

-- The least index in the class of 5 is 2, and 1 and 4 have the same.
least⟨⟩-5 : Fin.Least⟨_⟩.witness least⟨ 5F ⟩ ≡ 2F
least⟨⟩-5 = refl

least-cong-1-4 : least 1F ≡ least 4F × least 4F ≡ 1F
least-cong-1-4 = least-cong {1F} {4F} refl , refl

-- The number of classes is the number of first members.
size-classes-mod-3 : size classes ≡ Counting.∣_∣ (Finᶠ 6) first × Counting.∣_∣ (Finᶠ 6) first ≡ 3
size-classes-mod-3 = size-classes , refl

-- 3 divides a sum of six 3s, with quotient 6.
∣-sum-3s : _∣_.quotient (∣-sum {p = 3} (λ (_ : Fin 6) → 3) (λ _ → divides 1 refl)) ≡ 6
∣-sum-3s = refl

-- The sum of 1, 3, 1, 6, 9, 1 is the sum of its ones and of its other terms, 3 + 18; and the
-- number of ones is 3.
sum≡sumOn+sumOn∁-f₆ : sum f₆ ≡ sumOn One? f₆ + sumOn (¬? ∘ One?) f₆ × sumOn (¬? ∘ One?) f₆ ≡ 18
sum≡sumOn+sumOn∁-f₆ = sum≡sumOn+sumOn∁ One? f₆ , refl

sumOn-1-One : sumOn One? (λ _ → 1) ≡ Sub.∣ Vec.tabulate (λ i → does (One? i)) ∣
sumOn-1-One = sumOn-1 One?

-- 3 divides the terms other than the ones, 18, with quotient 6.
p∣sumOn∁-f₆ : _∣_.quotient (p∣sumOn∁ One? f₆ 3∣f₆) ≡ 6
p∣sumOn∁-f₆ = refl
```
