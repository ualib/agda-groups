---
layout: default
file: "src/Groups/Symmetric.lagda.md"
title: "Groups.Symmetric module"
date: "2026-11-27"
author: "the agda-groups development team"
---

### The symmetric groups Sym(n)

This is the `Groups.Symmetric` module of the agda-groups library.

The **symmetric group** Sym(X) on a set X is the group of all
permutations of X under composition, and when X has n elements it has
order n! (Aschbacher, § 15).  Here X is `Fin n`, and a permutation σ is
stored as two vectors, the images σ(0), ..., σ(n − 1) and the images of
σ⁻¹, with the two proofs that they compose to the identity, so that two
permutations are compared by comparing vectors, a decided equality.  Two
permutations are equal when their vectors of images are.  The product
στ is the composite σ ∘ τ, which applies τ first: the Agda Universal
Algebra Library's `_⨁_` on the vectors of images, with its `⨁-assoc`.
(Aschbacher, § 5, writes permutations on the right, x(αβ) = (xα)β, so
that his product applies α first.)

Sym(n) is a finite group of order n!, enumerated by a **factorial
numbering**: a permutation σ of `Fin (n + 1)` is the image σ(0), one of
n + 1 points, together with the permutation of `Fin n` that σ induces on
the other points, agda-stdlib's `remove 0 σ`; and conversely agda-stdlib's
`insert 0 j π` sends 0 to j and acts as π elsewhere.  So the index of σ
is the digit σ(0) followed by the index of `remove 0 σ`, read in
agda-stdlib's `combine`, a bijection of `Fin (n + 1) × Fin n!` with `Fin
(n + 1)!`.  The index map computes σ's digits from its vector of images
and normalizes no proof, as ADR 0001, § 1, asks; the enumeration is its
inverse, which builds the vectors of images by `insert`.  Measured, the
permutation at an index and the index of a permutation take about 0.5
ms together in Sym(5), and 1.9 ms in Sym(6) (`Groups.Symmetric.Examples`
and the findings of issue 8).

A **group of permutations** of `Fin n` is a subgroup of Sym(n); given by
generators, as GAP gives one, it is `⟨ 𝔸 ⟩` for a record `𝔸 =
mkGenerators A _` of `Groups.Subgroup.Generated`'s `Generated (Sym n)`,
whose Schreier vector is indexed by this numbering.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Symmetric where

open import Agda.Primitive using () renaming ( Set to Type )

-- Imports from agda-stdlib ----------------------------------------------------
open import Data.Fin.Base                using  ( Fin ; zero ; suc ; combine
                                                ; remQuot ; punchIn ; punchOut )
open import Data.Fin.Permutation         using  ( Permutation′ ; permutation
                                                ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; inverseʳ
                                                ; inverseˡ ; insert ; remove
                                                ; insert-remove ; remove-insert
                                                ; transpose )
                                         renaming ( id to idᵖ ; _≈_ to _≈ᵖ_ )
open import Data.Fin.Properties          using  ( punchOut-cong ; any?
                                                ; combine-remQuot
                                                ; remQuot-combine )
                                         renaming ( _≟_ to _≟ᶠ_ )
open import Data.Nat.Base                using  ( ℕ ; zero ; suc ; _! )
open import Data.Product.Base            using  ( _,_ ; proj₁ ; proj₂ ; map₂
                                                ; uncurry )
open import Data.Vec.Base                using  ( Vec ; lookup ; tabulate )
open import Data.Vec.Properties          using  ( lookup∘tabulate ; ≡-dec
                                                ; tabulate∘lookup
                                                ; tabulate-cong )
open import Function.Base                using  ( id ; _∘_ )
open import Function.Bundles             using  ( Inverse )
open import Level                        using  ( 0ℓ )
open import Relation.Binary.Bundles      using  ( Setoid )
open import Relation.Binary.Definitions  using  ( Decidable )
open import Relation.Binary.PropositionalEquality
                                         using  ( _≡_ ; _≢_ ; refl ; sym ; trans
                                                ; cong ; cong₂
                                                ; module ≡-Reasoning )
                                         renaming ( setoid to ≡-setoid )
open import Relation.Nullary.Decidable   using  ( yes ; no )

import Relation.Binary.Construct.On as On

-- Imports from agda-algebras ----------------------------------------------------
open import Classical.Structures.Group  using  ( Group ; setoidEqsToGroup
                                               ; _⨁_ ; ⨁-assoc )

-- Imports from agda-groups ------------------------------------------------------
open import Groups.Finite.Group   using  ( FiniteGroup )
open import Groups.Finite.Setoid  using  ( FiniteSetoid ; fromInverse
                                         ; toIrredundant )

open ≡-Reasoning using ( begin_ ; step-≡-⟩ ; step-≡-⟨ ; _∎ )
```
-->

#### Vectors of images

The identity permutation's vector is `ι`, the points in order; it is a
two-sided identity for `_⨁_`.  A vector u with a vector v such that u ⨁
v and v ⨁ u are `ι` is a permutation, and two such products cancel.

```agda
module _ {n : ℕ} where

  -- The identity vector: the points of Fin n in order.
  ι : Vec (Fin n) n
  ι = tabulate id

  -- It is an identity on the left ...
  ⨁-identityˡ : (u : Vec (Fin n) n) → ι ⨁ u ≡ u
  ⨁-identityˡ u =
    trans  (tabulate-cong (λ p → lookup∘tabulate id (lookup u p)))
           (tabulate∘lookup u)

  -- ... and on the right.
  ⨁-identityʳ : (u : Vec (Fin n) n) → u ⨁ ι ≡ u
  ⨁-identityʳ u =
    trans  (tabulate-cong (λ p → cong (lookup u) (lookup∘tabulate id p)))
           (tabulate∘lookup u)

  -- When u ⨁ v is ι, it cancels between two vectors.
  ⨁-cancel : (u v w x : Vec (Fin n) n) → u ⨁ v ≡ ι
    → (w ⨁ u) ⨁ (v ⨁ x) ≡ w ⨁ x
  ⨁-cancel u v w x uv =
    trans  (⨁-assoc w u (v ⨁ x))
           (cong  (w ⨁_)
                  (trans  (sym (⨁-assoc u v x))
                          (trans (cong (_⨁ x) uv) (⨁-identityˡ x))))
```

#### Permutations

A permutation of `Fin n` is a vector of images with a vector of images
of its inverse.  Two permutations are equal, `_≈_`, when their vectors of
images are: the vector of the inverse is then equal too (`⁻¹-cong`
below), so nothing is lost, and the equality is decided by comparing n
points.

```agda
-- A permutation of Fin n, by its images and the images of its inverse.
record Perm (n : ℕ) : Type where
  constructor perm
  field
    images            : Vec (Fin n) n
    preimages         : Vec (Fin n) n
    images-preimages  : images ⨁ preimages ≡ ι
    preimages-images  : preimages ⨁ images ≡ ι

open Perm public

module _ {n : ℕ} where

  -- The image of a point.
  _⟨$⟩_ : Perm n → Fin n → Fin n
  σ ⟨$⟩ i = lookup (images σ) i

  -- The setoid of permutations: equal when their images are.
  setoid : Setoid 0ℓ 0ℓ
  setoid = On.setoid (≡-setoid (Vec (Fin n) n)) (images {n})

  open Setoid setoid public using ( _≈_ )

  infix 4 _≟_

  -- Equality of permutations, decided by comparing their images.
  _≟_ : Decidable _≈_
  σ ≟ τ = ≡-dec _≟ᶠ_ (images σ) (images τ)
```

The product applies its right factor first, the identity is `ι`, and the
inverse exchanges the two vectors.

```agda
  infixl 7 _∘ₚ_
  infix  8 _⁻¹

  -- The product στ: first τ, then σ.
  _∘ₚ_ : Perm n → Perm n → Perm n
  σ ∘ₚ τ = perm (images σ ⨁ images τ) (preimages τ ⨁ preimages σ)
    (trans  (⨁-cancel  (images τ) (preimages τ) (images σ) (preimages σ)
                       (images-preimages τ))
            (images-preimages σ))
    (trans  (⨁-cancel  (preimages σ) (images σ) (preimages τ) (images τ)
                       (preimages-images σ))
            (preimages-images τ))

  -- The identity permutation.
  idₚ : Perm n
  idₚ = perm ι ι (⨁-identityˡ ι) (⨁-identityˡ ι)

  -- The inverse permutation.
  _⁻¹ : Perm n → Perm n
  σ ⁻¹ = perm  (preimages σ) (images σ)
               (preimages-images σ) (images-preimages σ)

  -- Equal permutations have equal inverses.
  ⁻¹-cong : (σ τ : Perm n) → σ ≈ τ → σ ⁻¹ ≈ τ ⁻¹
  ⁻¹-cong σ τ σ≈τ = begin
    s′                    ≡⟨ ⨁-identityʳ s′ ⟨
    s′ ⨁ ι                ≡⟨ cong (s′ ⨁_) (images-preimages τ) ⟨
    s′ ⨁ (t ⨁ t′)         ≡⟨ ⨁-assoc s′ t t′ ⟨
    (s′ ⨁ t) ⨁ t′         ≡⟨ cong (λ u → (s′ ⨁ u) ⨁ t′) σ≈τ ⟨
    (s′ ⨁ images σ) ⨁ t′  ≡⟨ cong (_⨁ t′) (preimages-images σ) ⟩
    ι ⨁ t′                ≡⟨ ⨁-identityˡ t′ ⟩
    t′                    ∎
    where
    s′ = preimages σ
    t  = images τ
    t′ = preimages τ
```

#### The group Sym(n)

The group laws hold of the vectors of images: associativity is
`⨁-assoc`, the identity laws are those of `ι`, and the inverse laws are
the two proofs each permutation carries.

```agda
-- The symmetric group on Fin n.
symGroup : (n : ℕ) → Group 0ℓ 0ℓ
symGroup n = setoidEqsToGroup (setoid {n}) _∘ₚ_ idₚ _⁻¹
  (cong₂ _⨁_)
  (λ {σ} {τ} → ⁻¹-cong σ τ)
  (λ σ τ ρ → ⨁-assoc (images σ) (images τ) (images ρ))
  (⨁-identityˡ ∘ images)
  (⨁-identityʳ ∘ images)
  preimages-images
  images-preimages
```

#### Permutations from agda-stdlib's, and back

agda-stdlib's `Permutation′ n` (`Data.Fin.Permutation`) is a bijection
of `Fin n` given by two functions.  `tabulateₚ` stores its images in
vectors, and `lookupₚ` reads them back; each undoes the other, up to the
equality of each.

```agda
module _ {n : ℕ} where

  -- An agda-stdlib permutation, stored as vectors of images.
  tabulateₚ : Permutation′ n → Perm n
  tabulateₚ π = perm (tabulate (π ⟨$⟩ʳ_)) (tabulate (π ⟨$⟩ˡ_))
    (tabulate-cong λ i →
      trans  (lookup∘tabulate (π ⟨$⟩ʳ_) _)
             (trans  (cong (π ⟨$⟩ʳ_) (lookup∘tabulate (π ⟨$⟩ˡ_) i))
                     (inverseʳ π)))
    (tabulate-cong λ i →
      trans  (lookup∘tabulate (π ⟨$⟩ˡ_) _)
             (trans  (cong (π ⟨$⟩ˡ_) (lookup∘tabulate (π ⟨$⟩ʳ_) i))
                     (inverseˡ π)))

  -- Read off a product of vectors at a point.
  private
    at : (u v : Vec (Fin n) n) → u ⨁ v ≡ ι → ∀ i → lookup u (lookup v i) ≡ i
    at u v uv i =
      trans  (sym (lookup∘tabulate (λ p → lookup u (lookup v p)) i))
             (trans (cong (λ w → lookup w i) uv) (lookup∘tabulate id i))

  -- A permutation, as an agda-stdlib permutation.
  lookupₚ : Perm n → Permutation′ n
  lookupₚ σ = permutation  (lookup (images σ))
                           (lookup (preimages σ))
                           (at (images σ) (preimages σ) (images-preimages σ))
                           (at (preimages σ) (images σ) (preimages-images σ))

  -- Reading back a stored permutation gives it again ...
  lookupₚ-tabulateₚ : (π : Permutation′ n) → lookupₚ (tabulateₚ π) ≈ᵖ π
  lookupₚ-tabulateₚ π i = lookup∘tabulate (π ⟨$⟩ʳ_) i

  -- ... and storing a permutation read back gives it again.
  tabulateₚ-lookupₚ : (σ : Perm n) → tabulateₚ (lookupₚ σ) ≈ σ
  tabulateₚ-lookupₚ σ = tabulate∘lookup (images σ)

  -- Storing respects the equalities ...
  tabulateₚ-cong : (π ρ : Permutation′ n) → π ≈ᵖ ρ → tabulateₚ π ≈ tabulateₚ ρ
  tabulateₚ-cong _ _ = tabulate-cong

  -- ... and so does reading back.
  lookupₚ-cong : (σ τ : Perm n) → σ ≈ τ → lookupₚ σ ≈ᵖ lookupₚ τ
  lookupₚ-cong _ _ σ≈τ i = cong (λ u → lookup u i) σ≈τ

  -- The transposition of two points.
  transposition : Fin n → Fin n → Perm n
  transposition i j = tabulateₚ (transpose i j)
```

A permutation given by its vector of images alone has the vector of its
inverse found by a search: at the point i, the first j with σ(j) = i.
For a concrete vector the two proofs are `refl`, which Agda checks by
evaluation.

```agda
  -- The first point that a vector sends to i, or i if there is none.
  preimage : Vec (Fin n) n → Fin n → Fin n
  preimage v i with any? (λ j → lookup v j ≟ᶠ i)
  ... | yes (j , _)  = j
  ... | no _         = i

  -- A permutation from its vector of images, with the two proofs,
  -- refl for a concrete vector.
  fromImages : (v : Vec (Fin n) n) → v ⨁ tabulate (preimage v) ≡ ι
    → tabulate (preimage v) ⨁ v ≡ ι → Perm n
  fromImages v = perm v (tabulate (preimage v))
```

#### The factorial numbering

The index of an agda-stdlib permutation π of `Fin (n + 1)` combines the
image π(0) with the index of `remove 0 π`; the permutation at an index
inserts its first digit at 0 into the permutation at the rest.  Both
respect the equality of agda-stdlib's permutations, since `remove 0`
does, and the two are inverse to each other, by agda-stdlib's
`remove-insert`, `insert-remove`, `remQuot-combine` and
`combine-remQuot`.

```agda
-- punchOut respects equality in both of its points.
punchOut-cong₂ : ∀ {n} {i i′ j j′ : Fin (suc n)} {p : i ≢ j} {q : i′ ≢ j′}
  → i ≡ i′ → j ≡ j′ → punchOut p ≡ punchOut q
punchOut-cong₂ {i = i} refl refl = punchOut-cong i refl

-- remove 0 respects equality.
remove-cong : ∀ {n} (π ρ : Permutation′ (suc n))
  → π ≈ᵖ ρ → remove zero π ≈ᵖ remove zero ρ
remove-cong _ _ π≈ρ j = punchOut-cong₂ (π≈ρ zero) (π≈ρ (suc j))

-- insert i j respects equality.
insert-cong : ∀ {n} (i j : Fin (suc n)) (π ρ : Permutation′ n)
  → π ≈ᵖ ρ → insert i j π ≈ᵖ insert i j ρ
insert-cong i j _ _ π≈ρ k with i ≟ᶠ k
... | yes _    = refl
... | no i≢k  = cong (punchIn j) (π≈ρ (punchOut i≢k))

-- The index of an agda-stdlib permutation.
rankᵖ : ∀ {n} → Permutation′ n → Fin (n !)
rankᵖ {zero}   _ = zero
rankᵖ {suc n}  π = combine (π ⟨$⟩ʳ zero) (rankᵖ (remove zero π))

-- The permutation at an index: its first digit inserted at 0 into the
-- permutation at the rest.
unrankᵖ : ∀ {n} → Fin (n !) → Permutation′ n
unrankᵖ {zero}   _ = idᵖ
unrankᵖ {suc n}  k =
  uncurry (insert zero) (map₂ (unrankᵖ {n}) (remQuot {suc n} (n !) k))

-- The index respects equality.
rankᵖ-cong : ∀ {n} (π ρ : Permutation′ n) → π ≈ᵖ ρ → rankᵖ π ≡ rankᵖ ρ
rankᵖ-cong {zero}   _ _ _   = refl
rankᵖ-cong {suc n}  π ρ π≈ρ =
  cong₂  combine
         (π≈ρ zero)
         (rankᵖ-cong (remove zero π) (remove zero ρ) (remove-cong π ρ π≈ρ))

-- The index of the permutation at k is k ...
rankᵖ-unrankᵖ : (n : ℕ) (k : Fin (n !)) → rankᵖ (unrankᵖ {n} k) ≡ k
rankᵖ-unrankᵖ zero     zero = refl
rankᵖ-unrankᵖ (suc n)  k    =
  trans  (cong  (combine j)
                (trans  (rankᵖ-cong  (remove zero (insert zero j π)) π
                                     (remove-insert zero j π))
                        (rankᵖ-unrankᵖ n k′)))
         (combine-remQuot {suc n} (n !) k)
  where
  j : Fin (suc n)
  j = remQuot {suc n} (n !) k .proj₁

  k′ : Fin (n !)
  k′ = remQuot {suc n} (n !) k .proj₂

  π : Permutation′ n
  π = unrankᵖ {n} k′

-- ... and the permutation at the index of π is π.
unrankᵖ-rankᵖ : ∀ {n} (π : Permutation′ n) → unrankᵖ {n} (rankᵖ π) ≈ᵖ π
unrankᵖ-rankᵖ {zero}   π ()
unrankᵖ-rankᵖ {suc n}  π k =
  trans  (cong  (λ p → uncurry (insert zero) (map₂ (unrankᵖ {n}) p) ⟨$⟩ʳ k)
                (remQuot-combine (π ⟨$⟩ʳ zero) (rankᵖ (remove zero π))))
         (trans  (insert-cong  zero (π ⟨$⟩ʳ zero)
                               (unrankᵖ {n} (rankᵖ (remove zero π)))
                               (remove zero π)
                               (unrankᵖ-rankᵖ (remove zero π)) k)
                 (insert-remove zero π k))
```

The numbering of `Perm n` reads a permutation as agda-stdlib's, with
`lookupₚ`, and the permutation at an index is stored with `tabulateₚ`.
It is a bijection of the setoid of permutations with `Fin n!`.

```agda
module _ {n : ℕ} where

  -- The index of a permutation.
  rank : Perm n → Fin (n !)
  rank σ = rankᵖ (lookupₚ σ)

  -- The permutation at an index.
  unrank : Fin (n !) → Perm n
  unrank k = tabulateₚ (unrankᵖ {n} k)

  -- The factorial numbering, a bijection of the permutations with Fin n!.
  numbering : Inverse (setoid {n}) (≡-setoid (Fin (n !)))
  numbering = record
    { to         = rank
    ; from       = unrank
    ; to-cong    = λ {σ} {τ} σ≈τ
                   → rankᵖ-cong (lookupₚ σ) (lookupₚ τ) (lookupₚ-cong σ τ σ≈τ)
    ; from-cong  = λ { refl → refl }
    ; inverse    =
        (λ {k} {σ} σ≈ →
          trans  (rankᵖ-cong  (lookupₚ σ) (lookupₚ (unrank k))
                              (lookupₚ-cong σ (unrank k) σ≈))
                 (trans  (rankᵖ-cong  (lookupₚ (unrank k)) (unrankᵖ {n} k)
                                      (lookupₚ-tabulateₚ (unrankᵖ {n} k)))
                         (rankᵖ-unrankᵖ n k))) ,
        (λ { {σ} refl →
          trans  (tabulateₚ-cong  (unrankᵖ {n} (rank σ)) (lookupₚ σ)
                                  (unrankᵖ-rankᵖ (lookupₚ σ)))
                 (tabulateₚ-lookupₚ σ) })
    }
```

#### Sym(n) as a finite group

```agda
-- The permutations of Fin n as a finite setoid, by the factorial numbering.
finite : (n : ℕ) → FiniteSetoid (setoid {n})
finite n = fromInverse numbering

-- Sym(n) as a finite group, enumerated by the factorial numbering.
Sym : (n : ℕ) → FiniteGroup 0ℓ 0ℓ
Sym n = record { group = symGroup n ; irredundant = toIrredundant (finite n) }

-- Its order is n!, by definition.
∣Sym∣≡n! : (n : ℕ) → FiniteGroup.order (Sym n) ≡ n !
∣Sym∣≡n! _ = refl

-- Its index map is the factorial numbering.
idx≡rank : (n : ℕ) (σ : Perm n) → FiniteGroup.idx (Sym n) σ ≡ rank σ
idx≡rank _ _ = refl
```
