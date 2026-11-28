---
layout: default
file: "src/Groups/Subgroups/Generated.lagda.md"
title: "Groups.Subgroups.Generated module"
date: "2026-11-27"
author: "the agda-groups development team"
---

### Subgroups given by generators

This is the `Groups.Subgroups.Generated` module of the agda-groups library.

A subgroup is given as GAP gives one, by generators (ADR 0001, § 2).  For
a list A of elements of a finite group G, a *letter* is an element of A
or the inverse of one, a *word* is a list of letters, and the subgroup
**generated** by A, ⟨A⟩, is the set of the elements that some word
evaluates to.  That is the textbook's description of ⟨A⟩ (Aschbacher
(1.3)), and a proof of membership carries its word.  Its *universal
property* is the textbook's definition, the least subgroup that holds A
(Aschbacher, § 1): a subgroup that holds every element of A holds ⟨A⟩.

A decider for ⟨A⟩ reads a **Schreier vector**: for each index of G's
enumeration, a word that reaches the element there, or nothing.  A
breadth-first search from the identity computes it, as GAP's orbit
algorithm computes an orbit with its transversal.  Three decided checks
make it a **certificate**: the identity is reached; the reached indices
are closed under multiplication by every letter; and every word in the
vector evaluates to the element at its index.  A concrete group
discharges the checks by evaluation, so nothing rests on the search
being right: a wrong search fails to type-check.  With a certificate,
the indices the vector reaches are exactly the elements of ⟨A⟩, so the
two forms of ⟨A⟩ (the least subgroup that holds A, and the elements a
search reaches) agree, as ADR 0001's § 5 asks.

A certificate is held in a record, never written in a type at a call
(ADR 0001, § 2).  Where Agda compares such a type with another spelling
of it, it evaluates the certificate again, and under a bound variable it
evaluates it symbolically: sixty certificates passed that way exhausted
a 6 GB heap in 49 s.  The record `Generators` holds a list with its
vector and certificate, and `Adjoined B` the certificates of every ⟨x,
B⟩, x in G; Agda compares a record type by its name and arguments.  Each
is built by `mkGenerators` and `mkAdjoined` with its checks solved by `_`
where the record is made.

From the universal property, inclusion, the normalizer and the equality
of two conjugates are decided by testing the generators alone: |A|
questions where a sweep of the enumeration asks |G|.  The decider of ⟨A⟩
for every finite group, which closes A under the letters in at most |G|
steps and needs no certificate, is M3-4's; a certificate serves a
concrete group.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Subgroups.Generated where

-- Imports from the Agda Standard Library
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Bool.Base                         using ( Bool ; true ; false ; T )
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Base                          using ( Fin ; zero ; suc )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; _++_ ; length ; lookup ; map
                                                         ; allFin )
open import Data.Maybe.Base                        using ( Maybe ; just ; nothing ; is-just )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc )
open import Data.Product.Base                      using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Unit.Polymorphic                  using ( ⊤ ; tt )
open import Data.Vec.Base                          using ( Vec ; replicate )
                                                   renaming ( lookup to lookupᵛ ; _[_]≔_ to _[_]≔ᵛ_ )
open import Function.Bundles                       using ( _⇔_ ; mk⇔ )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary.Bundles                using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( subst )
open import Relation.Nullary.Decidable             using ( Dec ; yes ; no ; map′ ; _×?_ ; _→?_ ; True
                                                         ; toWitness ; T? )
open import Relation.Unary                         using ( Pred ; _∈_ ; _⊆_ ; _≐_ )

import Algebra.Properties.Group                    as GroupProperties
import Data.Fin.Properties                         as Fin

-- Imports from the Agda Universal Algebra Library
open import Classical.Bundles.Group                using ( ⟨_⟩ᵍᵖ )
open import Classical.Structures.Group.Basic       using ( Group ; module Group-Op )
open import Classical.Structures.Group.Conjugation using ( module Conjugate )
open import Classical.Structures.Group.Subgroups   using ( IsSubgroup ; mkIsSubgroup ; DecSubgroup )

-- Imports from this library
open import Groups.Finite.Group                    using ( FiniteGroup )
open import Groups.Subgroups.Basic                 using ( module Subgroups )

private variable α ρ : Level
```
-->

Everything below is about one finite group 𝔾, the parameter of the
module `Generated`.

<!--
```agda
module Generated (𝔾 : FiniteGroup α ρ) where
  private
    𝒢 : Group α ρ
    𝒢 = FiniteGroup.group 𝔾

  open FiniteGroup 𝔾  using ( Carrier ; setoid ; order ; enum ; idx ; enum-idx ; idx-cong ; _≟_ )
  open Setoid setoid  using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Group-Op 𝒢     using ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; ⁻¹-cong ; assoc-law ; idˡ-law ; idʳ-law )
  open Conjugate 𝒢    using ( conj-syntax ; conj-conj⁻¹ ; conj⁻¹-conj )
  open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ using ( ε⁻¹≈ε ; ⁻¹-involutive ; ⁻¹-anti-homo-∙ )
  open Subgroups 𝔾    using ( set ; isSubgroup ; _∈?_ ; preimage ; conjugateᵈ ; Normalizes
                            ; normalizes-isSubgroup )

  private variable ℓ : Level
```
-->

#### Words

A letter of A is an index into A with a Boolean: `true` for the
generator, `false` for its inverse.  A word is a list of letters, its
head the last letter, so that `l ∷ w` evaluates to the value of w times
the letter l.  The inverse of a word is its letters flipped, in the
opposite order.

```agda
  module _ (A : List Carrier) where

    -- A letter: a generator (true) or the inverse of one (false).
    Letter : Type
    Letter = Fin (length A) × Bool

    -- The element a letter names.
    letter : Letter → Carrier
    letter (k , true)   = lookup A k
    letter (k , false)  = lookup A k ⁻¹

    -- The letter of the inverse.
    flip : Letter → Letter
    flip (k , true)   = k , false
    flip (k , false)  = k , true

    -- A word: a list of letters.
    Word : Type
    Word = List Letter

    -- The value of a word: l ∷ w is w followed by l.
    eval : Word → Carrier
    eval []       = ε
    eval (l ∷ w)  = eval w ∙ letter l

    -- The value of a concatenation.
    eval-++ : (v w : Word) → eval (v ++ w) ≈ eval w ∙ eval v
    eval-++ []       w = ≈sym (idʳ-law (eval w))
    eval-++ (l ∷ v)  w = ≈trans (∙-cong (eval-++ v w) ≈refl) (assoc-law (eval w) (eval v) (letter l))

    -- The flipped letter names the inverse.
    letter-flip : (l : Letter) → letter (flip l) ≈ letter l ⁻¹
    letter-flip (k , true)   = ≈refl
    letter-flip (k , false)  = ≈sym (⁻¹-involutive _)

    -- The inverse of a word: its letters flipped, in the opposite order.
    inverse : Word → Word
    inverse []       = []
    inverse (l ∷ w)  = inverse w ++ (flip l ∷ [])

    -- It evaluates to the inverse.
    eval-inverse : (w : Word) → eval (inverse w) ≈ eval w ⁻¹
    eval-inverse []       = ≈sym ε⁻¹≈ε
    eval-inverse (l ∷ w)  =
      ≈trans (eval-++ (inverse w) (flip l ∷ []))
        (≈trans (∙-cong (≈trans (idˡ-law _) (letter-flip l)) (eval-inverse w))
                (≈sym (⁻¹-anti-homo-∙ (eval w) (letter l))))
```

#### The generated subgroup

x lies in ⟨A⟩ when some word evaluates to x.  It is a subgroup: the
product of two words is their concatenation, and the inverse of a word
is its inverse word.  Each generator lies in it, as a word of one
letter, and a subgroup that holds every generator holds it, by
induction on words.

```agda
    -- The subgroup generated by A, as a predicate.
    InGen : Pred Carrier ρ
    InGen x = Σ[ w ∈ Word ] (eval w ≈ x)

    -- It is a subgroup.
    inGen-isSubgroup : IsSubgroup 𝒢 InGen
    inGen-isSubgroup = mkIsSubgroup 𝒢 resp ∙-c ([] , ≈refl) ⁻¹-c
      where
      resp : ∀ {x y} → x ≈ y → InGen x → InGen y
      resp x≈y (w , p) = w , ≈trans p x≈y
      ∙-c : ∀ {x y} → InGen x → InGen y → InGen (x ∙ y)
      ∙-c (w , p) (v , q) = (v ++ w) , ≈trans (eval-++ v w) (∙-cong p q)
      ⁻¹-c : ∀ {x} → InGen x → InGen (x ⁻¹)
      ⁻¹-c (w , p) = inverse w , ≈trans (eval-inverse w) (⁻¹-cong p)

    -- Each generator lies in ⟨A⟩.
    gens∈ : (k : Fin (length A)) → lookup A k ∈ InGen
    gens∈ k = ((k , true) ∷ []) , idˡ-law (lookup A k)

    -- The universal property: a subgroup that holds A holds ⟨A⟩.
    gen⊆ : (K : Pred Carrier ℓ) → IsSubgroup 𝒢 K → (∀ k → lookup A k ∈ K) → InGen ⊆ K
    gen⊆ K K-sg A⊆K (w , p) = respects p (eval∈ w)
      where
      open IsSubgroup K-sg using ( respects ; ∙-closed ; ε-closed ; ⁻¹-closed )
      letter∈ : (l : Letter) → letter l ∈ K
      letter∈ (k , true)   = A⊆K k
      letter∈ (k , false)  = ⁻¹-closed (A⊆K k)
      eval∈ : (w : Word) → eval w ∈ K
      eval∈ []       = ε-closed
      eval∈ (l ∷ w)  = ∙-closed (eval∈ w) (letter∈ l)
```

#### The Schreier vector

The vector holds, at each index of the enumeration, a word that reaches
the element there, or nothing.  The search keeps a *frontier*, the
indices reached in the last round with their words, and in each round
multiplies each of them by every letter, recording each new index with
its word.  It starts from the identity, with the empty word, and stops
when a round reaches nothing new; at most |G| rounds are needed, since
each round that does not stop reaches a new index.

```agda
    -- A Schreier vector: a word, or nothing, at each index.
    SV : Type
    SV = Vec (Maybe Word) order

    private
      -- The indices reached in the last round, with their words.
      Frontier : Type
      Frontier = List (Fin order × Word)

      -- Every letter: the generators, then their inverses.
      letters : List Letter
      letters = map (_, true) (allFin (length A)) ++ map (_, false) (allFin (length A))

      -- Record the index j with the word w, unless it is already reached.
      visit : Fin order → Word → SV × Frontier → SV × Frontier
      visit j w (sv , fr) with lookupᵛ sv j
      ... | just _   = sv , fr
      ... | nothing  = (sv [ j ]≔ᵛ just w) , ((j , w) ∷ fr)

      -- Multiply the element at i, reached by w, by each letter.
      visitAll : List Letter → Fin order → Word → SV × Frontier → SV × Frontier
      visitAll []        i w acc = acc
      visitAll (l ∷ ls)  i w acc = visitAll ls i w (visit (idx (enum i ∙ letter l)) (l ∷ w) acc)

      -- One round: every index of the frontier, by every letter.
      round : Frontier → SV × Frontier → SV × Frontier
      round []               acc = acc
      round ((i , w) ∷ old)  acc = round old (visitAll letters i w acc)

      mutual
        -- The search, with at most k more rounds.
        bfs : ℕ → SV → Frontier → SV
        bfs zero     sv fr        = sv
        bfs (suc k)  sv []        = sv
        bfs (suc k)  sv (f ∷ fr)  = next k (round (f ∷ fr) (sv , []))

        next : ℕ → SV × Frontier → SV
        next k (sv , fr) = bfs k sv fr

    -- The Schreier vector of A, from the identity.
    schreier : SV
    schreier = bfs order (replicate order nothing [ idx ε ]≔ᵛ just []) ((idx ε , []) ∷ [])
```

#### The certificate, and the decider it gives

The three checks are `Cert sv`, decided by `cert?`.  From a certificate,
the value of every word is reached, by induction on the word: the empty
word evaluates to the identity, which is reached, and a reached index
times a letter is reached.  So an index the vector holds nothing at is no
word's value, and the decider reads its answer off the vector.

```agda
    -- The vector holds a word at the index i.
    Reached : SV → Fin order → Type
    Reached sv i = T (is-just (lookupᵛ sv i))

    -- The word at i, if any, evaluates to the element at i.
    Sound : Maybe Word → Fin order → Type ρ
    Sound nothing   i = ⊤
    Sound (just w)  i = eval w ≈ enum i

    sound? : (m : Maybe Word) (i : Fin order) → Dec (Sound m i)
    sound? nothing   i = yes tt
    sound? (just w)  i = eval w ≟ enum i

    -- The certificate: the identity is reached, the reached indices are
    -- closed under every letter, and every word is sound.
    Cert : SV → Type ρ
    Cert sv =  Reached sv (idx ε)
            ×  (∀ i → Reached sv i → (l : Letter) → Reached sv (idx (enum i ∙ letter l)))
            ×  (∀ i → Sound (lookupᵛ sv i) i)

    private
      -- A property of every letter, decided.
      allLetters? : {p : Level} {P : Letter → Type p} → (∀ l → Dec (P l)) → Dec (∀ l → P l)
      allLetters? P? = map′ (λ f → λ { (k , true) → proj₁ (f k) ; (k , false) → proj₂ (f k) })
                            (λ g k → g (k , true) , g (k , false))
                            (Fin.all? (λ k → P? (k , true) ×? P? (k , false)))

    -- The three checks, decided.
    cert? : (sv : SV) → Dec (Cert sv)
    cert? sv =     T? (is-just (lookupᵛ sv (idx ε)))
              ×?  Fin.all? (λ i → T? (is-just (lookupᵛ sv i))
                       →? allLetters? (λ l → T? (is-just (lookupᵛ sv (idx (enum i ∙ letter l))))))
              ×?  Fin.all? (λ i → sound? (lookupᵛ sv i) i)

    module _ (sv : SV) (c : Cert sv) where

      -- The value of every word is reached.
      reached : (w : Word) → Reached sv (idx (eval w))
      reached []       = proj₁ c
      reached (l ∷ w)  = subst (Reached sv) (idx-cong (∙-cong (enum-idx (eval w)) ≈refl))
                           (proj₁ (proj₂ c) (idx (eval w)) (reached w) l)

      -- A reached index is the value of its word.
      reached⇒InGen : ∀ x → Reached sv (idx x) → InGen x
      reached⇒InGen x r with lookupᵛ sv (idx x) in eq
      ... | just w   = w , ≈trans (subst (λ m → Sound m (idx x)) eq (proj₂ (proj₂ c) (idx x))) (enum-idx x)
      ... | nothing  = ⊥-elim r

      -- The two forms of ⟨A⟩ agree: the indices the vector reaches are its elements.
      reached⇔InGen : ∀ x → Reached sv (idx x) ⇔ InGen x
      reached⇔InGen x = mk⇔ (reached⇒InGen x) (λ (w , p) → subst (Reached sv) (idx-cong p) (reached w))

      -- The decider of ⟨A⟩, read off the vector.
      inGen? : ∀ x → Dec (InGen x)
      inGen? x with lookupᵛ sv (idx x) in eq
      ... | just w   = yes (w , ≈trans (subst (λ m → Sound m (idx x)) eq (proj₂ (proj₂ c) (idx x)))
                                       (enum-idx x))
      ... | nothing  = no (λ (w , p) → subst (λ m → T (is-just m)) eq
                                         (subst (Reached sv) (idx-cong p) (reached w)))
```

Two facts about adjoining a generator, for the subgroups ⟨x, B⟩ of
`Groups.Subgroups.Notions`: ⟨B⟩ lies in ⟨x, B⟩, and ⟨x, B⟩ depends
on x only up to `≈`.

```agda
  -- ⟨B⟩ lies in ⟨x, B⟩ ...
  InGen-∷ : (x : Carrier) (B : List Carrier) → InGen B ⊆ InGen (x ∷ B)
  InGen-∷ x B = gen⊆ B (InGen (x ∷ B)) (inGen-isSubgroup (x ∷ B)) (λ k → gens∈ (x ∷ B) (suc k))

  -- ... and ⟨x, B⟩ ⊆ ⟨y, B⟩ when x ≈ y.
  InGen-∷-cong : (B : List Carrier) {x y : Carrier} → x ≈ y → InGen (x ∷ B) ⊆ InGen (y ∷ B)
  InGen-∷-cong B {x} {y} x≈y = gen⊆ (x ∷ B) (InGen (y ∷ B)) (inGen-isSubgroup (y ∷ B)) gens
    where
    gens : ∀ k → lookup (x ∷ B) k ∈ InGen (y ∷ B)
    gens zero     = IsSubgroup.respects (inGen-isSubgroup (y ∷ B)) (≈sym x≈y) (gens∈ (y ∷ B) zero)
    gens (suc k)  = gens∈ (y ∷ B) (suc k)
```

#### Certificates in records

`Generators` holds a list with its vector and certificate, and
`mkGenerators A _` builds it from the list, Agda solving the `_` by
evaluating the three checks once, there.  `Adjoined B` holds the
certificates of every ⟨x, B⟩, x in G, and `adjoin` gives the generators
x ∷ B of each.  A function of a subgroup by generators takes the record.

```agda
  -- A list of generators, with its Schreier vector and certificate.
  record Generators : Type (α ⊔ ρ) where
    constructor generators
    field
      gens  : List Carrier
      vec   : SV gens
      cert  : Cert gens vec

  open Generators public

  -- Generators whose certificate is checked by evaluation, once, here.
  mkGenerators : (A : List Carrier) → True (cert? A (schreier A)) → Generators
  mkGenerators A c = generators A (schreier A) (toWitness c)

  -- The certificates of every ⟨x, B⟩, x in the group.
  record Adjoined (B : List Carrier) : Type ρ where
    constructor adjoined
    field
      certs : ∀ i → Cert (enum i ∷ B) (schreier (enum i ∷ B))

  open Adjoined public

  -- The certificates of every ⟨x, B⟩, checked by evaluation, once, here.
  mkAdjoined : (B : List Carrier) → True (Fin.all? (λ i → cert? (enum i ∷ B) (schreier (enum i ∷ B))))
    → Adjoined B
  mkAdjoined B c = adjoined (toWitness c)

  -- The generators x ∷ B, for x the i-th element of the group.
  adjoin : {B : List Carrier} → Adjoined B → Fin order → Generators
  adjoin {B} 𝔸 i = generators (enum i ∷ B) (schreier (enum i ∷ B)) (certs 𝔸 i)

  -- The subgroup generated by a list of generators.
  ⟨_⟩ : Generators → DecSubgroup 𝒢 ρ
  ⟨ 𝔸 ⟩ = (InGen (gens 𝔸) , inGen-isSubgroup (gens 𝔸)) , inGen? (gens 𝔸) (vec 𝔸) (cert 𝔸)
```

#### Decisions by the generators alone

⟨A⟩ ⊆ K exactly when every generator lies in K, as GAP tests the
inclusion of one group in another (its `IsSubset` for groups).  With
x ^ g for the conjugate g x g⁻¹, as in `Groups.Subgroups.Basic`,
g normalizes ⟨A⟩ exactly when a ^ g and a ^ g⁻¹ lie in ⟨A⟩ for every
generator a, by the universal property applied to the preimages of ⟨A⟩
under conjugation; the normalizer by generators is the textbook
predicate of `Groups.Subgroups.Basic` with this faster decider.  And
g ⟨A⟩ g⁻¹ ⊆ K exactly when every a ^ g lies in K, which decides the
equality of two conjugates by |A| questions each way.

```agda
  -- ⟨A⟩ ⊆ K, decided by the generators.
  gen⊆? : (A : List Carrier) (K : DecSubgroup 𝒢 ℓ) → Dec (InGen A ⊆ set K)
  gen⊆? A K = map′ (gen⊆ A (set K) (isSubgroup K)) (λ s k → s (gens∈ A k)) (Fin.all? (λ k → lookup A k ∈? K))

  -- g normalizes ⟨A⟩, decided by the generators.
  normalizesGen? : (𝔸 : Generators) (g : Carrier) → Dec (Normalizes ⟨ 𝔸 ⟩ g)
  normalizesGen? 𝔸 g = map′ to (λ N k → N (gens∈ A k))
    (Fin.all? (λ k → (lookup A k ^ g ∈? ⟨ 𝔸 ⟩) ×? (lookup A k ^ (g ⁻¹) ∈? ⟨ 𝔸 ⟩)))
    where
    A : List Carrier
    A = gens 𝔸
    to : (∀ k → (lookup A k ^ g ∈ InGen A) × (lookup A k ^ (g ⁻¹) ∈ InGen A)) → Normalizes ⟨ 𝔸 ⟩ g
    to t x∈H =  gen⊆ A (set (preimage g ⟨ 𝔸 ⟩)) (isSubgroup (preimage g ⟨ 𝔸 ⟩)) (λ k → proj₁ (t k)) x∈H
             ,  gen⊆ A (set (preimage (g ⁻¹) ⟨ 𝔸 ⟩)) (isSubgroup (preimage (g ⁻¹) ⟨ 𝔸 ⟩))
                    (λ k → proj₂ (t k)) x∈H

  -- The normalizer of ⟨A⟩: the textbook predicate, decided by the generators.
  normalizerGen : Generators → DecSubgroup 𝒢 (α ⊔ ρ)
  normalizerGen 𝔸 = (Normalizes ⟨ 𝔸 ⟩ , normalizes-isSubgroup ⟨ 𝔸 ⟩) , normalizesGen? 𝔸

  -- g ⟨A⟩ g⁻¹ ⊆ K, decided by the generators.
  conjGen⊆? : (𝔸 : Generators) (g : Carrier) (K : DecSubgroup 𝒢 ℓ) → Dec (set (conjugateᵈ g ⟨ 𝔸 ⟩) ⊆ set K)
  conjGen⊆? 𝔸 g K = map′ to from (Fin.all? (λ k → lookup A k ^ g ∈? K))
    where
    A : List Carrier
    A = gens 𝔸
    to : (∀ k → lookup A k ^ g ∈ set K) → set (conjugateᵈ g ⟨ 𝔸 ⟩) ⊆ set K
    to t {x} p = IsSubgroup.respects (isSubgroup K) (conj-conj⁻¹ g x)
                   (gen⊆ A (set (preimage g K)) (isSubgroup (preimage g K)) t p)
    from : set (conjugateᵈ g ⟨ 𝔸 ⟩) ⊆ set K → ∀ k → lookup A k ^ g ∈ set K
    from s k = s (IsSubgroup.respects (inGen-isSubgroup A) (≈sym (conj⁻¹-conj g (lookup A k))) (gens∈ A k))

  -- Two conjugates of ⟨A⟩ are equal, decided by the generators.
  conjGen≐? : (𝔸 : Generators) (g h : Carrier)
    → Dec (set (conjugateᵈ g ⟨ 𝔸 ⟩) ≐ set (conjugateᵈ h ⟨ 𝔸 ⟩))
  conjGen≐? 𝔸 g h = conjGen⊆? 𝔸 g (conjugateᵈ h ⟨ 𝔸 ⟩) ×? conjGen⊆? 𝔸 h (conjugateᵈ g ⟨ 𝔸 ⟩)
```
