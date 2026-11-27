---
layout: default
file: "src/Groups/Finite/Subset.lagda.md"
title: "Groups.Finite.Subset module"
date: "2026-11-26"
author: "the agda-groups development team"
---

### Decidable subsets of a finite setoid

This is the `Groups.Finite.Subset` module of the agda-groups library.

A subset of a setoid is *detachable*, in the vocabulary of Mines, Richman
and Ruitenburg, when membership in it is decidable.  The library's
decidable subsets are predicates that respect `≈`, as the Agda Universal
Algebra Library's subgroups do (its `IsSubgroup.respects`), with a
decision procedure for membership; two of them are equal when they have
the same elements, `≐`, a pair of inclusions.

Over a finite setoid of size n, a decidable subset P has a *table*, its
decisions at the n enumerated elements, a vector of n Booleans
(agda-stdlib's `Subset n`).  The size of P, written `∣ P ∣`, is the size of
its table, the number of positions it holds.  The inequalities between
sizes are agda-stdlib's facts about `Subset n`
(`Data.Fin.Subset.Properties`), carried along the table: a subset of a
subset is no larger, a proper subset is smaller, and the complement has
the remaining size; so a subset of a subset with the same size contains
it.  That last fact needs the respect of `≈`.  On `Bool`
with `≈` total, enumerated by `true` alone, the predicates "is `true`" and
"anything" have the same size 1, and the first lies in the second, but
`false` lies in the second only; the first does not respect `≈`.

A decidable subset is also a finite setoid in its own right, the
*subsetoid* of its members compared in the setoid, enumerated by the
positions its table holds, in increasing order, and of the subset's size.
A table, read back through the index map, is a decidable subset again,
with the round trips that remember a decision procedure as its table (ADR
0001's `memo`).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Finite.Subset where

-- Imports from the Agda Standard Library
open import Agda.Primitive                         using () renaming ( Set to Type )
open import Data.Bool.Base                         using ( true ; false ; not ; T )
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Base                          using ( Fin ; zero ; suc )
open import Data.Fin.Subset                        using ( Subset )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _≤_ ; _<_ ; _∸_ ; _+_ )
open import Data.Nat.Properties                    using ( ≤-reflexive ; <⇒≱ ; m+[n∸m]≡n )
open import Data.Product.Base                      using ( _,_ ; proj₁ ; _×_ ; Σ ; ∃-syntax )
open import Data.Unit.Base                         using ( tt )
open import Data.Vec.Base                          using ( _∷_ ; tabulate ; lookup )
open import Data.Vec.Properties                    using ( lookup∘tabulate ; tabulate∘lookup
                                                         ; tabulate-cong ; tabulate-∘
                                                         ; []=⇒lookup ; lookup⇒[]= )
open import Level                                  using ( Level ; _⊔_ ; 0ℓ )
                                                   renaming ( suc to lsuc )
open import Relation.Binary.Bundles                using ( Setoid )
open import Relation.Binary.Definitions            using ( _Respects_ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong ; subst )
open import Relation.Nullary.Decidable             using ( Dec ; yes ; no ; does ; map′ ; _×?_
                                                         ; _→?_ ; ¬? ; T? ; decidable-stable )
open import Relation.Unary                         using ( Pred ; Decidable ; _∈_ ; _∉_ ; _⊆_
                                                         ; _⊈_ ; _⊂_ ; _≐_ ; U ; ∅ )

import Data.Fin.Properties                         as Fin
import Data.Fin.Subset                             as Sub
import Data.Fin.Subset.Properties                  as SubP
import Relation.Binary.Construct.On                as On
import Relation.Unary                              as U

-- Imports from this library
open import Groups.Finite.Setoid                   using ( FiniteSetoid )

private variable a ℓ p q : Level
```
-->

#### Decidable subsets

`DecSubset S p` is the type of the decidable subsets of the setoid `S`, at
level p: a predicate on the carrier, the proof that it respects `≈`, and
the decision procedure for membership.

```agda
record DecSubset (S : Setoid a ℓ) (p : Level) : Type (a ⊔ ℓ ⊔ lsuc p) where
  open Setoid S using ( Carrier ; _≈_ )
  field
    set       : Pred Carrier p
    respects  : set Respects _≈_
    decide    : Decidable set

open DecSubset public
```

The complement of a decidable subset is decidable; so are the whole
setoid and the empty subset.  The *subsetoid* of P is the setoid of the
members of P, each with its proof of membership, compared as elements of
the setoid (agda-stdlib's `Relation.Binary.Construct.On`).

```agda
module _ {S : Setoid a ℓ} where
  open Setoid S using ( Carrier ; _≈_ ) renaming ( sym to ≈sym )

  -- The complement of P.
  ∁ : DecSubset S p → DecSubset S p
  ∁ P = record
    { set       = U.∁ (set P)
    ; respects  = λ x≈y ¬px py → ¬px (respects P (≈sym x≈y) py)
    ; decide    = λ x → ¬? (decide P x)
    }

  -- The whole setoid.
  full : DecSubset S 0ℓ
  full = record { set = U ; respects = λ _ _ → tt ; decide = λ _ → yes tt }

  -- The empty subset.
  empty : DecSubset S 0ℓ
  empty = record { set = ∅ ; respects = λ _ () ; decide = λ _ → no λ () }

  -- The members of P, compared in S.
  subsetoid : DecSubset S p → Setoid (a ⊔ p) ℓ
  subsetoid P = On.setoid {B = Σ Carrier (set P)} S proj₁
```

#### The positions a table holds

Three functions on agda-stdlib's `Subset n`: the k-th position the table
t holds (`pos`), the rank of a position it holds among them (`rank`), and
their laws.  `rank` uses the proof that t holds i only to rule out the
impossible case, so evaluating it walks the table and never the proof.

```agda
private
  -- The k-th position that t holds, in increasing order.
  pos : ∀ {n} (t : Subset n) → Fin Sub.∣ t ∣ → Fin n
  pos (true  ∷ t) zero     = zero
  pos (true  ∷ t) (suc k)  = suc (pos t k)
  pos (false ∷ t) k        = suc (pos t k)

  -- t holds its k-th position.
  pos-∈ : ∀ {n} (t : Subset n) k → T (lookup t (pos t k))
  pos-∈ (true  ∷ t) zero     = tt
  pos-∈ (true  ∷ t) (suc k)  = pos-∈ t k
  pos-∈ (false ∷ t) k        = pos-∈ t k

  -- Distinct ranks give distinct positions.
  pos-inj : ∀ {n} (t : Subset n) {k k′} → pos t k ≡ pos t k′ → k ≡ k′
  pos-inj (true  ∷ t) {zero}  {zero}   _  = refl
  pos-inj (true  ∷ t) {zero}  {suc k′} ()
  pos-inj (true  ∷ t) {suc k} {zero}   ()
  pos-inj (true  ∷ t) {suc k} {suc k′} e  = cong suc (pos-inj t (Fin.suc-injective e))
  pos-inj (false ∷ t)                  e  = pos-inj t (Fin.suc-injective e)

  -- The rank of a position that t holds.
  rank : ∀ {n} (t : Subset n) (i : Fin n) → T (lookup t i) → Fin Sub.∣ t ∣
  rank (true  ∷ t) zero     _  = zero
  rank (true  ∷ t) (suc i)  m  = suc (rank t i m)
  rank (false ∷ t) zero     ()
  rank (false ∷ t) (suc i)  m  = rank t i m

  -- The position of the rank of i is i.
  pos-rank : ∀ {n} (t : Subset n) i (m : T (lookup t i)) → pos t (rank t i m) ≡ i
  pos-rank (true  ∷ t) zero     _  = refl
  pos-rank (true  ∷ t) (suc i)  m  = cong suc (pos-rank t i m)
  pos-rank (false ∷ t) zero     ()
  pos-rank (false ∷ t) (suc i)  m  = cong suc (pos-rank t i m)

  -- A decision that answers yes proves its proposition ...
  does⇒ : ∀ {A : Type p} (d : Dec A) → T (does d) → A
  does⇒ (yes a) _  = a
  does⇒ (no _)  ()

  -- ... and a proof of the proposition makes it answer yes.
  ⇒does : ∀ {A : Type p} (d : Dec A) → A → T (does d)
  ⇒does (yes _) _  = tt
  ⇒does (no ¬a) a  = ¬a a

  -- Decisions of equivalent propositions agree.
  does-cong : ∀ {A : Type p} {B : Type q} → (A → B) → (B → A) → (d : Dec A) (e : Dec B) → does d ≡ does e
  does-cong f g (yes a) (yes b)  = refl
  does-cong f g (yes a) (no ¬b)  = ⊥-elim (¬b (f a))
  does-cong f g (no ¬a) (yes b)  = ⊥-elim (¬a (g b))
  does-cong f g (no ¬a) (no ¬b)  = refl

  -- The table of everything holds every position.
  ∣tabulate-true∣ : ∀ n → Sub.∣ tabulate {n = n} (λ _ → true) ∣ ≡ n
  ∣tabulate-true∣ zero     = refl
  ∣tabulate-true∣ (suc n)  = cong suc (∣tabulate-true∣ n)

  -- The table of nothing holds no position.
  ∣tabulate-false∣ : ∀ n → Sub.∣ tabulate {n = n} (λ _ → false) ∣ ≡ 0
  ∣tabulate-false∣ zero     = refl
  ∣tabulate-false∣ (suc n)  = ∣tabulate-false∣ n
```

#### Tables and sizes

From here on the setoid is finite: the module `Counting F` holds the
tables and sizes of the decidable subsets of the finite setoid `F`.

```agda
module Counting {S : Setoid a ℓ} (F : FiniteSetoid S) where
  open Setoid S using ( Carrier ; _≈_ ; reflexive ) renaming ( sym to ≈sym ; trans to ≈trans )
  open FiniteSetoid F using ( size ; enum ; enum-inj ; idx ; enum-idx ; idx-cong ; idx-enum
                            ; all? ; any? )

  -- The table of P: its decisions at the enumerated elements.
  table : DecSubset S p → Subset size
  table P = tabulate (λ i → does (decide P (enum i)))

  -- The size of P: the number of positions its table holds.
  ∣_∣ : DecSubset S p → ℕ
  ∣ P ∣ = Sub.∣ table P ∣
```

The table holds the position i exactly when P holds the i-th element.

```agda
  -- The i-th entry of the table.
  lookup-table : (P : DecSubset S p) (i : Fin size) → lookup (table P) i ≡ does (decide P (enum i))
  lookup-table P i = lookup∘tabulate _ i

  -- An entry that holds is a member ...
  T-table⇒∈ : (P : DecSubset S p) {i : Fin size} → T (lookup (table P) i) → enum i ∈ set P
  T-table⇒∈ P {i} t = does⇒ (decide P (enum i)) (subst T (lookup-table P i) t)

  -- ... and a member's entry holds.
  ∈⇒T-table : (P : DecSubset S p) {i : Fin size} → enum i ∈ set P → T (lookup (table P) i)
  ∈⇒T-table P {i} pi = subst T (sym (lookup-table P i)) (⇒does (decide P (enum i)) pi)

  -- The same, for agda-stdlib's membership in a Subset: an index in the table is a member's ...
  ∈table⇒∈ : (P : DecSubset S p) {i : Fin size} → i Sub.∈ table P → enum i ∈ set P
  ∈table⇒∈ P {i} m = T-table⇒∈ P (subst T (sym ([]=⇒lookup m)) tt)

  -- ... and a member's index is in the table.
  ∈⇒∈table : (P : DecSubset S p) {i : Fin size} → enum i ∈ set P → i Sub.∈ table P
  ∈⇒∈table P {i} pi = lookup⇒[]= i (table P) (T-true (∈⇒T-table P pi))
    where
    T-true : ∀ {b} → T b → b ≡ true
    T-true {true}  _  = refl
    T-true {false} ()
```

Inclusion and equality of decidable subsets are decided at the enumerated
elements and carried to every element by the respect of `≈`, and a
failed inclusion has a witness, found by a search of the enumeration.

```agda
  -- Inclusion is decidable.
  infix 4 _⊆?_ _≐?_
  _⊆?_ : (P : DecSubset S p) (Q : DecSubset S q) → Dec (set P ⊆ set Q)
  P ⊆? Q = map′ (λ h {x} → h x) (λ h x → h {x}) (all? resp (λ x → decide P x →? decide Q x))
    where
    resp : (λ x → x ∈ set P → x ∈ set Q) Respects _≈_
    resp x≈y h py = respects Q x≈y (h (respects P (≈sym x≈y) py))

  -- Equality, ≐, is decidable.
  _≐?_ : (P : DecSubset S p) (Q : DecSubset S q) → Dec (set P ≐ set Q)
  P ≐? Q = (P ⊆? Q) ×? (Q ⊆? P)

  -- A failed inclusion has a witness.
  ⊈⇒∃ : (P : DecSubset S p) (Q : DecSubset S q) → set P ⊈ set Q → ∃[ x ] (x ∈ set P × x ∉ set Q)
  ⊈⇒∃ P Q P⊈Q = search (any? resp (λ x → decide P x ×? ¬? (decide Q x)))
    where
    resp : (λ x → x ∈ set P × x ∉ set Q) Respects _≈_
    resp x≈y (px , ¬qx) = respects P x≈y px , λ qy → ¬qx (respects Q (≈sym x≈y) qy)
    search : Dec (∃[ x ] (x ∈ set P × x ∉ set Q)) → ∃[ x ] (x ∈ set P × x ∉ set Q)
    search (yes w)     = w
    search (no  none)  = ⊥-elim (P⊈Q λ {x} px → decidable-stable (decide Q x) (λ ¬qx → none (x , px , ¬qx)))
```

The sizes, from agda-stdlib's lemmas on `Subset n`: no subset is larger
than the setoid; equal subsets have equal tables, so equal sizes; a
subset of a subset is no larger, and smaller when the second holds an
element outside the first; and the complement has the remaining size.

```agda
  -- Equal subsets have equal tables ...
  table-cong : (P : DecSubset S p) (Q : DecSubset S q) → set P ≐ set Q → table P ≡ table Q
  table-cong P Q (P⊆Q , Q⊆P) = tabulate-cong (λ i → does-cong P⊆Q Q⊆P (decide P (enum i)) (decide Q (enum i)))

  -- ... so equal sizes.
  P≐Q⇒∣P∣≡∣Q∣ : (P : DecSubset S p) (Q : DecSubset S q) → set P ≐ set Q → ∣ P ∣ ≡ ∣ Q ∣
  P≐Q⇒∣P∣≡∣Q∣ P Q eq = cong Sub.∣_∣ (table-cong P Q eq)

  -- No subset is larger than the setoid.
  ∣P∣≤n : (P : DecSubset S p) → ∣ P ∣ ≤ size
  ∣P∣≤n P = SubP.∣p∣≤n (table P)

  -- The whole setoid has its size ...
  ∣full∣≡n : ∣ full ∣ ≡ size
  ∣full∣≡n = ∣tabulate-true∣ size

  -- ... and the empty subset size 0.
  ∣empty∣≡0 : ∣ empty ∣ ≡ 0
  ∣empty∣≡0 = ∣tabulate-false∣ size

  -- An inclusion of subsets is an inclusion of their tables.
  table-mono : (P : DecSubset S p) (Q : DecSubset S q) → set P ⊆ set Q → table P Sub.⊆ table Q
  table-mono P Q P⊆Q m = ∈⇒∈table Q (P⊆Q (∈table⇒∈ P m))

  -- A subset of a subset is no larger.
  P⊆Q⇒∣P∣≤∣Q∣ : (P : DecSubset S p) (Q : DecSubset S q) → set P ⊆ set Q → ∣ P ∣ ≤ ∣ Q ∣
  P⊆Q⇒∣P∣≤∣Q∣ P Q P⊆Q = SubP.p⊆q⇒∣p∣≤∣q∣ (table-mono P Q P⊆Q)

  -- A subset of a subset that holds an element outside it is smaller.
  P⊆Q∧x∈Q∖P⇒∣P∣<∣Q∣ : (P : DecSubset S p) (Q : DecSubset S q) → set P ⊆ set Q
    → ∀ {x} → x ∈ set Q → x ∉ set P → ∣ P ∣ < ∣ Q ∣
  P⊆Q∧x∈Q∖P⇒∣P∣<∣Q∣ P Q P⊆Q {x} qx ¬px = SubP.p⊂q⇒∣p∣<∣q∣
    ( table-mono P Q P⊆Q , idx x
    , ∈⇒∈table Q (respects Q (≈sym (enum-idx x)) qx)
    , λ m → ¬px (respects P (enum-idx x) (∈table⇒∈ P m)) )

  -- A proper subset is smaller.
  P⊂Q⇒∣P∣<∣Q∣ : (P : DecSubset S p) (Q : DecSubset S q) → set P ⊂ set Q → ∣ P ∣ < ∣ Q ∣
  P⊂Q⇒∣P∣<∣Q∣ P Q (P⊆Q , Q⊈P) with ⊈⇒∃ Q P Q⊈P
  ... | x , qx , ¬px = P⊆Q∧x∈Q∖P⇒∣P∣<∣Q∣ P Q P⊆Q qx ¬px

  -- The table of the complement is the complement of the table ...
  table-∁ : (P : DecSubset S p) → table (∁ P) ≡ Sub.∁ (table P)
  table-∁ P = tabulate-∘ not (λ i → does (decide P (enum i)))

  -- ... so the complement has the remaining size.
  ∣∁P∣≡n∸∣P∣ : (P : DecSubset S p) → ∣ ∁ P ∣ ≡ size ∸ ∣ P ∣
  ∣∁P∣≡n∸∣P∣ P = trans (cong Sub.∣_∣ (table-∁ P)) (SubP.∣∁p∣≡n∸∣p∣ (table P))

  -- A subset and its complement together have the size of the setoid.
  ∣P∣+∣∁P∣≡n : (P : DecSubset S p) → ∣ P ∣ + ∣ ∁ P ∣ ≡ size
  ∣P∣+∣∁P∣≡n P = trans (cong (∣ P ∣ +_) (∣∁P∣≡n∸∣P∣ P)) (m+[n∸m]≡n (∣P∣≤n P))
```

A subset of a subset with the same size contains it, so the two are
equal, stated as inclusions.  It is the contrapositive of the strict
inequality above, and it is where the respect of `≈` is needed, through
the witness of the failed inclusion.

```agda
  -- A subset Q of which P is a subset, and no larger than P, lies in P.
  P⊆Q∧∣Q∣≤∣P∣⇒Q⊆P : (P : DecSubset S p) (Q : DecSubset S q) → set P ⊆ set Q → ∣ Q ∣ ≤ ∣ P ∣ → set Q ⊆ set P
  P⊆Q∧∣Q∣≤∣P∣⇒Q⊆P P Q P⊆Q ∣Q∣≤∣P∣ {x} qx =
    decidable-stable (decide P x) λ ¬px → <⇒≱ (P⊆Q∧x∈Q∖P⇒∣P∣<∣Q∣ P Q P⊆Q qx ¬px) ∣Q∣≤∣P∣

  -- A subset of a subset with the same size is equal to it.
  P⊆Q∧∣P∣≡∣Q∣⇒P≐Q : (P : DecSubset S p) (Q : DecSubset S q) → set P ⊆ set Q → ∣ P ∣ ≡ ∣ Q ∣ → set P ≐ set Q
  P⊆Q∧∣P∣≡∣Q∣⇒P≐Q P Q P⊆Q eq = P⊆Q , P⊆Q∧∣Q∣≤∣P∣⇒Q⊆P P Q P⊆Q (≤-reflexive (sym eq))

  -- A subset with the size of the setoid holds every element.
  ∣P∣≡n⇒∈P : (P : DecSubset S p) → ∣ P ∣ ≡ size → ∀ x → x ∈ set P
  ∣P∣≡n⇒∈P P eq x = P⊆Q∧∣Q∣≤∣P∣⇒Q⊆P P full (λ _ → tt) (≤-reflexive (trans ∣full∣≡n (sym eq))) {x} tt

  -- A subset with a member has positive size ...
  ∈⇒0<∣P∣ : (P : DecSubset S p) → ∀ {x} → x ∈ set P → 0 < ∣ P ∣
  ∈⇒0<∣P∣ P {x} px = subst (_< ∣ P ∣) ∣empty∣≡0 (P⊆Q∧x∈Q∖P⇒∣P∣<∣Q∣ empty P (λ ()) px (λ ()))

  -- ... and a subset of positive size has a member.
  0<∣P∣⇒∃ : (P : DecSubset S p) → 0 < ∣ P ∣ → ∃[ x ] x ∈ set P
  0<∣P∣⇒∃ P 0<∣P∣ with any? (respects P) (decide P)
  ... | yes w     = w
  ... | no  none  = ⊥-elim (<⇒≱ 0<∣P∣ (subst (∣ P ∣ ≤_) ∣empty∣≡0
                      (P⊆Q⇒∣P∣≤∣Q∣ P empty λ {x} px → none (x , px))))
```

#### A table as a decidable subset

A table over the enumeration, read back through the index map, is a
decidable subset: x is in it when the table holds the position of x.  The
table of that subset is the table, and the subset of the table of P is P,
as inclusions; so a decision procedure is remembered as its table.

```agda
  -- The decidable subset of the elements whose positions t holds.
  fromTable : Subset size → DecSubset S 0ℓ
  fromTable t = record
    { set       = λ x → T (lookup t (idx x))
    ; respects  = λ x≈y → subst (λ i → T (lookup t i)) (idx-cong x≈y)
    ; decide    = λ x → T? (lookup t (idx x))
    }

  -- The table of fromTable t is t ...
  table-fromTable : (t : Subset size) → table (fromTable t) ≡ t
  table-fromTable t = trans (tabulate-cong (λ i → cong (lookup t) (idx-enum i))) (tabulate∘lookup t)

  -- ... and the subset of the table of P is P.
  fromTable-table : (P : DecSubset S p) → set (fromTable (table P)) ≐ set P
  fromTable-table P =  (λ {x} t → respects P (enum-idx x) (T-table⇒∈ P t))
                    ,  (λ {x} px → ∈⇒T-table P (respects P (≈sym (enum-idx x)) px))
```

#### A decidable subset as a finite setoid

The subsetoid of P is a finite setoid of size `∣ P ∣`: its k-th element is
the element at the k-th position the table holds, and the position of a
member x is the rank of `idx x` among them.  So a theorem about finite
setoids applies to a decidable subset, and a subgroup's order is its size.

```agda
  -- The subsetoid of P, enumerated by the positions its table holds.
  finite : (P : DecSubset S p) → FiniteSetoid (subsetoid P)
  finite P = record
    { size      = ∣ P ∣
    ; enum      = λ k → enum (pos t k) , T-table⇒∈ P (pos-∈ t k)
    ; enum-sur  = sur
    ; enum-inj  = λ e → pos-inj t (enum-inj e)
    }
    where
    t = table P
    sur : ∀ (u : Σ Carrier (set P)) → ∃[ k ] enum (pos t k) ≈ proj₁ u
    sur (x , px) = rank t (idx x) m , ≈trans (reflexive (cong enum (pos-rank t (idx x) m))) (enum-idx x)
      where
      m : T (lookup t (idx x))
      m = ∈⇒T-table P (respects P (≈sym (enum-idx x)) px)
```
