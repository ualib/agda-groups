{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: A₅ (agda-algebras'
-- AlternatingGroup5, on Fin 60 with 0 the identity) and four of its
-- subgroups, as subsets of the index set of an irredundant enumeration.

module Spike.A5.Common where

open import Data.Bool.Base        using ( Bool ; false ; _∨_ ; _∧_ )
open import Data.Fin.Base         using ( Fin )
open import Data.Fin.Patterns     using ( 0F ; 4F )
open import Data.Fin.Properties   renaming ( _≟_ to _≟ᶠ_ ) using ()
open import Data.List.Base        using ( List ; [] ; _∷_ )
open import Data.Nat.Base         using ( ℕ )
open import Data.Product          using ( proj₁ ; _,_ )
open import Relation.Binary.PropositionalEquality using ( refl )
open import Data.Vec.Base         using ( tabulate )
open import Relation.Nullary.Decidable.Core using ( isYes )

open import Examples.Classical.Groups.AlternatingGroup5         using ( a5-group ; a5-act ; _·_ )
open import Examples.Classical.Groups.AlternatingGroup5.Tables  using ( a5-gen-s ; a5-gen-t )
open import Setoid.Algebras.Finite.Irredundant                  using ( IrredundantEnumeration )

open import Spike.Finite   using ( module Tables )
open import Spike.Counting using ( module Counting )

elem : Fin 60 → List (Fin 60) → Bool
elem x []        = false
elem x (g ∷ gs)  = isYes (x ≟ᶠ g) ∨ elem x gs

s t : Fin 60
s = a5-gen-s     -- (0 1 2 3 4)
t = a5-gen-t     -- (0 1 2)

-- The identity enumeration of Fin 60, given directly.
a5-given : IrredundantEnumeration (proj₁ a5-group)
a5-given = record  { icard = 60 ; ienum[_] = λ i → i ; ienum-sur = λ x → x , refl
                   ; ienum-inj = λ e → e }


module A5 (𝑰 : IrredundantEnumeration (proj₁ a5-group)) where
  open Tables a5-group 𝑰 public
  open Counting a5-group 𝑰 public

  ofList : List (Fin 60) → _
  ofList gs = tabulate (λ i → elem e[ i ] gs)

  -- A Sylow 5-subgroup ⟨s⟩, a Sylow 3-subgroup ⟨t⟩, a Sylow 2-subgroup V
  -- (the double transpositions fixing the point 4, with 1), and the
  -- point stabilizer A₄ of the point 4.
  P₅χ P₃χ Vχ A₄χ : _
  P₅χ  = ofList (0F ∷ s ∷ s · s ∷ s · s · s ∷ s · s · s · s ∷ [])
  P₃χ  = ofList (0F ∷ t ∷ t · t ∷ [])
  Vχ   = tabulate (λ i → isYes (a5-act e[ i ] 4F ≟ᶠ 4F) ∧ isYes (e[ i ] · e[ i ] ≟ᶠ 0F))
  A₄χ  = tabulate (λ i → isYes (a5-act e[ i ] 4F ≟ᶠ 4F))
