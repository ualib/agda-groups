{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: the orders of the Klein
-- four-group and of S₃ and of their subgroups, and the counts of Sylow's
-- third theorem in S₃, computed by evaluation (each `refl` below is a
-- computation that Agda carries out while checking this module).
--
-- Each group is taken twice: with the irredundant enumeration that
-- agda-algebras derives from a FiniteAlgebra witness by deduplication
-- (suffix ᵈ), and with the identity enumeration given directly (suffix ⁱ).

module Spike.SmallExamples where

open import Data.Bool.Base        using ( Bool ; true ; false ; _∨_ )
open import Data.Fin.Base         using ( Fin )
open import Data.Fin.Patterns     using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F )
open import Data.Fin.Properties   renaming ( _≟_ to _≟ᶠ_ ) using ()
open import Data.Fin.Subset       using ( ∣_∣ )
open import Data.List.Base        using ( List ; [] ; _∷_ )
open import Data.Nat.Base         using ( ℕ )
open import Data.Product          using ( _,_ ; proj₁ )
open import Data.Vec.Base         using ( tabulate )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Relation.Nullary.Decidable.Core using ( isYes )

open import Examples.Classical.Groups.KleinFourGroup  using ( v4-group )
open import Examples.Classical.Groups.SymmetricGroup3 using ( s3-group )
open import Setoid.Algebras.Finite                    using ( FiniteAlgebra )
open import Setoid.Algebras.Finite.Irredundant        using ( IrredundantEnumeration
                                                            ; irredundantEnumeration )

open import Spike.Finite   using ( module Tables )
open import Spike.Counting using ( module Counting )

-- Membership in a list of elements of Fin k.
elem : {k : ℕ} → Fin k → List (Fin k) → Bool
elem x []        = false
elem x (g ∷ gs)  = isYes (x ≟ᶠ g) ∨ elem x gs

------------------------------------------------------------------------
-- The Klein four-group, on Fin 4 with 0 the identity.

v4-finite : FiniteAlgebra (proj₁ v4-group)
v4-finite = record { _≟_ = _≟ᶠ_ ; card = 4 ; enum = λ i → i ; enum-sur = λ x → x , refl }

v4-given : IrredundantEnumeration (proj₁ v4-group)
v4-given = record  { icard = 4 ; ienum[_] = λ i → i ; ienum-sur = λ x → x , refl
                   ; ienum-inj = λ e → e }

module V4 (𝑰 : IrredundantEnumeration (proj₁ v4-group)) where
  open Tables v4-group 𝑰 public
  open Counting v4-group 𝑰 public

  ofList : List (Fin 4) → _
  ofList gs = tabulate (λ i → elem e[ i ] gs)

  trivialχ wholeχ twoχ : _
  trivialχ  = ofList (0F ∷ [])
  wholeχ    = ofList (0F ∷ 1F ∷ 2F ∷ 3F ∷ [])
  twoχ      = ofList (0F ∷ 1F ∷ [])

-- The closure proofs are computed where the enumeration is concrete.
module V4ᵈ where
  open V4 (irredundantEnumeration v4-finite) public
  trivial whole two : SubgroupTable
  trivial = trivialχ , _ ; whole = wholeχ , _ ; two = twoχ , _

module V4ⁱ where
  open V4 v4-given public
  trivial whole two : SubgroupTable
  trivial = trivialχ , _ ; whole = wholeχ , _ ; two = twoχ , _

_ : V4ᵈ.order ≡ 4
_ = refl

_ : V4ᵈ.orderᵗ V4ᵈ.trivial ∷ V4ᵈ.orderᵗ V4ᵈ.two ∷ V4ᵈ.orderᵗ V4ᵈ.whole ∷ [] ≡ 1 ∷ 2 ∷ 4 ∷ []
_ = refl

_ : V4ⁱ.orderᵗ V4ⁱ.trivial ∷ V4ⁱ.orderᵗ V4ⁱ.two ∷ V4ⁱ.orderᵗ V4ⁱ.whole ∷ [] ≡ 1 ∷ 2 ∷ 4 ∷ []
_ = refl

-- In an abelian group every subgroup is its only conjugate.
_ : V4ᵈ.#conjugates (proj₁ V4ᵈ.two) ≡ 1
_ = refl

------------------------------------------------------------------------
-- S₃, on Fin 6: 0 = e, 1 = r, 2 = r², 3 = s, 4 = rs, 5 = r²s.

s3-finite : FiniteAlgebra (proj₁ s3-group)
s3-finite = record { _≟_ = _≟ᶠ_ ; card = 6 ; enum = λ i → i ; enum-sur = λ x → x , refl }

s3-given : IrredundantEnumeration (proj₁ s3-group)
s3-given = record  { icard = 6 ; ienum[_] = λ i → i ; ienum-sur = λ x → x , refl
                   ; ienum-inj = λ e → e }

module S3 (𝑰 : IrredundantEnumeration (proj₁ s3-group)) where
  open Tables s3-group 𝑰 public
  open Counting s3-group 𝑰 public

  ofList : List (Fin 6) → _
  ofList gs = tabulate (λ i → elem e[ i ] gs)

  trivialχ wholeχ A₃χ ⟨s⟩χ : _
  trivialχ  = ofList (0F ∷ [])
  wholeχ    = ofList (0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ [])
  A₃χ       = ofList (0F ∷ 1F ∷ 2F ∷ [])
  ⟨s⟩χ      = ofList (0F ∷ 3F ∷ [])

module S3ᵈ where
  open S3 (irredundantEnumeration s3-finite) public
  trivial whole A₃ ⟨s⟩ : SubgroupTable
  trivial = trivialχ , _ ; whole = wholeχ , _ ; A₃ = A₃χ , _ ; ⟨s⟩ = ⟨s⟩χ , _

module S3ⁱ where
  open S3 s3-given public
  trivial whole A₃ ⟨s⟩ : SubgroupTable
  trivial = trivialχ , _ ; whole = wholeχ , _ ; A₃ = A₃χ , _ ; ⟨s⟩ = ⟨s⟩χ , _

_ : S3ᵈ.order ≡ 6
_ = refl

_ :  S3ᵈ.orderᵗ S3ᵈ.trivial ∷ S3ᵈ.orderᵗ S3ᵈ.⟨s⟩ ∷ S3ᵈ.orderᵗ S3ᵈ.A₃ ∷ S3ᵈ.orderᵗ S3ᵈ.whole ∷ []
  ≡  1 ∷ 2 ∷ 3 ∷ 6 ∷ []
_ = refl

-- The Sylow 2-subgroup ⟨s⟩ has 3 conjugates, its own normalizer (order 2),
-- and index 3, counted both ways; the Sylow 3-subgroup A₃ is normal.
_ :  S3ᵈ.#conjugates (proj₁ S3ᵈ.⟨s⟩)
     ∷ ∣ S3ᵈ.normalizer (proj₁ S3ᵈ.⟨s⟩) ∣
     ∷ S3ᵈ.index S3ᵈ.⟨s⟩ ∷ S3ᵈ.indexᵗ (proj₁ S3ᵈ.⟨s⟩)
     ∷ S3ᵈ.#conjugates (proj₁ S3ᵈ.A₃) ∷ []
  ≡  3 ∷ 2 ∷ 3 ∷ 3 ∷ 1 ∷ []
_ = refl

_ :  S3ⁱ.#conjugates (proj₁ S3ⁱ.⟨s⟩) ∷ S3ⁱ.index S3ⁱ.⟨s⟩ ∷ S3ⁱ.#conjugates (proj₁ S3ⁱ.A₃) ∷ []
  ≡  3 ∷ 3 ∷ 1 ∷ []
_ = refl
