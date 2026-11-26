{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: the cost of A₅'s index
-- map through agda-algebras' deduplicated enumeration (D), one lookup and
-- 60 lookups (one conjugate table), against the identity enumeration
-- given directly (I); and the order, which needs no lookup.

module Spike.A5.IndexCost where

open import Data.Fin.Patterns     using ( 0F )
open import Data.Fin.Subset       using ( ∣_∣ )
open import Data.Product          using ( proj₁ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

open import Examples.Classical.Groups.AlternatingGroup5  using ( a5-finite ; _·_ )
open import Setoid.Algebras.Finite.Irredundant           using ( irredundantEnumeration )

open import Spike.A5.Common using ( module A5 ; a5-given ; s ; t )

module D = A5 (irredundantEnumeration a5-finite)
module I = A5 a5-given

-- The order of A₅, the size of the deduplicated enumeration.
orderᵈ : D.order ≡ 60
orderᵈ = refl

-- One lookup of the index map, through each enumeration.
one-lookupᵈ : D.idx (s · t) ≡ I.idx (s · t)
one-lookupᵈ = refl

one-lookupⁱ : I.idx (s · t) ≡ s · t
one-lookupⁱ = refl

-- Sixty lookups: the conjugate of the Sylow 5-subgroup by t, as a table.
sixty-lookupsᵈ : ∣ D.conj t D.P₅χ ∣ ≡ 5
sixty-lookupsᵈ = refl

sixty-lookupsⁱ : ∣ I.conj t I.P₅χ ∣ ≡ 5
sixty-lookupsⁱ = refl
