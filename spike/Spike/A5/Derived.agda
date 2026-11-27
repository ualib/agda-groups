{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: the checks of
-- Spike.A5.Given, through the irredundant enumeration that agda-algebras
-- derives from the FiniteAlgebra witness a5-finite by deduplication.
--
-- This module does not finish in reasonable time, and spike/check.sh
-- leaves it out.  On 2026-11-26 a check under `timeout 1200` was stopped
-- after 20 minutes with no result.  Spike.A5.IndexCost measures why: one
-- lookup of the index map costs 141 to 195 ms here, and the 60 lookups of
-- one conjugate table cost 21 to 24 s, so the distinct conjugates of one
-- subgroup (60 tables, 3,600 lookups) would take about 21 minutes.

module Spike.A5.Derived where

open import Data.List.Base        using ( List ; [] ; _∷_ )
open import Data.Product          using ( _,_ ; proj₁ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

open import Examples.Classical.Groups.AlternatingGroup5  using ( a5-finite )
open import Setoid.Algebras.Finite.Irredundant           using ( irredundantEnumeration )

open import Spike.A5.Common using ( module A5 ; a5-given )

open A5 (irredundantEnumeration a5-finite)

order-60 : order ≡ 60
order-60 = refl

-- The closure of each table is decided as it is built.
P₅ : SubgroupTable
P₅ = P₅χ , _

P₃ : SubgroupTable
P₃ = P₃χ , _

V : SubgroupTable
V = Vχ , _

A₄ : SubgroupTable
A₄ = A₄χ , _

orders : orderᵗ P₅ ∷ orderᵗ P₃ ∷ orderᵗ V ∷ orderᵗ A₄ ∷ [] ≡ 5 ∷ 3 ∷ 4 ∷ 12 ∷ []
orders = refl

-- The number of distinct conjugates of each Sylow subgroup.
conjugates₅ : #conjugates P₅χ ≡ 6
conjugates₅ = refl

conjugates₃ : #conjugates P₃χ ≡ 10
conjugates₃ = refl

conjugates₂ : #conjugates Vχ ≡ 5
conjugates₂ = refl

-- The normalizers, their closure decided, and their orders.
N₅ : SubgroupTable
N₅ = normalizer P₅χ , _

N₃ : SubgroupTable
N₃ = normalizer P₃χ , _

N₂ : SubgroupTable
N₂ = normalizer Vχ , _

normalizer-orders : orderᵗ N₅ ∷ orderᵗ N₃ ∷ orderᵗ N₂ ∷ [] ≡ 10 ∷ 6 ∷ 12 ∷ []
normalizer-orders = refl

-- The index of each normalizer, as the size of agda-algebras' coset space.
index₅ : index N₅ ≡ 6
index₅ = refl

index₃ : index N₃ ≡ 10
index₃ = refl

index₂ : index N₂ ≡ 5
index₂ = refl

-- The same indices, as the number of distinct left cosets as tables.
indexᵗ₅ : indexᵗ (proj₁ N₅) ≡ 6
indexᵗ₅ = refl

indexᵗ₃ : indexᵗ (proj₁ N₃) ≡ 10
indexᵗ₃ = refl

indexᵗ₂ : indexᵗ (proj₁ N₂) ≡ 5
indexᵗ₂ = refl
