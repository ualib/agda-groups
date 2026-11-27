{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: the orders of A₅'s
-- subgroups and the counts of Sylow's third theorem, computed by
-- evaluation through agda-algebras' Group and the identity enumeration of Fin 60, given directly.
-- Each named check is one evaluation; --profile=definitions times it.

module Spike.A5.Given where

open import Data.List.Base        using ( List ; [] ; _∷_ )
open import Data.Product          using ( _,_ ; proj₁ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

open import Examples.Classical.Groups.AlternatingGroup5  using ( a5-finite )
open import Setoid.Algebras.Finite.Irredundant           using ( irredundantEnumeration )

open import Spike.A5.Common using ( module A5 ; a5-given )

open A5 a5-given

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
