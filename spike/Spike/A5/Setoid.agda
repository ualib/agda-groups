{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: the checks of
-- Spike.A5.Given on the setoid route, through the identity enumeration of
-- Fin 60.  Each subgroup is a DecSubgroup, given twice: by the decider of
-- its table in Spike.A5.Common (suffix ˢ), and by generators with a
-- checked Schreier vector (no suffix).  Each named check is one
-- evaluation; --profile=definitions times it.

module Spike.A5.Setoid where

open import Data.Fin                using ( #_ )
open import Data.Fin.Base           using ( Fin )
open import Data.List.Base          using ( List ; [] ; _∷_ )
open import Data.Product            using ( _,_ )
open import Level                   using ( 0ℓ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Relation.Nullary.Decidable.Core using ( from-yes )
open import Relation.Unary          using ( _≐_ )

open import Classical.Structures.Group.Subgroups        using ( DecSubgroup )
open import Examples.Classical.Groups.AlternatingGroup5 using ( a5-group )

open import Spike.A5.Common  using ( module A5 ; a5-given ; s ; t )
open import Spike.Setoid     using ( module Setoids )
open import Spike.Generated  using ( module Generated )

open A5 a5-given using ( P₅χ ; P₃χ ; Vχ ; A₄χ )
open Setoids a5-group a5-given
open Generated a5-group a5-given

-- Two of the double transpositions that fix the point 4: with 1 and
-- their product, the subgroup V of Spike.A5.Common.
v₁ v₂ : Fin 60
v₁ = # 13
v₂ = # 30

------------------------------------------------------------------------
-- The subgroups, by the deciders of their tables.

P₅ˢ P₃ˢ Vˢ A₄ˢ : DecSubgroup a5-group 0ℓ
P₅ˢ  = toDec (P₅χ , _)
P₃ˢ  = toDec (P₃χ , _)
Vˢ   = toDec (Vχ , _)
A₄ˢ  = toDec (A₄χ , _)

orders-ˢ : orderˢ P₅ˢ ∷ orderˢ P₃ˢ ∷ orderˢ Vˢ ∷ orderˢ A₄ˢ ∷ [] ≡ 5 ∷ 3 ∷ 4 ∷ 12 ∷ []
orders-ˢ = refl

------------------------------------------------------------------------
-- The same subgroups, by generators: each certificate is checked here.

B₅ B₃ B₂ B₁₂ : List (Fin 60)
B₅   = s ∷ []
B₃   = t ∷ []
B₂   = v₁ ∷ v₂ ∷ []
B₁₂  = t ∷ v₁ ∷ []

𝔾₅ 𝔾₃ 𝔾₂ 𝔾₁₂ : Generators
𝔾₅   = mkGenerators B₅ _
𝔾₃   = mkGenerators B₃ _
𝔾₂   = mkGenerators B₂ _
𝔾₁₂  = mkGenerators B₁₂ _

⟨s⟩ ⟨t⟩ V A₄ : DecSubgroup a5-group 0ℓ
⟨s⟩  = ⟪ 𝔾₅ ⟫
⟨t⟩  = ⟪ 𝔾₃ ⟫
V    = ⟪ 𝔾₂ ⟫
A₄   = ⟪ 𝔾₁₂ ⟫

orders : orderˢ ⟨s⟩ ∷ orderˢ ⟨t⟩ ∷ orderˢ V ∷ orderˢ A₄ ∷ [] ≡ 5 ∷ 3 ∷ 4 ∷ 12 ∷ []
orders = refl

-- Each generated subgroup is its table's, as ≐ decided over the enumeration.
same-P₅ : set ⟨s⟩ ≐ set P₅ˢ
same-P₅ = from-yes (⟨s⟩ ≐? P₅ˢ)

same-A₄ : set A₄ ≐ set A₄ˢ
same-A₄ = from-yes (A₄ ≐? A₄ˢ)

------------------------------------------------------------------------
-- The distinct conjugates of the Sylow 5-, 3- and 2-subgroups, decided by
-- the generators (the conjugate g ⟨A⟩ g⁻¹ is compared by the g a g⁻¹).

conjugates₅ : #conjugates⟪⟫ 𝔾₅ ≡ 6
conjugates₅ = refl

conjugates₃ : #conjugates⟪⟫ 𝔾₃ ≡ 10
conjugates₃ = refl

conjugates₂ : #conjugates⟪⟫ 𝔾₂ ≡ 5
conjugates₂ = refl

------------------------------------------------------------------------
-- The normalizers and their orders: the textbook decider (every element
-- of P tested), and the decider by generators.

normalizer₅ˢ : orderˢ (normalizerˢ P₅ˢ) ≡ 10
normalizer₅ˢ = refl

normalizer₃ˢ : orderˢ (normalizerˢ P₃ˢ) ≡ 6
normalizer₃ˢ = refl

normalizer₂ˢ : orderˢ (normalizerˢ Vˢ) ≡ 12
normalizer₂ˢ = refl

N₅ N₃ N₂ : DecSubgroup a5-group 0ℓ
N₅  = normalizer⟪⟫ 𝔾₅
N₃  = normalizer⟪⟫ 𝔾₃
N₂  = normalizer⟪⟫ 𝔾₂

normalizer₅ : orderˢ N₅ ≡ 10
normalizer₅ = refl

normalizer₃ : orderˢ N₃ ≡ 6
normalizer₃ = refl

normalizer₂ : orderˢ N₂ ≡ 12
normalizer₂ = refl

------------------------------------------------------------------------
-- The indices of the normalizers (6, 10, 5), by agda-algebras' coset
-- space: with the deciders by generators, and with the textbook deciders
-- remembered as tables.

index₅ : indexᶜ N₅ ≡ 6
index₅ = refl

index₃ : indexᶜ N₃ ≡ 10
index₃ = refl

index₂ : indexᶜ N₂ ≡ 5
index₂ = refl

index₅ᵐ : indexᶜ (memo (normalizerˢ P₅ˢ)) ≡ 6
index₅ᵐ = refl

index₃ᵐ : indexᶜ (memo (normalizerˢ P₃ˢ)) ≡ 10
index₃ᵐ = refl

index₂ᵐ : indexᶜ (memo (normalizerˢ Vˢ)) ≡ 5
index₂ᵐ = refl

-- The same indices, as the number of left cosets counted by their first
-- members, with the deciders by generators.

indexᶠ₅ : indexˢ N₅ ≡ 6
indexᶠ₅ = refl

indexᶠ₃ : indexˢ N₃ ≡ 10
indexᶠ₃ = refl

indexᶠ₂ : indexˢ N₂ ≡ 5
indexᶠ₂ = refl

------------------------------------------------------------------------
-- A₄ inside A₅, with no group built on A₄: the Sylow 3-subgroup ⟨t⟩ has 4
-- conjugates by the elements of A₄, and V has 1 (V is normal in A₄).

a4-conjugates : #conjugates⟪⟫-in 𝔾₃ A₄ ∷ #conjugates⟪⟫-in 𝔾₂ A₄ ∷ [] ≡ 4 ∷ 1 ∷ []
a4-conjugates = refl
