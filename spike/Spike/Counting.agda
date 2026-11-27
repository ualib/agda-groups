{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: the counts that Sylow's
-- third theorem relates, computed from one subgroup in hand.
--
-- +  the number of distinct conjugates of a subgroup table (the conjugate
--    tables, deduplicated);
-- +  the normalizer as a table, and its order;
-- +  the index of a subgroup, twice: as the size of the irredundant
--    enumeration of agda-algebras' coset space G/K (cosetAlgebra), and as
--    the number of distinct left cosets as tables.

module Spike.Counting where

open import Agda.Primitive using () renaming ( Set to Type )

open import Data.Bool.Base        using ( Bool ; true ; false ; T )
open import Data.Bool.Properties  using ( T? ) renaming ( _≟_ to _≟ᵇ_ )
open import Data.Fin.Base         using ( Fin )
open import Data.Fin.Properties   using ( all? )
open import Data.Fin.Subset       using ( Subset ; ∣_∣ )
open import Data.List.Base        using ( List ; length ; deduplicate ) renaming ( tabulate to tabulateᴸ )
open import Data.Nat.Base         using ( ℕ )
open import Data.Product          using ( _,_ ; proj₁ ; proj₂ )
open import Data.Vec.Base         using ( lookup ; tabulate )
open import Data.Vec.Properties   using ( ≡-dec )
open import Level                 using ( Level )
open import Relation.Nullary.Decidable.Core using ( isYes ; _→?_ )

open import Classical.Structures.Group.Basic   using ( Group ; module Group-Op )
open import Classical.Structures.Group.Cosets  using ( module Coset )
open import Classical.Structures.Group.GSet    using ( module CosetAction )
open import Setoid.Algebras.Finite.Irredundant using ( IrredundantEnumeration ; irredundantEnumeration )

open import Spike.Finite using ( module Tables )

private variable α ρ : Level

module Counting (𝒢 : Group α ρ) (𝑰 : IrredundantEnumeration (proj₁ 𝒢)) where

  open Tables 𝒢 𝑰
  open Group-Op 𝒢 using ( _∙_ ; _⁻¹ )

  -- The table of the conjugate g χ g⁻¹: y lies in it when g⁻¹ y g lies in χ.
  conj : G → Subset n → Subset n
  conj g χ = tabulate (λ i → lookup χ (idx (g ⁻¹ ∙ e[ i ] ∙ g)))

  -- The distinct conjugates of χ, and their number.
  conjugates : Subset n → List (Subset n)
  conjugates χ = deduplicate (≡-dec _≟ᵇ_) (tabulateᴸ (λ i → conj e[ i ] χ))

  #conjugates : Subset n → ℕ
  #conjugates χ = length (conjugates χ)

  -- The normalizer of χ, as a table: the g with g χ g⁻¹ inside χ.
  normalizes : G → Subset n → Bool
  normalizes g χ = isYes (all? (λ i → T? (lookup χ i) →? T? (lookup χ (idx (g ∙ e[ i ] ∙ g ⁻¹)))))

  normalizer : Subset n → Subset n
  normalizer χ = tabulate (λ i → normalizes e[ i ] χ)

  -- The left coset g χ as a table: y lies in it when g⁻¹ y lies in χ.
  leftCoset : G → Subset n → Subset n
  leftCoset g χ = tabulate (λ i → lookup χ (idx (g ⁻¹ ∙ e[ i ])))

  -- The index as the number of distinct left cosets, as tables.
  indexᵗ : Subset n → ℕ
  indexᵗ χ = length (deduplicate (≡-dec _≟ᵇ_) (tabulateᴸ (λ i → leftCoset e[ i ] χ)))

  -- The index as the size of the coset space G/K of agda-algebras
  -- (Classical.Structures.Group.Cosets and GSet), whose finiteness witness
  -- is G's enumeration with the coset relation, deduplicated.
  index : SubgroupTable → ℕ
  index 𝑲@(χ , _) = IrredundantEnumeration.icard (irredundantEnumeration cosetsFinite)
    where
    open Coset 𝒢 (_∈ᵗ χ) (∈ᵗ-isSubgroup 𝑲) using ( ∼-dec )
    open CosetAction 𝒢 (_∈ᵗ χ) (∈ᵗ-isSubgroup 𝑲) using ( cosetAlgebra-FiniteAlgebra )
    cosetsFinite = cosetAlgebra-FiniteAlgebra toFiniteAlgebra (∼-dec (λ x → T? (lookup χ (idx x))))
