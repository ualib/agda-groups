{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: Sylow's third theorem
-- typed (not proved) in the two forms the candidates allow, with the
-- number of Sylow p-subgroups a natural number.
--
-- +  Over subgroup tables, the subgroups of a finite group form a finite
--    set (the closed tables among the 2ⁿ subsets of the index set), so
--    n_p is the number of subgroup tables of order pᵃ, as Aschbacher
--    defines it (|Syl_p(G)|), and Agda computes it for small groups.
-- +  Over decidable subgroups alone there is no finite set of subgroups to
--    count, so n_p is the number of conjugates of one Sylow subgroup P in
--    hand, and the statement adds that every Sylow subgroup is a conjugate
--    of P (Sylow's second theorem), which is what makes that number n_p.

module Spike.Sylow where

open import Agda.Primitive using () renaming ( Set to Type )

open import Data.Bool.Base        using ( Bool ; true ; false ; _∧_ )
open import Data.Bool.Properties  using ( T? )
open import Data.Fin.Subset       using ( Subset ; ∣_∣ )
open import Data.List.Base        using ( List ; [] ; _∷_ ; _++_ ; map ; filter ; length )
open import Data.Nat.Base         using ( ℕ ; zero ; suc ; _^_ ; _*_ )
open import Data.Nat.Divisibility using ( _∣_ )
open import Data.Nat.Primality    using ( Prime )
open import Data.Nat.Properties   renaming ( _≟_ to _≟ℕ_ ) using ()
open import Data.Product          using ( Σ-syntax ; _×_ ; _,_ ; proj₁ )
open import Data.Vec.Base         using ( Vec ; [] ; _∷_ )
open import Level                 using ( Level ; _⊔_ ) renaming ( suc to lsuc )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Relation.Nullary      using ( ¬_ )
open import Relation.Nullary.Decidable.Core using ( isYes )

open import Classical.Structures.Group.Basic      using ( Group )
open import Classical.Structures.Group.Subgroups  using ( DecSubgroup )
open import Setoid.Algebras.Finite.Irredundant    using ( IrredundantEnumeration )

open import Spike.Finite   using ( module Tables )
open import Spike.Counting using ( module Counting )

private variable α ρ ℓ : Level

-- The 2ᵏ subsets of Fin k.
allSubsets : (k : ℕ) → List (Subset k)
allSubsets zero     = [] ∷ []
allSubsets (suc k)  = map (true ∷_) (allSubsets k) ++ map (false ∷_) (allSubsets k)

module Sylow (𝒢 : Group α ρ) (𝑰 : IrredundantEnumeration (proj₁ 𝒢)) where

  open Tables 𝒢 𝑰
  open Counting 𝒢 𝑰

  -- A subset is a subgroup table of order m.
  ofOrder : ℕ → Subset n → Bool
  ofOrder m χ = isYes (closed? χ) ∧ isYes (∣ χ ∣ ≟ℕ m)

  -- The number of subgroups of order m, counted among all 2ⁿ subsets.
  #subgroupsOfOrder : ℕ → ℕ
  #subgroupsOfOrder m = length (filter (λ χ → T? (ofOrder m χ)) (allSubsets n))

  -- Sylow's third theorem over tables (Aschbacher, Sylow's Theorem (3)):
  -- with |G| = pᵃ m and p prime to m, the number of subgroups of order pᵃ
  -- is the number of conjugates of any one of them, is 1 modulo p, and
  -- divides m.
  Sylow₃ᵗ : Type
  Sylow₃ᵗ = (p a m : ℕ) → Prime p → n ≡ p ^ a * m → ¬ (p ∣ m)
    → (𝑷 : SubgroupTable) → orderᵗ 𝑷 ≡ p ^ a
    → let nₚ = #subgroupsOfOrder (p ^ a) in
      (nₚ ≡ #conjugates (proj₁ 𝑷)) × (Σ[ k ∈ ℕ ] nₚ ≡ suc (k * p)) × (nₚ ∣ m)

  -- Sylow's third theorem over decidable subgroups: the count is of the
  -- conjugates of P, and Sylow's second theorem is part of the statement.
  Sylow₃ᵈ : (ℓ : Level) → Type (α ⊔ ρ ⊔ lsuc ℓ)
  Sylow₃ᵈ ℓ = (p a m : ℕ) → Prime p → n ≡ p ^ a * m → ¬ (p ∣ m)
    → (𝑷 : DecSubgroup 𝒢 ℓ) → orderᵈ 𝑷 ≡ p ^ a
    → let nₚ = #conjugates (table 𝑷) in
      (Σ[ k ∈ ℕ ] nₚ ≡ suc (k * p)) × (nₚ ∣ m)
      × ((𝑸 : DecSubgroup 𝒢 ℓ) → orderᵈ 𝑸 ≡ p ^ a → Σ[ g ∈ G ] (conj g (table 𝑷) ≡ table 𝑸))
