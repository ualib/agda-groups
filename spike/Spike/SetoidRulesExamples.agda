{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: the second rule on the
-- setoid route, decided by evaluation.
--
-- +  S₃: every decidable subgroup between 1 and A₃ is 1 or A₃, and the
--    condition fails between 1 and S₃ (⟨s⟩ lies between).
-- +  A₅: every decidable subgroup between ⟨t⟩ and A₄ is ⟨t⟩ or A₄ (⟨t⟩ is
--    a maximal subgroup of A₄).  A search of the tables of A₅ would run
--    over 2⁶⁰ subsets; the condition asks one ⟨x, t⟩ for each x.

module Spike.SetoidRulesExamples where

open import Data.Fin.Patterns     using ( 0F ; 1F ; 3F )
open import Data.List.Base        using ( List ; [] ; _∷_ ; length )
open import Data.Sum.Base         using ( _⊎_ )
open import Level                 using ( Level ; 0ℓ )
open import Relation.Nullary      using ( ¬_ )
open import Relation.Nullary.Decidable.Core using ( from-yes ; from-no )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Relation.Unary        using ( _⊆_ ; _≐_ )

open import Classical.Structures.Group.Subgroups        using ( DecSubgroup )
open import Examples.Classical.Groups.AlternatingGroup5 using ( a5-group )
open import Examples.Classical.Groups.SymmetricGroup3   using ( s3-group )

open import Spike.A5.Common      using ( a5-given ; t )
open import Spike.SmallExamples  using ( s3-given )
open import Spike.Setoid         using ( module Setoids )
open import Spike.Generated      using ( module Generated )
open import Spike.SetoidRules    using ( module Rulesˢ )

private variable ℓ : Level

------------------------------------------------------------------------
-- S₃, on Fin 6: 0 = e, 1 = r, 2 = r², 3 = s, 4 = rs, 5 = r²s.

module S3 where
  open Setoids s3-group s3-given using ( e[_] ; set )
  open Generated s3-group s3-given
  open Rulesˢ s3-group s3-given

  -- Each certificate is checked by evaluation where it is built.
  𝔾₁ 𝔾A₃ 𝔾S₃ : Generators
  𝔾₁   = mkGenerators [] _
  𝔾A₃  = mkGenerators (1F ∷ []) _
  𝔾S₃  = mkGenerators (1F ∷ 3F ∷ []) _

  -- The certificates of every ⟨x⟩.
  cs : Adjoined []
  cs = mkAdjoined [] _

  A₃ S₃ : DecSubgroup s3-group 0ℓ
  A₃ = ⟪ 𝔾A₃ ⟫
  S₃ = ⟪ 𝔾S₃ ⟫

  -- The condition holds between 1 and A₃, and fails between 1 and S₃.
  generates-1-A₃ : Generates 𝔾₁ cs A₃
  generates-1-A₃ = from-yes (generates? 𝔾₁ cs A₃)

  not-generates-1-S₃ : ¬ Generates 𝔾₁ cs S₃
  not-generates-1-S₃ = from-no (generates? 𝔾₁ cs S₃)

  -- Every decidable subgroup between 1 and A₃ is 1 or A₃.
  between-1-A₃ : (𝑳 : DecSubgroup s3-group ℓ) → InGen [] ⊆ set 𝑳 → set 𝑳 ⊆ set A₃
    → (set 𝑳 ≐ InGen []) ⊎ (set 𝑳 ≐ set A₃)
  between-1-A₃ = between 𝔾₁ cs A₃ generates-1-A₃

  -- The classical counts n₂ = 3 and n₃ = 1, by the cyclic subgroups of
  -- prime order (Spike.SmallExamples searches the 64 subsets instead).
  sylow-counts : length (cyclicOfOrder cs 2) ∷ length (cyclicOfOrder cs 3) ∷ [] ≡ 3 ∷ 1 ∷ []
  sylow-counts = refl

------------------------------------------------------------------------
-- A₅: ⟨t⟩ is maximal in A₄.

module A5 where
  open Setoids a5-group a5-given using ( e[_] ; set )
  open Generated a5-group a5-given
  open Rulesˢ a5-group a5-given

  open import Spike.A5.Setoid using ( 𝔾₃ ; A₄ )

  -- The certificates of every ⟨x, t⟩.
  cs : Adjoined (t ∷ [])
  cs = mkAdjoined (t ∷ []) _

  generates-⟨t⟩-A₄ : Generates 𝔾₃ cs A₄
  generates-⟨t⟩-A₄ = from-yes (generates? 𝔾₃ cs A₄)

  -- Every decidable subgroup of A₅ between ⟨t⟩ and A₄ is ⟨t⟩ or A₄.
  between-⟨t⟩-A₄ : (𝑳 : DecSubgroup a5-group ℓ) → InGen (t ∷ []) ⊆ set 𝑳 → set 𝑳 ⊆ set A₄
    → (set 𝑳 ≐ InGen (t ∷ [])) ⊎ (set 𝑳 ≐ set A₄)
  between-⟨t⟩-A₄ = between 𝔾₃ cs A₄ generates-⟨t⟩-A₄
