{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: the numbers of Sylow
-- subgroups of V₄ and S₃ computed by evaluation, as the number of
-- subgroup tables of the right order among all 2ⁿ subsets (16 for V₄, 64
-- for S₃).  For A₅ the same count would range over 2⁶⁰ subsets, so it is
-- computed through one Sylow subgroup in hand (Spike.A5.Given).

module Spike.SylowExamples where

open import Data.List.Base        using ( List ; [] ; _∷_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

open import Examples.Classical.Groups.KleinFourGroup  using ( v4-group )
open import Examples.Classical.Groups.SymmetricGroup3 using ( s3-group )
open import Setoid.Algebras.Finite.Irredundant        using ( irredundantEnumeration )

open import Spike.Sylow          using ( module Sylow )
open import Spike.SmallExamples  using ( v4-given ; s3-given ; s3-finite )

module V4S = Sylow v4-group v4-given
module S3S = Sylow s3-group s3-given
module S3Sᵈ = Sylow s3-group (irredundantEnumeration s3-finite)

-- V₄: one subgroup of order 4 (n₂ = 1), three of order 2.
v4-counts : V4S.#subgroupsOfOrder 4 ∷ V4S.#subgroupsOfOrder 2 ∷ V4S.#subgroupsOfOrder 1 ∷ []
          ≡ 1 ∷ 3 ∷ 1 ∷ []
v4-counts = refl

-- S₃: n₂ = 3 and n₃ = 1.
s3-counts : S3S.#subgroupsOfOrder 2 ∷ S3S.#subgroupsOfOrder 3 ∷ []  ≡ 3 ∷ 1 ∷ []
s3-counts = refl

-- The same through the deduplicated enumeration of S₃.
s3-countsᵈ : S3Sᵈ.#subgroupsOfOrder 2 ∷ S3Sᵈ.#subgroupsOfOrder 3 ∷ []  ≡ 3 ∷ 1 ∷ []
s3-countsᵈ = refl
