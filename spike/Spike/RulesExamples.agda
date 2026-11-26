{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: the second rule on S₃,
-- decided by evaluation over its 64 subsets, and carried to the witnessed
-- form over agda-algebras' decidable subgroups.

module Spike.RulesExamples where

open import Data.Product          using ( proj₁ )
open import Relation.Nullary      using ( ¬_ )
open import Relation.Nullary.Decidable.Core using ( from-yes ; from-no )

open import Examples.Classical.Groups.SymmetricGroup3 using ( s3-group )

open import Spike.Rules          using ( module Rules )
open import Spike.SmallExamples  using ( module S3ⁱ ; s3-given )

open Rules s3-group s3-given
open S3ⁱ using ( trivial ; whole ; A₃ ; ⟨s⟩ ; toDec ; fromDec ; fromDec∘toDec )

-- Every subgroup of S₃ between 1 and A₃ is 1 or A₃ ...
between-1-A₃ : Between₂ trivial A₃
between-1-A₃ = from-yes (between₂? trivial A₃)

-- ... but not every subgroup between 1 and S₃ is 1 or S₃ (⟨s⟩ is between).
not-between-1-S₃ : ¬ Between₂ trivial whole
not-between-1-S₃ = from-no (between₂? trivial whole)

-- The witnessed form over decidable subgroups, from the table form.
between-1-A₃ʷ : Between₂ʷ (toDec trivial) (toDec A₃)
between-1-A₃ʷ = tables→witnessed (toDec trivial) (toDec A₃)
  between-1-A₃′
  where

  open import Relation.Binary.PropositionalEquality using ( subst ; sym )
  between-1-A₃′ : Between₂ (fromDec (toDec trivial)) (fromDec (toDec A₃))
  between-1-A₃′ = subst (λ 𝑯 → Between₂ 𝑯 (fromDec (toDec A₃))) (sym (fromDec∘toDec trivial))
                    (subst (λ 𝑲 → Between₂ trivial 𝑲) (sym (fromDec∘toDec A₃)) between-1-A₃)
