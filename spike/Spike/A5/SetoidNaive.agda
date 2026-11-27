{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: the counts of
-- Spike.A5.Setoid with deciders composed and never remembered.  The
-- conjugates are compared by ≐ over the enumeration (every element asked
-- of both), and the normalizer's textbook decider (every element of P
-- tested) is asked afresh at each step of the coset space's
-- deduplication.  Each named check is one evaluation.

module Spike.A5.SetoidNaive where

open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

open import Examples.Classical.Groups.AlternatingGroup5 using ( a5-group )

open import Spike.A5.Common  using ( a5-given )
open import Spike.A5.Setoid  using ( P₅ˢ ; P₃ˢ ; Vˢ )
open import Spike.Setoid     using ( module Setoids )

open Setoids a5-group a5-given

-- The distinct conjugates of the Sylow 5-subgroup, deduplicated under ≐.
conjugates₅ : #conjugatesˢ P₅ˢ ≡ 6
conjugates₅ = refl

-- The index of its normalizer, by agda-algebras' coset space, with the
-- textbook decider of the normalizer not remembered.
index₅ : indexᶜ (normalizerˢ P₅ˢ) ≡ 6
index₅ = refl
