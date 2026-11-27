{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: the classical count of
-- Sylow subgroups of prime order in A₅, by a search of its cyclic
-- subgroups rather than of its 2⁶⁰ subsets.  Every subgroup of prime
-- order p is ⟨x⟩ for each of its elements x ≠ 1 (a consequence of
-- Lagrange's theorem, not proved here), so the distinct ⟨x⟩ of order p
-- are the Sylow p-subgroups when p² does not divide 60.  Two cyclic
-- subgroups are compared by their generators: ⟨x⟩ ⊆ ⟨y⟩ when x ∈ ⟨y⟩.

module Spike.A5.Cyclic where

open import Data.List.Base        using ( [] ; length )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

open import Examples.Classical.Groups.AlternatingGroup5 using ( a5-group )

open import Spike.A5.Common  using ( a5-given )
open import Spike.Generated  using ( module Generated )

open Generated a5-group a5-given

-- The certificates of every cyclic subgroup ⟨x⟩.
cs : Adjoined []
cs = mkAdjoined [] _

-- |Syl₅(A₅)| = 6 and |Syl₃(A₅)| = 10, as the classical counts.
sylow₅ : length (cyclicOfOrder cs 5) ≡ 6
sylow₅ = refl

sylow₃ : length (cyclicOfOrder cs 3) ≡ 10
sylow₃ = refl
