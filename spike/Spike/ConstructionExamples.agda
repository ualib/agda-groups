{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: a subgroup and a
-- quotient as finite groups, with their orders computed by evaluation.

module Spike.ConstructionExamples where

open import Data.Product          using ( _,_ ; proj₁ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

open import Examples.Classical.Groups.KleinFourGroup  using ( v4-group )
open import Examples.Classical.Groups.SymmetricGroup3 using ( s3-group )
open import Examples.Classical.Groups.AlternatingGroup5 using ( a5-group )
open import Setoid.Algebras.Finite.Irredundant        using ( irredundantEnumeration )

open import Spike.Constructions  using ( module Constructions )
open import Spike.SmallExamples  using ( module V4ⁱ ; module S3ⁱ ; module S3ᵈ ; v4-given ; s3-given ; s3-finite )
open import Spike.A5.Common      using ( module A5 ; a5-given )

-- S₃/A₃ has order 2, and S₃/1 has order 6.
module S3Q = Constructions s3-group s3-given
module S3/A₃ = S3Q.Quotient S3ⁱ.A₃ _
module S3/1  = S3Q.Quotient S3ⁱ.trivial _

s3/a3-order : S3/A₃.quotient-order ≡ 2
s3/a3-order = refl

s3/1-order : S3/1.quotient-order ≡ 6
s3/1-order = refl

-- The same quotient through the deduplicated enumeration of S₃.
module S3Qᵈ = Constructions s3-group (irredundantEnumeration s3-finite)
module S3/A₃ᵈ = S3Qᵈ.Quotient S3ᵈ.A₃ _

s3/a3-orderᵈ : S3/A₃ᵈ.quotient-order ≡ 2
s3/a3-orderᵈ = refl

-- A₃ and ⟨s⟩ as finite groups in their own right.
module A₃-as-group = S3Q.AsGroup S3ⁱ.A₃
module ⟨s⟩-as-group = S3Q.AsGroup S3ⁱ.⟨s⟩

a3-order : A₃-as-group.H-order ≡ 3
a3-order = refl

s-order : ⟨s⟩-as-group.H-order ≡ 2
s-order = refl

-- V₄ modulo a subgroup of order 2 has order 2.
module V4Q = Constructions v4-group v4-given
module V4/two = V4Q.Quotient V4ⁱ.two _

v4/two-order : V4/two.quotient-order ≡ 2
v4/two-order = refl

-- In A₅ (given enumeration): the point stabilizer A₄ as a finite group of
-- order 12, and the quotient of A₅ by the trivial subgroup, of order 60.
module A5G = A5 a5-given
module A5Q = Constructions a5-group a5-given

A₄ : A5G.SubgroupTable
A₄ = A5G.A₄χ , _

trivial : A5G.SubgroupTable
trivial = A5G.ofList (Data.Fin.Patterns.0F Data.List.Base.∷ Data.List.Base.[]) , _
  where import Data.Fin.Patterns ; import Data.List.Base

module A₄-as-group = A5Q.AsGroup A₄

a4-order : A₄-as-group.H-order ≡ 12
a4-order = refl

module A5/1 = A5Q.Quotient trivial _

a5/1-order : A5/1.quotient-order ≡ 60
a5/1-order = refl
