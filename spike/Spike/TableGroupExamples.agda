{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: the second candidate,
-- groups on Fin n, on the examples.  V₄, S₃ and A₅ re-tabulated from their
-- given enumerations have orders 4, 6 and 60 by definition; their
-- subgroups are the same subsets; and the quotient S₃/A₃, re-tabulated
-- through its deduplicated enumeration, is the group of order 2.

module Spike.TableGroupExamples where

open import Data.Fin.Patterns     using ( 0F ; 1F )
open import Data.List.Base        using ( List ; [] ; _∷_ )
open import Data.Product          using ( _,_ ; proj₁ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

open import Examples.Classical.Groups.KleinFourGroup    using ( v4-group )
open import Examples.Classical.Groups.SymmetricGroup3   using ( s3-group )
open import Examples.Classical.Groups.AlternatingGroup5 using ( a5-group )
open import Setoid.Algebras.Finite.Irredundant          using ( irredundantEnumeration )

open import Spike.Finite         using ( module Tables )
open import Spike.TableGroups    using ( FinGroup ; module Retabulate )
open import Spike.Constructions  using ( module Constructions )
open import Spike.SmallExamples  using ( v4-given ; s3-given ; module S3ⁱ ; module V4 ; module S3 )
open import Spike.A5.Common      using ( a5-given ; module A5 )

V4ᴮ S3ᴮ A5ᴮ : FinGroup
V4ᴮ = Retabulate.finGroup v4-group v4-given
S3ᴮ = Retabulate.finGroup s3-group s3-given
A5ᴮ = Retabulate.finGroup a5-group a5-given

orders : FinGroup.n V4ᴮ ∷ FinGroup.n S3ᴮ ∷ FinGroup.n A5ᴮ ∷ [] ≡ 4 ∷ 6 ∷ 60 ∷ []
orders = refl

-- Subgroups of the re-tabulated S₃: the same subsets of Fin 6.
module S3ᴮT = Tables (FinGroup.group S3ᴮ) (FinGroup.irredundant S3ᴮ)
A₃ᴮ ⟨s⟩ᴮ : S3ᴮT.SubgroupTable
A₃ᴮ  = S3ⁱ.A₃χ , _
⟨s⟩ᴮ = S3ⁱ.⟨s⟩χ , _

subgroup-orders : S3ᴮT.orderᵗ A₃ᴮ ∷ S3ᴮT.orderᵗ ⟨s⟩ᴮ ∷ [] ≡ 3 ∷ 2 ∷ []
subgroup-orders = refl

-- S₃/A₃ re-tabulated: a group on Fin 2 in which the non-identity squares
-- to the identity.
module Q = Constructions.Quotient s3-group s3-given S3ⁱ.A₃ _
Qᴮ : FinGroup
Qᴮ = Retabulate.finGroup Q.quotient-group (irredundantEnumeration Q.quotient-finite)

quotient-table : FinGroup.n Qᴮ ∷ [] ≡ 2 ∷ []
quotient-table = refl

quotient-square : FinGroup.mul Qᴮ 1F 1F ≡ 0F
quotient-square = refl
