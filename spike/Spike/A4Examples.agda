{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: a subgroup as a finite
-- group, counted inside.  A₄, the stabilizer of the point 4 in A₅, with
-- the direct enumeration of Spike.SubgroupEnumeration, has order 12; its
-- Sylow 3-subgroup ⟨t⟩ has 4 conjugates in A₄ and its Sylow 2-subgroup V
-- is normal.  The same counts are made in the re-tabulated A₄ on Fin 12.

module Spike.A4Examples where

open import Data.Bool.Base        using ( _∧_ )
open import Data.Fin.Patterns     using ( 0F )
open import Data.Fin.Properties   renaming ( _≟_ to _≟ᶠ_ ) using ()
open import Data.Fin.Subset       using ( ∣_∣ )
open import Data.List.Base        using ( List ; [] ; _∷_ )
open import Data.Product          using ( _,_ ; proj₁ )
open import Data.Vec.Base         using ( tabulate )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Relation.Nullary.Decidable.Core using ( isYes )

open import Examples.Classical.Groups.AlternatingGroup5 using ( a5-group ; _·_ )

open import Spike.A5.Common            using ( module A5 ; a5-given ; elem ; t )
open import Spike.Finite               using ( module Tables )
open import Spike.Counting             using ( module Counting )
open import Spike.SubgroupEnumeration  using ( module SubgroupEnumeration )
open import Spike.TableGroups          using ( FinGroup ; module Retabulate )

module A5G = A5 a5-given

A₄ : A5G.SubgroupTable
A₄ = A5G.A₄χ , _

-- A₄ as a finite group, with the enumeration by positions.
module A4 = SubgroupEnumeration.Positions a5-group a5-given A₄
module A4T = Tables A4.H-group A4.H-irredundant
module A4C = Counting A4.H-group A4.H-irredundant

a4-order : A4T.order ≡ 12
a4-order = refl

-- ⟨t⟩ and V as subsets of A₄'s own index set.
⟨t⟩χ Vχ : _
⟨t⟩χ = tabulate (λ k → elem (proj₁ A4T.e[ k ]) (0F ∷ t ∷ t · t ∷ []))
Vχ   = tabulate (λ k → isYes (proj₁ A4T.e[ k ] · proj₁ A4T.e[ k ] ≟ᶠ 0F))

⟨t⟩ V : A4T.SubgroupTable
⟨t⟩ = ⟨t⟩χ , _
V   = Vχ , _

a4-subgroup-orders : A4T.orderᵗ ⟨t⟩ ∷ A4T.orderᵗ V ∷ [] ≡ 3 ∷ 4 ∷ []
a4-subgroup-orders = refl

a4-conjugates : A4C.#conjugates ⟨t⟩χ ∷ A4C.#conjugates Vχ ∷ [] ≡ 4 ∷ 1 ∷ []
a4-conjugates = refl

a4-normalizer : ∣ A4C.normalizer ⟨t⟩χ ∣ ≡ 3
a4-normalizer = refl

-- The re-tabulated A₄, on Fin 12, and the same counts there.
module A4R = Retabulate A4.H-group A4.H-irredundant
A4B : FinGroup
A4B = A4R.finGroup
module A4BT = Tables (FinGroup.group A4B) (FinGroup.irredundant A4B)
module A4BC = Counting (FinGroup.group A4B) (FinGroup.irredundant A4B)

a4B-order : A4BT.order ≡ 12
a4B-order = refl

⟨t⟩ᴮ Vᴮ : A4BT.SubgroupTable
⟨t⟩ᴮ = ⟨t⟩χ , _
Vᴮ   = Vχ , _

a4B-conjugates : A4BC.#conjugates ⟨t⟩χ ∷ A4BC.#conjugates Vχ ∷ [] ≡ 4 ∷ 1 ∷ []
a4B-conjugates = refl
