{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: a direct irredundant
-- enumeration of a subgroup as a finite group, by the positions of its
-- table, so that its index map costs one walk of the parent's index set
-- instead of a deduplication.

module Spike.SubgroupEnumeration where

open import Data.Bool.Base        using ( T )
open import Data.Bool.Properties  using ( T? )
open import Data.Empty            using ( ⊥-elim )
open import Data.Fin.Base         using ( Fin )
open import Data.Fin.Properties   using ( <-cmp )
open import Data.List.Base        using ( List ; length ; filter ; allFin )
import Data.List.Base
open import Data.List.Relation.Unary.All using ( All ) renaming ( lookup to lookupᴬ )
open import Data.List.Relation.Unary.All.Properties using ( all-filter )
open import Data.List.Relation.Unary.Any using ( index )
open import Data.List.Relation.Unary.Any.Properties using ( lookup-index )
open import Data.List.Relation.Unary.Unique.Propositional using ( Unique )
open import Data.List.Relation.Unary.Unique.Propositional.Properties
                                  using ( allFin⁺ ) renaming ( filter⁺ to unique-filter⁺ )
open import Data.List.Membership.Propositional using ( _∈_ )
open import Data.List.Membership.Propositional.Properties using ( ∈-filter⁺ ; ∈-allFin ; ∈-lookup )
open import Data.Product          using ( _,_ ; proj₁ ; proj₂ )
open import Data.Vec.Base         renaming ( lookup to lookupᵛ ) using ()
open import Level                 using ( Level )
open import Relation.Binary       using ( Setoid ; tri< ; tri≈ ; tri> )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; trans ; subst ; cong )

open import Classical.Structures.Group.Basic    using ( Group )
open import Setoid.Algebras.Basic               using ( 𝔻[_] )
open import Setoid.Algebras.Finite.Irredundant  using ( IrredundantEnumeration ; lookup-AllPairs )

open import Spike.Finite         using ( module Tables )
open import Spike.Constructions  using ( module Constructions )

private variable α ρ : Level

module SubgroupEnumeration (𝒢 : Group α ρ) (𝑰 : IrredundantEnumeration (proj₁ 𝒢)) where

  open Tables 𝒢 𝑰
  open Setoid 𝔻[ proj₁ 𝒢 ] using ( _≈_ ) renaming ( trans to ≈trans )

  module Positions (𝑯 : SubgroupTable) where
    private
      χ = proj₁ 𝑯
    open Constructions.AsGroup 𝒢 𝑰 𝑯 using ( H-group ) public

    -- The indices of G that H holds, in increasing order.
    positions : List (Fin n)
    positions = filter (λ i → T? (lookupᵛ χ i)) (allFin n)

    positions-in : All (λ i → T (lookupᵛ χ i)) positions
    positions-in = all-filter (λ i → T? (lookupᵛ χ i)) (allFin n)

    positions-unique : Unique positions
    positions-unique = unique-filter⁺ (λ i → T? (lookupᵛ χ i)) (allFin⁺ n)

    -- The k-th element of H is the element at the k-th position.
    member : (k : Fin (length positions)) → e[ Data.List.Base.lookup positions k ] ∈ᵗ χ
    member k = subst (λ j → T (lookupᵛ χ j)) (sym (idx-e _)) (lookupᴬ positions-in (∈-lookup k))

    -- An element of H is at the position of its own index.
    position : ∀ x → x ∈ᵗ χ → idx x ∈ positions
    position x p = ∈-filter⁺ (λ i → T? (lookupᵛ χ i)) (∈-allFin (idx x)) p

    H-irredundant : IrredundantEnumeration (proj₁ H-group)
    H-irredundant = record
      { icard      = length positions
      ; ienum[_]   = λ k → e[ Data.List.Base.lookup positions k ] , member k
      ; ienum-sur  = λ (x , p) →  index (position x p)
                               ,  subst (λ j → e[ j ] ≈ x) (lookup-index (position x p)) (idx-≈ x)
      ; ienum-inj  = inj }
      where
      inj : ∀ {k l} → e[ Data.List.Base.lookup positions k ] ≈ e[ Data.List.Base.lookup positions l ] → k ≡ l
      inj {k} {l} eq with <-cmp k l
      ... | tri< k<l _ _ = ⊥-elim (lookup-AllPairs positions-unique k<l same)
        where same = trans (sym (idx-e _)) (trans (idx-cong eq) (idx-e _))
      ... | tri≈ _ k≡l _ = k≡l
      ... | tri> _ _ l<k = ⊥-elim (lookup-AllPairs positions-unique l<k (sym same))
        where same = trans (sym (idx-e _)) (trans (idx-cong eq) (idx-e _))
