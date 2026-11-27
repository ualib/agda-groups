{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: the second candidate of
-- issue 5, a finite group whose carrier is Fin n with propositional
-- equality, and the passage to it from any group with an irredundant
-- enumeration (re-tabulation), which makes every finite group of the first
-- candidate isomorphic to one of the second.

module Spike.TableGroups where

open import Agda.Primitive using () renaming ( Set to Type )

open import Data.Fin.Base         using ( Fin )
open import Data.Nat.Base         using ( ℕ )
open import Data.Product          using ( _,_ ; proj₁ ; proj₂ )
open import Level                 using ( Level ; 0ℓ )
open import Relation.Binary       using ( Setoid )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; trans )

open import Classical.Structures.Group.Basic    using ( Group ; module Group-Op ; eqsToGroup )
open import Setoid.Algebras.Basic               using ( 𝔻[_] )
open import Setoid.Algebras.Finite.Irredundant  using ( IrredundantEnumeration )

open import Spike.Finite using ( module Tables )

private variable α ρ : Level

-- A finite group on Fin n: its order is n by definition.
record FinGroup : Type where
  field
    n      : ℕ
    mul    : Fin n → Fin n → Fin n
    inv    : Fin n → Fin n
    unit   : Fin n
    assoc  : ∀ a b c → mul (mul a b) c ≡ mul a (mul b c)
    idˡ    : ∀ a → mul unit a ≡ a
    idʳ    : ∀ a → mul a unit ≡ a
    invˡ   : ∀ a → mul (inv a) a ≡ unit
    invʳ   : ∀ a → mul a (inv a) ≡ unit

  -- The agda-algebras Group, and its identity enumeration.
  group : Group 0ℓ 0ℓ
  group = eqsToGroup mul unit inv assoc idˡ idʳ invˡ invʳ

  irredundant : IrredundantEnumeration (proj₁ group)
  irredundant = record  { icard = n ; ienum[_] = λ i → i ; ienum-sur = λ x → x , refl
                        ; ienum-inj = λ e → e }

-- Re-tabulation: the group on the index set of an irredundant enumeration.
module Retabulate (𝒢 : Group α ρ) (𝑰 : IrredundantEnumeration (proj₁ 𝒢)) where

  open Tables 𝒢 𝑰
  open Setoid 𝔻[ proj₁ 𝒢 ] using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Group-Op 𝒢 using  ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; assoc-law ; idˡ-law ; idʳ-law
                         ; invˡ-law ; invʳ-law )

  finGroup : FinGroup
  finGroup = record
    { n      = n
    ; mul    = λ a b → idx (e[ a ] ∙ e[ b ])
    ; inv    = λ a → idx (e[ a ] ⁻¹)
    ; unit   = idx ε
    ; assoc  = λ a b c → idx-cong (≈trans (∙-cong (idx-≈ _) ≈refl)
                           (≈trans (assoc-law _ _ _) (∙-cong ≈refl (≈sym (idx-≈ _)))))
    ; idˡ    = λ a → trans (idx-cong (≈trans (∙-cong (idx-≈ ε) ≈refl) (idˡ-law e[ a ]))) (idx-e a)
    ; idʳ    = λ a → trans (idx-cong (≈trans (∙-cong ≈refl (idx-≈ ε)) (idʳ-law e[ a ]))) (idx-e a)
    ; invˡ   = λ a → idx-cong (≈trans (∙-cong (idx-≈ _) ≈refl) (invˡ-law e[ a ]))
    ; invʳ   = λ a → idx-cong (≈trans (∙-cong ≈refl (idx-≈ _)) (invʳ-law e[ a ]))
    }

  -- The enumeration is an isomorphism from the re-tabulated group onto 𝒢:
  -- it is a bijection up to ≈ (the enumeration's own laws), and it
  -- carries products to products.
  e-hom : ∀ a b → e[ FinGroup.mul finGroup a b ] ≈ e[ a ] ∙ e[ b ]
  e-hom a b = idx-≈ (e[ a ] ∙ e[ b ])
