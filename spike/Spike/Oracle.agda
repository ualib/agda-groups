{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: why the second rule is
-- needed for subgroups that are predicates.  In S₃, the premise "every
-- subgroup L between 1 and A₃ lies in 1 or holds A₃", quantified over
-- agda-algebras' subgroups (predicates), proves excluded middle: for any
-- proposition P, the predicate {1} ∪ {x ∈ A₃ | P} is such a subgroup.
-- Over tables the same premise is decided (Spike.RulesExamples).

module Spike.Oracle where

open import Agda.Primitive using () renaming ( Set to Type )

import Data.Fin.Base
open import Data.Fin.Patterns     using ( 0F ; 1F )
open import Data.Product          using ( _×_ ; _,_ ; proj₁ )
open import Data.Sum.Base         using ( _⊎_ ; inj₁ ; inj₂ )
open import Level                 using ( 0ℓ )
import Level
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; subst )
open import Relation.Nullary      using ( ¬_ )
open import Relation.Unary        using ( Pred ; _⊆_ )

open import Classical.Structures.Group.Basic      using ( module Group-Op )
open import Classical.Structures.Group.Subgroups  using ( IsSubgroup ; mkIsSubgroup ; Subgroup )
open import Examples.Classical.Groups.SymmetricGroup3 using ( s3-group )

open import Spike.SmallExamples using ( module S3ⁱ )

open Group-Op s3-group using ( _∙_ ; ε ; _⁻¹ )
open S3ⁱ using ( _∈ᵗ_ ; A₃χ ; A₃ ; ∈ᵗ-isSubgroup )
open IsSubgroup (∈ᵗ-isSubgroup A₃) using ( ∙-closed ; ε-closed ; ⁻¹-closed )

-- The trivial subgroup and A₃, as predicates on Fin 6.
Triv InA₃ : Pred (Data.Fin.Base.Fin 6) 0ℓ
Triv x = x ≡ 0F
InA₃ x = x ∈ᵗ A₃χ

-- The oracle subgroup of a proposition P.
module _ (P : Type) where
  L : Pred (Data.Fin.Base.Fin 6) 0ℓ
  L x = Triv x ⊎ (P × InA₃ x)

  L-isSubgroup : IsSubgroup s3-group L
  L-isSubgroup = mkIsSubgroup s3-group (λ x≡y → subst L x≡y) ∙-c (inj₁ refl) ⁻¹-c
    where
    ∙-c : ∀ {x y} → L x → L y → L (x ∙ y)
    ∙-c (inj₁ refl)               (inj₁ refl)       = inj₁ refl
    ∙-c {y = y} (inj₁ refl)       (inj₂ (p , y∈))   = inj₂ (p , ∙-closed {ε} {y} ε-closed y∈)
    ∙-c {x = x} (inj₂ (p , x∈))   (inj₁ refl)       = inj₂ (p , ∙-closed {x} {ε} x∈ ε-closed)
    ∙-c {x} {y} (inj₂ (p , x∈))   (inj₂ (_ , y∈))   = inj₂ (p , ∙-closed {x} {y} x∈ y∈)
    ⁻¹-c : ∀ {x} → L x → L (x ⁻¹)
    ⁻¹-c (inj₁ refl)          = inj₁ refl
    ⁻¹-c {x} (inj₂ (p , x∈))  = inj₂ (p , ⁻¹-closed {x} x∈)

  oracle : Subgroup s3-group 0ℓ
  oracle = L , L-isSubgroup

-- The disjunctive premise, over every subgroup of agda-algebras.
Disjunctive : Type (Level.suc 0ℓ)
Disjunctive = (𝑳 : Subgroup s3-group 0ℓ) → Triv ⊆ proj₁ 𝑳 → proj₁ 𝑳 ⊆ InA₃
  → (proj₁ 𝑳 ⊆ Triv) ⊎ (InA₃ ⊆ proj₁ 𝑳)

-- It proves excluded middle.
module _ (P : Type) where
  private
    below : L P ⊆ InA₃
    below (inj₁ refl)      = ε-closed
    below (inj₂ (_ , x∈))  = x∈

    no-r : ¬ (_≡_ {A = Data.Fin.Base.Fin 6} 1F 0F)
    no-r ()

    decide : (L P ⊆ Triv) ⊎ (InA₃ ⊆ L P) → P ⊎ ¬ P
    decide (inj₁ L⊆1)   = inj₂ (λ p → no-r (L⊆1 {1F} (inj₂ (p , _))))
    decide (inj₂ A₃⊆L)  = from-r (A₃⊆L {1F} _)
      where
      from-r : L P 1F → P ⊎ ¬ P
      from-r (inj₁ ())
      from-r (inj₂ (p , _)) = inj₁ p

  disjunctive→LEM : Disjunctive → P ⊎ ¬ P
  disjunctive→LEM d = decide (d (oracle P) inj₁ below)
