{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: the two rules for the
-- types of subgroups, on the setoid route.
--
-- +  The first rule: equality of subgroups is ≐, which _≐?_ of
--    Spike.Setoid decides; ≡ is never asked of two subgroups.
-- +  The second rule: "every subgroup between H and K is H or K" is a
--    disjunction over every decidable subgroup L, proved constructively
--    from a condition on generators that a finite search decides: each
--    element x of K outside H = ⟨B⟩ generates K together with B.  No
--    subgroup is built from an arbitrary proposition, since L comes with
--    a decider.  The condition and the disjunction are equivalent.

module Spike.SetoidRules where

open import Agda.Primitive using () renaming ( Set to Type )

open import Data.Empty            using ( ⊥-elim )
open import Data.Fin.Base         using ( Fin ; zero ; suc )
open import Data.Fin.Properties   using ( all? )
open import Data.List.Base        using ( List ; _∷_ ; lookup )
open import Data.Product          using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base         using ( _⊎_ ; inj₁ ; inj₂ )
open import Level                 using ( Level ; _⊔_ )
open import Relation.Nullary      using ( Dec ; yes ; no ; ¬_ )
open import Relation.Nullary.Decidable.Core using ( _→?_ ; ¬? )
open import Relation.Unary        using ( _∈_ ; _⊆_ ; _≐_ )

open import Classical.Structures.Group.Basic      using ( Group )
open import Classical.Structures.Group.Subgroups  using ( DecSubgroup )
open import Setoid.Algebras.Finite.Irredundant    using ( IrredundantEnumeration )

open import Spike.Setoid    using ( module Setoids )
open import Spike.Generated using ( module Generated )

private variable α ρ ℓ ℓ′ : Level

module Rulesˢ (𝒢 : Group α ρ) (𝑰 : IrredundantEnumeration (proj₁ 𝒢)) where

  open Setoids 𝒢 𝑰 using ( G ; n ; e[_] ; set ; isSub ; _∈?_ ; _⊆?_ ; ⊈-witness )
  open Generated 𝒢 𝑰 using ( InGen ; Generators ; Adjoined ; ⟪_⟫ ; adjoin
                            ; gen⊆ ; gens∈ ; inGen-isSubgroup )

  -- H = ⟨B⟩, the certificates of every ⟨x, B⟩, and K a decidable subgroup.
  module _ (𝔹 : Generators) (cs : Adjoined (Generators.gens 𝔹)) (𝑲 : DecSubgroup 𝒢 ℓ) where

    private
      B : List G
      B = Generators.gens 𝔹
      𝑯 : DecSubgroup 𝒢 ρ
      𝑯 = ⟪ 𝔹 ⟫
      ⟨_,B⟩ : Fin n → DecSubgroup 𝒢 ρ
      ⟨ i ,B⟩ = ⟪ adjoin cs i ⟫

      H⊆⟨x,B⟩ : ∀ i → InGen B ⊆ InGen (e[ i ] ∷ B)
      H⊆⟨x,B⟩ i = gen⊆ B (InGen (e[ i ] ∷ B)) (inGen-isSubgroup (e[ i ] ∷ B))
                    (λ k → gens∈ (e[ i ] ∷ B) (suc k))

      ⟨x,B⟩⊆K : InGen B ⊆ set 𝑲 → ∀ i → e[ i ] ∈ set 𝑲 → InGen (e[ i ] ∷ B) ⊆ set 𝑲
      ⟨x,B⟩⊆K H⊆K i x∈K = gen⊆ (e[ i ] ∷ B) (set 𝑲) (isSub 𝑲)
                            (λ { zero → x∈K ; (suc k) → H⊆K (gens∈ B k) })

    -- Each element of K outside H generates K together with B.
    Generates : Type (α ⊔ ρ ⊔ ℓ)
    Generates = ∀ i → e[ i ] ∈ set 𝑲 → ¬ (e[ i ] ∈ InGen B) → set 𝑲 ⊆ InGen (e[ i ] ∷ B)

    generates? : Dec Generates
    generates? = all? (λ i → (e[ i ] ∈? 𝑲) →? (¬? (e[ i ] ∈? 𝑯) →? (𝑲 ⊆? ⟨ i ,B⟩)))

    -- Every decidable subgroup between H and K is H or K: L ⊆ H is decided,
    -- and otherwise a search finds x ∈ L outside H, and ⟨x, B⟩ ⊆ L holds K.
    between : Generates → (𝑳 : DecSubgroup 𝒢 ℓ′) → InGen B ⊆ set 𝑳 → set 𝑳 ⊆ set 𝑲
      → (set 𝑳 ≐ InGen B) ⊎ (set 𝑳 ≐ set 𝑲)
    between gen 𝑳 H⊆L L⊆K with 𝑳 ⊆? 𝑯
    ... | yes L⊆H  = inj₁ (L⊆H , H⊆L)
    ... | no L⊈H   with ⊈-witness 𝑳 𝑯 L⊈H
    ...   | i , i∈L , i∉H = inj₂ (L⊆K , λ y∈K → gen⊆ (e[ i ] ∷ B) (set 𝑳) (isSub 𝑳)
                                                    (gens⊆L i i∈L) (gen i (L⊆K i∈L) i∉H y∈K))
      where
      gens⊆L : ∀ i → e[ i ] ∈ set 𝑳 → ∀ k → lookup (e[ i ] ∷ B) k ∈ set 𝑳
      gens⊆L i i∈L zero     = i∈L
      gens⊆L i i∈L (suc k)  = H⊆L (gens∈ B k)

    -- Conversely, when H ⊆ K, the disjunction for the subgroups ⟨x, B⟩
    -- gives the condition.
    generates : InGen B ⊆ set 𝑲
      → (∀ (𝑳 : DecSubgroup 𝒢 ρ) → InGen B ⊆ set 𝑳 → set 𝑳 ⊆ set 𝑲
           → (set 𝑳 ≐ InGen B) ⊎ (set 𝑳 ≐ set 𝑲))
      → Generates
    generates H⊆K b i x∈K x∉H with b ⟨ i ,B⟩ (H⊆⟨x,B⟩ i) (⟨x,B⟩⊆K H⊆K i x∈K)
    ... | inj₁ (L⊆H , _)  = ⊥-elim (x∉H (L⊆H (gens∈ (e[ i ] ∷ B) zero)))
    ... | inj₂ (_ , K⊆L)  = K⊆L
