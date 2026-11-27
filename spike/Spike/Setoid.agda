{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: the setoid route.
--
-- A subgroup is agda-algebras' DecSubgroup (a predicate with a decider of
-- its membership), and two subgroups are equal when they have the same
-- elements (≐, a pair of inclusions), which the enumeration of the group
-- decides.  The constructions below (conjugates, normalizers, indices)
-- build deciders from deciders; no table is built unless asked for, by
-- memo, which remembers a decider as a table over the enumeration.

module Spike.Setoid where

open import Agda.Primitive using () renaming ( Set to Type )

open import Data.Bool.Base        using ( Bool ; true ; false ; not ; _∨_ ; if_then_else_ )
open import Data.Empty            using ( ⊥-elim )
open import Data.Fin.Base         using ( Fin ; zero ; suc )
open import Data.Fin.Properties   using ( all? ; any? )
open import Data.List.Base        using ( List ; length ; deduplicate ) renaming ( tabulate to tabulateᴸ )
open import Data.Nat.Base         using ( ℕ ; zero ; suc ; _+_ )
open import Data.Product          using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Function              using ( _∘_ )
open import Level                 using ( Level ; 0ℓ ; _⊔_ )
open import Relation.Binary       using ( Setoid )
open import Relation.Nullary      using ( Dec ; yes ; no ; ¬_ ; does )
open import Relation.Nullary.Decidable.Core using ( map′ ; _×?_ ; _→?_ ; ¬? ; decidable-stable )
open import Relation.Unary        using ( Pred ; _∈_ ; _⊆_ ; _≐_ )

import Algebra.Properties.Group as GroupProperties

open import Classical.Bundles.Group                using ( ⟨_⟩ᵍᵖ )
open import Classical.Structures.Group.Basic       using ( Group ; module Group-Op )
open import Classical.Structures.Group.Conjugation using ( module Conjugate )
open import Classical.Structures.Group.Cosets      using ( module Coset )
open import Classical.Structures.Group.GSet        using ( module CosetAction )
open import Classical.Structures.Group.Subgroups   using ( IsSubgroup ; mkIsSubgroup ; DecSubgroup )
open import Setoid.Algebras.Basic                  using ( 𝔻[_] )
open import Setoid.Algebras.Finite.Irredundant     using ( IrredundantEnumeration
                                                         ; irredundantEnumeration )

open import Spike.Finite using ( module Tables )

private variable α ρ ℓ ℓ′ : Level

-- The number of indices at which a Boolean function holds.
count : ∀ {m} → (Fin m → Bool) → ℕ
count {zero}  f = 0
count {suc m} f = (if f zero then 1 else 0) + count (f ∘ suc)

-- Whether a Boolean function holds at some index below i.
anyBelow : ∀ {m} → Fin m → (Fin m → Bool) → Bool
anyBelow zero    p = false
anyBelow (suc i) p = p zero ∨ anyBelow i (p ∘ suc)

-- The number of classes of a relation on the indices, counted by their
-- first members: i is first when no index below it is related to it.
#classes : ∀ {m} → (Fin m → Fin m → Bool) → ℕ
#classes r = count (λ i → not (anyBelow i (λ j → r j i)))

module Setoids (𝒢 : Group α ρ) (𝑰 : IrredundantEnumeration (proj₁ 𝒢)) where

  open Tables 𝒢 𝑰 using ( G ; n ; e[_] ; idx ; idx-≈ ; toFiniteAlgebra ; SubgroupTable ; toDec
                        ; fromDec ; toDec∘fromDec ) public
  open Setoid 𝔻[ proj₁ 𝒢 ] using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Group-Op 𝒢 using ( _∙_ ; ε ; _⁻¹ ; ⁻¹-cong )
  open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ using ( ε⁻¹≈ε ; ⁻¹-involutive ; ⁻¹-anti-homo-∙ )
  open Conjugate 𝒢 using ( conj ; conj-cong ; conj-congᵍ ; conj-ε ; conj-∙-hom ; conj-⁻¹
                         ; conj-action-∙ ; conj-action-ε )

  ----------------------------------------------------------------------
  -- The projections of a decidable subgroup.

  set : DecSubgroup 𝒢 ℓ → Pred G ℓ
  set 𝑯 = proj₁ (proj₁ 𝑯)

  isSub : (𝑯 : DecSubgroup 𝒢 ℓ) → IsSubgroup 𝒢 (set 𝑯)
  isSub 𝑯 = proj₂ (proj₁ 𝑯)

  infix 4 _∈?_
  _∈?_ : ∀ x (𝑯 : DecSubgroup 𝒢 ℓ) → Dec (x ∈ set 𝑯)
  x ∈? 𝑯 = proj₂ 𝑯 x

  ----------------------------------------------------------------------
  -- Orders, inclusion and equality, decided over the enumeration.

  -- The order of a decidable subgroup: the indices its decider accepts.
  orderˢ : DecSubgroup 𝒢 ℓ → ℕ
  orderˢ 𝑯 = count (λ i → does (e[ i ] ∈? 𝑯))

  -- Inclusion is decided at the enumerated elements and carried to every
  -- element by the respects fields.
  infix 4 _⊆?_ _≐?_
  _⊆?_ : (𝑯 : DecSubgroup 𝒢 ℓ) (𝑲 : DecSubgroup 𝒢 ℓ′) → Dec (set 𝑯 ⊆ set 𝑲)
  𝑯 ⊆? 𝑲 = map′ lift (λ s i h → s h) (all? (λ i → (e[ i ] ∈? 𝑯) →? (e[ i ] ∈? 𝑲)))
    where
    lift : (∀ i → e[ i ] ∈ set 𝑯 → e[ i ] ∈ set 𝑲) → set 𝑯 ⊆ set 𝑲
    lift t {x} x∈H = IsSubgroup.respects (isSub 𝑲) (idx-≈ x)
                       (t (idx x) (IsSubgroup.respects (isSub 𝑯) (≈sym (idx-≈ x)) x∈H))

  -- Equality of subgroups is ≐, the same elements, and it is decidable.
  _≐?_ : (𝑯 : DecSubgroup 𝒢 ℓ) (𝑲 : DecSubgroup 𝒢 ℓ′) → Dec (set 𝑯 ≐ set 𝑲)
  𝑯 ≐? 𝑲 = (𝑯 ⊆? 𝑲) ×? (𝑲 ⊆? 𝑯)

  -- A failed inclusion has a witness, found by a search of the enumeration.
  ⊈-witness : (𝑳 : DecSubgroup 𝒢 ℓ) (𝑯 : DecSubgroup 𝒢 ℓ′) → ¬ (set 𝑳 ⊆ set 𝑯)
    → Σ[ i ∈ Fin n ] (e[ i ] ∈ set 𝑳 × ¬ (e[ i ] ∈ set 𝑯))
  ⊈-witness 𝑳 𝑯 L⊈H with any? (λ i → (e[ i ] ∈? 𝑳) ×? ¬? (e[ i ] ∈? 𝑯))
  ... | yes w    = w
  ... | no none  = ⊥-elim (L⊈H L⊆H)
    where
    L⊆H : set 𝑳 ⊆ set 𝑯
    L⊆H {x} x∈L = IsSubgroup.respects (isSub 𝑯) (idx-≈ x)
                    (decidable-stable (e[ idx x ] ∈? 𝑯)
                      (λ ¬h → none (idx x , IsSubgroup.respects (isSub 𝑳) (≈sym (idx-≈ x)) x∈L , ¬h)))

  ----------------------------------------------------------------------
  -- Conjugates.

  -- The preimage of H under conjugation by g, {x | g x g⁻¹ ∈ H}, that is,
  -- g⁻¹ H g; its decider asks H's.
  preˢ : G → DecSubgroup 𝒢 ℓ → DecSubgroup 𝒢 ℓ
  preˢ g 𝑯 = (P , mkIsSubgroup 𝒢 resp ∙-c ε-c ⁻¹-c) , (λ x → conj g x ∈? 𝑯)
    where
    open IsSubgroup (isSub 𝑯) using ( respects ; ∙-closed ; ε-closed ; ⁻¹-closed )
    P : Pred G _
    P x = conj g x ∈ set 𝑯
    resp : ∀ {x y} → x ≈ y → P x → P y
    resp x≈y = respects (conj-cong g x≈y)
    ∙-c : ∀ {x y} → P x → P y → P (x ∙ y)
    ∙-c {x} {y} px py = respects (≈sym (conj-∙-hom g x y)) (∙-closed px py)
    ε-c : P ε
    ε-c = respects (≈sym (conj-ε g)) ε-closed
    ⁻¹-c : ∀ {x} → P x → P (x ⁻¹)
    ⁻¹-c {x} px = respects (≈sym (conj-⁻¹ g x)) (⁻¹-closed px)

  -- The conjugate g H g⁻¹ = {x | g⁻¹ x g ∈ H}.
  conjugateˢ : G → DecSubgroup 𝒢 ℓ → DecSubgroup 𝒢 ℓ
  conjugateˢ g = preˢ (g ⁻¹)

  -- The distinct conjugates of H, deduplicated under ≐, as Spike.Counting
  -- deduplicates conjugate tables under ≡.
  conjugatesˢ : DecSubgroup 𝒢 ℓ → List (DecSubgroup 𝒢 ℓ)
  conjugatesˢ 𝑯 = deduplicate (λ 𝑲 𝑳 → 𝑲 ≐? 𝑳) (tabulateᴸ (λ i → conjugateˢ e[ i ] 𝑯))

  #conjugatesˢ : DecSubgroup 𝒢 ℓ → ℕ
  #conjugatesˢ 𝑯 = length (conjugatesˢ 𝑯)

  ----------------------------------------------------------------------
  -- Normalizers.

  -- g normalizes H: conjugation by g and by g⁻¹ maps H into H.
  Normalizes : DecSubgroup 𝒢 ℓ → Pred G (α ⊔ ℓ)
  Normalizes 𝑯 g = ∀ {x} → x ∈ set 𝑯 → (conj g x ∈ set 𝑯) × (conj (g ⁻¹) x ∈ set 𝑯)

  normalizes-isSubgroup : (𝑯 : DecSubgroup 𝒢 ℓ) → IsSubgroup 𝒢 (Normalizes 𝑯)
  normalizes-isSubgroup 𝑯 = mkIsSubgroup 𝒢 resp ∙-c ε-c ⁻¹-c
    where
    open IsSubgroup (isSub 𝑯) using ( respects )
    resp : ∀ {g h} → g ≈ h → Normalizes 𝑯 g → Normalizes 𝑯 h
    resp {g} {h} g≈h N {x} x∈H =  respects (conj-congᵍ x g≈h) (proj₁ (N x∈H))
                               ,  respects (conj-congᵍ x (⁻¹-cong g≈h)) (proj₂ (N x∈H))
    ∙-c : ∀ {g h} → Normalizes 𝑯 g → Normalizes 𝑯 h → Normalizes 𝑯 (g ∙ h)
    ∙-c {g} {h} Ng Nh {x} x∈H =
         respects (≈sym (conj-action-∙ g h x)) (proj₁ (Ng (proj₁ (Nh x∈H))))
      ,  respects (≈sym (≈trans (conj-congᵍ x (⁻¹-anti-homo-∙ g h)) (conj-action-∙ (h ⁻¹) (g ⁻¹) x)))
                  (proj₂ (Nh (proj₂ (Ng x∈H))))
    ε-c : Normalizes 𝑯 ε
    ε-c {x} x∈H =  respects (≈sym (conj-action-ε x)) x∈H
                ,  respects (≈sym (≈trans (conj-congᵍ x ε⁻¹≈ε) (conj-action-ε x))) x∈H
    ⁻¹-c : ∀ {g} → Normalizes 𝑯 g → Normalizes 𝑯 (g ⁻¹)
    ⁻¹-c {g} Ng {x} x∈H =  proj₂ (Ng x∈H)
                        ,  respects (≈sym (conj-congᵍ x (⁻¹-involutive g))) (proj₁ (Ng x∈H))

  -- The textbook decider: test every enumerated element of H.
  normalizes? : (𝑯 : DecSubgroup 𝒢 ℓ) → ∀ g → Dec (Normalizes 𝑯 g)
  normalizes? 𝑯 g = map′ lift (λ N i h → N h)
    (all? (λ i → (e[ i ] ∈? 𝑯) →? ((conj g e[ i ] ∈? 𝑯) ×? (conj (g ⁻¹) e[ i ] ∈? 𝑯))))
    where
    open IsSubgroup (isSub 𝑯) using ( respects )
    lift : (∀ i → e[ i ] ∈ set 𝑯 → (conj g e[ i ] ∈ set 𝑯) × (conj (g ⁻¹) e[ i ] ∈ set 𝑯))
      → Normalizes 𝑯 g
    lift t {x} x∈H with t (idx x) (respects (≈sym (idx-≈ x)) x∈H)
    ... | p , q = respects (conj-cong g (idx-≈ x)) p , respects (conj-cong (g ⁻¹) (idx-≈ x)) q

  normalizerˢ : DecSubgroup 𝒢 ℓ → DecSubgroup 𝒢 (α ⊔ ℓ)
  normalizerˢ 𝑯 = (Normalizes 𝑯 , normalizes-isSubgroup 𝑯) , normalizes? 𝑯

  ----------------------------------------------------------------------
  -- Indices, and a decider remembered as a table.

  -- The index of K: its left cosets x K, counted by their first members
  -- (x K = y K exactly when x⁻¹ y ∈ K).
  indexˢ : DecSubgroup 𝒢 ℓ → ℕ
  indexˢ 𝑲 = #classes (λ j i → does ((e[ j ] ⁻¹ ∙ e[ i ]) ∈? 𝑲))

  -- The index as the size of agda-algebras' coset space G/K, whose
  -- finiteness witness is the enumeration of G with K's decider.
  indexᶜ : DecSubgroup 𝒢 ℓ → ℕ
  indexᶜ 𝑲 = IrredundantEnumeration.icard (irredundantEnumeration cosetsFinite)
    where
    open Coset 𝒢 (set 𝑲) (isSub 𝑲) using ( ∼-dec )
    open CosetAction 𝒢 (set 𝑲) (isSub 𝑲) using ( cosetAlgebra-FiniteAlgebra )
    cosetsFinite = cosetAlgebra-FiniteAlgebra toFiniteAlgebra (∼-dec (proj₂ 𝑲))

  -- The same subgroup with its decider remembered as a table over the
  -- enumeration (toDec∘fromDec gives set (memo H) ≐ set H): a decider is a
  -- function, and Agda does not remember what a function has answered.
  memo : DecSubgroup 𝒢 ℓ → DecSubgroup 𝒢 0ℓ
  memo 𝑯 = toDec (fromDec 𝑯)

  memo-≐ : (𝑯 : DecSubgroup 𝒢 ℓ) → set (memo 𝑯) ≐ set 𝑯
  memo-≐ = toDec∘fromDec
