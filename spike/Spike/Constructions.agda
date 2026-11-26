{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: two constructions that
-- must stay inside the notion of finite group.
--
-- +  A subgroup (a table) of a finite group is a finite group: an
--    agda-algebras Group on the subtype, with a surjective enumeration of
--    the same size as the parent's (the indices outside the subgroup go to
--    the identity), from which agda-algebras' deduplication computes the
--    order.
-- +  The quotient G/N by a normal subgroup (a table) is a finite group: an
--    agda-algebras Group on the same carrier with the coarser equality of
--    the normal subgroup's congruence, with G's own enumeration, so that no
--    representative is chosen until the order is counted.

module Spike.Constructions where

open import Agda.Primitive using () renaming ( Set to Type )

open import Data.Bool.Base        using ( T )
open import Data.Bool.Properties  using ( T? )
open import Data.Empty            using ( ⊥-elim )
open import Data.Fin.Base         using ( Fin )
open import Data.Fin.Properties   using ( all? )
open import Data.Fin.Subset       using ( Subset )
open import Data.Product          using ( Σ-syntax ; _,_ ; proj₁ ; proj₂ )
open import Data.Vec.Base         using ( lookup )
open import Level                 using ( Level ; 0ℓ ; _⊔_ )
open import Relation.Binary       using ( Setoid )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; subst )
open import Relation.Nullary      using ( Dec ; yes ; no )
open import Relation.Nullary.Decidable.Core using ( True ; toWitness ; map′ ; _→?_ )

open import Classical.Structures.Group.Basic        using ( Group ; module Group-Op ; setoidEqsToGroup )
open import Classical.Structures.Group.Subgroups    using ( IsSubgroup )
open import Classical.Structures.Group.Congruences  using ( module GroupCongruences )
open import Classical.Structures.Group.Conjugation  using ( module Conjugate )
open import Setoid.Algebras.Basic                   using ( 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite                  using ( FiniteAlgebra )
open import Setoid.Algebras.Finite.Irredundant      using ( IrredundantEnumeration
                                                          ; irredundantEnumeration )

open import Spike.Finite using ( module Tables )

private variable α ρ : Level

module Constructions (𝒢 : Group α ρ) (𝑰 : IrredundantEnumeration (proj₁ 𝒢)) where

  open Tables 𝒢 𝑰
  open Setoid 𝔻[ proj₁ 𝒢 ]  using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Group-Op 𝒢  using  ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; ⁻¹-cong
                          ; assoc-law ; idˡ-law ; idʳ-law ; invˡ-law ; invʳ-law )

  ----------------------------------------------------------------------
  -- A subgroup as a finite group.

  module AsGroup (𝑯 : SubgroupTable) where
    private
      χ = proj₁ 𝑯
    open IsSubgroup (∈ᵗ-isSubgroup 𝑯) using ( ∙-closed ; ε-closed ; ⁻¹-closed )

    -- The carrier: the elements of H, compared in G.
    H-setoid : Setoid α ρ
    H-setoid = record
      { Carrier        = Σ[ x ∈ G ] x ∈ᵗ χ
      ; _≈_            = λ a b → proj₁ a ≈ proj₁ b
      ; isEquivalence  = record { refl = ≈refl ; sym = ≈sym ; trans = ≈trans } }

    H-group : Group α ρ
    H-group = setoidEqsToGroup H-setoid
      (λ (x , p) (y , q) → x ∙ y , ∙-closed p q) (ε , ε-closed) (λ (x , p) → x ⁻¹ , ⁻¹-closed p)
      ∙-cong ⁻¹-cong
      (λ a b c → assoc-law (proj₁ a) (proj₁ b) (proj₁ c))
      (λ a → idˡ-law (proj₁ a)) (λ a → idʳ-law (proj₁ a))
      (λ a → invˡ-law (proj₁ a)) (λ a → invʳ-law (proj₁ a))

    -- An index of G names its element when that is in H, and the identity
    -- otherwise: a surjective enumeration of H by Fin n, with repetitions.
    pick : (i : Fin n) → Dec (T (lookup χ i)) → Σ[ x ∈ G ] x ∈ᵗ χ
    pick i (yes t)  = e[ i ] , subst (λ j → T (lookup χ j)) (sym (idx-e i)) t
    pick i (no _)   = ε , ε-closed

    pick-≈ : (i : Fin n) (d : Dec (T (lookup χ i))) → T (lookup χ i) → proj₁ (pick i d) ≈ e[ i ]
    pick-≈ i (yes _)  _ = ≈refl
    pick-≈ i (no ¬t)  t = ⊥-elim (¬t t)

    H-finite : FiniteAlgebra (proj₁ H-group)
    H-finite = record
      { _≟_       = λ a b → proj₁ a ≟ proj₁ b
      ; card      = n
      ; enum      = λ i → pick i (T? (lookup χ i))
      ; enum-sur  = λ (x , p) → idx x , ≈trans (pick-≈ (idx x) (T? (lookup χ (idx x))) p) (idx-≈ x) }

    -- The order of H as a finite group in its own right.
    H-order : _
    H-order = IrredundantEnumeration.icard (irredundantEnumeration H-finite)

  ----------------------------------------------------------------------
  -- The quotient by a normal subgroup as a finite group.

  open Conjugate 𝒢 using ( IsNormal )

  -- Normality of a table, decided by a sweep: conjugates of members by
  -- every enumerated element are members.
  Normalᵗ : Subset n → Type
  Normalᵗ χ = ∀ g i → T (lookup χ i) → T (lookup χ (idx (e[ g ] ∙ e[ i ] ∙ e[ g ] ⁻¹)))

  normal? : (χ : Subset n) → Dec (Normalᵗ χ)
  normal? χ = all? (λ g → all? (λ i → T? (lookup χ i) →? T? (lookup χ (idx (e[ g ] ∙ e[ i ] ∙ e[ g ] ⁻¹)))))

  module Quotient (𝑵 : SubgroupTable) (nrm : True (normal? (proj₁ 𝑵))) where
    private
      χ = proj₁ 𝑵

    isNormal : IsNormal (_∈ᵗ χ)
    isNormal g {x} p = ∈ᵗ-resp χ eq (toWitness nrm (idx g) (idx x) p)
      where
      eq : e[ idx g ] ∙ e[ idx x ] ∙ e[ idx g ] ⁻¹ ≈ g ∙ x ∙ g ⁻¹
      eq = ∙-cong (∙-cong (idx-≈ g) (idx-≈ x)) (⁻¹-cong (idx-≈ g))

    open GroupCongruences 𝒢 using ( NormalSubgroup ; module NormalCon )
    𝑵ⁿ : NormalSubgroup 0ℓ
    𝑵ⁿ = (_∈ᵗ χ) , ∈ᵗ-isSubgroup 𝑵 , isNormal
    open NormalCon 𝑵ⁿ using ( _∼_ ; ∼-isEquivalence ; ∼-∙ ; ∼-⁻¹ ; ≈⇒∼ )

    -- G/N: the carrier of G under the congruence of N.
    quotient-setoid : Setoid α 0ℓ
    quotient-setoid = record { Carrier = G ; _≈_ = _∼_ ; isEquivalence = ∼-isEquivalence }

    quotient-group : Group α 0ℓ
    quotient-group = setoidEqsToGroup quotient-setoid _∙_ ε _⁻¹ ∼-∙ ∼-⁻¹
      (λ a b c → ≈⇒∼ (assoc-law a b c)) (λ a → ≈⇒∼ (idˡ-law a)) (λ a → ≈⇒∼ (idʳ-law a))
      (λ a → ≈⇒∼ (invˡ-law a)) (λ a → ≈⇒∼ (invʳ-law a))

    -- Finite with G's own enumeration: equality is decided by one lookup.
    quotient-finite : FiniteAlgebra (proj₁ quotient-group)
    quotient-finite = record
      { _≟_       = λ x y → T? (lookup χ (idx (x ∙ y ⁻¹)))
      ; card      = n
      ; enum      = e[_]
      ; enum-sur  = λ x → idx x , ≈⇒∼ (idx-≈ x) }

    -- |G/N|, computed by deduplicating G's enumeration under the congruence.
    quotient-order : _
    quotient-order = IrredundantEnumeration.icard (irredundantEnumeration quotient-finite)
