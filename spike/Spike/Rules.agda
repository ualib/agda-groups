{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: the second rule for the
-- types of subgroups, in both forms, and the passage between them.
--
-- +  Over tables, "every subgroup between H and K is H or K" is a
--    statement about the finitely many tables, decidable, with equality
--    of subgroups as ≡ and the disjunction harmless: a table is decided
--    data, and no table can be built from an arbitrary proposition.
-- +  Over decidable subgroups the same content is stated with inclusions
--    and a witness: "a subgroup between H and K that holds an element
--    outside H contains K".
-- +  The two forms are equivalent over a finite group, constructively.

module Spike.Rules where

open import Agda.Primitive using () renaming ( Set to Type )

open import Data.Bool.Base        using ( T )
open import Data.Bool.Properties  using ( T? ; T-irrelevant )
open import Data.Empty            using ( ⊥-elim )
open import Data.Fin.Base         using ( Fin )
open import Data.Fin.Properties   using ( all? ; any? )
open import Data.Fin.Subset       using ( Subset )
open import Data.Fin.Subset.Properties using ( anySubset? )
open import Data.Product          using ( Σ-syntax ; ∃-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base         using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Vec.Base         using ( lookup )
open import Level                 using ( Level ; 0ℓ ; _⊔_ ) renaming ( suc to lsuc )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; subst ; cong )
open import Relation.Nullary      using ( Dec ; yes ; no ; ¬_ )
open import Relation.Nullary.Decidable.Core
                                  using ( True ; map′ ; isYes ; _×?_ ; _⊎?_ ; _→?_ ; ¬?
                                        ; decidable-stable ; fromWitness )
open import Relation.Unary        using ( _∈_ ; _⊆_ )

open import Classical.Structures.Group.Basic      using ( Group )
open import Classical.Structures.Group.Subgroups  using ( DecSubgroup )
open import Setoid.Algebras.Finite.Irredundant    using ( IrredundantEnumeration )

open import Spike.Finite using ( module Tables )

private variable α ρ : Level

-- A universal statement about the subsets of Fin k is decidable when each
-- instance is (from agda-stdlib's anySubset?).
allSubset? : {k : Level} {m : _} {P : Subset m → Type k}
  → ((χ : Subset m) → Dec (P χ)) → Dec (∀ χ → P χ)
allSubset? P? = map′  (λ ¬∃ χ → decidable-stable (P? χ) (λ ¬p → ¬∃ (χ , ¬p)))
                      (λ ∀p (χ , ¬p) → ¬p (∀p χ))
                      (¬? (anySubset? (λ χ → ¬? (P? χ))))

module Rules (𝒢 : Group α ρ) (𝑰 : IrredundantEnumeration (proj₁ 𝒢)) where

  open Tables 𝒢 𝑰

  -- Inclusion of subsets of the index set, decided by a sweep.
  _⊆ᵗ_ : Subset n → Subset n → Type
  χ ⊆ᵗ ψ = ∀ i → T (lookup χ i) → T (lookup ψ i)

  _⊆ᵗ?_ : (χ ψ : Subset n) → Dec (χ ⊆ᵗ ψ)
  χ ⊆ᵗ? ψ = all? (λ i → T? (lookup χ i) →? T? (lookup ψ i))

  -- Index-wise inclusion is element-wise inclusion.
  ⊆ᵗ→⊆ : (χ ψ : Subset n) → χ ⊆ᵗ ψ → ∀ x → x ∈ᵗ χ → x ∈ᵗ ψ
  ⊆ᵗ→⊆ χ ψ χ⊆ψ x = χ⊆ψ (idx x)

  ⊆→⊆ᵗ : (χ ψ : Subset n) → (∀ x → x ∈ᵗ χ → x ∈ᵗ ψ) → χ ⊆ᵗ ψ
  ⊆→⊆ᵗ χ ψ h i t =  subst (λ j → T (lookup ψ j)) (idx-e i)
                          (h e[ i ] (subst (λ j → T (lookup χ j)) (sym (idx-e i)) t))

  ----------------------------------------------------------------------
  -- The table form: a disjunction about every subgroup table.

  -- Every subgroup between H and K is H or K.
  Between₂ : SubgroupTable → SubgroupTable → Type
  Between₂ 𝑯 𝑲 = (𝑳 : SubgroupTable) → proj₁ 𝑯 ⊆ᵗ proj₁ 𝑳 → proj₁ 𝑳 ⊆ᵗ proj₁ 𝑲 → (𝑳 ≡ 𝑯) ⊎ (𝑳 ≡ 𝑲)

  -- Quantifying over the proofs of a decided closure is quantifying over
  -- at most one proof.
  Π-True? : (χ : Subset n) {Q : True (closed? χ) → Type}
    → ((c : True (closed? χ)) → Dec (Q c)) → Dec ((c : True (closed? χ)) → Q c)
  Π-True? χ {Q} Q? with T? (isYes (closed? χ))
  ... | yes c  = map′ (λ q c′ → subst Q (T-irrelevant c c′) q) (λ f → f c) (Q? c)
  ... | no ¬c  = yes (λ c → ⊥-elim (¬c c))

  between₂? : (𝑯 𝑲 : SubgroupTable) → Dec (Between₂ 𝑯 𝑲)
  between₂? 𝑯 𝑲 = map′ (λ f (χ , c) → f χ c) (λ f χ c → f (χ , c))
    (allSubset? (λ χ → Π-True? χ (λ c →
      (proj₁ 𝑯 ⊆ᵗ? χ) →? ((χ ⊆ᵗ? proj₁ 𝑲) →? (((χ , c) ≟ᵗ 𝑯) ⊎? ((χ , c) ≟ᵗ 𝑲))))))

  ----------------------------------------------------------------------
  -- The witnessed form, over decidable subgroups of agda-algebras.

  module _ (𝑯 𝑲 : DecSubgroup 𝒢 0ℓ) where
    private
      H = proj₁ (proj₁ 𝑯)
      K = proj₁ (proj₁ 𝑲)

    -- A subgroup between H and K that holds an element outside H holds K.
    Between₂ʷ : Type (α ⊔ ρ ⊔ lsuc 0ℓ)
    Between₂ʷ = (𝑳 : DecSubgroup 𝒢 0ℓ) → H ⊆ proj₁ (proj₁ 𝑳) → proj₁ (proj₁ 𝑳) ⊆ K
      → ∀ x → x ∈ proj₁ (proj₁ 𝑳) → ¬ (x ∈ H) → K ⊆ proj₁ (proj₁ 𝑳)

    -- From the table form to the witnessed form.
    tables→witnessed : Between₂ (fromDec 𝑯) (fromDec 𝑲) → Between₂ʷ
    tables→witnessed b 𝑳 H⊆L L⊆K x x∈L x∉H {y} y∈K with b (fromDec 𝑳)
                                                           (⊆→⊆ᵗ (proj₁ (fromDec 𝑯)) (proj₁ (fromDec 𝑳)) (λ z t → ∈→∈ᵗ-table 𝑳 (H⊆L (∈ᵗ-table→∈ 𝑯 t))))
                                                           (⊆→⊆ᵗ (proj₁ (fromDec 𝑳)) (proj₁ (fromDec 𝑲)) (λ z t → ∈→∈ᵗ-table 𝑲 (L⊆K (∈ᵗ-table→∈ 𝑳 t))))
    ... | inj₁ L≡H = ⊥-elim (x∉H (∈ᵗ-table→∈ 𝑯 (subst (λ 𝑴 → x ∈ᵗ proj₁ 𝑴) L≡H (∈→∈ᵗ-table 𝑳 x∈L))))
    ... | inj₂ L≡K = ∈ᵗ-table→∈ 𝑳 (subst (λ 𝑴 → y ∈ᵗ proj₁ 𝑴) (sym L≡K) (∈→∈ᵗ-table 𝑲 y∈K))

    -- From the witnessed form to the table form: a table between H and K
    -- is inside H, or it holds an index outside H, found by a search.
    witnessed→tables : Between₂ʷ → Between₂ (fromDec 𝑯) (fromDec 𝑲)
    witnessed→tables w 𝑳@(λ⁰ , _) H⊆L L⊆K with λ⁰ ⊆ᵗ? proj₁ (fromDec 𝑯)
    ... | yes L⊆H = inj₁ (same-elements→≡ 𝑳 (fromDec 𝑯) (⊆ᵗ→⊆ λ⁰ (proj₁ (fromDec 𝑯)) L⊆H) (⊆ᵗ→⊆ (proj₁ (fromDec 𝑯)) λ⁰ H⊆L))
    ... | no L⊈H with any? (λ i → T? (lookup λ⁰ i) ×? ¬? (T? (lookup (proj₁ (fromDec 𝑯)) i)))
    ...   | no none = ⊥-elim (L⊈H (λ i t → decidable-stable (T? (lookup (proj₁ (fromDec 𝑯)) i))
                                             (λ ¬h → none (i , t , ¬h))))
    ...   | yes (i , t , ¬h) = inj₂ (same-elements→≡ 𝑳 (fromDec 𝑲) (⊆ᵗ→⊆ λ⁰ (proj₁ (fromDec 𝑲)) L⊆K) K⊆L)
      where
      -- The witness: the enumerated element at i, in L and outside H.
      x∈L : e[ i ] ∈ᵗ λ⁰
      x∈L = subst (λ j → T (lookup λ⁰ j)) (sym (idx-e i)) t
      x∉H : ¬ (e[ i ] ∈ H)
      x∉H p = ¬h (subst (λ j → T (lookup (proj₁ (fromDec 𝑯)) j)) (idx-e i) (∈→∈ᵗ-table 𝑯 p))
      K⊆L : ∀ y → y ∈ᵗ proj₁ (fromDec 𝑲) → y ∈ᵗ λ⁰
      K⊆L y t′ = w (toDec 𝑳)
                   (λ p → ⊆ᵗ→⊆ (proj₁ (fromDec 𝑯)) λ⁰ H⊆L _ (∈→∈ᵗ-table 𝑯 p))
                   (λ p → ∈ᵗ-table→∈ 𝑲 (⊆ᵗ→⊆ λ⁰ (proj₁ (fromDec 𝑲)) L⊆K _ p))
                   e[ i ] x∈L x∉H (∈ᵗ-table→∈ 𝑲 t′)
