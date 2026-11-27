{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: the candidate notions of
-- a finite group and of its subgroups, on agda-algebras' Group.
--
-- A finite group is an agda-algebras Group with an irredundant enumeration
-- of its carrier (a bijection, up to the setoid equality, with Fin n), in
-- the sense of Setoid.Algebras.Finite.Irredundant.  The enumeration either
-- comes from a FiniteAlgebra witness (decidable equality and a surjective
-- enumeration) by agda-algebras' deduplication, or is given directly.
--
-- Subgroups come in two forms: agda-algebras' DecSubgroup (a predicate
-- with a decider), and tables (a Subset of the index set Fin n, with a
-- Boolean closure check), with the passage between them.

module Spike.Finite where

open import Agda.Primitive using () renaming ( Set to Type )

open import Data.Bool.Base        using ( Bool ; true ; false ; T ; _∧_ )
open import Data.Bool.Properties  using ( T? ; T-irrelevant ) renaming ( _≟_ to _≟ᵇ_ )
open import Data.Empty            using ( ⊥-elim )
open import Data.Fin.Base         using ( Fin )
open import Data.Fin.Properties   using ( all? ; any? ) renaming ( _≟_ to _≟ᶠ_ )
open import Data.Fin.Subset       using ( Subset ; ∣_∣ ) renaming ( _⊆_ to _⊆ˢ_ )
open import Data.Fin.Subset.Properties using ( _⊆?_ )
open import Data.List.Base        using ( List ; [] ; _∷_ ; length ; deduplicate ; _++_ ; map ; filter )
                                  renaming ( tabulate to tabulateᴸ )
open import Data.Nat.Base         using ( ℕ ; zero ; suc )
open import Data.Product          using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ ; ∃-syntax )
open import Data.Sum.Base         using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Vec.Base         using ( Vec ; [] ; _∷_ ; lookup ; tabulate )
open import Data.Vec.Properties   using ( lookup∘tabulate ; tabulate∘lookup ; tabulate-cong
                                        ; ≡-dec ; lookup⇒[]= ; []=⇒lookup )
open import Function              using ( _∘_ ; Func )
open import Level                 using ( Level ; 0ℓ ; _⊔_ ) renaming ( suc to lsuc )
open import Relation.Binary       using ( Setoid ; DecidableEquality )
open import Relation.Binary.PropositionalEquality
                                  using ( _≡_ ; refl ; sym ; trans ; cong ; subst ; _≢_ )
open import Relation.Nullary      using ( Dec ; yes ; no ; ¬_ ; does )
open import Relation.Nullary.Decidable.Core
                                  using ( True ; toWitness ; fromWitness ; map′ ; isYes
                                        ; _×?_ ; _⊎?_ ; _→?_ ; ¬? )
open import Relation.Unary        using ( Pred ; _∈_ ; _⊆_ ; _≐_ )

open import Classical.Structures.Group.Basic      using ( Group ; module Group-Op )
open import Classical.Structures.Group.Subgroups  using ( IsSubgroup ; mkIsSubgroup
                                                        ; Subgroup ; DecSubgroup )
open import Setoid.Algebras.Basic                 using ( Algebra ; 𝕌[_] ; 𝔻[_] )
open import Setoid.Algebras.Finite                using ( FiniteAlgebra )
open import Setoid.Algebras.Finite.Irredundant    using ( IrredundantEnumeration
                                                        ; irredundantEnumeration )

private variable α ρ ℓ : Level

------------------------------------------------------------------------
-- The two candidate records for a finite group.

-- Candidate A: a Group with agda-algebras' finiteness witness.
record FiniteGroupᶠ (α ρ : Level) : Type (lsuc (α ⊔ ρ)) where
  field
    group   : Group α ρ
    finite  : FiniteAlgebra (proj₁ group)

  irredundant : IrredundantEnumeration (proj₁ group)
  irredundant = irredundantEnumeration finite

-- Candidate A': a Group with an irredundant enumeration given directly
-- (a finite set in the sense of Mines, Richman and Ruitenburg).
record FiniteGroupⁱ (α ρ : Level) : Type (lsuc (α ⊔ ρ)) where
  field
    group        : Group α ρ
    irredundant  : IrredundantEnumeration (proj₁ group)

fromFiniteAlgebra : FiniteGroupᶠ α ρ → FiniteGroupⁱ α ρ
fromFiniteAlgebra 𝑭 = record  { group = FiniteGroupᶠ.group 𝑭
                              ; irredundant = FiniteGroupᶠ.irredundant 𝑭 }

------------------------------------------------------------------------
-- Everything below is relative to a group and an irredundant enumeration.

module Tables (𝒢 : Group α ρ) (𝑰 : IrredundantEnumeration (proj₁ 𝒢)) where

  private
    𝑮 = proj₁ 𝒢
  G : Type α
  G = 𝕌[ 𝑮 ]

  open Setoid 𝔻[ 𝑮 ]  using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Group-Op 𝒢     using ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; ⁻¹-cong )
  open IrredundantEnumeration 𝑰 renaming ( icard to n ; ienum[_] to e[_] ) public

  -- The order of the group.
  order : ℕ
  order = n

  -- The index map, and its laws.
  idx : G → Fin n
  idx x = proj₁ (ienum-sur x)

  idx-≈ : ∀ x → e[ idx x ] ≈ x
  idx-≈ x = proj₂ (ienum-sur x)

  idx-cong : ∀ {x y} → x ≈ y → idx x ≡ idx y
  idx-cong {x} {y} x≈y = ienum-inj (≈trans (idx-≈ x) (≈trans x≈y (≈sym (idx-≈ y))))

  idx-e : ∀ i → idx e[ i ] ≡ i
  idx-e i = ienum-inj (idx-≈ e[ i ])

  -- Decidable equality follows from the enumeration.
  _≟_ : ∀ x y → Dec (x ≈ y)
  x ≟ y = map′ to from (idx x ≟ᶠ idx y)
    where
    to : idx x ≡ idx y → x ≈ y
    to eq = ≈trans (≈sym (idx-≈ x)) (subst (λ i → e[ i ] ≈ y) (sym eq) (idx-≈ y))
    from : x ≈ y → idx x ≡ idx y
    from = idx-cong

  -- The FiniteAlgebra witness that the enumeration gives back.
  toFiniteAlgebra : FiniteAlgebra 𝑮
  toFiniteAlgebra = record { _≟_ = _≟_ ; card = n ; enum = e[_] ; enum-sur = ienum-sur }

  ----------------------------------------------------------------------
  -- Decidable subgroups (agda-algebras) and their orders.

  module _ (𝑯 : DecSubgroup 𝒢 ℓ) where
    private
      H = proj₁ (proj₁ 𝑯)
      H? = proj₂ 𝑯

    -- The table of a decidable subgroup: its decisions on the enumeration.
    table : Subset n
    table = tabulate (λ i → isYes (H? e[ i ]))

    -- The order of a decidable subgroup: the number of indices it holds.
    orderᵈ : ℕ
    orderᵈ = ∣ table ∣

  ----------------------------------------------------------------------
  -- Tables: membership, the closure check, and subgroups as tables.

  -- Membership in a table, through the index map.
  _∈ᵗ_ : G → Subset n → Type
  x ∈ᵗ χ = T (lookup χ (idx x))

  ∈ᵗ-resp : (χ : Subset n) {x y : G} → x ≈ y → x ∈ᵗ χ → y ∈ᵗ χ
  ∈ᵗ-resp χ x≈y = subst (λ i → T (lookup χ i)) (idx-cong x≈y)

  -- The closure conditions, stated on indices, and their decision.
  Closed : Subset n → Type
  Closed χ =  T (lookup χ (idx ε))
           ×  (∀ i j → T (lookup χ i) → T (lookup χ j) → T (lookup χ (idx (e[ i ] ∙ e[ j ]))))
           ×  (∀ i → T (lookup χ i) → T (lookup χ (idx (e[ i ] ⁻¹))))

  closed? : (χ : Subset n) → Dec (Closed χ)
  closed? χ =       T? (lookup χ (idx ε))
            ×?  all? (λ i → all? (λ j → T? (lookup χ i) →? (T? (lookup χ j)
                                            →? T? (lookup χ (idx (e[ i ] ∙ e[ j ]))))))
            ×?  all? (λ i → T? (lookup χ i) →? T? (lookup χ (idx (e[ i ] ⁻¹))))

  -- A subgroup as a table: a subset of the index set with a proof of its
  -- closure that is a T of a Boolean, so that any two proofs are equal.
  SubgroupTable : Type
  SubgroupTable = Σ[ χ ∈ Subset n ] True (closed? χ)

  -- Equality of subgroup tables is equality of their subsets ...
  ≡-of-subsets : {𝑯 𝑲 : SubgroupTable} → proj₁ 𝑯 ≡ proj₁ 𝑲 → 𝑯 ≡ 𝑲
  ≡-of-subsets {χ , c} {.χ , d} refl = cong (χ ,_) (T-irrelevant c d)

  -- ... and it is decidable.
  _≟ᵗ_ : DecidableEquality SubgroupTable
  𝑯 ≟ᵗ 𝑲 = map′ ≡-of-subsets (cong proj₁) (≡-dec _≟ᵇ_ (proj₁ 𝑯) (proj₁ 𝑲))

  -- The order of a subgroup table.
  orderᵗ : SubgroupTable → ℕ
  orderᵗ 𝑯 = ∣ proj₁ 𝑯 ∣

  -- From a table to a decidable subgroup of agda-algebras.
  module _ ((χ , c) : SubgroupTable) where
    private
      cl : Closed χ
      cl = toWitness c

    ∈ᵗ-isSubgroup : IsSubgroup 𝒢 (_∈ᵗ χ)
    ∈ᵗ-isSubgroup = mkIsSubgroup 𝒢 (∈ᵗ-resp χ) ∙-c (proj₁ cl) ⁻¹-c
      where
      ∙-c : ∀ {x y} → x ∈ᵗ χ → y ∈ᵗ χ → (x ∙ y) ∈ᵗ χ
      ∙-c {x} {y} px py = ∈ᵗ-resp χ (∙-cong (idx-≈ x) (idx-≈ y))
                            (proj₁ (proj₂ cl) (idx x) (idx y) px py)
      ⁻¹-c : ∀ {x} → x ∈ᵗ χ → (x ⁻¹) ∈ᵗ χ
      ⁻¹-c {x} px = ∈ᵗ-resp χ (⁻¹-cong (idx-≈ x)) (proj₂ (proj₂ cl) (idx x) px)

  toDec : SubgroupTable → DecSubgroup 𝒢 0ℓ
  toDec 𝑯@(χ , _) = ((_∈ᵗ χ) , ∈ᵗ-isSubgroup 𝑯) , (λ x → T? (lookup χ (idx x)))

  -- From a decidable subgroup to a table.
  module _ (𝑯 : DecSubgroup 𝒢 ℓ) where
    private
      H = proj₁ (proj₁ 𝑯)
      H-sg = proj₂ (proj₁ 𝑯)
      H? = proj₂ 𝑯
    open IsSubgroup H-sg using ( respects ; ∙-closed ; ε-closed ; ⁻¹-closed )

    -- A table entry is true exactly when the enumerated element is in H.
    table-true : ∀ i → T (lookup (table 𝑯) i) → e[ i ] ∈ H
    table-true i t = toWitness {a? = H? e[ i ]} (subst T (lookup∘tabulate _ i) t)

    true-table : ∀ i → e[ i ] ∈ H → T (lookup (table 𝑯) i)
    true-table i p = subst T (sym (lookup∘tabulate _ i)) (fromWitness {a? = H? e[ i ]} p)

    -- The table's membership is H's.
    ∈ᵗ-table→∈ : ∀ {x} → x ∈ᵗ table 𝑯 → x ∈ H
    ∈ᵗ-table→∈ {x} t = respects (idx-≈ x) (table-true (idx x) t)

    ∈→∈ᵗ-table : ∀ {x} → x ∈ H → x ∈ᵗ table 𝑯
    ∈→∈ᵗ-table {x} p = true-table (idx x) (respects (≈sym (idx-≈ x)) p)

    table-closed : Closed (table 𝑯)
    table-closed =  ∈→∈ᵗ-table ε-closed
                 ,  (λ i j ti tj → ∈→∈ᵗ-table (∙-closed (table-true i ti) (table-true j tj)))
                 ,  (λ i ti → ∈→∈ᵗ-table (⁻¹-closed (table-true i ti)))

    fromDec : SubgroupTable
    fromDec = table 𝑯 , fromWitness table-closed

    -- The round trip from H is H, as a predicate (two inclusions).
    toDec∘fromDec : proj₁ (proj₁ (toDec fromDec)) ≐ H
    toDec∘fromDec = ∈ᵗ-table→∈ , ∈→∈ᵗ-table

  isYes-T? : ∀ b → isYes (T? b) ≡ b
  isYes-T? false = refl
  isYes-T? true  = refl

  -- The round trip from a table is the table itself, propositionally.
  fromDec∘toDec : (𝑯 : SubgroupTable) → fromDec (toDec 𝑯) ≡ 𝑯
  fromDec∘toDec 𝑯@(χ , c) = ≡-of-subsets (trans (tabulate-cong pt) (tabulate∘lookup χ))
    where
    pt : ∀ i → isYes (T? (lookup χ (idx e[ i ]))) ≡ lookup χ i
    pt i = trans (isYes-T? (lookup χ (idx e[ i ]))) (cong (lookup χ) (idx-e i))

  ----------------------------------------------------------------------
  -- The first rule: subgroups with the same elements.

  -- Two Booleans with the same truth are equal.
  T-ext : ∀ {b c} → (T b → T c) → (T c → T b) → b ≡ c
  T-ext {false} {false} _ _ = refl
  T-ext {false} {true}  _ g = ⊥-elim (g _)
  T-ext {true}  {false} f _ = ⊥-elim (f _)
  T-ext {true}  {true}  _ _ = refl

  -- Two subgroup tables with the same elements are equal, with no axiom.
  same-elements→≡ : (𝑯 𝑲 : SubgroupTable)
    → (∀ x → x ∈ᵗ proj₁ 𝑯 → x ∈ᵗ proj₁ 𝑲) → (∀ x → x ∈ᵗ proj₁ 𝑲 → x ∈ᵗ proj₁ 𝑯) → 𝑯 ≡ 𝑲
  same-elements→≡ (χ , _) (ψ , _) H⊆K K⊆H = ≡-of-subsets
    (trans (sym (tabulate∘lookup χ)) (trans (tabulate-cong pt) (tabulate∘lookup ψ)))
    where
    at : ∀ i → T (lookup χ i) → T (lookup ψ i)
    at i t = subst (λ j → T (lookup ψ j)) (idx-e i)
               (H⊆K e[ i ] (subst (λ j → T (lookup χ j)) (sym (idx-e i)) t))
    ta : ∀ i → T (lookup ψ i) → T (lookup χ i)
    ta i t = subst (λ j → T (lookup χ j)) (idx-e i)
               (K⊆H e[ i ] (subst (λ j → T (lookup ψ j)) (sym (idx-e i)) t))
    pt : ∀ i → lookup χ i ≡ lookup ψ i
    pt i = T-ext (at i) (ta i)

  -- For decidable subgroups the first rule reads: the same elements (two
  -- inclusions) exactly when the tables are equal.
  module _ (𝑯 : DecSubgroup 𝒢 ℓ) (𝑲 : DecSubgroup 𝒢 ℓ) where
    private
      H = proj₁ (proj₁ 𝑯)
      K = proj₁ (proj₁ 𝑲)

    ≐→table≡ : H ≐ K → fromDec 𝑯 ≡ fromDec 𝑲
    ≐→table≡ (H⊆K , K⊆H) = same-elements→≡ (fromDec 𝑯) (fromDec 𝑲)
      (λ x t → ∈→∈ᵗ-table 𝑲 (H⊆K (∈ᵗ-table→∈ 𝑯 t)))
      (λ x t → ∈→∈ᵗ-table 𝑯 (K⊆H (∈ᵗ-table→∈ 𝑲 t)))

    table≡→≐ : fromDec 𝑯 ≡ fromDec 𝑲 → H ≐ K
    table≡→≐ eq =  (λ {x} p → ∈ᵗ-table→∈ 𝑲 (subst (λ 𝑳 → x ∈ᵗ proj₁ 𝑳) eq (∈→∈ᵗ-table 𝑯 p)))
                ,  (λ {x} p → ∈ᵗ-table→∈ 𝑯 (subst (λ 𝑳 → x ∈ᵗ proj₁ 𝑳) (sym eq) (∈→∈ᵗ-table 𝑲 p)))

    -- So the equality of two decidable subgroups of a finite group is
    -- decidable, though it is a pair of inclusions.
    ≐? : Dec (H ≐ K)
    ≐? = map′ table≡→≐ ≐→table≡ (fromDec 𝑯 ≟ᵗ fromDec 𝑲)
