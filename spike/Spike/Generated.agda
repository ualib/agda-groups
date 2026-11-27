{-# OPTIONS --without-K --exact-split --safe #-}

-- Spike for ADR 0001 (issue 5), not library code: subgroups given by
-- generators, as GAP gives them (Subgroup(G, gens)), on the setoid route.
--
-- +  x lies in ⟨A⟩ when some word in the generators and their inverses
--    evaluates to x: the predicate is the inductive definition, and a
--    proof of membership carries its word.
-- +  The decider reads a Schreier vector: for each index of the group,
--    a word reaching it, or nothing.  A breadth-first search computes the
--    vector, as GAP's orbit algorithm does, and three checks make it a
--    certificate (the identity is reached, the reached indices are closed
--    under every letter, and every word evaluates to its index); a
--    concrete group discharges them by evaluation, so nothing rests on
--    the search being right.
-- +  Inclusion, the normalizer and the equality of conjugates are decided
--    by testing the generators alone, from the universal property of ⟨A⟩
--    (a subgroup holding A holds ⟨A⟩).

module Spike.Generated where

open import Agda.Primitive using () renaming ( Set to Type )

open import Data.Bool.Base        using ( Bool ; true ; false ; T )
open import Data.Bool.Properties  using ( T? )
open import Data.Fin.Base         using ( Fin )
open import Data.Fin.Properties   using ( all? )
open import Data.List.Base        using ( List ; [] ; _∷_ ; _++_ ; length ; lookup ; map ; allFin
                                        ; deduplicate ; filter ) renaming ( tabulate to tabulateᴸ )
open import Data.Nat.Properties   using () renaming ( _≟_ to _≟ⁿ_ )
open import Data.Maybe.Base       using ( Maybe ; just ; nothing ; is-just )
open import Data.Nat.Base         using ( ℕ ; zero ; suc )
open import Data.Product          using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Unit.Polymorphic using ( ⊤ ; tt )
open import Data.Vec.Base         using ( Vec ; replicate ) renaming ( lookup to lookupᵛ ; _[_]≔_ to _[_]≔ᵛ_ )
open import Level                 using ( Level ; _⊔_ )
open import Relation.Binary       using ( Setoid )
open import Relation.Binary.PropositionalEquality using ( subst )
open import Relation.Nullary      using ( Dec ; yes ; no )
open import Relation.Nullary.Decidable.Core using ( True ; toWitness ; map′ ; _×?_ ; _→?_ )
open import Relation.Unary        using ( Pred ; _∈_ ; _⊆_ ; _≐_ )

import Algebra.Properties.Group as GroupProperties

open import Classical.Bundles.Group                using ( ⟨_⟩ᵍᵖ )
open import Classical.Structures.Group.Basic       using ( Group ; module Group-Op )
open import Classical.Structures.Group.Conjugation using ( module Conjugate )
open import Classical.Structures.Group.Subgroups   using ( IsSubgroup ; mkIsSubgroup ; DecSubgroup )
open import Setoid.Algebras.Basic                  using ( 𝔻[_] )
open import Setoid.Algebras.Finite.Irredundant     using ( IrredundantEnumeration )

open import Spike.Finite using ( module Tables )
open import Spike.Setoid using ( module Setoids )

private variable α ρ ℓ : Level

module Generated (𝒢 : Group α ρ) (𝑰 : IrredundantEnumeration (proj₁ 𝒢)) where

  open Tables 𝒢 𝑰 using ( G ; n ; e[_] ; idx ; idx-≈ ; idx-cong ; _≟_ )
  open Setoids 𝒢 𝑰 using ( set ; isSub ; _∈?_ ; orderˢ ; preˢ ; conjugateˢ ; Normalizes
                          ; normalizes-isSubgroup )
  open Setoid 𝔻[ proj₁ 𝒢 ] using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym ; trans to ≈trans )
  open Group-Op 𝒢 using ( _∙_ ; ε ; _⁻¹ ; ∙-cong ; ⁻¹-cong ; assoc-law ; idˡ-law ; idʳ-law )
  open GroupProperties ⟨ 𝒢 ⟩ᵍᵖ using ( ε⁻¹≈ε ; ⁻¹-involutive ; ⁻¹-anti-homo-∙ )
  open Conjugate 𝒢 using ( conj ; conj-conj⁻¹ ; conj⁻¹-conj )

  -- Everything about one list A of generators.
  module Words (A : List G) where

    ----------------------------------------------------------------------
    -- Words in the generators and their inverses.

    -- A letter is a generator (true) or its inverse (false).
    Letter : Type
    Letter = Fin (length A) × Bool

    letter : Letter → G
    letter (k , true)   = lookup A k
    letter (k , false)  = lookup A k ⁻¹

    flip : Letter → Letter
    flip (k , true)   = k , false
    flip (k , false)  = k , true

    Word : Type
    Word = List Letter

    -- The head of a word is its last letter: l ∷ w is w followed by l.
    eval : Word → G
    eval []       = ε
    eval (l ∷ w)  = eval w ∙ letter l

    eval-++ : (v w : Word) → eval (v ++ w) ≈ eval w ∙ eval v
    eval-++ []       w = ≈sym (idʳ-law (eval w))
    eval-++ (l ∷ v)  w = ≈trans (∙-cong (eval-++ v w) ≈refl) (assoc-law (eval w) (eval v) (letter l))

    letter-flip : (l : Letter) → letter (flip l) ≈ letter l ⁻¹
    letter-flip (k , true)   = ≈refl
    letter-flip (k , false)  = ≈sym (⁻¹-involutive _)

    -- The inverse of a word: its letters flipped, in the opposite order.
    inverse : Word → Word
    inverse []       = []
    inverse (l ∷ w)  = inverse w ++ (flip l ∷ [])

    eval-inverse : (w : Word) → eval (inverse w) ≈ eval w ⁻¹
    eval-inverse []       = ≈sym ε⁻¹≈ε
    eval-inverse (l ∷ w)  =
      ≈trans (eval-++ (inverse w) (flip l ∷ []))
        (≈trans (∙-cong (≈trans (idˡ-law _) (letter-flip l)) (eval-inverse w))
                (≈sym (⁻¹-anti-homo-∙ (eval w) (letter l))))

    ----------------------------------------------------------------------
    -- The generated subgroup, as a predicate.

    InGen : Pred G ρ
    InGen x = Σ[ w ∈ Word ] (eval w ≈ x)

    inGen-isSubgroup : IsSubgroup 𝒢 InGen
    inGen-isSubgroup = mkIsSubgroup 𝒢 resp ∙-c ([] , ≈refl) ⁻¹-c
      where
      resp : ∀ {x y} → x ≈ y → InGen x → InGen y
      resp x≈y (w , p) = w , ≈trans p x≈y
      ∙-c : ∀ {x y} → InGen x → InGen y → InGen (x ∙ y)
      ∙-c (w , p) (v , q) = (v ++ w) , ≈trans (eval-++ v w) (∙-cong p q)
      ⁻¹-c : ∀ {x} → InGen x → InGen (x ⁻¹)
      ⁻¹-c (w , p) = inverse w , ≈trans (eval-inverse w) (⁻¹-cong p)

    -- Each generator lies in ⟨A⟩, as a word of one letter.
    gens∈ : (k : Fin (length A)) → lookup A k ∈ InGen
    gens∈ k = ((k , true) ∷ []) , idˡ-law (lookup A k)

    -- The universal property: a subgroup holding A holds ⟨A⟩.
    gen⊆ : (K : Pred G ℓ) → IsSubgroup 𝒢 K
      → (∀ k → lookup A k ∈ K) → InGen ⊆ K
    gen⊆ K K-sg A⊆K (w , p) = respects p (eval∈ w)
      where
      open IsSubgroup K-sg using ( respects ; ∙-closed ; ε-closed ; ⁻¹-closed )
      letter∈ : (l : Letter) → letter l ∈ K
      letter∈ (k , true)   = A⊆K k
      letter∈ (k , false)  = ⁻¹-closed (A⊆K k)
      eval∈ : (w : Word) → eval w ∈ K
      eval∈ []       = ε-closed
      eval∈ (l ∷ w)  = ∙-closed (eval∈ w) (letter∈ l)

    ----------------------------------------------------------------------
    -- The Schreier vector, by breadth-first search.

    SV : Type
    SV = Vec (Maybe Word) n

    Frontier : Type
    Frontier = List (Fin n × Word)

    letters : List Letter
    letters = map (_, true) (allFin (length A)) ++ map (_, false) (allFin (length A))

    visit : Fin n → Word → SV × Frontier → SV × Frontier
    visit j w (sv , fr) with lookupᵛ sv j
    ... | just _   = sv , fr
    ... | nothing  = (sv [ j ]≔ᵛ just w) , ((j , w) ∷ fr)

    visitAll : List Letter → Fin n → Word → SV × Frontier → SV × Frontier
    visitAll []        i w acc = acc
    visitAll (l ∷ ls)  i w acc = visitAll ls i w (visit (idx (e[ i ] ∙ letter l)) (l ∷ w) acc)

    round : Frontier → SV × Frontier → SV × Frontier
    round []               acc = acc
    round ((i , w) ∷ old)  acc = round old (visitAll letters i w acc)

    mutual
      bfs : ℕ → SV → Frontier → SV
      bfs zero     sv fr        = sv
      bfs (suc k)  sv []        = sv
      bfs (suc k)  sv (f ∷ fr)  = next k (round (f ∷ fr) (sv , []))

      next : ℕ → SV × Frontier → SV
      next k (sv , fr) = bfs k sv fr

    schreier : SV
    schreier = bfs n (replicate n nothing [ idx ε ]≔ᵛ just []) ((idx ε , []) ∷ [])

    ----------------------------------------------------------------------
    -- The certificate, and the decider it yields.

    Reached : SV → Fin n → Type
    Reached sv i = T (is-just (lookupᵛ sv i))

    Sound : Maybe Word → Fin n → Type ρ
    Sound nothing   i = ⊤
    Sound (just w)  i = eval w ≈ e[ i ]

    sound? : (m : Maybe Word) (i : Fin n) → Dec (Sound m i)
    sound? nothing   i = yes tt
    sound? (just w)  i = eval w ≟ e[ i ]

    Cert : SV → Type ρ
    Cert sv =  Reached sv (idx ε)
            ×  (∀ i → Reached sv i → (l : Letter) → Reached sv (idx (e[ i ] ∙ letter l)))
            ×  (∀ i → Sound (lookupᵛ sv i) i)

    allLetters? : {p : Level} {P : Letter → Type p}
      → (∀ l → Dec (P l)) → Dec (∀ l → P l)
    allLetters? P? = map′ (λ f → λ { (k , true) → proj₁ (f k) ; (k , false) → proj₂ (f k) })
                          (λ g k → g (k , true) , g (k , false))
                          (all? (λ k → P? (k , true) ×? P? (k , false)))

    cert? : (sv : SV) → Dec (Cert sv)
    cert? sv =     T? (is-just (lookupᵛ sv (idx ε)))
              ×?  all? (λ i → T? (is-just (lookupᵛ sv i))
                       →? allLetters? (λ l → T? (is-just (lookupᵛ sv (idx (e[ i ] ∙ letter l))))))
              ×?  all? (λ i → sound? (lookupᵛ sv i) i)

    module _ (sv : SV) (c : Cert sv) where

      -- The value of every word is reached, by induction on the word.
      reached : (w : Word) → Reached sv (idx (eval w))
      reached []       = proj₁ c
      reached (l ∷ w)  = subst (Reached sv) (idx-cong (∙-cong (idx-≈ (eval w)) ≈refl))
                           (proj₁ (proj₂ c) (idx (eval w)) (reached w) l)

      inGen? : ∀ x → Dec (InGen x)
      inGen? x with lookupᵛ sv (idx x) in eq
      ... | just w   = yes (w , ≈trans (subst (λ m → Sound m (idx x)) eq (proj₂ (proj₂ c) (idx x)))
                                       (idx-≈ x))
      ... | nothing  = no (λ (w , p) → subst (λ m → T (is-just m)) eq
                                         (subst (Reached sv) (idx-cong p) (reached w)))

      genˢ : DecSubgroup 𝒢 ρ
      genˢ = (InGen , inGen-isSubgroup) , inGen?

  open Words public

  -- The certificate of A, once its check has been evaluated.
  certificate : (A : List G) → True (cert? A (schreier A)) → Cert A (schreier A)
  certificate A c = toWitness c

  -- A list of generators with its Schreier vector and certificate.  A
  -- function of the subgroup takes this record, so that no certificate
  -- stands in the type at a call, where Agda would compare it by
  -- evaluating it again.
  record Generators : Type (α ⊔ ρ) where
    constructor generators
    field
      gens  : List G
      vec   : SV gens
      cert  : Cert gens vec

  -- Generators whose certificate is checked by evaluation, once, here.
  mkGenerators : (A : List G) → True (cert? A (schreier A)) → Generators
  mkGenerators A c = generators A (schreier A) (certificate A c)

  -- The certificates of every ⟨x, B⟩, x in the group, in a record: Agda
  -- compares a record type by its name, so a call never compares (and
  -- never evaluates) the certificates themselves.
  record Adjoined (B : List G) : Type ρ where
    constructor adjoined
    field
      certs : ∀ i → Cert (e[ i ] ∷ B) (schreier (e[ i ] ∷ B))

  mkAdjoined : (B : List G) → True (all? (λ i → cert? (e[ i ] ∷ B) (schreier (e[ i ] ∷ B))))
    → Adjoined B
  mkAdjoined B c = adjoined (toWitness c)

  -- For every element x of the group, the generators x ∷ B.
  adjoin : {B : List G} → Adjoined B → Fin n → Generators
  adjoin {B} 𝔸 i = generators (e[ i ] ∷ B) (schreier (e[ i ] ∷ B)) (Adjoined.certs 𝔸 i)

  -- The subgroup generated by a list of generators.
  ⟪_⟫ : Generators → DecSubgroup 𝒢 ρ
  ⟪ 𝔸 ⟫ = genˢ (Generators.gens 𝔸) (Generators.vec 𝔸) (Generators.cert 𝔸)

  ----------------------------------------------------------------------
  -- Decisions by the generators alone.

  -- ⟨A⟩ ⊆ K exactly when every generator lies in K (GAP's test).
  gen⊆? : (A : List G) (𝑲 : DecSubgroup 𝒢 ℓ) → Dec (InGen A ⊆ set 𝑲)
  gen⊆? A 𝑲 = map′ (gen⊆ A (set 𝑲) (isSub 𝑲)) (λ s k → s (gens∈ A k))
                   (all? (λ k → lookup A k ∈? 𝑲))

  -- The distinct cyclic subgroups of order m, each given by the first of
  -- its generators: ⟨x⟩ ⊆ ⟨y⟩ exactly when x ∈ ⟨y⟩.
  cyclicOfOrder : Adjoined [] → ℕ → List (Fin n)
  cyclicOfOrder cs m =
    deduplicate (λ i j → gen⊆? (e[ i ] ∷ []) ⟪ adjoin cs j ⟫ ×? gen⊆? (e[ j ] ∷ []) ⟪ adjoin cs i ⟫)
                (filter (λ i → orderˢ ⟪ adjoin cs i ⟫ ≟ⁿ m) (allFin n))

  module _ (𝔸 : Generators) where
    private
      A : List G
      A = Generators.gens 𝔸
      𝑯 : DecSubgroup 𝒢 ρ
      𝑯 = ⟪ 𝔸 ⟫

    -- g normalizes ⟨A⟩ exactly when conjugation by g and by g⁻¹ maps each
    -- generator into ⟨A⟩.
    normalizesGen? : ∀ g → Dec (Normalizes 𝑯 g)
    normalizesGen? g = map′ to (λ N k → N (gens∈ A k))
      (all? (λ k → (conj g (lookup A k) ∈? 𝑯) ×? (conj (g ⁻¹) (lookup A k) ∈? 𝑯)))
      where
      to : (∀ k → (conj g (lookup A k) ∈ InGen A) × (conj (g ⁻¹) (lookup A k) ∈ InGen A))
        → Normalizes 𝑯 g
      to t x∈H =  gen⊆ A (set (preˢ g 𝑯)) (isSub (preˢ g 𝑯)) (λ k → proj₁ (t k)) x∈H
               ,  gen⊆ A (set (preˢ (g ⁻¹) 𝑯)) (isSub (preˢ (g ⁻¹) 𝑯)) (λ k → proj₂ (t k)) x∈H

    -- The normalizer of ⟨A⟩: the textbook predicate, decided by generators.
    normalizer⟪⟫ : DecSubgroup 𝒢 (α ⊔ ρ)
    normalizer⟪⟫ = (Normalizes 𝑯 , normalizes-isSubgroup 𝑯) , normalizesGen?

    -- g ⟨A⟩ g⁻¹ ⊆ K exactly when g a g⁻¹ ∈ K for every generator a.
    conjGen⊆? : ∀ g (𝑲 : DecSubgroup 𝒢 ℓ) → Dec (set (conjugateˢ g 𝑯) ⊆ set 𝑲)
    conjGen⊆? g 𝑲 = map′ to from (all? (λ k → conj g (lookup A k) ∈? 𝑲))
      where
      to : (∀ k → conj g (lookup A k) ∈ set 𝑲) → set (conjugateˢ g 𝑯) ⊆ set 𝑲
      to t {x} p = IsSubgroup.respects (isSub 𝑲) (conj-conj⁻¹ g x)
                     (gen⊆ A (set (preˢ g 𝑲)) (isSub (preˢ g 𝑲)) t p)
      from : set (conjugateˢ g 𝑯) ⊆ set 𝑲 → ∀ k → conj g (lookup A k) ∈ set 𝑲
      from s k = s (IsSubgroup.respects (inGen-isSubgroup A) (≈sym (conj⁻¹-conj g (lookup A k)))
                                        (gens∈ A k))

    -- Two conjugates of ⟨A⟩ are equal, decided by the generators.
    conjGen≐? : ∀ g h → Dec (set (conjugateˢ g 𝑯) ≐ set (conjugateˢ h 𝑯))
    conjGen≐? g h = conjGen⊆? g (conjugateˢ h 𝑯) ×? conjGen⊆? h (conjugateˢ g 𝑯)

    -- The distinct conjugates of ⟨A⟩: the elements of the group,
    -- deduplicated by the conjugate each gives.
    #conjugates⟪⟫ : ℕ
    #conjugates⟪⟫ = length (deduplicate conjGen≐? (tabulateᴸ e[_]))

    -- The distinct conjugates of ⟨A⟩ by the elements of a subgroup K.
    #conjugates⟪⟫-in : DecSubgroup 𝒢 ℓ → ℕ
    #conjugates⟪⟫-in 𝑲 = length (deduplicate conjGen≐? (filter (λ g → g ∈? 𝑲) (tabulateᴸ e[_])))
