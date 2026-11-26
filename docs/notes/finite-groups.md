<!-- File: docs/notes/finite-groups.md -->

# Finite groups and their subgroups

The companion note to [ADR 0001], which records the decisions; this note
explains them and records the search of prior formalizations behind them.
It describes the design that M2-2 to M2-4 ([#6], [#7], [#8]) implement,
as the spike of issue [#5] built it.  The spike is the scratch modules
under `spike/` at commit [`c86d93e`]; the pull request that adds this
note removes them before the merge, and `spike/README.md` at that commit
has their map and timings.

The names in `code` that the spike defines are in the modules
`Spike.Finite`, `Spike.Counting`, `Spike.Constructions`,
`Spike.SubgroupEnumeration`, `Spike.TableGroups`, `Spike.Sylow` and
`Spike.Rules`; the library's own names, in M2-2 to M2-4, may differ.

## 1.  Finite sets, constructively

Mines, Richman and Ruitenburg's *A Course in Constructive Algebra*
([MRR], Chapter I, § 2) gives the vocabulary, as follows:

+  a set is **discrete** if equality on it is decidable: for any a and b,
   either a = b or a ≠ b;
+  a subset A of S is **detachable** if membership in it is decidable:
   for each x in S, either x ∈ A or x ∉ A; equivalently (their Exercise
   5), A has a characteristic function from S to {0, 1};
+  two subsets of S are **equal** if each is contained in the other;
+  a set has **cardinality n** if it is in bijection with {1, ..., n},
   and a **finite** set is a discrete set of some cardinality n;
+  a set is **finitely enumerable** if it is empty or the image of a
   function from {1, ..., n}, and "a finitely enumerable set is discrete
   if and only if it is finite".

In agda-algebras a set is a **setoid**: a type with an equivalence
relation `_≈_` that plays the part of equality.  Its finiteness record
`FiniteAlgebra` ([`Setoid.Algebras.Finite`]) asks for decidable `≈` and
a **surjective enumeration** `enum : Fin card → carrier` that hits every
element up to `≈`, possibly more than once; so it makes the carrier
discrete and finitely enumerable, hence finite.  agda-algebras proves the
last step: `irredundantEnumeration` ([`Setoid.Algebras.Finite.Irredundant`])
deduplicates the enumeration and returns an **irredundant enumeration**,
the record `IrredundantEnumeration` with four fields, as follows:

+  `icard : ℕ`, the number of elements;
+  `ienum[_] : Fin icard → carrier`, the enumeration;
+  `ienum-sur`, every element is `≈` to an enumerated one;
+  `ienum-inj`, two enumerated elements that are `≈` have the same index.

That is a bijection, up to `≈`, between the carrier and `Fin icard`: the
carrier is a finite set of cardinality `icard`.  Its **index map** sends
an element to its position, `idx x = proj₁ (ienum-sur x)`.  The index
map respects `≈` and inverts the enumeration (`idx-cong`, `idx-e` in
`Spike.Finite`), and it decides equality: `x ≈ y` exactly when `idx x ≡
idx y`, which is decidable in `Fin icard`.  So a finite set is discrete,
as Mines, Richman and Ruitenburg say.

A detachable subset of a finite set of cardinality n is determined by its
characteristic function on the n positions, a vector of n Booleans:
agda-stdlib's `Subset n` (`Data.Fin.Subset`, a `Vec Bool n`).  Two
detachable subsets are equal (each contained in the other) exactly when
their vectors are equal, propositionally, since a vector is first-order
data.  This note calls such a vector a **table**.

## 2.  Finite groups

A **finite group** is agda-algebras' `Group α ρ` (an algebra of the
signature of groups that satisfies the five group equations,
[`Classical.Structures.Group.Basic`]) together with an irredundant
enumeration of its carrier, as data: the record `FiniteGroupⁱ` of the
spike, `FiniteGroup` in M2-3.  Its **order** is `icard`.  From the
enumeration come the index map, decidable equality, and a
`FiniteAlgebra` witness (`toFiniteAlgebra`), so that agda-algebras'
finite group theory applies unchanged: the decidable normal closure
`NormalClosureᵈ`, the minimal-normal descent of `MinimalNormalDescent`,
and the finite coset space `cosetAlgebra-FiniteAlgebra`, all of which
take a `FiniteAlgebra`.

The enumeration is data, not something recomputed, because of what it
costs to compute through.  A group that comes with a `FiniteAlgebra`
witness gets an irredundant enumeration from agda-algebras'
deduplication (`fromFiniteAlgebra`; the spike's `FiniteGroupᶠ`), and
every theorem about it holds; but its index map reads an element's
position off a membership proof that Agda normalizes through the
deduplicated list at each lookup.  On A₅, one lookup costs 141 ms and the
60 lookups of one table 21 s, against 23 ms for the 60 lookups of the
identity enumeration given directly (`Spike.A5.IndexCost`; § 8).  So
each finite group is given its enumeration where it is made, as follows:

+  a group on `Fin n` with propositional equality (agda-algebras'
   `TableGroup` and the examples of `Examples.Classical.Groups`) has the
   identity enumeration, whose index map is the identity;
+  a subgroup, as a finite group in its own right, has the enumeration by
   the positions of its table (§ 6);
+  a quotient G/N is given one by M3-6 ([#14]), whose index map
   normalizes no proof (least representatives are one way); the spike's
   quotient used deduplication (§ 6);
+  a group known only through a `FiniteAlgebra` witness has agda-algebras'
   deduplication, which is correct and slow to evaluate.

The other notions issue [#5] listed were tried as well.  A group with
only a `FiniteAlgebra` witness, the order derived on demand, is the type
above with the slow index map built in.  A group whose carrier is `Fin
n` (`FinGroup` in `Spike.TableGroups`, with its operations as functions
and the order n by definition) is reached from every finite group by
**re-tabulation**: the group on `Fin n` whose product is `idx (e[ a ] ∙
e[ b ])`, with the enumeration an isomorphism onto the original
(`Retabulate`, `e-hom`).  It is kept as a constructor and a view (M2-4,
[#8]), not as the type: subgroups and quotients would have to be
re-tabulated each time, and a re-tabulated table buys no speed, since
Agda keeps no table of a function's values: each product recomputes
`idx (e[ a ] ∙ e[ b ])`.  The re-tabulated A₄ counted its Sylow
subgroups in 2,203 ms against 1,057 ms for A₄ itself (§ 8).  Groups of
permutations of `Fin n` were not tried; Cayley's theorem (M2-4) passes
to them.

## 3.  Subgroups as tables

A **subgroup** of a finite group G of order n is a table χ, a `Subset n`
over the index set of G's enumeration, with a proof of its closure, as
follows:

    Subgroup G = Σ[ χ ∈ Subset n ] True (closed? χ)

+  **Membership**: `x ∈ (χ , _) = T (lookup χ (idx x))`, the entry of χ
   at the position of x; it respects `≈`, by `idx-cong`.
+  **The closure check** `closed? χ` decides three conditions on
   positions: the identity is in χ, and products and inverses of members
   are members.  `True d` is agda-stdlib's `T (isYes d)`, the type of
   proofs that the decision d said yes: `⊤` or `⊥`, so any two of its
   proofs are equal with no axiom (`T-irrelevant`).
+  **The order** of a subgroup is the number of its entries that are
   true, agda-stdlib's `∣ χ ∣`.
+  **Equality**.  Two subgroups with the same elements have the same
   table, entry by entry (at position i, the element `e[ i ]`), and two
   vectors with the same entries are equal (`tabulate∘lookup`,
   `tabulate-cong`); their closure proofs are equal by `T-irrelevant`.
   So `same-elements→≡` proves `H ≡ K` from the two inclusions, with no
   axiom, and `_≟ᵗ_` decides `H ≡ K` by comparing vectors.
+  **The universe level**.  A table is a vector of Booleans, so
   `Subgroup G : Type` (that is, `Set₀`) whatever the levels α and ρ of
   G.
+  **The finite set of subgroups**.  The subgroups of G are the closed
   tables among the 2ⁿ subsets of `Fin n`, so they form a finite set, and
   so does every decidable family of them (the Sylow p-subgroups, the
   normal subgroups, the subgroups between two).  The set exists as a
   definition; enumerating it is feasible only for small n (§ 5).
+  **agda-algebras' subgroups**.  `toDec` makes a table into
   agda-algebras' `DecSubgroup` (a predicate with `IsSubgroup` and a
   decider, at level `0ℓ`), and `fromDec` makes any `DecSubgroup`, at any
   level, into its table: the decisions on the enumeration, with closure
   proved from `IsSubgroup`.  The round trips are `fromDec (toDec H) ≡ H`
   and `toDec (fromDec H) ≐ H` (each predicate contained in the other).
   So agda-algebras' theorems about predicates (cosets, Dedekind's law,
   conjugation, complements) apply to tables through `toDec`, and its
   constructions (centralizers, normal closures, intersections) come back
   through `fromDec`.  Two decidable subgroups are `≐` exactly when their
   tables are equal (`≐→table≡`, `table≡→≐`), so `≐` is decidable too
   (`≐?`).

This is MathComp's representation in Agda (§ 9.1).  In MathComp a finite
set of a finite type is a `FinSet` of a finite function, a tuple of
Booleans over the type's enumeration, and a group is such a set with a
Boolean closure test, `group_set`.  Its designers began with sets as
characteristic functions and changed to these tables for quotients:
"Having sets for which function extensionality does not hold had forced
us to use setoid. ... Using intensional sets has simplified everything"
([GMRTT], § 3.3).  Under `--without-K --safe` the same holds here: a
predicate subgroup has no extensional equality, and a table has it by
computation.

A table is canonical only over an enumeration that lists each element
once.  Over a surjective enumeration with repetitions, two tables that
differ at two indices naming one element would denote the same subgroup;
the irredundant enumeration rules that out, and `ienum-inj` is the step
of `same-elements→≡` that uses it.

## 4.  The two rules for the types of subgroups

The plan states two rules for any type of subgroups under `--without-K
--safe` ([`GITHUB_PROJECT.md`], "Scope and decisions"), as follows:

+  **the first rule**: two subgroups with the same elements are not
   propositionally equal, so an equality of subgroups is stated as a pair
   of inclusions;
+  **the second rule**: a premise that ends in a disjunction about every
   subgroup proves excluded middle, since a subgroup can be built from an
   arbitrary proposition, so such a premise carries a witness instead.

Both are facts about subgroups that are predicates.  `Spike.Oracle`
checks the second on S₃: for any proposition P, the predicate "x is 1,
or P holds and x is in A₃" is a subgroup between 1 and A₃, so the premise
"every subgroup L between 1 and A₃ lies in 1 or contains A₃", over
agda-algebras' subgroups, proves `P ⊎ ¬ P` (`disjunctive→LEM`).

Tables meet both rules by construction.  Two tables with the same
elements are `≡` (§ 3).  A table cannot be built from an arbitrary
proposition, since each entry is a Boolean, and a statement about every
table between two is decidable: `between₂?` decides "every subgroup
between H and K is H or K" over the closed tables among the 2ⁿ subsets
(agda-stdlib's `anySubset?`), and on S₃ it says yes between 1 and A₃
and no between 1 and S₃, which has ⟨s⟩ between, in 25 ms
(`Spike.RulesExamples`).

So statements over tables use `≡` and may end in such disjunctions, and
the two rules stay for agda-algebras' predicates.  The witnessed form,
"a subgroup between H and K that holds an element outside H contains K",
quantified over agda-algebras' decidable subgroups, is equivalent to the
disjunctive form over tables, constructively, for every finite group
(`tables→witnessed`, `witnessed→tables` in `Spike.Rules`): one direction
passes a decidable subgroup to its table, the other finds the witness by
a search of `Fin n`.  A statement can therefore be given in both forms,
with the passage between them proved once.

## 5.  Counting

Every count is a natural number that Agda computes by evaluation (a check
by `refl`), as follows:

+  **the order** of a group, `icard`, and of a subgroup, `∣ χ ∣`;
+  **the index** of a subgroup K, twice: as the size of agda-algebras'
   coset space G/K (`cosetAlgebra-FiniteAlgebra`: G's enumeration with
   the coset relation, decidable through K's table), whose irredundant
   enumeration agda-algebras computes; and as the number of distinct left
   cosets gK as tables (`index` and `indexᵗ` in `Spike.Counting`);
+  **the conjugates** of a subgroup H: the tables of g H g⁻¹ for the n
   elements g, deduplicated by comparing vectors (`#conjugates`);
+  **the normalizer** of H, as a table: the g with g H g⁻¹ inside H,
   decided by a sweep (`normalizer`).

**The number nₚ of Sylow p-subgroups** has two forms ([ADR 0001], § 5:
both forms of a definition, the classical first), as follows:

+  **the classical form**: nₚ is the number of subgroups of order pᵃ, where
   pᵃ is the largest power of p dividing |G|, that is, the size of the
   finite set Syl_p(G) of § 3, as Aschbacher defines it ([Aschbacher],
   § 6, p. 19: "Write Syl_p(G) for the set of Sylow p-subgroups of G")
   and as MathComp, Mizar, HOL Light and Metamath count it (§ 9);
+  **the computed form**: the number of conjugates of one Sylow
   p-subgroup P in hand, or the index of its normalizer, |G : N_G(P)|.

Aschbacher's Sylow's Theorem (3) is that they agree: |Syl_p(G)| = |G :
N_G(P)| ≡ 1 (mod p).  The number of conjugates of P is |G : N_G(P)| by
the orbit-stabilizer theorem (Aschbacher (5.12)), and it is |Syl_p(G)|
because G is transitive on Syl_p(G), by conjugation (Sylow's Theorem
(2)).  `Spike.Sylow` types the theorem both ways: `Sylow₃ᵗ` over tables,
with the classical nₚ, and `Sylow₃ᵈ` over decidable subgroups, where
there is no finite set of subgroups to count, so the statement adds that
every Sylow p-subgroup is a conjugate of P.

What evaluation can reach, measured (§ 8), is as follows:

+  the classical nₚ ranges over all 2ⁿ subsets: for V₄ (16 subsets) and
   S₃ (64) Agda computes n₂(S₃) = 3 and n₃(S₃) = 1 in 22 ms, but for A₅
   it would range over 2⁶⁰ subsets;
+  the computed form needs one Sylow subgroup in hand: for A₅, the
   distinct conjugates of the Sylow 5-, 3- and 2-subgroups number 6, 10
   and 5 (about 0.65 s each), and the indices of their normalizers (of
   orders 10, 6 and 12) are 6, 10 and 5 (about 0.1 s each by the coset
   space, 0.5 s by coset tables).

So a concrete group's nₚ is computed through Sylow's third theorem: the
computed form evaluates, and the theorem equates it with the classical
one.  Enumerating the subgroups of A₅ by generators (each of its 59
subgroups is generated by two elements) is another route, not tried.

## 6.  Subgroups and quotients as finite groups

**A subgroup as a finite group** (`Constructions.AsGroup`).  The carrier
is the subtype of the members, `Σ[ x ∈ G ] x ∈ H`, compared in G; the
operations are G's, closed by the table's closure; the five equations
are G's (agda-algebras' `setoidEqsToGroup`).  Two enumerations of it
were built, as follows:

+  a surjective enumeration by all n indices of G, sending an index
   outside H to the identity, from which agda-algebras' deduplication
   computes the order (A₄ inside A₅: 12; A₃ and ⟨s⟩ inside S₃: 3 and 2);
+  the irredundant enumeration by the **positions** of H's table, the
   indices it holds in increasing order (`SubgroupEnumeration.Positions`),
   whose index map walks G's index set once.

Through the positions enumeration, A₄ is a finite group of order 12 in
which the Sylow 3-subgroup ⟨(0 1 2)⟩ has 4 conjugates, its normalizer has
order 3, and the Sylow 2-subgroup is normal: Sylow's theorems applied
inside a subgroup, counted in 1,057 ms (`Spike.A4Examples`).

**The quotient by a normal subgroup** (`Constructions.Quotient`).  For a
table N whose normality is decided by a sweep (`normal?`), the quotient
G/N is agda-algebras' `Group` on the same carrier with the coarser
equality x ∼ y when x y⁻¹ ∈ N (agda-algebras' `NormalCon`, the
congruence of a normal subgroup), and its `FiniteAlgebra` witness is G's
own enumeration, decided by one lookup in N's table.  No representative
is chosen until the order is counted, as agda-algebras' ADR 008 prefers
([`008-two-layer-congruence-discipline.md`]).  Its deduplication gives
the orders |S₃/A₃| = 2, |V₄/⟨1⟩| = 2 and |A₅/1| = 60, and its
re-tabulation is the group of order 2 (`Spike.ConstructionExamples`,
`Spike.TableGroupExamples`).  To compute inside a quotient, M3-6 ([#14])
gives it an irredundant enumeration whose index map normalizes no proof;
least representatives are one way (the coset of x named by the first
index of the enumeration whose element is ∼ x, as lean2agda's proof of
Lagrange's theorem chooses its transversal, § 9.9).

## 7.  The modules

[ADR 0001], § 8, names the modules as follows:

+  M2-2 ([#6]): `Groups.Finite.Setoid`, a setoid with an irredundant
   enumeration (`FiniteSetoid`, the four fields of agda-algebras'
   `IrredundantEnumeration` for a setoid that is not an algebra), with
   sizes, bijections and the pigeonhole principle; `Groups.Finite.Subset`,
   detachable subsets as tables, with their sizes; `Groups.Finite.Sum`,
   sums and products, partitions, and sums modulo p;
+  M2-3 ([#7]): `Groups.Finite.Group` (`FiniteGroup`, its order, index
   map, decidable equality, `fromFiniteAlgebra`, `toFiniteAlgebra`);
   `Groups.Subgroup` (subgroups as tables: membership, inclusion,
   equality, order, `toDec`, `fromDec`, and the finite set of subgroups);
   `Groups.Subgroup.Group` (a subgroup as a finite group, by positions);
   `Groups.Subgroup.Notions` (normal subgroups, abelian groups, powers,
   elementary abelian p-groups, the subgroups between two, complements,
   minimal normal subgroups);
+  M2-4 ([#8]): `Groups.Table` (groups on `Fin n`, re-tabulation, and
   agda-algebras' examples as finite groups); `Groups.Cyclic`,
   `Groups.Symmetric`, `Groups.Cayley`.

## 8.  What the spike measured

The record run is `bash spike/check.sh` at [`c86d93e`] on 2026-11-26, in
the dev shell (Agda 2.9.0 and agda-stdlib 2.4.1 from agda-algebras at
`66c324f8`, on a 12th Gen Intel Core i9-12900H): the 17 modules it lists
checked from scratch in 1 minute 22 seconds, each under `--without-K
--exact-split --safe` with no postulate, and the options check of M1-1
passed over all 18 modules of `spike/`.  The times are Agda's own, by
`--profile=definitions`, as follows:

| Check | Given enumeration | Deduplicated enumeration |
| --- | ---: | ---: |
| A₅: its order, 60 | | 45 ms |
| A₅: one lookup of the index map | | 141 ms |
| A₅: 60 lookups (one conjugate table) | 23 ms | 21,156 ms |
| A₅: the closure checks of ⟨s⟩, ⟨t⟩, V and A₄ | 155, 146, 163, 160 ms | |
| A₅: the distinct conjugates of the Sylow 5-, 3- and 2-subgroups (6, 10, 5) | 645, 665, 654 ms | |
| A₅: the closure checks of their normalizers | 247, 215, 238 ms | |
| A₅: the indices of the normalizers, by agda-algebras' coset space (6, 10, 5) | 93, 109, 91 ms | |
| A₅: the same indices, by distinct coset tables | 525, 509, 510 ms | |
| S₃: n₂ = 3 and n₃ = 1, among all 64 subsets | 22 ms | 291 ms |
| V₄: n₂ = 1, among all 16 subsets | 17 ms | |
| S₃: every subgroup between 1 and A₃ is 1 or A₃, decided | 25 ms | |
| A₄ in A₅, by positions: n₃(A₄) = 4 and V normal, by conjugates | 1,057 ms | |
| A₄ re-tabulated on `Fin 12`: the same | 2,203 ms | |

Here s = (0 1 2 3 4) and t = (0 1 2) are agda-algebras' generators of
A₅, V is the subgroup of the double transpositions that fix the point 4,
and A₄ is the stabilizer of the point 4; a blank cell was not measured.
Through the deduplicated enumeration, the checks of `Spike.A5.Given` were
not measured: `Spike.A5.Derived`, which makes them, was stopped by
`timeout 1200` after 20 minutes with no result.  At the rate measured,
the conjugates of one subgroup alone (60 tables of 60 lookups) would take
about 21 minutes.  In three earlier runs the same day one lookup took
194, 195 and 182 ms, and the 60 lookups 23,621, 23,641 and 20,960 ms.

## 9.  The search of prior formalizations

The search ran on 2026-11-26.  For each library it asked what a finite
group is, what a subgroup is and what its equality rests on, whether the
subgroups of a finite group (or its Sylow subgroups) form a finite set
with a cardinality, how conjugates and Sylow subgroups are counted, and
which proofs of Cauchy's and Sylow's theorems are formalized.  The
revisions read are named in each section; § 9.11 lists the queries.

### 9.1 MathComp

math-comp/math-comp, `master` at `99f568a2` (2026-11-24); the group files
are now under `finite_group/` and `solvable/`.

+  **Finite groups**.  `finGroupType` is a group structure on a finite
   type (`finite_group/fingroup.v:234-236`), and a finite type is an
   equality type with an enumeration that lists each element once:
   `finite_axiom ... := forall x : T, count_mem x e = 1`
   (`boot/fintype.v:173-174`).  The groups studied are sets `G : {group
   gT}` inside an ambient `gT : finGroupType`.
+  **Subgroups**.  A set is `FinSet of {ffun pred T}` (`boot/finset.v:136`),
   a finite function, which is a tuple over the enumeration
   (`boot/finfun.v:105-106`): a Boolean table.  A group is a set with the
   Boolean test `group_set A := (1 \in A) && (A * A \subset A)`
   (`fingroup.v:948`, the structure at 958-961).  Equality needs no axiom:
   `setP A B : A =i B <-> A = B` (`finset.v:228`) and `group_inj`
   (`fingroup.v:979`); the file says "hence Leibnitz and extensional
   equalities coincide on {set T}" (`finset.v:11-12`).
+  **The finite set of subgroups**.  `{group gT}` is itself a finite type
   (`fingroup.v:968`), so `'Syl_p(G)` (`solvable/pgroup.v:77`) is a finite
   set and `#|'Syl_p(G)|` a natural number.
+  **Counts**.  `card_conjugates A G : #|A :^: G| = #|G : 'N_G(A)|`
   (`finite_group/action.v:2577`) and `card_Syl P : p.-Sylow(G) P ->
   #|'Syl_p(G)| = #|G : 'N_G(P)|` (`solvable/sylow.v:198`).  `action.v`
   cites Aschbacher by number, as in "This is Aschbacher (5.2)" (1060).
+  **Proofs**.  One theorem, `Sylow's_theorem` (`sylow.v:88-92`), states
   Aschbacher's four parts: the maximal p-subgroups are the Sylow
   subgroups, G is transitive on `'Syl_p(G)` by conjugation,
   `#|'Syl_p(G)| = #|G : 'N_G(P)|`, and `#|'Syl_p(G)| %% p = 1`.  The
   proof lets G act by conjugation on the maximal p-subgroups and counts
   fixed points modulo p (`pgroup_fix_mod`), as Aschbacher's proof of § 6
   does.  Cauchy's theorem (`pgroup.v:622`) is proved by induction through
   the class equation.
+  **Aschbacher**.  A grep of the 31 files of `finite_group/` and
   `solvable/` at this revision finds Aschbacher on 64 lines in 10 files,
   and Kurzweil and Stellmacher on none.

### 9.2 Mathlib

leanprover-community/mathlib4, `master` at `348837d3` (2026-11-25).

+  **Finite groups**: a type with `[Group G] [Finite G]`, where `Finite α`
   is the proposition that some `α ≃ Fin n` exists
   (`Mathlib/Basic/Finite/Defs.lean:101-102`); orders are `Nat.card`.
+  **Subgroups**: a structure on a set with closure fields
   (`Algebra/Group/Subgroup/Defs.lean:298`).  `Subgroup.ext` is
   `SetLike.ext`, which is `Set.ext`, proved by `funext` and the axiom
   `propext` (`Data/Set/Defs.lean:78-79`).
+  **The finite set of Sylow subgroups**: `structure Sylow` is a subgroup
   with `maximal_isPGroup` (`GroupTheory/Sylow.lean:54-55`), finite by an
   instance for any `SetLike` type over a finite type
   (`Data/SetLike/Fintype.lean:31-32`), whose `Fintype` form is
   noncomputable, with the comment "TODO: It should be possible to obtain
   a computable version".  The count is `Nat.card (Sylow p G)`.
+  **Counts**: `card_eq_index_normalizer` (`Sylow.lean:457-458`) and
   `card_dvd_index` (461-462), through `Sylow p G ≃ G ⧸ normalizer P`.
+  **Proofs**: existence of a Sylow subgroup by Zorn's lemma
   (`IsPGroup.exists_le_sylow`, 200); the growth step
   `exists_subgroup_card_pow_succ` (653-655), H acting on G ⧸ H with
   Cauchy's theorem in N(H)/H; conjugacy as `isPretransitive_of_finite`
   (349-350); `card_sylow_modEq_one` (377-378), P fixing only itself; all
   through `IsPGroup.card_modEq_card_fixedPoints`
   (`GroupTheory/PGroup.lean:317`).  Cauchy's theorem is McKay's proof,
   `exists_prime_orderOf_dvd_card` (`GroupTheory/Perm/Cycle/Type.lean:492-493`),
   over the vectors whose product is 1.

### 9.3 Isabelle and the Archive of Formal Proofs

HOL-Algebra in isabelle-prover/mirror-isabelle at `053b29cd` (2026-11-24),
and the Archive in isabelle-prover/mirror-afp-devel at `02fd3c6b`
(2026-11-25).

+  **Groups and subgroups**: a record with a carrier set, finite by
   hypothesis; a subgroup is a set (`Group.thy:654-659`), equal by set
   extensionality, which rests on HOL's axioms.
+  **Sylow**: HOL-Algebra proves existence only, by Wielandt's count of
   the subsets of size pᵃ (`Sylow.thy:333-335`, after Kammüller and
   Paulson, 1999).  The Archive's Secondary_Sylow (2014) proves that every
   p-subgroup lies in a Sylow subgroup, conjugacy, and `card
   (subgroups_of_size (p ^ a)) mod p = 1` (`SndSylow.thy:140`, 155-157,
   266-267), counting `subgroups_of_size p = {H. subgroup H G ∧ card H =
   p}`.  No Cauchy theorem for groups was found.
+  **The Archive's entries on finite groups**, by their names among the
   1,048 theory directories: Secondary_Sylow, Finitely_Generated_Abelian_Groups,
   Free-Groups, Group-Ring-Module, Rep_Fin_Groups, and Jordan_Hoelder.

### 9.4 Mizar

The Mizar Mathematical Library 5.106 (2026-11-06).  GROUP_10, "The Sylow
Theorems" (Marco Riccardi, 2007), is the one article of the 25 with
"group" in their names that proves them.  A subgroup's equality is
extensional, an axiom of the set theory (Tarski-Grothendieck).
`Subgroups G` is a finite set for a finite G (GROUP_3:15), the Sylow
p-subgroups a finite subset of it counted by `card` (GROUP_10:def 19),
and `card con_class H = Index Normalizer H` (GROUP_3:135).  Existence is
Wielandt's proof, and Cauchy's theorem a corollary of it (GROUP_10:10,
11); conjugacy and the count are GROUP_10:12 and 13.

### 9.5 Metamath

metamath/set.mm, `develop` at `c8228245` (2026-11-25).  A subgroup is a
subset (`df-subg`), equal by the axiom of extensionality.  `pSyl` is the
set of maximal p-subgroups (`df-slw`), counted by `#`.  `sylow1` is
Wielandt's proof; Cauchy's theorem, `odcau`, follows from it; `sylow2`
gives conjugacy, through the fixed-point congruence `sylow2a`; and
`sylow3` states that the count divides |G|/pᵃ and is 1 modulo p, with
`sylow3lem3`: "The number of Sylow subgroups is the same as the index
(number of cosets) of the normalizer".

### 9.6 HOL Light

jrh13/hol-light, `master` at `096417ca` (2026-11-24), `Library/grouptheory.ml`.
A subgroup is a set (`subgroup_of`), equal by extensionality.
`FINITE_RESTRICTED_SUBGROUPS` makes the subgroups of a finite group with
any property a finite set, counted by `CARD`.  All three Sylow theorems
are proved, with `SYLOW_THEOREM_COUNT_MOD` for the subgroups of every
order pᵏ dividing |G| (Frobenius' generalization), from which existence
and Cauchy's theorem follow; `CARD_CONJUGATE_SUBSETS` counts conjugates
by the normalizer.

### 9.7 agda-unimath

UniMath/agda-unimath, `master` at `c0022bfc` (2026-11-16), under
`--without-K` and not `--safe`.

+  **Finite groups**: `Finite-Group`
   (`src/finite-group-theory/finite-groups.lagda.md:93-95`), finiteness
   being the truncated existence of a count `Fin k ≃ X`.
+  **Subgroups**: a subtype, `A → Prop`; and "A finite subgroup of a
   finite group `G` is a decidable subgroup of `G`"
   (`src/finite-group-theory/subgroups-finite-groups.lagda.md:37-42`).
   `extensionality-Subgroup` (`src/group-theory/subgroups.lagda.md:385-392`)
   rests on function extensionality and univalence, both postulated in
   the library.  The library also notes that "Any proposition `P` induces
   a subgroup of any group `G`" (`subgroups.lagda.md:652`).
+  **No** finite set of subgroups, and no Lagrange, class equation,
   Cauchy or Sylow (a grep of `src/` matched no file).

### 9.8 The cubical library, the 1lab, TypeTopology and agda-stdlib

+  **agda/cubical**, `master` at `8f0a71b3` (2026-11-19): a subgroup is a
   predicate into `hProp` (`Cubical/Algebra/Group/Subgroup.agda:43-44`),
   equal by `funExt` and `ua`, theorems of cubical Agda.  No finite groups
   outside an experiment, and no Lagrange or Sylow.
+  **the1lab/1lab**, `main` at `d45acb1d` (2026-10-01): a subgroup is a
   subobject, a monomorphism (`src/Algebra/Group/Subgroup.lagda.md:41-42`),
   equal by univalence; no finite groups and no counting theorems.
+  **martinescardo/TypeTopology**, `master` at `acb7c0bc` (2026-11-25):
   `Groups.Subgroups` takes `ua : Univalence` as a module parameter
   (`source/Groups/Subgroups.lagda:36-38`), and `subgroup-equality` rests
   on it; no Lagrange or Sylow.
+  **agda/agda-stdlib**, v2.4.1 (commit `ac7c79b2`): new in 2.4,
   `Algebra.Construct.Sub.Group` makes a subgroup a group monomorphism
   (`src/Algebra/Construct/Sub/Group.agda:21-30`), with no equality of
   subgroups; no finite groups, cosets or quotient groups.

### 9.9 The Symmetry book, and Agda beyond the libraries

+  **The Symmetry book** (Bezem, Buchholtz, Cagne, Dundas and Grayson;
   UniMath/SymmetryBook, `master` at `cdc1dc87`, 2026-11-09), read for
   its ideas, since its groups need univalence, which the flags exclude.
   A group is a pointed connected groupoid, a finite group one whose
   symmetries form a finite set (`fingp.tex:57`), and a subgroup a
   pointed transitive G-set, so that the subgroups form a set
   (`actions.tex:730`, 796).  Every proof in its chapter on finite groups
   acts on G-sets: Lagrange's theorem by the orbits of H on G; Cauchy's
   theorem by McKay's argument; Sylow's first theorem by induction, Cauchy
   in the Weyl group N_G(K)/K; the third, `thm:sylow3` (`fingp.tex:292-298`),
   by transitivity and P acting by conjugation with P as its only fixed
   point.  Its Rocq formalization proves the counting form of Lagrange's
   theorem for decidable subgroups, and says why: "without decidability
   it does not: for a proposition [P], the symmetries [{e} ∪ {σ | P}] of
   [C_2] form a subgroup, and finiteness of [G/H] (or of [H]) would
   decide [P]" (`Formalization/FinGroups/S02_Lagrange.v:82-86`).
+  **formalverification/lean2agda**, `main` at `53fea3bb` (2026-11-24),
   the Agda corpus issue [#5] names:
   `corpus/subgroup-card-dvd/agda/SubgroupCardDvdFinite.agda` (421 lines,
   `--safe --cubical-compatible`, no postulate) proves that
   the order of a subgroup divides the order of the group, from
   enumerations `A ↔ Fin n` and `⟨ H ⟩ ↔ Fin m` passed as data.  A coset's
   representative is its first element in the enumeration of A, which
   "takes the place of Lean's Quotient.out" (256-258); the transversal is
   counted as a decidable subset of `Fin n`; and on the Klein four-group
   the index is 2 by `refl` (417-421).  No equality of subgroups is
   stated.
+  **Other Agda developments**, by GitHub code search:
   triqchem-lab/discrete-mathematics (`be523475`) proves Lagrange's
   theorem and the orbit-stabilizer theorem for groups on `Fin n` under
   `--rewriting --guardedness`, not `--safe`; Smaug123/agdaproofs
   (`0f423001`) has finite groups on setoids and an orbit-stabilizer
   module with holes; zaklogician/agda-ist-algebra
   (`a3fd828c`) has finite groups and no counting theorem;
   lean-dojo/ITPEval (`56f468dc`) and mikemol/metacatagory (`58d4e8d1`)
   have statements of Lagrange's and Sylow's theorems with no proof.  No
   Agda proof of Cauchy's theorem, of the class equation or of any of
   Sylow's theorems was found.

### 9.10 What the search says for this library

+  **Equality of subgroups**.  Every library in which two subgroups with
   the same elements are equal gets it from an axiom or a principle the
   flags exclude (extensionality in HOL, Mizar and Metamath; `funext` and
   `propext` in Mathlib; univalence in agda-unimath, cubical, the 1lab
   and TypeTopology), except MathComp, which gets it from Boolean tables
   over an enumeration.  The `--safe --without-K` Agda developments state
   no equality of subgroups.  Tables are the one design that meets the
   first rule under this library's flags.
+  **Decidability**.  agda-unimath makes the subgroups of a finite group
   decidable, and the Symmetry book's Rocq formalization assumes the
   subgroup decidable in its counting form of Lagrange's theorem, for the
   reason of the second rule.
+  **Counting Sylow subgroups**.  MathComp, Mizar, HOL Light, Metamath
   and the Archive count them as a finite set of subgroups, and Mathlib as
   a finite type; each relates the count to the index of a normalizer, as
   Aschbacher's Sylow's Theorem (3) does.
+  **The proofs**.  Wielandt's count of subsets (Isabelle, Mizar,
   Metamath), the growth step through N(H)/H (Mathlib, the Symmetry book,
   the 2007 MathComp of [GMRTT] § 4.1), and the maximal p-subgroups of
   Aschbacher's § 6 (MathComp today) all occur; M4-3 ([#17]) chooses.
+  **Agda**.  No Agda development proves Cauchy's theorem, the class
   equation or any of Sylow's theorems, so this library's would be the
   first, under `--safe` or otherwise, that the search found.

### 9.11 The queries

All on 2026-11-26.  GitHub code searches (`gh api search/code`), with
their counts of files, were as follows:

+  `Sylow language:Agda` 73; `Cauchy group language:Agda` 325; `Lagrange
   subgroup language:Agda` 20; `FiniteGroup language:Agda` 71;
   `"orbit-stabilizer" language:Agda` 19; `"class equation" language:Agda`
   4; `"Lagrange's theorem" language:Agda` 12;
+  for comparison, `Sylow language:Lean` 82,176; `Sylow language:Coq`
   253; `Sylow language:Isabelle` 70;
+  `Sylow language:"Literate Agda"` 0; `"open import" Sylow extension:md`
   0; `"open import" Lagrange subgroup extension:md` 5; `"open import"
   Cauchy group order extension:md` 19, none of them group theory;
+  `repo:UniMath/agda-unimath Finite-Group` 55 (`language:Agda` 0 and
   `language:Markdown` 54, since GitHub indexes `.lagda.md` as Markdown);
   `repo:UniMath/agda-unimath Decidable-Subgroup` 3;
+  `repo:leanprover-community/mathlib4 "stabilizer_eq_normalizer"` 1;
   `... "index_normalizer"` 1; `... stabilizer normalizer MulAut.conj` 1;
   `... "normalizer_eq_stabilizer"` 0; `... normalizer orbit index conj`
   6, none a lemma about an arbitrary subgroup;
+  `repo:isabelle-prover/mirror-isabelle path:src/HOL/Algebra Cauchy` 1
   (`UnivPoly.thy`); `repo:isabelle-prover/mirror-afp-devel sylow` 72;
   `... "Cauchy" "element of order"` 0; `... Cauchy group prime ord
   extension:thy` 9, none about groups.

Beside them, the file trees of the repositories named above were read
through the GitHub API at the revisions given, their files through
`raw.githubusercontent.com` at those revisions, Mizar's `mml.lar` and
abstracts from `mizar.uwb.edu.pl/version/current/`, and the Archive's
entry list from the tree of its mirror's `thys/` (1,048 entries).  The
2007 paper [GMRTT] was read in its HAL version (INRIA research report
RR-6156, inria-00139131v2), through the Internet Archive's capture of 24
October 2023; the MathComp book [MC] from Zenodo.

## References

+  [Aschbacher]: M. Aschbacher, *Finite Group Theory*, 2nd ed., Cambridge
   Studies in Advanced Mathematics 10, Cambridge University Press, 2000:
   § 4 (representations), § 5 ((5.3), (5.11) to (5.17)) and § 6 (Sylow's
   Theorem, p. 19).
+  [MRR]: R. Mines, F. Richman and W. Ruitenburg, *A Course in
   Constructive Algebra*, Universitext, Springer, 1988, Chapter I, § 2.
+  [GMRTT]: G. Gonthier, A. Mahboubi, L. Rideau, E. Tassi and L. Théry,
   "A modular formalisation of finite group theory", TPHOLs 2007, Lecture
   Notes in Computer Science 4732, 86-101, doi 10.1007/978-3-540-74591-4_8;
   read as INRIA research report RR-6156 (2007).
+  [MC]: A. Mahboubi and E. Tassi, *Mathematical Components*, Zenodo,
   2022, doi 10.5281/zenodo.7118596, §§ 7.3 to 7.6 (finite types, finite
   functions, finite sets).
+  [ADR 0001]; the plan, [`GITHUB_PROJECT.md`]; the spike, [`c86d93e`].
+  agda-algebras at `66c324f8`: [`Setoid.Algebras.Finite`],
   [`Setoid.Algebras.Finite.Irredundant`],
   [`Classical.Structures.Group.Basic`], and its ADR 008,
   [`008-two-layer-congruence-discipline.md`].

[ADR 0001]: ../adr/0001-finite-groups.md
[`GITHUB_PROJECT.md`]: ../GITHUB_PROJECT.md
[`c86d93e`]: https://github.com/ualib/agda-groups/tree/c86d93e2796e7568962b6eaa94b6efce1b31e15f/spike
[#5]: https://github.com/ualib/agda-groups/issues/5
[#6]: https://github.com/ualib/agda-groups/issues/6
[#7]: https://github.com/ualib/agda-groups/issues/7
[#8]: https://github.com/ualib/agda-groups/issues/8
[#14]: https://github.com/ualib/agda-groups/issues/14
[#17]: https://github.com/ualib/agda-groups/issues/17
[Aschbacher]: #references
[MRR]: #references
[GMRTT]: #references
[MC]: #references
[`Setoid.Algebras.Finite`]: https://github.com/ualib/agda-algebras/blob/66c324f89de176c2d5b4d3513d76034e4ffff2dd/src/Setoid/Algebras/Finite.lagda.md
[`Setoid.Algebras.Finite.Irredundant`]: https://github.com/ualib/agda-algebras/blob/66c324f89de176c2d5b4d3513d76034e4ffff2dd/src/Setoid/Algebras/Finite/Irredundant.lagda.md
[`Classical.Structures.Group.Basic`]: https://github.com/ualib/agda-algebras/blob/66c324f89de176c2d5b4d3513d76034e4ffff2dd/src/Classical/Structures/Group/Basic.lagda.md
[`008-two-layer-congruence-discipline.md`]: https://github.com/ualib/agda-algebras/blob/66c324f89de176c2d5b4d3513d76034e4ffff2dd/docs/adr/008-two-layer-congruence-discipline.md
