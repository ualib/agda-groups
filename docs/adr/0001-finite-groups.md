<!-- File: docs/adr/0001-finite-groups.md -->

# ADR 0001: finite groups

File: `agda-groups/docs/adr/0001-finite-groups.md`

+  **Status**: Proposed.  William chose the option of every decision area
   below on 2026-11-26, from the evidence recorded here; accepting the
   record is his, and M2-2 to M2-4 implement it.
+  **Date**: 2026-11-26.
+  **Tracking**: [#5] (M2-1, this record); [#6], [#7] and [#8] (M2-2 to
   M2-4, which implement it); [#14] (M3-6, the enumeration of a quotient,
   § 6); [#19] (M4-5, the two forms of the number of Sylow subgroups,
   § 4); [#25] (M6-1, the statements module, § 7).
+  **Ancestry**: the plan's "One notion of finite group" and "Two rules
   for the types of subgroups" ([`GITHUB_PROJECT.md`], "Scope and
   decisions", from the setup pull request [#1]); [#2] (M1-1, the
   toolchain and the options check, PR [#28]); agda-algebras' [ADR 008]
   (its two-layer discipline for finite algebras) and its irredundant
   enumerations; the spike at commit [`c86d93e`]; and the companion note
   [`finite-groups.md`], which explains the design and records the search
   of prior formalizations.

## Executive summary

**The idea**.  A finite group is agda-algebras' `Group` together with an
*irredundant enumeration* of its carrier: a bijection, up to the group's
own equality, between the carrier and `Fin n`, where n is the order.  A
subgroup is a *table*: a vector of n Booleans over the positions of the
enumeration (agda-stdlib's `Subset n`) that a Boolean test finds closed
under the group's operations.  So two subgroups with the same elements
are equal, propositionally and with no axiom; the subgroups of a finite
group form a finite set; and the number of Sylow p-subgroups is the size
of a finite set, as Aschbacher, the library's main reference, defines it.
agda-algebras' subgroups, which are predicates, pass to tables and back,
so its group theory applies unchanged.

**Why it is shaped this way**.  Three facts decided it, as follows:

+  under the library's flags, `--without-K --exact-split --safe`, two
   subgroups that are predicates with the same elements cannot be proved
   equal, and a premise that ends in a disjunction about every such
   subgroup proves excluded middle; of the libraries searched, MathComp
   alone gets equality of subgroups without an axiom or univalence, from
   Boolean tables over an enumeration;
+  a lookup of the index map (an element's position in the enumeration)
   through the enumeration agda-algebras derives by deduplication costs
   141 ms on A₅, against 23 ms for sixty lookups through an enumeration
   given directly, so the enumeration is data a finite group carries;
+  Aschbacher states Sylow's theorem about the set Syl_p(G) of Sylow
   p-subgroups, which needs the subgroups to form a finite set.

**Where it stands**.  Proposed.  The spike (`spike/` at [`c86d93e`])
built every notion in Agda under the library's flags with no postulate:
the orders of agda-algebras' Klein four-group V₄, S₃ and A₅ and of their
subgroups by evaluation; a subgroup and a quotient as finite groups;
Sylow's third theorem typed in two forms; the second rule in two forms,
with the passage between them; and A₅'s numbers of Sylow subgroups (6, 10
and 5) computed through one Sylow subgroup each, in under a second.
William chose the option of each area on 2026-11-26.

**Where it goes**.  M2-2 to M2-4 implement the types in the modules of
§ 8; M3-6 gives quotients an enumeration with a cheap index map (§ 6);
M4-5 proves the two forms of the number of Sylow subgroups equal (§ 4).

---

## 1.  The type of a finite group

(See also [#7], [`finite-groups.md`] §§ 1 and 2, and `Spike.Finite`,
`Spike.A5.IndexCost` and `Spike.TableGroups` at [`c86d93e`].)

**Decision**.  A finite group is a record of agda-algebras' `Group α ρ`
and agda-algebras' `IrredundantEnumeration` of its carrier, as data, and
its order is the enumeration's size.

+  **The terms**.  A *setoid* is a type with an equivalence relation `≈`
   that plays the part of equality; agda-algebras' algebras have setoid
   carriers.  An *irredundant enumeration* (agda-algebras'
   [`Setoid.Algebras.Finite.Irredundant`]) is a size `icard` with an
   enumeration `ienum[_] : Fin icard → carrier` that reaches every element
   up to `≈` and no element twice.  Its *index map* `idx` sends an element
   to its position.  In the vocabulary of Mines, Richman and Ruitenburg
   ([MRR], Chapter I, § 2), the carrier is then a *finite set*: a
   *discrete* set (equality decidable) in bijection with {1, ..., n}.
+  **The record**: `FiniteGroup α ρ` has the fields `group : Group α ρ`
   and `irredundant : IrredundantEnumeration (proj₁ group)`; `order` is
   `icard`.  The index map, decidable equality (`x ≈ y` exactly when `idx
   x ≡ idx y`) and a `FiniteAlgebra` witness are derived, so that
   agda-algebras' finite group theory (`NormalClosureᵈ`,
   `MinimalNormalDescent`, `cosetAlgebra-FiniteAlgebra`) applies.
+  **Where the enumeration comes from**: the identity, for a group on
   `Fin n` with propositional equality (agda-algebras' `TableGroup` and
   its examples); the positions of a table, for a subgroup (§ 6); one with
   an index map that normalizes no proof, for a quotient (§ 6); and
   agda-algebras' deduplication, `fromFiniteAlgebra`, for a group known
   only by a `FiniteAlgebra` witness (decidable `≈` and an enumeration
   that may repeat), which is correct and slow to evaluate.
+  **Groups on `Fin n`**, the second candidate of [#5], are a constructor
   and a view (M2-4), not the type: `FinGroup` is a group on `Fin n` with
   propositional equality, and *re-tabulation* takes every finite group to
   an isomorphic one, through its enumeration.

**Evidence**.  The record run of `spike/check.sh` at [`c86d93e`]
(2026-11-26, Agda 2.9.0, `--profile=definitions`), as follows:

+  **The index map through deduplication** (`Spike.A5.IndexCost`): on A₅,
   one lookup took 141 ms and the sixty lookups of one conjugate table
   21,156 ms (194, 195 and 182 ms, and 23,621, 23,641 and 20,960 ms, in
   three earlier runs the same day), against 23 ms for the same sixty
   lookups through the identity enumeration given directly.  The module
   that makes A₅'s counts through the deduplicated enumeration,
   `Spike.A5.Derived`, was stopped by `timeout 1200` after 20 minutes with
   no result; the distinct conjugates of one subgroup alone need 3,600
   lookups, about 21 minutes at that rate.  The same counts through the
   given enumeration (`Spike.A5.Given`) took 7.9 s for the whole module.
+  **The order without lookups**: through deduplication A₅'s order, 60,
   took 45 ms, so a group that is only counted needs no given enumeration.
+  **Re-tabulation** (`Spike.TableGroups`, `Spike.A4Examples`): A₄ inside
   A₅, re-tabulated onto `Fin 12`, counted its Sylow subgroups in 2,203
   ms against 1,057 ms for A₄ itself, since Agda keeps no table of a
   function's values; V₄, S₃ and A₅ re-tabulated have orders 4, 6 and 60
   by definition (`Spike.TableGroupExamples`).
+  **Applies to agda-algebras**: `toFiniteAlgebra` feeds
   `cosetAlgebra-FiniteAlgebra` in `Spike.Counting`, whose coset space
   gave the indices of § 4.

**Status**.  Chosen by William on 2026-11-26; M2-3 ([#7]) implements the
record in `Groups.Finite.Group`, and M2-4 ([#8]) the groups on `Fin n`.
Open: the quotient's enumeration ([#14], § 6).  Groups of permutations of
`Fin n`, the third candidate of [#5], were not tried; Cayley's theorem
(M2-4) passes to them.

## 2.  Subgroups as tables

(See also [#7], [`finite-groups.md`] § 3, and `Spike.Finite` at
[`c86d93e`].)

**Decision**.  The library's `Subgroup G` is a table over G's
enumeration with a proof of its closure, in `Set` whatever G's levels,
with the passage to and from agda-algebras' decidable subgroups.

+  **The type**: `Subgroup G = Σ[ χ ∈ Subset (order G) ] True (closed?
   χ)`, where `closed? χ` decides that the identity's position is in χ
   and that χ is closed under products and inverses, position by
   position.  `True d` is agda-stdlib's type of proofs that the decision
   d said yes, which has at most one element, so a subgroup is determined
   by its table.
+  **Membership and order**: x is in (χ , _) when the entry of χ at `idx
   x` is true; the order of a subgroup is the number of its true entries,
   agda-stdlib's `∣ χ ∣`.
+  **The bridge**: `toDec` makes a table into agda-algebras'
   `DecSubgroup` (a predicate with a proof that it is a subgroup and a
   decision procedure for its membership), and `fromDec` makes a
   `DecSubgroup` at any level into its table, with `fromDec (toDec H) ≡
   H` and `toDec (fromDec H) ≐ H` (each predicate inside the other).
+  **The finite set of subgroups**: the subgroups of G are the closed
   tables among the 2ⁿ subsets of `Fin n`, a finite set, as is every
   decidable family of them.

**Evidence**.  `Spike.Finite` at [`c86d93e`] proves the bridge, both
round trips, `same-elements→≡` (two tables with the same elements are
`≡`, with no axiom: § 3), the decidable equality of tables (`_≟ᵗ_`) and
of decidable subgroups up to `≐` (`≐?`).  The orders of the subgroups of
V₄ (1, 2, 4), S₃ (1, 2, 3, 6) and A₅ (5, 3, 4, 12) are computed by `refl`
(`Spike.SmallExamples`, `Spike.A5.Given`); a closure check on A₅ took
146 to 163 ms.  MathComp's representation is the same: a finite set is a
Boolean table over a type's enumeration, a group a set with the Boolean
test `group_set`, and `setP` and `group_inj` give equality with no axiom
([`finite-groups.md`] § 9.1).  Its designers moved from characteristic
functions to tables because the former "had forced us to use setoid"
([GMRTT], § 3.3).

**Status**.  Chosen by William on 2026-11-26; M2-3 ([#7]) implements it
in `Groups.Subgroup`.  No open follow-up.

## 3.  The two rules: equality and betweenness of subgroups

(See also [#7], [`finite-groups.md`] § 4, the plan's "Two rules", and
`Spike.Rules`, `Spike.RulesExamples` and `Spike.Oracle` at [`c86d93e`].)

**Decision**.  Statements over the library's subgroups say that two are
equal with `≡`, and may end in a disjunction about every subgroup; the
plan's two rules stay for agda-algebras' predicates.

+  **The rules**, as the plan states them for subgroups that are
   predicates: *the first rule*, that two subgroups with the same
   elements are not propositionally equal, so an equality of subgroups is
   a pair of inclusions; *the second rule*, that a premise ending in a
   disjunction about every subgroup proves excluded middle, so such a
   premise carries a witness ("a subgroup between H and K that holds an
   element outside H contains K").
+  **Tables meet both by construction**: two with the same elements are
   `≡` (§ 2), and a statement about every table between two is decidable,
   since there are finitely many and each entry is a Boolean.
+  **Both forms where a statement serves both**: the disjunctive form
   over tables and the witnessed form over agda-algebras' decidable
   subgroups are equivalent over every finite group, constructively, and
   a statement may give both, with the passage proved once.

**Evidence**.  `Spike.Oracle` proves, for S₃, that the disjunctive premise
"every subgroup between 1 and A₃ lies in 1 or contains A₃", over
agda-algebras' subgroups, gives `P ⊎ ¬ P` for every proposition P, by the
subgroup "x is 1, or P holds and x is in A₃".  Over tables the same
premise is decided: `between₂?` says yes between 1 and A₃ and no between
1 and S₃, over S₃'s 64 subsets, in 25 ms (`Spike.RulesExamples`).
`tables→witnessed` and `witnessed→tables` (`Spike.Rules`) prove the two
forms equivalent for every finite group.  The search found the same
trap stated by the Symmetry book's Rocq formalization, whose counting
form of Lagrange's theorem assumes the subgroup decidable, since
otherwise "finiteness of [G/H] (or of [H]) would decide [P]"
([`finite-groups.md`] § 9.9).

**Status**.  Chosen by William on 2026-11-26; M2-3 ([#7]) states the
notions over tables and gives the witnessed forms where agda-algebras'
notions (`MinimalNormal`, `MinimalNormalDescent`) quantify over
predicates.  No open follow-up.

## 4.  Counting conjugates and Sylow subgroups

(See also [#12], [#19], [`finite-groups.md`] § 5, and `Spike.Counting`,
`Spike.Sylow` and `Spike.SylowExamples` at [`c86d93e`].)

**Decision**.  The number nₚ of Sylow p-subgroups is defined in two
forms, the classical first: the number of subgroups of order pᵃ, and the
number of conjugates of one Sylow p-subgroup in hand; Sylow's third
theorem proves them equal.

+  **The classical form**: with pᵃ the largest power of p dividing |G|,
   nₚ is the size of the finite set Syl_p(G) of the subgroups of order pᵃ
   (§ 2), as Aschbacher writes it ([Aschbacher], § 6, p. 19) and as
   MathComp, Mizar, HOL Light and Metamath count it.
+  **The computed form**: the number of distinct conjugates g P g⁻¹ of
   one Sylow p-subgroup P (their tables, deduplicated), which is the
   index of its normalizer, |G : N_G(P)|, by the orbit-stabilizer
   theorem (Aschbacher (5.12)).
+  **Sylow's third theorem** (Aschbacher, Sylow's Theorem (3)) states the
   classical form: |Syl_p(G)| = |G : N_G(P)| ≡ 1 (mod p), so that it
   divides |G : P|.  A concrete group's nₚ is computed by the computed
   form and carried to the classical one by the theorem.
+  **The other counts** are as follows: the index |G : K| as the size of
   agda-algebras' coset space G/K, and as the number of distinct cosets
   as tables; the normalizer as a table.

**Evidence**.  The record run at [`c86d93e`], as follows:

+  **A₅** (`Spike.A5.Given`): the distinct conjugates of its Sylow 5-, 3-
   and 2-subgroups number 6, 10 and 5 (645, 665 and 654 ms); their
   normalizers have orders 10, 6 and 12, and indices 6, 10 and 5 by the
   coset space (93, 109, 91 ms) and by coset tables (525, 509, 510 ms).
+  **The classical form evaluated**: n₂(S₃) = 3 and n₃(S₃) = 1 among S₃'s
   64 subsets in 22 ms, and n₂(V₄) = 1 among 16 in 17 ms
   (`Spike.SylowExamples`); for A₅ the classical form ranges over 2⁶⁰
   subsets, and is not evaluated.
+  **Typed**: `Sylow₃ᵗ` states the theorem over tables with the classical
   nₚ; `Sylow₃ᵈ` over agda-algebras' decidable subgroups, which are
   predicates and form no finite set to count, so it adds that every
   Sylow p-subgroup is a conjugate of P (`Spike.Sylow`).

**Status**.  Chosen by William on 2026-11-26, with the rule of § 5.  M4-5
([#19]) proves the theorem in its classical form and the equality of the
two forms, and M3-4 ([#12]) the number of conjugates as the index of the
normalizer.  Open: enumerating a group's subgroups by generators (each of
A₅'s 59 subgroups is generated by two elements), which would make the
classical form evaluable beyond small groups; not tried.

## 5.  Both forms of a definition, the classical first

(See also [#6], [#7], [#19] and § 4.)

**Decision**.  Where a notion has a classical definition and a computed
one, the library gives both, the classical, natural one first (even when
it is the slower to evaluate), with the theorem that they agree.

+  **The rule is William's** (2026-11-26), stated for the number of
   Sylow subgroups "and other definitions".
+  **Its cases in the plan** include the following: the number of Sylow
   p-subgroups (§ 4); the number of conjugates of a subgroup (the size of
   its orbit, and the index of its normalizer); the index (the number of
   cosets, and |G|/|H| by Lagrange's theorem); the subgroup generated by a
   subset (the least subgroup that holds it, and its closure under
   products); and the decidable statements about every subgroup (§ 3).

**Evidence**.  § 4: the classical nₚ evaluates only for small groups,
and the computed form evaluates on A₅ in under a second; neither alone
gives both Aschbacher's statement and a computed number.

**Status**.  Chosen by William on 2026-11-26; M2-2 to M2-4 and each later
issue apply it where a notion has the two forms.  No open follow-up.

## 6.  Subgroups and quotients as finite groups

(See also [#7], [#14], [`finite-groups.md`] § 6, and
`Spike.Constructions`, `Spike.SubgroupEnumeration`,
`Spike.ConstructionExamples` and `Spike.A4Examples` at [`c86d93e`].)

**Decision**.  A subgroup is a finite group on the subtype of its
members, enumerated by the positions of its table; a quotient G/N is a
finite group on G's carrier under the congruence of N, whose
enumeration's index map normalizes no proof.

+  **A subgroup**: the carrier `Σ[ x ∈ G ] x ∈ H`, compared in G, with
   G's operations and equations (agda-algebras' `setoidEqsToGroup`), and
   the irredundant enumeration by the indices of G that H holds, in
   increasing order, whose index map walks G's index set once.
+  **A quotient by a normal subgroup N** (a table whose normality is
   decided by a sweep): agda-algebras' congruence of N (x ∼ y when x y⁻¹
   ∈ N) as the equality on G's carrier, so no representative is chosen
   until the order is counted, as agda-algebras' [ADR 008] prefers; its
   order by deduplication, and, for computing inside it, an enumeration
   with a cheap index map (least representatives are one way).

**Evidence**.  `Spike.ConstructionExamples` and `Spike.A4Examples` at
[`c86d93e`]: A₃ and ⟨s⟩ in S₃ are finite groups of orders 3 and 2, and A₄
in A₅ of order 12; |S₃/A₃| = 2, |V₄/⟨1⟩| = 2 and |A₅/1| = 60 (272 ms)
by deduplication.  Through the positions enumeration, A₄'s Sylow
3-subgroup has 4 conjugates, its normalizer has order 3, and its Sylow
2-subgroup is normal: Sylow's theorems counted inside a subgroup, in
1,057 ms.

**Status**.  The subgroup's enumeration by positions was part of the
option of § 1 that William chose on 2026-11-26, and M2-3 ([#7])
implements it in `Groups.Subgroup.Group`.  The quotient's is proposed
here.  Open: the quotient group and its enumeration, M3-6 ([#14]).

## 7.  The references

(See also [#5]'s comment of 2026-11-26, [#25], and the plan's "Sources".)

**Decision**.  Aschbacher's *Finite Group Theory* is the library's main
reference (William, 2026-11-26): the library follows its order where it
can, a module cites Aschbacher's number first and the plan's other books
beside it, and the statements module of M6-1 ([#25]) names each result
by Aschbacher's number where he states it.

+  **Why Aschbacher**, as William's comment on [#5] gives it: Aschbacher
   treats an action as a representation, a homomorphism into Sym(X),
   Aut(V) or Aut(H) ([Aschbacher], § 4), which is how agda-algebras sees
   a G-set; the book covers Sylow's theorem (§ 6), 1-cohomology (§ 17),
   coprime action (§ 18) and central extensions (§ 33); and MathComp's
   finite group theory cites it in more files than Gorenstein, Isaacs or
   Kurzweil and Stellmacher.
+  **The foundations**: Mines, Richman and Ruitenburg ([MRR]) name the
   notions (§ 1).
+  **The design**: Gonthier, Mahboubi, Rideau, Tassi and Théry ([GMRTT])
   and the MathComp book ([MC]), for finite types, finite functions and
   finite sets (§ 2).
+  **The others**: Kurzweil and Stellmacher, where a reader should learn
   from it; Gorenstein, for the results the plan cites by his numbers
   (Theorem 10.1.2 of M5-1); and the Symmetry book, read for its ideas,
   since its groups need univalence, which the flags exclude.

**Evidence**.  At MathComp's `master` of 2026-11-24, a grep of the 31
files of `finite_group/` and `solvable/` finds Aschbacher on 64 lines in
10 files and Kurzweil and Stellmacher on none; `action.v` reads "This is
Aschbacher (5.2)" ([`finite-groups.md`] § 9.1).  MathComp's
`Sylow's_theorem` states Aschbacher's four parts and proves them as
Aschbacher's § 6 does, through the maximal p-subgroups.

**Status**.  Decided by William on 2026-11-26, recorded here and not
reopened.  [#25]'s description names the main reference; the plan's
"Scope and decisions" still records the deferral of 2026-11-25 and
mirrors [#25] at its next `make update`, which is William's.

## 8.  The modules of M2-2 to M2-4

(See also [#6], [#7], [#8] and [`finite-groups.md`] § 7.)

**Decision**.  The types live in modules nested by topic under `Groups`,
as follows:

+  **M2-2** ([#6]): `Groups.Finite.Setoid` (`FiniteSetoid`, a setoid with
   an irredundant enumeration, the four fields of agda-algebras' record
   for a setoid that is not an algebra; sizes, bijections, the pigeonhole
   principle); `Groups.Finite.Subset` (detachable subsets as tables, and
   their sizes); `Groups.Finite.Sum` (sums and products, partitions, sums
   modulo p);
+  **M2-3** ([#7]): `Groups.Finite.Group` (`FiniteGroup`, `order`, the
   index map, decidable equality, `fromFiniteAlgebra`, `toFiniteAlgebra`);
   `Groups.Subgroup` (`Subgroup`, membership, inclusion, equality, order,
   `toDec`, `fromDec`, the finite set of subgroups);
   `Groups.Subgroup.Group` (a subgroup as a finite group);
   `Groups.Subgroup.Notions` (normal subgroups, abelian groups, powers,
   elementary abelian p-groups, the subgroups between two, complements,
   minimal normal subgroups);
+  **M2-4** ([#8]): `Groups.Table` (`FinGroup`, re-tabulation, and
   agda-algebras' examples as finite groups); `Groups.Cyclic`,
   `Groups.Symmetric` and `Groups.Cayley`.

**Evidence**.  The spike's modules at [`c86d93e`] are the first draft of
each, by topic: `Spike.Finite` of `Groups.Finite.Group` and
`Groups.Subgroup`, `Spike.SubgroupEnumeration` of
`Groups.Subgroup.Group`, `Spike.TableGroups` of `Groups.Table`.

**Status**.  Chosen by William on 2026-11-26.  M2-2 to M2-4 may split a
module, and say so in their pull requests.

## 9.  The spike

(See also [#5] and `spike/README.md` at [`c86d93e`].)

**Decision**.  The spike lives on the issue branch at [`c86d93e`], which
this record cites, and the pull request's last commit removes it.

+  **What it is**: 18 scratch modules under `spike/`, outside the library
   file's `include: src`, checked by `spike/check.sh` (`agda -i spike -i
   src`, under `make check`'s heap limit); `Spike.A5.Derived` is the one
   left out, since it does not finish.
+  **What it is not**: library code.  M2-2 to M2-4 write the library's
   modules afresh, and may take from the spike what serves.

**Evidence**.  The record run: the 17 modules of `spike/check.sh`
checked from scratch in 1 minute 22 seconds, and the options check of
M1-1 (`scripts/check-safety.sh`) passed over all 18 (each with
`--without-K --exact-split --safe` and no postulate).

**Status**.  Chosen by William on 2026-11-26.  The removal is this pull
request's last commit.

---

## 10.  Decision log

| # | Decision | Status | Evidence |
| --- | --- | --- | --- |
| 1 | A finite group is agda-algebras' `Group` with agda-algebras' `IrredundantEnumeration` of its carrier, as data; its order is `icard` (§ 1) | Proposed; chosen 2026-11-26; M2-3 ([#7]) | 141 ms per index lookup through deduplication on A₅, 23 ms for sixty through a given enumeration; the deduplicated module stopped at 20 minutes |
| 2 | Groups on `Fin n` are a constructor and a view, by re-tabulation, not the type (§ 1) | Proposed; chosen 2026-11-26; M2-4 ([#8]) | Re-tabulated A₄ 2,203 ms against 1,057 ms |
| 3 | A subgroup is a table over the enumeration with a Boolean closure proof, in `Set` (§ 2) | Proposed; chosen 2026-11-26; M2-3 ([#7]) | `same-elements→≡` with no axiom; MathComp's `{group gT}` |
| 4 | `toDec` and `fromDec` pass between tables and agda-algebras' `DecSubgroup`, with both round trips (§ 2) | Proposed; chosen 2026-11-26; M2-3 ([#7]) | `Spike.Finite`; `≐?` decides `≐` |
| 5 | Statements over tables use `≡` and may end in disjunctions about every subgroup; the two rules stay for predicates (§ 3) | Proposed; chosen 2026-11-26; M2-3 ([#7]) | `disjunctive→LEM` on S₃; `between₂?` decided in 25 ms |
| 6 | The disjunctive and witnessed forms are equivalent over a finite group, and a statement may give both (§ 3) | Proposed; chosen 2026-11-26 | `tables→witnessed`, `witnessed→tables` |
| 7 | nₚ in two forms, the classical first: the size of Syl_p(G), and the number of conjugates of one P; Sylow's third theorem equates them (§ 4) | Proposed; chosen 2026-11-26; M4-5 ([#19]) | A₅: 6, 10, 5 in under a second each; S₃ classical in 22 ms; A₅ classical over 2⁶⁰ subsets |
| 8 | Both forms of a definition, the classical first, with the theorem that they agree (§ 5) | Proposed; William's rule of 2026-11-26 | § 4 |
| 9 | A subgroup is a finite group enumerated by the positions of its table (§ 6) | Proposed; chosen 2026-11-26; M2-3 ([#7]) | A₄'s Sylow counts in 1,057 ms |
| 10 | A quotient is a finite group on G's carrier under N's congruence, with an index map that normalizes no proof (§ 6) | Proposed; for M3-6 ([#14]) | The orders of S₃/A₃ and A₅/1, 2 and 60, by deduplication |
| 11 | Aschbacher is the main reference; Mines, Richman and Ruitenburg the vocabulary; Gonthier et al. and the MathComp book the design (§ 7) | Decided by William, 2026-11-26 | His comment on [#5]; Aschbacher on 64 lines of MathComp |
| 12 | The modules of M2-2 to M2-4, nested by topic under `Groups` (§ 8) | Proposed; chosen 2026-11-26 | The spike's modules |
| 13 | The spike is cited at its commit and removed by the pull request's last commit (§ 9) | Proposed; chosen 2026-11-26 | `spike/check.sh`, 17 modules in 1 minute 22 seconds |

## References

+  **Issues**: [#5] (M2-1, this record, and William's comment of
   2026-11-26 on the main reference); [#2] (M1-1); [#6], [#7], [#8]
   (M2-2 to M2-4); [#12] (M3-4); [#14] (M3-6); [#19] (M4-5); [#25]
   (M6-1).
+  **Pull requests**: [#1] (the setup, which brought the plan); [#28]
   (M1-1).
+  **Docs**: the companion note [`finite-groups.md`]; the plan,
   [`GITHUB_PROJECT.md`]; agda-algebras' [ADR 008].
+  **The spike**: `spike/` at [`c86d93e`], with its `README.md`.
+  **Code** (agda-algebras at `66c324f8`):
   [`Setoid.Algebras.Finite`] (`FiniteAlgebra`),
   [`Setoid.Algebras.Finite.Irredundant`] (`IrredundantEnumeration`,
   `irredundantEnumeration`), [`Classical.Structures.Group.Subgroups`]
   (`IsSubgroup`, `DecSubgroup`).
+  **Books and papers**, as follows:
   +  [Aschbacher]: M. Aschbacher, *Finite Group Theory*, 2nd ed.,
      Cambridge Studies in Advanced Mathematics 10, Cambridge University
      Press, 2000;
   +  [MRR]: R. Mines, F. Richman and W. Ruitenburg, *A Course in
      Constructive Algebra*, Universitext, Springer, 1988;
   +  [GMRTT]: G. Gonthier, A. Mahboubi, L. Rideau, E. Tassi and L.
      Théry, "A modular formalisation of finite group theory", TPHOLs
      2007, Lecture Notes in Computer Science 4732, 86-101, doi
      10.1007/978-3-540-74591-4_8;
   +  [MC]: A. Mahboubi and E. Tassi, *Mathematical Components*, Zenodo,
      2022, doi 10.5281/zenodo.7118596.

[#1]: https://github.com/ualib/agda-groups/pull/1
[#2]: https://github.com/ualib/agda-groups/issues/2
[#5]: https://github.com/ualib/agda-groups/issues/5
[#6]: https://github.com/ualib/agda-groups/issues/6
[#7]: https://github.com/ualib/agda-groups/issues/7
[#8]: https://github.com/ualib/agda-groups/issues/8
[#12]: https://github.com/ualib/agda-groups/issues/12
[#14]: https://github.com/ualib/agda-groups/issues/14
[#19]: https://github.com/ualib/agda-groups/issues/19
[#25]: https://github.com/ualib/agda-groups/issues/25
[#28]: https://github.com/ualib/agda-groups/pull/28
[`finite-groups.md`]: ../notes/finite-groups.md
[`GITHUB_PROJECT.md`]: ../GITHUB_PROJECT.md
[`c86d93e`]: https://github.com/ualib/agda-groups/tree/c86d93e2796e7568962b6eaa94b6efce1b31e15f/spike
[ADR 008]: https://github.com/ualib/agda-algebras/blob/66c324f89de176c2d5b4d3513d76034e4ffff2dd/docs/adr/008-two-layer-congruence-discipline.md
[`Setoid.Algebras.Finite`]: https://github.com/ualib/agda-algebras/blob/66c324f89de176c2d5b4d3513d76034e4ffff2dd/src/Setoid/Algebras/Finite.lagda.md
[`Setoid.Algebras.Finite.Irredundant`]: https://github.com/ualib/agda-algebras/blob/66c324f89de176c2d5b4d3513d76034e4ffff2dd/src/Setoid/Algebras/Finite/Irredundant.lagda.md
[`Classical.Structures.Group.Subgroups`]: https://github.com/ualib/agda-algebras/blob/66c324f89de176c2d5b4d3513d76034e4ffff2dd/src/Classical/Structures/Group/Subgroups.lagda.md
[Aschbacher]: #references
[MRR]: #references
[GMRTT]: #references
[MC]: #references
