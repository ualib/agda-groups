<!-- File: docs/adr/0001-finite-groups.md -->

# ADR 0001: finite groups

File: `agda-groups/docs/adr/0001-finite-groups.md`

+  **Status**: Proposed.  William chose the option of every decision area
   on 2026-11-26, and reopened the representation of subgroups the same
   day; §§ 2 to 4 record the option the second spike measured, which he
   asked for.  Accepting the record is his, and M2-2 to M2-4 implement it.
+  **Date**: 2026-11-26 (§§ 2 to 4, 6, 8 and 9 revised the same day).
+  **Tracking**: [#5] (M2-1, this record); [#6], [#7] and [#8] (M2-2 to
   M2-4, which implement it); [#10] (M3-2, the action on the conjugates of
   a subgroup, § 4); [#12] (M3-4, normalizers and generated subgroups,
   §§ 2 and 4); [#14] (M3-6, the enumeration of a quotient, § 6); [#19]
   (M4-5, the two forms of the number of Sylow subgroups, § 4); [#20]
   (M4-6, the worked examples, § 4); [#25] (M6-1, the statements module,
   § 7).
+  **Ancestry**: the plan's "One notion of finite group" and "Two rules
   for the types of subgroups" ([`GITHUB_PROJECT.md`], "Scope and
   decisions", from the setup pull request [#1]); [#2] (M1-1, the
   toolchain and the options check, PR [#28]); agda-algebras' [ADR 008]
   (its two-layer discipline for finite algebras), its irredundant
   enumerations and its decidable subgroups; GAP's subgroups, given by
   generators ([GAP]); the spike at commits [`c86d93e`] (the first) and
   [`1996be2`] (the second, which adds the setoid route); and the
   companion note [`finite-groups.md`], which explains the design and
   records the search of prior formalizations.

## Executive summary

**The idea**.  A finite group is agda-algebras' `Group` together with an
*irredundant enumeration* of its carrier: a bijection, up to the group's
own equality, between the carrier and `Fin n`, where n is the order.  A
subgroup is agda-algebras' *decidable subgroup*: a predicate on the
carrier, with a proof that it is a subgroup and a decision procedure for
its membership.  Two subgroups are equal when they have the same
elements (`≐`, a pair of inclusions), which the enumeration decides.  A
subgroup is given as GAP gives it, by generators: x lies in ⟨A⟩ when a
word in A and its inverses evaluates to x, and the decision procedure
reads a vector of such words, one for each element reached, that a
search computes and Agda checks.  Inclusion, normalizers and conjugates
are then decided by testing the generators alone.

**Why it is shaped this way**.  Four facts decided it, as follows:

+  agda-algebras is built on setoids, and its group theory on predicate
   subgroups up to `≐`; William's view (2026-11-26) is that setoids make
   the mathematics clearer and simpler, so the library keeps them rather
   than designing around them;
+  the two traps that the plan's rules guard against are traps for
   predicates in general: a decidable subgroup has a decided `≐`, and a
   disjunction about every decidable subgroup proves no excluded middle,
   since a subgroup built from a proposition P is decidable only when P
   is (§ 3);
+  by generators, no check on A₅ that the spike measured takes longer
   than by the tables of the first spike (Boolean vectors over the
   enumeration), beyond one index that took 130 ms against 129, and the
   counts of conjugates take a quarter of the time; two checks that a
   search of all 2⁶⁰ subsets of A₅ cannot reach take a third of a second
   or less, once their certificates are checked (§§ 3 and 4);
+  a lookup of the index map (an element's position in the enumeration)
   through the enumeration agda-algebras derives by deduplication costs
   141 ms on A₅, against 23 ms for sixty lookups through an enumeration
   given directly, so the enumeration is data a finite group carries
   (§ 1).

**Where it stands**.  Proposed.  The spike built every notion in Agda
under the library's flags with no postulate: the first spike
([`c86d93e`]) the finite groups and the tables, the second ([`1996be2`])
the decidable subgroups given by generators, beside the tables on the
same examples.  On A₅ the distinct conjugates of its Sylow subgroups take
167 to 206 ms by generators against 635 to 649 ms by tables, and A₄'s
Sylow counts inside A₅ 36 ms against 1,044 ms.  William chose the option
of each area on 2026-11-26.

**Where it goes**.  M2-2 to M2-4 implement the types in the modules of
§ 8; M3-6 gives quotients an enumeration with a cheap index map (§ 6);
M4-5 proves the two forms of the number of Sylow subgroups equal, and
M4-6 computes both on small groups (§ 4).

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
   its examples); the indices of G that a subgroup's decider accepts, for
   a subgroup as a group (§ 6); one with an index map that normalizes no
   proof, for a quotient (§ 6); and agda-algebras' deduplication,
   `fromFiniteAlgebra`, for a group known only by a `FiniteAlgebra`
   witness (decidable `≈` and an enumeration that may repeat), which is
   correct and slow to evaluate.
+  **Groups on `Fin n`**, the second candidate of [#5], are a constructor
   and a view (M2-4), not the type: `FinGroup` is a group on `Fin n` with
   propositional equality, and *re-tabulation* takes every finite group to
   an isomorphic one, through its enumeration.

**Evidence**.  The record run of `spike/check.sh` at [`c86d93e`]
(2026-11-26, Agda 2.9.0, `--profile=definitions`), as follows:

+  **The index map through deduplication** (`Spike.A5.IndexCost`): on A₅,
   one lookup took 141 ms and the sixty lookups of one conjugate table
   21,156 ms (194, 195 and 182 ms, and 23,621, 23,641 and 20,960 ms, in
   three earlier runs the same day; 171 ms and 19,653 ms in the record run
   at [`1996be2`]), against 23 ms for the same sixty lookups through the
   identity enumeration given directly.  The module that makes A₅'s
   counts through the deduplicated enumeration, `Spike.A5.Derived`, was
   stopped by `timeout 1200` after 20 minutes with no result; the
   distinct conjugates of one subgroup alone need 3,600 lookups, about 21
   minutes at that rate.
+  **The order without lookups**: through deduplication A₅'s order, 60,
   took 45 ms, so a group that is only counted needs no given enumeration.
+  **Re-tabulation** (`Spike.TableGroups`, `Spike.A4Examples`): A₄ inside
   A₅, re-tabulated onto `Fin 12`, counted its Sylow subgroups in 2,203
   ms against 1,057 ms for A₄ itself, since Agda keeps no table of a
   function's values; V₄, S₃ and A₅ re-tabulated have orders 4, 6 and 60
   by definition (`Spike.TableGroupExamples`).
+  **Applies to agda-algebras**: `toFiniteAlgebra` feeds
   `cosetAlgebra-FiniteAlgebra`, whose coset space gave the indices of
   § 4.

**Status**.  Chosen by William on 2026-11-26; M2-3 ([#7]) implements the
record in `Groups.Finite.Group`, and M2-4 ([#8]) the groups on `Fin n`.
Open: the quotient's enumeration ([#14], § 6).  Groups of permutations of
`Fin n`, the third candidate of [#5], were not tried; Cayley's theorem
(M2-4) passes to them.

## 2.  Subgroups as decidable predicates, given by generators

(See also [#7], [#12], [`finite-groups.md`] § 3, and `Spike.Setoid`,
`Spike.Generated`, `Spike.A5.Setoid`, `Spike.A5.SetoidNaive` and
`Spike.A5.Cyclic` at [`1996be2`].)

**Decision**.  The library's subgroup of G is agda-algebras'
`DecSubgroup`; two subgroups are equal when they have the same elements,
which G's enumeration decides; and a subgroup is given by generators,
with the textbook predicate and a decider that a checked certificate
makes fast.

+  **The terms**.  A *decidable subgroup* (agda-algebras'
   [`Classical.Structures.Group.Subgroups`]) is a predicate on G's
   carrier, a proof that it is a subgroup (it respects `≈` and is closed
   under the operations), and a decision procedure, a *decider*, for its
   membership.  `H ≐ K` (agda-stdlib's `Relation.Unary`) is the pair of
   inclusions H ⊆ K and K ⊆ H.  The type of decidable subgroups at level
   ℓ lies a universe above G's carrier, so a setoid of subgroups (the
   Sylow p-subgroups, § 4) does too.
+  **Order, inclusion and equality**: the order of H is the number of
   indices its decider accepts; H ⊆ K is decided at the enumerated
   elements and carried to every element by the respects field; `H ≐ K`
   is decided as two inclusions; and a failed inclusion yields a witness,
   an element of H outside K, by a search.
+  **The generated subgroup** ⟨A⟩ of a list A: x lies in it when some
   *word*, a list of elements of A and their inverses, evaluates to x.
   That is the textbook's description, and a proof of membership carries
   its word.  Its *universal property*: a subgroup that holds A holds
   ⟨A⟩, by induction on words.
+  **Its decider** reads a *Schreier vector*: for each index of G, a word
   that reaches it, or nothing.  A breadth-first search computes it, as
   GAP's orbit algorithm does, and three decided checks make it a
   *certificate*: the identity is reached, the reached indices are closed
   under every letter, and every word evaluates to its index.  A concrete
   group discharges the checks by evaluation, so the search is never
   trusted: a wrong one fails to type-check.
+  **Decisions by the generators alone**, from the universal property:
   ⟨A⟩ ⊆ K exactly when every element of A lies in K, as GAP tests
   inclusion of groups; g normalizes ⟨A⟩ exactly when g a g⁻¹ and g⁻¹ a g
   lie in ⟨A⟩ for every a in A; and two conjugates g⟨A⟩g⁻¹ and h⟨A⟩h⁻¹
   are compared through the |A| elements g a g⁻¹ each way.
+  **Constructions carry their proofs**: a conjugate (the preimage of H
   under conjugation) and a normalizer (the textbook predicate,
   conjugation by g and by g⁻¹ maps H into H) are subgroups by one proof
   each, for every H, and come with the textbook decider, which tests
   every enumerated element; a table needs a closure check of n² products
   for each new one.
+  **Certificates live in records**: `Generators` holds a list with its
   Schreier vector and certificate, and `Adjoined B` the certificates of
   every ⟨x, B⟩, so that no certificate stands in a type at a call (see
   the evidence).
+  **Tables** (agda-stdlib's `Subset n` over the enumeration, with a
   Boolean closure check) are not the library's subgroups.  `memo H`
   remembers a decider as its table over the enumeration, with `memo H ≐
   H`, for a computation that asks one decider many questions; and a
   search over all 2ⁿ subsets serves only the smallest groups.

**Evidence**.  The record run of `spike/check.sh` at [`1996be2`]
(2026-11-26, the same machine and toolchain: all 24 modules in 1 minute
50 seconds; `spike/README.md`, "The setoid route, measured"), as
follows:

+  **Building a subgroup**: the certificates of ⟨s⟩, ⟨t⟩ and V in A₅
   took under 10 ms each and A₄'s 12 ms, against 142 to 170 ms for the
   closure checks of their tables in the same run.  Here s = (0 1 2 3 4)
   and t = (0 1 2) are agda-algebras' generators of A₅, V is the subgroup
   of the double transpositions that fix the point 4, and A₄ the
   stabilizer of the point 4.
+  **Normalizers**: the orders of the normalizers of the Sylow 5-, 3- and
   2-subgroups (10, 6 and 12) took 21, 12 and 22 ms by generators, and
   90, 61 and 81 ms by the textbook decider; by tables, 190 ms for the
   three, after 242, 246 and 297 ms of closure checks.
+  **Deciders alone are not enough**: Agda does not remember what a
   function has answered, so with conjugates built from deciders and
   compared over the whole enumeration, the 60 conjugates of the Sylow
   5-subgroup took 2,314 ms, against 644 ms by tables and 167 ms by
   generators; with the normalizer's textbook decider asked afresh, the
   index of the normalizer took 388 ms, and 115 ms with the decider
   remembered by `memo`.
+  **The trap**: a module opened with arguments defines copies of its
   names, and Agda compares a copy with the original by evaluating both.
   The 60 certificates of the ⟨x, t⟩, x in A₅, passed where the
   parameter's type spelled `t ∷ []` as a projection of a record,
   exhausted the 6 GB heap in 49 s, the evaluation under a bound variable
   being symbolic; held in the record `Adjoined`, which Agda compares by
   name, they cost their own check, 3,982 ms.
+  **GAP** ([GAP], `master` at `407bf981`): `Subgroup(G, gens)` makes a
   subgroup from generators and records G as its parent
   (`lib/grp.gd:3946-3956`); two domains are equal when their sets of
   elements are (`lib/domain.gd:61-65`); `IsSubset` for two groups tests
   the generators (`lib/magma.gi:1232-1238`); and a stabilizer chain keeps
   a Schreier tree, "the orbit and transversal" of its generators
   (`lib/stbc.gd:760-775`).
+  **Why the first spike chose tables**, and why that no longer holds:
   MathComp gets equality of subgroups without an axiom from Boolean
   tables, whose designers left characteristic functions because they
   "had forced us to use setoid" ([GMRTT], § 3.3), for quotients; here a
   quotient is a setoid quotient on the same carrier (§ 6), and `≐`
   decided is the equality the mathematics uses.

**Status**.  Revised 2026-11-26, after William reopened the option of
tables chosen that morning; M2-3 ([#7]) implements it in
`Groups.Subgroup` and `Groups.Subgroup.Generated`, and M3-4 ([#12])
states the normalizer and the subgroup generated by a decidable subset
with it.  A certificate checked by evaluation serves a concrete group
only, so a theorem about every finite group (the commutator subgroup as
a decidable subgroup, ⟨H, x⟩ in Sylow's first theorem) needs a decider
of ⟨A⟩ for every finite group: M3-4 ([#12]) gives one, by closing A
under the letters in at most |G| steps, which the pigeonhole principle
of M2-2 bounds, and the certified Schreier vector stays the faster
decider of the same predicate for a concrete group.  Open: stabilizer
chains, for permutation groups too large to list.

## 3.  The two rules: equality and betweenness of subgroups

(See also [#7], [`finite-groups.md`] § 4, the plan's "Two rules",
`Spike.Rules`, `Spike.RulesExamples` and `Spike.Oracle` at [`c86d93e`],
and `Spike.SetoidRules` and `Spike.SetoidRulesExamples` at [`1996be2`].)

**Decision**.  An equality of subgroups is `≐`, never `≡`; a statement
may end in a disjunction about every decidable subgroup between two; and
the witnessed form serves where a statement quantifies over subgroups
that are predicates.

+  **The rules**, as the plan states them for subgroups that are
   predicates: *the first rule*, that two subgroups with the same
   elements are not propositionally equal, so an equality of subgroups is
   a pair of inclusions; *the second rule*, that a premise ending in a
   disjunction about every subgroup proves excluded middle, so such a
   premise carries a witness ("a subgroup between H and K that holds an
   element outside H contains K").
+  **Over decidable subgroups both rules are met**: `≐` is the equality,
   and it is decided; and the subgroup that the second rule builds from a
   proposition P, "x is 1, or P holds and x is in K", is decidable only
   when P is, so a disjunction about every decidable subgroup decides
   nothing new.
+  **The generator condition**: for H = ⟨B⟩ and a decidable K, every
   element x of K outside H generates K together with B (K ⊆ ⟨x, B⟩).  A
   search decides it, with one ⟨x, B⟩ for each x.  From it, every
   decidable subgroup L between H and K is H or K: L ⊆ H is decided, and
   otherwise a search finds an x in L outside H, so that ⟨x, B⟩ ⊆ L holds
   K.  Conversely, when H ⊆ K, the disjunction for the subgroups ⟨x, B⟩
   gives the condition.

**Evidence**.  At [`c86d93e`], `Spike.Oracle` proves, for S₃, that the
disjunctive premise over agda-algebras' predicate subgroups gives `P ⊎ ¬
P` for every proposition P, by the subgroup above.  At [`1996be2`],
`between` and `generates` (`Spike.SetoidRules`) prove the two directions
for every finite group, and `Spike.SetoidRulesExamples` decides the
condition on S₃ (yes between 1 and A₃, no between 1 and S₃, where ⟨s⟩
lies between) in under 10 ms each, against 22 ms for the search of S₃'s
64 subsets by tables; and on A₅ (every subgroup between ⟨t⟩ and A₄ is
one of the two, that is, ⟨t⟩ is maximal in A₄) in 93 ms, after 3,982 ms
for the 60 certificates of the ⟨x, t⟩, where the search by tables would
run over 2⁶⁰ subsets.  The search of prior formalizations found the same
trap in the Symmetry book's Rocq formalization, whose counting form of
Lagrange's theorem assumes the subgroup decidable, since otherwise
"finiteness of [G/H] (or of [H]) would decide [P]" ([`finite-groups.md`]
§ 9.9).

**Status**.  Revised 2026-11-26; M2-3 ([#7]) states the notions over
decidable subgroups, with both forms where a statement serves both, and
the witnessed forms where agda-algebras' notions (`MinimalNormal`,
`MinimalNormalDescent`) quantify over predicates.  No open follow-up.

## 4.  Counting conjugates and Sylow subgroups

(See also [#10], [#12], [#19], [#20], [`finite-groups.md`] § 5,
`Spike.Counting`, `Spike.Sylow` and `Spike.SylowExamples` at
[`c86d93e`], and `Spike.A5.Setoid` and `Spike.A5.Cyclic` at
[`1996be2`].)

**Decision**.  The number nₚ of Sylow p-subgroups is defined in two
forms, the textbook's first (§ 5): the size of the finite setoid
Syl_p(G), and the number of distinct conjugates of one Sylow p-subgroup
in hand; Sylow's third theorem proves them equal.

+  **The textbook form**: with pᵃ the largest power of p dividing |G|,
   Syl_p(G) is the setoid of the decidable subgroups of order pᵃ, under
   `≐`, as Aschbacher writes it ([Aschbacher], § 6, p. 19), and nₚ is its
   size as a finite setoid: the length of an irredundant enumeration of
   it (§ 1).  Sylow's second theorem enumerates it in general, by the
   conjugates of P; for a concrete group the search through generated
   subgroups checks it directly, since a subgroup of prime order is ⟨x⟩
   for each of its elements x other than 1 (by Lagrange's theorem).
+  **The computed form**: the number of distinct conjugates g P g⁻¹ of
   one Sylow p-subgroup P, decided by the generators (§ 2), which is the
   index of its normalizer, |G : N_G(P)|, by the orbit-stabilizer theorem
   (Aschbacher (5.12)).
+  **The conjugates of a subgroup H as a finite setoid**: G's elements,
   with g and h the same when g H g⁻¹ ≐ h H h⁻¹, which is the coset space
   G/N_G(H); so G acts on the conjugates of H by left multiplication on
   cosets (agda-algebras' `CosetAction`), and the setoid of subgroups is
   never acted on directly.
+  **Sylow's third theorem** (Aschbacher, Sylow's Theorem (3)) states the
   textbook form: |Syl_p(G)| = |G : N_G(P)| ≡ 1 (mod p), so that it
   divides |G : P|.
+  **The other counts** are as follows: the index |G : K| as the number
   of left cosets counted by their first members (x K = y K exactly when
   x⁻¹ y ∈ K), and as the size of agda-algebras' coset space G/K; the
   normalizer as a decidable subgroup.

**Evidence**.  The record run at [`1996be2`], as follows:

+  **A₅**: the distinct conjugates of its Sylow 5-, 3- and 2-subgroups
   number 6, 10 and 5, in 167, 206 and 169 ms by generators
   (`Spike.A5.Setoid`), against 644, 649 and 635 ms by tables in the same
   run; the indices of their normalizers are 6, 10 and 5, in 94, 130 and
   74 ms by the coset space and 61, 161 and 95 ms by first members,
   against 114, 129 and 92 ms and 613, 562 and 595 ms by tables.
+  **A₄ inside A₅**, with no group built on A₄: its Sylow 3-subgroup ⟨t⟩
   has 4 conjugates by the elements of A₄, and V has 1, in 36 ms, against
   1,044 ms by tables through A₄ as a finite group (§ 6).
+  **The textbook form evaluated**: |Syl₅(A₅)| = 6 and |Syl₃(A₅)| = 10,
   as the distinct cyclic subgroups of orders 5 and 3, in 308 and 204 ms
   after 632 ms for the 60 certificates of the ⟨x⟩ (`Spike.A5.Cyclic`),
   where tables range over 2⁶⁰ subsets; n₂(S₃) = 3 and n₃(S₃) = 1 the
   same way in under 10 ms, against 21 ms for S₃'s 64 subsets by tables.
+  **Typed**: at [`c86d93e`], `Spike.Sylow` states the theorem over tables
   with the textbook nₚ, and over decidable subgroups with the statement
   that every Sylow p-subgroup is a conjugate of P.

**Status**.  Revised 2026-11-26, with the rule of § 5.  M4-5 ([#19])
proves the theorem in its textbook form and the equality of the two
forms; M3-4 ([#12]) the number of conjugates as the index of the
normalizer; M3-2 ([#10]) the action on the conjugates; M4-6 ([#20]) both
forms on small groups.  Open: A₅'s Sylow 2-subgroups are not cyclic, so
the search for them adjoins a second generator, as GAP's cyclic
extension does; not tried.

## 5.  Both forms of a definition, the textbook's first

(See also [#6], [#7], [#19] and § 4.)

**Decision**.  Where a notion has a textbook definition and a computed
one, the library gives both, the textbook's first (even when it is the
slower to evaluate), with the theorem that they agree.

+  **The rule is William's** (2026-11-26), stated for the number of
   Sylow subgroups "and other definitions": both forms, "the 'natural' or
   classical (and potentially slower) one first".  *Classical* there
   means the textbook's definition, not classical logic: both forms are
   constructive.
+  **Its cases in the plan** include the following: the number of Sylow
   p-subgroups (§ 4); the number of conjugates of a subgroup (the size of
   its orbit, and the index of its normalizer); the index (the number of
   cosets, and |G|/|H| by Lagrange's theorem); the subgroup generated by
   a subset (the least subgroup that holds it, as the universal property
   states it, and the indices a Schreier vector reaches, with the
   certificate as the theorem that they agree); and the statements about
   every subgroup between two (the disjunction, and the generator
   condition, § 3).

**Evidence**.  § 4: the textbook nₚ evaluates on A₅ for p = 3 and 5 by
the search through cyclic subgroups, and the computed one for every p;
neither alone gives both Aschbacher's statement and a computed number
for every group.

**Status**.  Chosen by William on 2026-11-26; M2-2 to M2-4 and each later
issue apply it where a notion has the two forms.  No open follow-up.

## 6.  Subgroups and quotients as finite groups

(See also [#7], [#14], [`finite-groups.md`] § 6, and
`Spike.Constructions`, `Spike.SubgroupEnumeration`,
`Spike.ConstructionExamples` and `Spike.A4Examples` at [`c86d93e`].)

**Decision**.  A subgroup is a finite group on the subtype of its
members, enumerated by the indices of G that its decider accepts; a
quotient G/N is a finite group on G's carrier under the congruence of N,
whose enumeration's index map normalizes no proof.

+  **A subgroup**: the carrier `Σ[ x ∈ G ] x ∈ H`, compared in G, with
   G's operations and equations (agda-algebras' `setoidEqsToGroup`), and
   the irredundant enumeration by the indices of G whose elements H's
   decider accepts, in increasing order, whose index map walks G's index
   set once.  A theorem about finite groups applies to H this way (a
   Sylow subgroup of a subgroup); a count inside H needs no group built on
   it, since H's elements are G's indices that its decider accepts (§ 4).
+  **A quotient by a normal subgroup N** (a decidable subgroup whose
   normality is decided, by a sweep or by its generators): agda-algebras'
   congruence of N (x ∼ y when x y⁻¹ ∈ N) as the equality on G's carrier,
   so no representative is chosen until the order is counted, as
   agda-algebras' [ADR 008] prefers; its order by deduplication, and, for
   computing inside it, an enumeration with a cheap index map (least
   representatives are one way).

**Evidence**.  At [`c86d93e`], `Spike.ConstructionExamples` and
`Spike.A4Examples`: A₃ and ⟨s⟩ in S₃ are finite groups of orders 3 and
2, and A₄ in A₅ of order 12; |S₃/A₃| = 2, |V₄/⟨1⟩| = 2 and |A₅/1| = 60
(272 ms) by deduplication; through A₄'s own enumeration, its Sylow
3-subgroup has 4 conjugates, its normalizer has order 3, and its Sylow
2-subgroup is normal, in 1,057 ms.  At [`1996be2`], the same counts
inside A₅, with no group built on A₄, took 36 ms (§ 4).  The spike's
subgroups as groups were enumerated by the positions of their tables,
which are the indices their deciders accept.

**Status**.  The subgroup's enumeration was part of the option of § 1
that William chose on 2026-11-26, and M2-3 ([#7]) implements it in
`Groups.Subgroup.Group`.  The quotient's is proposed here.  Open: the
quotient group and its enumeration, M3-6 ([#14]).

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
+  **The design**: GAP ([GAP]), for subgroups given by generators and
   decided through them (§ 2); Gonthier, Mahboubi, Rideau, Tassi and
   Théry ([GMRTT]) and the MathComp book ([MC]), for finite types, finite
   functions and finite sets, and the tables of the first spike.
+  **The others**: Kurzweil and Stellmacher, where a reader should learn
   from it; Gorenstein, for the results the plan cites by his numbers
   (Theorem 10.1.2 of M5-1); and the Symmetry book, read for its ideas,
   since its groups need univalence, which the flags can neither prove
   nor postulate.

**Evidence**.  At MathComp's `master` of 2026-11-24, a grep of the 31
files of `finite_group/` and `solvable/` finds Aschbacher on 64 lines in
10 files and Kurzweil and Stellmacher on none; `action.v` reads "This is
Aschbacher (5.2)" ([`finite-groups.md`] § 9.1).  MathComp's
`Sylow's_theorem` states Aschbacher's four parts and proves them as
Aschbacher's § 6 does, through the maximal p-subgroups.

**Status**.  Decided by William on 2026-11-26, recorded here and not
reopened.  [#25]'s description names the main reference, and the plan's
"Scope and decisions" records it.

## 8.  The modules of M2-2 to M2-4

(See also [#6], [#7], [#8] and [`finite-groups.md`] § 7.)

**Decision**.  The types live in modules nested by topic under `Groups`,
as follows:

+  **M2-2** ([#6]): `Groups.Finite.Setoid` (`FiniteSetoid`, a setoid with
   an irredundant enumeration, the four fields of agda-algebras' record
   for a setoid that is not an algebra, at any universe level, since the
   setoid of a group's subgroups lies a universe above the group; sizes,
   bijections, the pigeonhole principle); `Groups.Finite.Subset`
   (detachable subsets as tables, which `memo` builds, and their sizes);
   `Groups.Finite.Sum` (sums and products, partitions, sums modulo p);
+  **M2-3** ([#7]): `Groups.Finite.Group` (`FiniteGroup`, `order`, the
   index map, decidable equality, `fromFiniteAlgebra`, `toFiniteAlgebra`);
   `Groups.Subgroup` (the library's subgroups, agda-algebras'
   `DecSubgroup`: membership, order, inclusion and equality decided, the
   witness of a failed inclusion, conjugates and normalizers with their
   textbook deciders, and `memo`); `Groups.Subgroup.Generated` (words, the
   generated subgroup and its universal property, Schreier vectors and
   their certificates, the records `Generators` and `Adjoined`, and the
   decisions by generators); `Groups.Subgroup.Group` (a subgroup as a
   finite group); `Groups.Subgroup.Notions` (normal subgroups, abelian
   groups, powers, elementary abelian p-groups, the subgroups between two
   with the generator condition, complements, minimal normal subgroups);
+  **M2-4** ([#8]): `Groups.Table` (`FinGroup`, re-tabulation, and
   agda-algebras' examples as finite groups); `Groups.Cyclic`,
   `Groups.Symmetric` and `Groups.Cayley`.

**Evidence**.  The spike's modules are the first draft of each, by
topic: `Spike.Finite` (at [`c86d93e`]) of `Groups.Finite.Group`;
`Spike.Setoid`, `Spike.Generated` and `Spike.SetoidRules` (at
[`1996be2`]) of `Groups.Subgroup`, `Groups.Subgroup.Generated` and the
subgroups between two; `Spike.SubgroupEnumeration` of
`Groups.Subgroup.Group`; `Spike.TableGroups` of `Groups.Table`.

**Status**.  Chosen by William on 2026-11-26, and revised with § 2 the
same day.  M2-2 to M2-4 may split a module, and say so in their pull
requests.

## 9.  The spike

(See also [#5] and `spike/README.md` at [`1996be2`].)

**Decision**.  The spike lives on the issue branch at two commits, which
this record cites, and the commit of the same pull request after its
revision removes it.  Merged with a merge commit, as pull requests [#1]
and [#28] were, the pull request keeps both commits in `main`'s
history.

+  **What it is**: scratch modules under `spike/`, outside the library
   file's `include: src`, checked by `spike/check.sh` (`agda -i spike -i
   src`, under `make check`'s heap limit): 18 at [`c86d93e`], and at
   [`1996be2`] the same 18 with seven more for the setoid route;
   `Spike.A5.Derived` is the one left out, since it does not finish.
+  **What it is not**: library code.  M2-2 to M2-4 write the library's
   modules afresh, and may take from the spike what serves, with `git
   show 1996be2:spike/Spike/Generated.agda`, say.

**Evidence**.  The record runs: at [`c86d93e`], 17 modules in 1 minute
22 seconds; at [`1996be2`], 24 in 1 minute 50 seconds; each time the
options check of M1-1 (`scripts/check-safety.sh`) passed over every
module of `spike/` (each with `--without-K --exact-split --safe` and no
postulate).

**Status**.  Chosen by William on 2026-11-26.  The pull request that
adds this record removes the spike, in the commit after its revision.

---

## 10.  Decision log

| # | Decision | Status | Evidence |
| --- | --- | --- | --- |
| 1 | A finite group is agda-algebras' `Group` with agda-algebras' `IrredundantEnumeration` of its carrier, as data; its order is `icard` (§ 1) | Proposed; chosen 2026-11-26; M2-3 ([#7]) | 141 ms per index lookup through deduplication on A₅, 23 ms for sixty through a given enumeration; the deduplicated module stopped at 20 minutes |
| 2 | Groups on `Fin n` are a constructor and a view, by re-tabulation, not the type (§ 1) | Proposed; chosen 2026-11-26; M2-4 ([#8]) | Re-tabulated A₄ 2,203 ms against 1,057 ms |
| 3 | A subgroup is agda-algebras' `DecSubgroup`, and equality of subgroups is `≐`, decided over the enumeration (§ 2) | Proposed; revised 2026-11-26 from tables; M2-3 ([#7]) | The second spike; William's preference for setoids |
| 4 | A subgroup is given by generators: membership is a word, decided by a Schreier vector whose certificate a concrete group checks by evaluation; inclusion, normalizers and conjugates are decided by the generators (§ 2) | Proposed; 2026-11-26; M2-3 ([#7]), M3-4 ([#12]) | A₅'s conjugates 167 to 206 ms against 635 to 649 ms by tables; certificates 12 ms or less against closure checks of 142 to 170 ms |
| 5 | Certificates are held in records (`Generators`, `Adjoined`), never in a type at a call (§ 2) | Proposed; 2026-11-26; M2-3 ([#7]) | The heap exhausted in 49 s, against 3,982 ms in a record |
| 6 | A decider asked many questions is remembered as a table (`memo`); tables are otherwise a search for the smallest groups (§ 2) | Proposed; 2026-11-26; M2-3 ([#7]) | Deciders composed: 2,314 ms; the normalizer's index 388 ms afresh, 115 ms remembered |
| 7 | Equality of subgroups is `≐`; a statement may end in a disjunction about every decidable subgroup between two, from the generator condition; the witnessed form serves predicates (§ 3) | Proposed; revised 2026-11-26; M2-3 ([#7]) | `disjunctive→LEM` for predicates on S₃; `between` and `generates`, decided on S₃ and on A₅ |
| 8 | nₚ in two forms, the textbook's first: the size of the finite setoid Syl_p(G), and the number of conjugates of one P; Sylow's third theorem equates them (§ 4) | Proposed; revised 2026-11-26; M4-5 ([#19]) | A₅'s computed forms in 167 to 206 ms; its textbook forms for p = 5 and 3 in 308 and 204 ms |
| 9 | Both forms of a definition, the textbook's first, with the theorem that they agree (§ 5) | Proposed; William's rule of 2026-11-26 | § 4 |
| 10 | A subgroup is a finite group enumerated by the indices its decider accepts (§ 6) | Proposed; chosen 2026-11-26; M2-3 ([#7]) | A₄'s Sylow counts in 1,057 ms as a group, 36 ms inside A₅ |
| 11 | A quotient is a finite group on G's carrier under N's congruence, with an index map that normalizes no proof (§ 6) | Proposed; for M3-6 ([#14]) | The orders of S₃/A₃ and A₅/1, 2 and 60, by deduplication |
| 12 | Aschbacher is the main reference; Mines, Richman and Ruitenburg the vocabulary; GAP, Gonthier et al. and the MathComp book the design (§ 7) | Decided by William, 2026-11-26 | His comment on [#5]; Aschbacher on 64 lines of MathComp |
| 13 | The modules of M2-2 to M2-4, nested by topic under `Groups` (§ 8) | Proposed; chosen and revised 2026-11-26 | The spike's modules |
| 14 | The spike is cited at its two commits and removed by the same pull request (§ 9) | Proposed; chosen 2026-11-26 | `spike/check.sh`: 17 modules in 1 minute 22 seconds, then 24 in 1 minute 50 seconds |

## References

+  **Issues**: [#5] (M2-1, this record, and William's comment of
   2026-11-26 on the main reference); [#2] (M1-1); [#6], [#7], [#8]
   (M2-2 to M2-4); [#10] (M3-2); [#12] (M3-4); [#14] (M3-6); [#19]
   (M4-5); [#20] (M4-6); [#25] (M6-1).
+  **Pull requests**: [#1] (the setup, which brought the plan); [#28]
   (M1-1).
+  **Docs**: the companion note [`finite-groups.md`]; the plan,
   [`GITHUB_PROJECT.md`]; agda-algebras' [ADR 008].
+  **The spike**: `spike/` at [`c86d93e`] and at [`1996be2`], each with
   its `README.md`.
+  **Code** (agda-algebras at `66c324f8`): [`Setoid.Algebras.Finite`]
   (`FiniteAlgebra`), [`Setoid.Algebras.Finite.Irredundant`]
   (`IrredundantEnumeration`, `irredundantEnumeration`),
   [`Classical.Structures.Group.Subgroups`] (`IsSubgroup`,
   `DecSubgroup`), [`Classical.Structures.Group.Conjugation`]
   (`Conjugate`, whose laws give the conjugates and normalizers of § 2).
+  **GAP** ([GAP], `master` at `407bf981`, 2026-11-26): [`lib/grp.gd`],
   [`lib/domain.gd`], [`lib/magma.gi`], [`lib/stbc.gd`].
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
      2022, doi 10.5281/zenodo.7118596;
   +  [GAP]: The GAP Group, *GAP: Groups, Algorithms, and Programming*,
      <https://www.gap-system.org>, read in its source at
      <https://github.com/gap-system/gap>.

[#1]: https://github.com/ualib/agda-groups/pull/1
[#2]: https://github.com/ualib/agda-groups/issues/2
[#5]: https://github.com/ualib/agda-groups/issues/5
[#6]: https://github.com/ualib/agda-groups/issues/6
[#7]: https://github.com/ualib/agda-groups/issues/7
[#8]: https://github.com/ualib/agda-groups/issues/8
[#10]: https://github.com/ualib/agda-groups/issues/10
[#12]: https://github.com/ualib/agda-groups/issues/12
[#14]: https://github.com/ualib/agda-groups/issues/14
[#19]: https://github.com/ualib/agda-groups/issues/19
[#20]: https://github.com/ualib/agda-groups/issues/20
[#25]: https://github.com/ualib/agda-groups/issues/25
[#28]: https://github.com/ualib/agda-groups/pull/28
[`finite-groups.md`]: ../notes/finite-groups.md
[`GITHUB_PROJECT.md`]: ../GITHUB_PROJECT.md
[`c86d93e`]: https://github.com/ualib/agda-groups/tree/c86d93e2796e7568962b6eaa94b6efce1b31e15f/spike
[`1996be2`]: https://github.com/ualib/agda-groups/tree/1996be2fb8250b67d55debb0b7335699cab2eb58/spike
[ADR 008]: https://github.com/ualib/agda-algebras/blob/66c324f89de176c2d5b4d3513d76034e4ffff2dd/docs/adr/008-two-layer-congruence-discipline.md
[`Setoid.Algebras.Finite`]: https://github.com/ualib/agda-algebras/blob/66c324f89de176c2d5b4d3513d76034e4ffff2dd/src/Setoid/Algebras/Finite.lagda.md
[`Setoid.Algebras.Finite.Irredundant`]: https://github.com/ualib/agda-algebras/blob/66c324f89de176c2d5b4d3513d76034e4ffff2dd/src/Setoid/Algebras/Finite/Irredundant.lagda.md
[`Classical.Structures.Group.Subgroups`]: https://github.com/ualib/agda-algebras/blob/66c324f89de176c2d5b4d3513d76034e4ffff2dd/src/Classical/Structures/Group/Subgroups.lagda.md
[`Classical.Structures.Group.Conjugation`]: https://github.com/ualib/agda-algebras/blob/66c324f89de176c2d5b4d3513d76034e4ffff2dd/src/Classical/Structures/Group/Conjugation.lagda.md
[`lib/grp.gd`]: https://github.com/gap-system/gap/blob/407bf9814f63742fe2a296a06582d568bf2c5d77/lib/grp.gd#L3946-L3956
[`lib/domain.gd`]: https://github.com/gap-system/gap/blob/407bf9814f63742fe2a296a06582d568bf2c5d77/lib/domain.gd#L61-L65
[`lib/magma.gi`]: https://github.com/gap-system/gap/blob/407bf9814f63742fe2a296a06582d568bf2c5d77/lib/magma.gi#L1232-L1238
[`lib/stbc.gd`]: https://github.com/gap-system/gap/blob/407bf9814f63742fe2a296a06582d568bf2c5d77/lib/stbc.gd#L760-L775
[Aschbacher]: #references
[MRR]: #references
[GMRTT]: #references
[MC]: #references
[GAP]: #references
