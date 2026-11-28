<!-- File: docs/notes/finite-groups.md -->

# Finite groups and their subgroups

The companion note to [ADR 0001], which records the decisions; this note
explains them and records the search of prior formalizations behind them.
It describes the design that M2-2 to M2-4 ([#6], [#7], [#8]) implement,
as the spike of issue [#5] built it.  The spike is the scratch modules
under `spike/`, at two commits: [`c86d93e`], which built the finite
groups and the tables, and [`1996be2`], which added the setoid route of
§§ 3 to 5 beside them.  The pull request that adds this note removes
them before the merge, and `spike/README.md` at the second commit has
their map and timings.

The names in `code` that the spike defines are in the modules
`Spike.Finite`, `Spike.Counting`, `Spike.Constructions`,
`Spike.SubgroupEnumeration`, `Spike.TableGroups`, `Spike.Sylow`,
`Spike.Rules`, `Spike.Setoid`, `Spike.Generated` and `Spike.SetoidRules`;
the library's own names, in M2-2 to M2-4, may differ.

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
   the indices of G that its decider accepts (§ 6);
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

## 3.  Subgroups

A **subgroup** of a finite group G is agda-algebras' `DecSubgroup`: a
predicate H on G's carrier, a proof that it is a subgroup (`IsSubgroup
H`: H respects `≈` and is closed under the operations), and a *decider*
of its membership, `∀ x → Dec (x ∈ H)`.  The names below are those of
`Spike.Setoid` and `Spike.Generated` at [`1996be2`].

+  **Order, inclusion and equality**.  The order of H counts the indices
   whose elements its decider accepts (`orderˢ`).  H ⊆ K is decided at
   the n enumerated elements and carried to every x by the respects
   fields, through `idx x` (`_⊆?_`); H ≐ K, the two inclusions, is
   decided as both (`_≐?_`); and a failed inclusion yields an index whose
   element lies in H and not in K, by a search (`⊈-witness`).  So the
   decidable subgroups of a finite group form a discrete setoid under
   `≐`, in the sense of § 1.
+  **The universe level**.  A decidable subgroup at level ℓ is a
   predicate with its proofs, so the type of them lies in `Type (α ⊔ ρ ⊔
   suc ℓ)`, a universe above G's carrier.  A setoid of subgroups, such as
   Syl_p(G) (§ 5), lies there too, and M2-2 takes its finite setoids at
   any level.
+  **Constructions**.  The preimage of H under conjugation by g, {x | g x
   g⁻¹ ∈ H}, is a subgroup for every H, by agda-algebras' laws of
   conjugation (`Conjugate`: conjugation by g is an endomorphism)
   (`preˢ`); the conjugate g H g⁻¹ is the preimage under g⁻¹
   (`conjugateˢ`); and the normalizer is the textbook predicate,
   "conjugation by g and by g⁻¹ maps H into H", a subgroup by one proof
   for every H (`Normalizes`, `normalizes-isSubgroup`).  Each comes with
   its textbook decider: the preimage's asks H's at g x g⁻¹, and the
   normalizer's tests every enumerated element of H.

**Subgroups by generators**.  GAP makes a subgroup from generators
(`Subgroup(G, gens)`, [GAP] `lib/grp.gd:3946-3956`), computes its
structure when asked, and tests the inclusion of one group in another on
the generators (`lib/magma.gi:1232-1238`).  `Spike.Generated` does the
same, as follows:

+  **Words**.  For a list A of elements of G, a *letter* is an element of
   A or its inverse (an index into A and a Boolean), a *word* is a list of
   letters, and `eval` multiplies a word out.  x lies in ⟨A⟩ when some
   word evaluates to x (`InGen A x = Σ[ w ∈ Word ] eval w ≈ x`): the
   textbook's description of the subgroup generated by A, and a proof of
   membership carries its word.  It is a subgroup: the product of two
   words is their concatenation, and the inverse of a word is its letters
   flipped, in the opposite order.
+  **The universal property**: a subgroup that holds every element of A
   holds ⟨A⟩, by induction on words (`gen⊆`).  It is the textbook's
   "least subgroup that holds A", stated without a quantifier over all
   subgroups.
+  **The Schreier vector**: for each index of G, a word that reaches it,
   or nothing.  A breadth-first search over the letters computes it from
   the identity, as GAP's orbit algorithm computes an orbit with its
   transversal (a stabilizer chain keeps such a Schreier tree,
   `lib/stbc.gd:760-775`).  Three checks make it a *certificate*
   (`Cert`): the identity's index is reached; the reached indices are
   closed under right multiplication by every letter; and every word
   evaluates to the element at its index.  Each check is decidable, and a
   concrete group discharges it by evaluation, so nothing rests on the
   search being right: a wrong search fails to type-check.
+  **The decider**.  x is in ⟨A⟩ when the vector holds a word at `idx x`,
   and the third check makes that word the proof.  When the vector holds
   nothing there, the first two checks show, by induction on words, that
   every word evaluates to a reached index, so no word reaches x.
+  **Decisions by the generators alone**, from the universal property:
   ⟨A⟩ ⊆ K exactly when every element of A lies in K (`gen⊆?`), |A|
   questions to K's decider where the enumeration asks n; g normalizes
   ⟨A⟩ exactly when g a g⁻¹ and g⁻¹ a g lie in ⟨A⟩ for every a in A
   (`normalizesGen?`, the universal property applied to the preimages of
   ⟨A⟩ under conjugation); and g⟨A⟩g⁻¹ ⊆ h⟨A⟩h⁻¹ exactly when every g a
   g⁻¹ lies in h⟨A⟩h⁻¹ (`conjGen⊆?`).  The normalizer by generators is
   the textbook predicate with the faster decider (`normalizer⟪⟫`).
+  **Certificates in records**.  `Generators` holds a list, its Schreier
   vector and its certificate, and `Adjoined B` the certificates of every
   ⟨x, B⟩, x in G.  A function of a subgroup takes the record, so that no
   certificate stands in a type at a call: there Agda compares it with
   another spelling of itself by evaluating both, and under a bound
   variable it evaluates them symbolically.  Passed that way, the 60
   certificates of the ⟨x, t⟩ in A₅ exhausted the 6 GB heap in 49 s; in
   the record they cost their own check, 3,982 ms (§ 8).

**Tables** (§ 1) were the first spike's subgroups: a `Subset n` over the
enumeration with a Boolean closure check, `Σ[ χ ∈ Subset n ] True
(closed? χ)` (`Spike.Finite` at [`c86d93e`]).  Two tables with the same
elements are equal, `≡`, with no axiom (`same-elements→≡`), and the
tables of G form a finite set, the closed ones among the 2ⁿ subsets.
That is MathComp's representation (§ 9.1), whose designers moved from
characteristic functions to Boolean tables because the former "had
forced us to use setoid" ([GMRTT], § 3.3), for quotients.  Here
quotients are setoid quotients on the same carrier (§ 6), and tables
keep two roles, as follows:

+  `memo H` remembers a decider as its table, `toDec (fromDec H)`, with
   `memo H ≐ H` (`toDec∘fromDec`): a decider is a function, and Agda does
   not remember what a function has answered, so a computation that asks
   one decider many questions asks it once per index instead;
+  a search over all 2ⁿ subsets decides statements about every subgroup
   of the smallest groups (S₃ has 64 subsets, A₅ 2⁶⁰).

The first spike's `toDec` and `fromDec` pass between the two, with
`fromDec (toDec H) ≡ H` and `toDec (fromDec H) ≐ H`.

## 4.  The two rules for the types of subgroups

The plan states two rules for any type of subgroups under `--without-K
--safe` ([`GITHUB_PROJECT.md`], "Scope and decisions"), as follows:

+  **the first rule**: two subgroups with the same elements are not
   propositionally equal, so an equality of subgroups is stated as a pair
   of inclusions;
+  **the second rule**: a premise that ends in a disjunction about every
   subgroup proves excluded middle, since a subgroup can be built from an
   arbitrary proposition, so such a premise carries a witness instead.

Both are facts about subgroups that are predicates.  `Spike.Oracle` (at
[`c86d93e`]) checks the second on S₃: for any proposition P, the
predicate "x is 1, or P holds and x is in A₃" is a subgroup between 1
and A₃, so the premise "every subgroup L between 1 and A₃ lies in 1 or
contains A₃", over agda-algebras' subgroups, proves `P ⊎ ¬ P`
(`disjunctive→LEM`).

Decidable subgroups meet both rules.  Equality is `≐`, the pair of
inclusions, and it is decided (§ 3).  The subgroup that the oracle
builds is decidable only when P is, so a disjunction about every
*decidable* subgroup decides nothing new, and a statement over the
library's subgroups may end in one.

**The generator condition** makes such a disjunction provable for a
concrete group.  For H = ⟨B⟩ and a decidable K, the condition is that
every element x of K outside H generates K together with B, K ⊆ ⟨x, B⟩
(`Generates`, in `Spike.SetoidRules` at [`1996be2`]).  A search decides
it (`generates?`), with one ⟨x, B⟩ for each x, whose certificates
`Adjoined B` holds.  From it, every decidable subgroup L between H and K,
at any level, is H or K (`between`): L ⊆ H is decided; if it fails,
`⊈-witness` finds an x in L outside H, x is in K, and ⟨x, B⟩ ⊆ L by the
universal property, since L holds x and B; so L holds K.  Conversely,
when H ⊆ K, the disjunction for the subgroups ⟨x, B⟩ gives the condition
(`generates`).  So over decidable subgroups the disjunctive form and the
plan's witnessed form are equivalent, constructively.

`Spike.SetoidRulesExamples` decides the condition on S₃ (yes between 1
and A₃; no between 1 and S₃, which has ⟨s⟩ between) and on A₅, between
⟨t⟩ and A₄, where it shows ⟨t⟩ maximal in A₄ in 93 ms after 3,982 ms of
certificates (§ 8).  The first spike decided the case of S₃ by tables,
over its 64 subsets (`between₂?`, in 22 to 25 ms); for A₅ that search
would run over 2⁶⁰.

## 5.  Counting

Every count is a natural number that Agda computes by evaluation (a check
by `refl`), as follows:

+  **the order** of a group, `icard`, and of a subgroup, the indices its
   decider accepts;
+  **the index** of a subgroup K, twice: as the number of left cosets x K
   counted by their first members, the indices i with no smaller j such
   that e[j]⁻¹ e[i] ∈ K (`indexˢ`, through `#classes`); and as the size of
   agda-algebras' coset space G/K (`cosetAlgebra-FiniteAlgebra`: G's
   enumeration with the coset relation, decided by K's decider), whose
   irredundant enumeration agda-algebras computes (`indexᶜ`);
+  **the conjugates** of a subgroup H: G's elements, deduplicated by the
   conjugate each gives, g and h the same when g H g⁻¹ ≐ h H h⁻¹, decided
   by the generators when H has them (`#conjugates⟪⟫`).  The classes are
   the left cosets of N_G(H), so the conjugates of H form the finite
   setoid G/N_G(H), on which G acts by left multiplication;
+  **the normalizer** of H, as a decidable subgroup, by the textbook
   decider or by the generators.

**The number nₚ of Sylow p-subgroups** has two forms ([ADR 0001], § 5:
both forms of a definition, the textbook's first), as follows:

+  **the textbook form**: with pᵃ the largest power of p dividing |G|, nₚ
   is the size of the finite setoid Syl_p(G) of the decidable subgroups
   of order pᵃ under `≐`, as Aschbacher defines it ([Aschbacher], § 6, p.
   19: "Write Syl_p(G) for the set of Sylow p-subgroups of G") and as
   MathComp, Mizar, HOL Light and Metamath count it (§ 9); its size is
   the length of an irredundant enumeration of it;
+  **the computed form**: the number of distinct conjugates of one Sylow
   p-subgroup P in hand, or the index of its normalizer, |G : N_G(P)|.

Aschbacher's Sylow's Theorem (3) is that they agree: |Syl_p(G)| = |G :
N_G(P)| ≡ 1 (mod p).  The number of conjugates of P is |G : N_G(P)| by
the orbit-stabilizer theorem (Aschbacher (5.12)), and it is |Syl_p(G)|
because G is transitive on Syl_p(G), by conjugation (Sylow's Theorem
(2)), which also gives Syl_p(G) its enumeration, by the conjugates of P.
`Spike.Sylow` (at [`c86d93e`]) types the theorem both ways.

What evaluation reaches, measured (§ 8), is as follows:

+  **the computed form**, for every p: on A₅ the distinct conjugates of
   the Sylow 5-, 3- and 2-subgroups number 6, 10 and 5, in 167, 206 and
   169 ms by generators (by tables, 635 to 649 ms each), and the indices
   of their normalizers (of orders 10, 6 and 12) are 6, 10 and 5;
+  **the textbook form**, by a search through generated subgroups: a
   subgroup of prime order is ⟨x⟩ for each of its elements x other than
   1 (by Lagrange's theorem, M3-1), so when p² does not divide |G| the
   distinct cyclic subgroups of order p are Syl_p(G).  On A₅, |Syl₅(A₅)|
   = 6 and |Syl₃(A₅)| = 10 in 308 and 204 ms, after 632 ms for the 60
   certificates of the ⟨x⟩ (`Spike.A5.Cyclic`); on S₃, n₂ = 3 and n₃ = 1
   in under 10 ms.  The tables' search over all subsets reaches S₃ (64
   subsets, in 21 to 22 ms) and not A₅ (2⁶⁰).

A₅'s Sylow 2-subgroups are Klein four-groups, not cyclic, so the textbook
search for them adjoins a second generator to a cyclic subgroup, as GAP's
cyclic extension builds a group's subgroups ([GAP], `lib/grplatt.gd`);
it was not tried.

## 6.  Subgroups and quotients as finite groups

**A subgroup as a finite group** (`Constructions.AsGroup` at
[`c86d93e`]).  The carrier is the subtype of the members, `Σ[ x ∈ G ] x
∈ H`, compared in G; the operations are G's, closed by H's closure; the
five equations are G's (agda-algebras' `setoidEqsToGroup`).  Two
enumerations of it were built, as follows:

+  a surjective enumeration by all n indices of G, sending an index
   outside H to the identity, from which agda-algebras' deduplication
   computes the order (A₄ inside A₅: 12; A₃ and ⟨s⟩ inside S₃: 3 and 2);
+  the irredundant enumeration by the indices of G whose elements H
   holds, in increasing order (`SubgroupEnumeration.Positions`, which
   read them off H's table: the indices its decider accepts), whose index
   map walks G's index set once.

Through the second, A₄ is a finite group of order 12 in which the Sylow
3-subgroup ⟨(0 1 2)⟩ has 4 conjugates, its normalizer has order 3, and
the Sylow 2-subgroup is normal: Sylow's theorems applied inside a
subgroup, counted in 1,057 ms (`Spike.A4Examples`).  A count inside a
subgroup needs no group built on it: the same counts inside A₅, by
generators, with the conjugates deduplicated over A₄'s elements, took 36
ms (`Spike.A5.Setoid` at [`1996be2`]).  The subgroup as a group serves a
theorem about finite groups applied to a subgroup.

**The quotient by a normal subgroup** (`Constructions.Quotient` at
[`c86d93e`]).  For a decidable subgroup N whose normality is decided (by
a sweep, `normal?`, or by its generators), the quotient G/N is
agda-algebras' `Group` on the same carrier with the coarser equality x ∼
y when x y⁻¹ ∈ N (agda-algebras' `NormalCon`, the congruence of a normal
subgroup), and its `FiniteAlgebra` witness is G's own enumeration,
decided by N's decider.  No representative is chosen until the order is
counted, as agda-algebras' ADR 008 prefers
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
   `IrredundantEnumeration` for a setoid that is not an algebra), at any
   universe level, with sizes, bijections and the pigeonhole principle;
   `Groups.Finite.Subset`, detachable subsets as tables, with their
   sizes; `Groups.Finite.Sum`, sums and products, partitions, and sums
   modulo p;
+  M2-3 ([#7]): `Groups.Finite.Group` (`FiniteGroup`, its order, index
   map, decidable equality, `fromFiniteAlgebra`, `toFiniteAlgebra`);
   `Groups.Subgroups.Basic` (agda-algebras' `DecSubgroup` as the library's
   subgroups: membership, order, inclusion and equality decided, the
   witness of a failed inclusion, conjugates and normalizers with their
   textbook deciders, and `memo`); `Groups.Subgroups.Generated` (words,
   the generated subgroup and its universal property, Schreier vectors
   and their certificates, `Generators` and `Adjoined`, and the
   decisions by generators); `Groups.Subgroups.Group` (a subgroup as a
   finite group); `Groups.Subgroups.Notions` (normal subgroups, abelian
   groups, powers, elementary abelian p-groups, the subgroups between two
   with the generator condition, complements, minimal normal subgroups);
+  M2-4 ([#8]): `Groups.Table` (groups on `Fin n`, re-tabulation, and
   agda-algebras' examples as finite groups); `Groups.Cyclic`,
   `Groups.Symmetric`, `Groups.Cayley`.

Each directory `Groups/X/` has a barrel `Groups.X`, which lists the
directory's modules and re-exports them, and `Groups` re-exports the
barrels; an examples module is named in its barrel and imported by
none (William, 2026-11-27).

## 8.  What the spike measured

**The first record run** is `bash spike/check.sh` at [`c86d93e`] on
2026-11-26, in the dev shell (Agda 2.9.0 and agda-stdlib 2.4.1 from
agda-algebras at `66c324f8`, on a 12th Gen Intel Core i9-12900H): the 17
modules it lists checked from scratch in 1 minute 22 seconds, each under
`--without-K --exact-split --safe` with no postulate, and the options
check of M1-1 passed over all 18 modules of `spike/`.  The times are
Agda's own, by `--profile=definitions`, as follows:

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

**The second record run** is `bash spike/check.sh` at [`1996be2`], later
the same day on the same machine and toolchain: the 24 modules it lists,
the 17 and seven for the setoid route, checked from scratch in 1 minute
50 seconds, and the options check passed over all 25 modules of
`spike/`.  Its times, with the first spike's modules rerun in the same
run, are in the table below, whose columns give a subgroup in three
ways, as follows:

+  **tables**: the first spike's modules;
+  **deciders composed**: subgroups by the deciders of their tables, with
   conjugates and normalizers built from them and never remembered, or
   remembered by `memo` where the row says so;
+  **generators**: subgroups by generators with a checked Schreier
   vector, each decision made by the generators alone.

| Check (on A₅ unless the row says otherwise) | Tables | Deciders composed | Generators |
| --- | ---: | ---: | ---: |
| Building ⟨s⟩, ⟨t⟩, V and A₄: the closure check, or the certificate | 151, 142, 163, 170 ms | | under 10, under 10, under 10, 12 ms |
| The distinct conjugates of the Sylow 5-, 3- and 2-subgroups (6, 10, 5) | 644, 649, 635 ms | 2,314 ms (the first) | 167, 206, 169 ms |
| The orders of their normalizers (10, 6, 12) | 190 ms (the three), after 242, 246, 297 ms of closure checks | 90, 61, 81 ms | 21, 12, 22 ms |
| The indices of the normalizers, by agda-algebras' coset space (6, 10, 5) | 114, 129, 92 ms | 388 ms (the first); remembered, 115, 109, 93 ms | 94, 130, 74 ms |
| The same indices, as distinct coset tables, or as cosets counted by first members | 613, 562, 595 ms | | 61, 161, 95 ms |
| A₄ in A₅: n₃(A₄) = 4 and V normal in A₄, by conjugates | 1,044 ms (A₄ by positions); 2,041 ms (A₄ on `Fin 12`) | | 36 ms, with no group built on A₄ |
| The textbook counts \|Syl₅(A₅)\| = 6 and \|Syl₃(A₅)\| = 10 | out of reach (2⁶⁰ subsets) | | 308, 204 ms, after 632 ms for the 60 certificates of the ⟨x⟩ |
| S₃: the textbook counts n₂ = 3 and n₃ = 1 | 21 ms (64 subsets) | | under 10 ms |
| S₃: every subgroup between 1 and A₃ is 1 or A₃, decided | 22 ms (64 subsets) | | under 10 ms |
| A₅: every subgroup between ⟨t⟩ and A₄ is ⟨t⟩ or A₄, decided | out of reach (2⁶⁰ subsets) | | 93 ms, after 3,982 ms for the 60 certificates of the ⟨x, t⟩ |

"Under 10 ms" marks a check the profile did not list; it listed no
entry under 10 ms in either run.  A blank cell was not measured.  In the
same run the index map through deduplication took 171 ms for one lookup
and 19,653 ms for sixty, against 31 ms for sixty through the given
enumeration.

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
   its ideas, since its groups need univalence, which the flags can
   neither prove nor postulate.
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
   no equality of subgroups.  Tables are the one design that makes
   equality of subgroups `≡` under this library's flags; this library
   meets the first rule instead with `≐`, which its finite groups decide
   (§ 4).
+  **Decidability**.  agda-unimath takes a finite subgroup of a finite
   group to be a decidable subgroup (`Subgroup-Finite-Group`), beside its
   subgroups of any group, which are subtypes; and the Symmetry book's
   Rocq formalization assumes the subgroup decidable in its counting form
   of Lagrange's theorem.  Both keep decidability as a hypothesis or as
   data, for the reason of the second rule: that every subgroup of a
   finite group is decidable would decide an arbitrary proposition, by
   the subgroup of § 4.
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
+  [GAP]: The GAP Group, *GAP: Groups, Algorithms, and Programming*,
   <https://www.gap-system.org>, read in its source at `master`,
   `407bf981` (2026-11-26): [`lib/grp.gd`], [`lib/magma.gi`],
   [`lib/stbc.gd`], [`lib/grplatt.gd`].
+  [ADR 0001]; the plan, [`GITHUB_PROJECT.md`]; the spike, at
   [`c86d93e`] and [`1996be2`].
+  agda-algebras at `66c324f8`: [`Setoid.Algebras.Finite`],
   [`Setoid.Algebras.Finite.Irredundant`],
   [`Classical.Structures.Group.Basic`], and its ADR 008,
   [`008-two-layer-congruence-discipline.md`].

[ADR 0001]: ../adr/0001-finite-groups.md
[`GITHUB_PROJECT.md`]: ../GITHUB_PROJECT.md
[`c86d93e`]: https://github.com/ualib/agda-groups/tree/c86d93e2796e7568962b6eaa94b6efce1b31e15f/spike
[`1996be2`]: https://github.com/ualib/agda-groups/tree/1996be2fb8250b67d55debb0b7335699cab2eb58/spike
[`lib/grp.gd`]: https://github.com/gap-system/gap/blob/407bf9814f63742fe2a296a06582d568bf2c5d77/lib/grp.gd#L3946-L3956
[`lib/magma.gi`]: https://github.com/gap-system/gap/blob/407bf9814f63742fe2a296a06582d568bf2c5d77/lib/magma.gi#L1232-L1238
[`lib/stbc.gd`]: https://github.com/gap-system/gap/blob/407bf9814f63742fe2a296a06582d568bf2c5d77/lib/stbc.gd#L760-L775
[`lib/grplatt.gd`]: https://github.com/gap-system/gap/blob/407bf9814f63742fe2a296a06582d568bf2c5d77/lib/grplatt.gd
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
[GAP]: #references
[`Setoid.Algebras.Finite`]: https://github.com/ualib/agda-algebras/blob/66c324f89de176c2d5b4d3513d76034e4ffff2dd/src/Setoid/Algebras/Finite.lagda.md
[`Setoid.Algebras.Finite.Irredundant`]: https://github.com/ualib/agda-algebras/blob/66c324f89de176c2d5b4d3513d76034e4ffff2dd/src/Setoid/Algebras/Finite/Irredundant.lagda.md
[`Classical.Structures.Group.Basic`]: https://github.com/ualib/agda-algebras/blob/66c324f89de176c2d5b4d3513d76034e4ffff2dd/src/Classical/Structures/Group/Basic.lagda.md
[`008-two-layer-congruence-discipline.md`]: https://github.com/ualib/agda-algebras/blob/66c324f89de176c2d5b4d3513d76034e4ffff2dd/docs/adr/008-two-layer-congruence-discipline.md
