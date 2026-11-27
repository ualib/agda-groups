<!-- File: spike/README.md -->

# The spike for ADR 0001

Scratch modules for [ADR 0001] (issue 5): the evidence for its decisions,
not library code.  The modules from `Spike.Setoid` on were added later on
2026-11-26, to measure the setoid route (subgroups as agda-algebras'
`DecSubgroup`, equal when they have the same elements) against the
tables, on the same examples.  The library file does not include `spike/`, and the
pull request's last commit removes the directory, so the modules stay in
the history at the commit the ADR cites.  Every module carries `--without-K
--exact-split --safe`, and none has a postulate.

## Checking

Inside `nix develop`, at the repository root, as follows:

    bash spike/check.sh          # every module, with its profile
    bash spike/time.sh Spike/A5/Given --profile=definitions

`time.sh` removes the module's own interface first, so that Agda checks it
again, and runs `.agda/bin/agda -i spike -i src` under the heap limit of
`make check` (`+RTS -M6G -A128M -RTS`).  The `-i spike` is needed because
the library file's `include: src` does not cover `spike/`.
`--profile=definitions` prints the time of each definition; a check by
`refl` is an evaluation that Agda carries out while checking the module.

## The modules

+  **The two notions** (`Spike.Finite`).  A finite group as agda-algebras'
   `Group` with an irredundant enumeration of its carrier (a bijection, up
   to the setoid equality, with `Fin n`): given directly (`FiniteGroupⁱ`)
   or derived from agda-algebras' `FiniteAlgebra` by its deduplication
   (`FiniteGroupᶠ`).  The index map `idx`, decidable equality, and the
   `FiniteAlgebra` witness that the enumeration gives back.  Subgroups as
   tables (`SubgroupTable`: a `Subset n` with a Boolean closure check),
   their orders, `toDec` and `fromDec` to and from agda-algebras'
   `DecSubgroup` with both round trips, `same-elements→≡` (two subgroup
   tables with the same elements are equal, with no axiom), and the
   decidable equality of decidable subgroups (`≐?`).
+  **The counts** (`Spike.Counting`).  The distinct conjugates of a table,
   the normalizer as a table, and the index of a subgroup twice: as the
   size of agda-algebras' coset space (`cosetAlgebra-FiniteAlgebra`,
   deduplicated) and as the number of distinct left cosets as tables.
+  **The examples** (`Spike.SmallExamples`, `Spike.A5.Common`,
   `Spike.A5.Given`, `Spike.A5.IndexCost`).  The Klein four-group, S₃ and
   A₅ of agda-algebras' `Examples.Classical.Groups`, each with both
   enumerations: the orders of the groups and of their subgroups, and the
   counts of Sylow's third theorem.
+  **Constructions** (`Spike.Constructions`,
   `Spike.ConstructionExamples`, `Spike.SubgroupEnumeration`,
   `Spike.A4Examples`).  A subgroup table as a finite group (an
   agda-algebras `Group` on the subtype), with a surjective enumeration
   deduplicated or with the direct enumeration by the positions of its
   table; the quotient by a normal table as a finite group on the same
   carrier with the coarser equality, so that no representative is chosen
   until the order is counted; A₄ inside A₅ as a finite group, with its
   Sylow subgroups counted inside it.
+  **The second candidate** (`Spike.TableGroups`,
   `Spike.TableGroupExamples`).  A finite group on `Fin n` with
   propositional equality (`FinGroup`), and re-tabulation: every group
   with an irredundant enumeration is isomorphic to one, by its
   enumeration.
+  **Sylow's third theorem typed** (`Spike.Sylow`, `Spike.SylowExamples`).
   Over tables, with nₚ the number of subgroup tables of order pᵃ among
   all 2ⁿ subsets (Aschbacher's |Syl_p(G)|); over decidable subgroups,
   with nₚ the number of conjugates of one Sylow subgroup and Sylow's
   second theorem in the statement.
+  **The two rules** (`Spike.Rules`, `Spike.RulesExamples`,
   `Spike.Oracle`).  "Every subgroup between H and K is H or K" over
   tables, decidable; the witnessed form over decidable subgroups; the
   passage between the two; and, for subgroups that are predicates, the
   proof that the disjunctive form gives excluded middle.

+  **The setoid route** (`Spike.Setoid`).  A subgroup is agda-algebras'
   `DecSubgroup`, and two subgroups are equal when they have the same
   elements (`≐`, a pair of inclusions), which the enumeration decides
   (`_⊆?_`, `_≐?_`); a failed inclusion yields a witness by a search
   (`⊈-witness`).  The order counts the indices that a decider accepts
   (`orderˢ`).  Conjugates (`conjugateˢ`, from the preimage under
   conjugation, `preˢ`), the normalizer with its textbook predicate and
   decider (`normalizerˢ`), the index as the number of left cosets counted
   by their first members (`indexˢ`) or as the size of agda-algebras'
   coset space (`indexᶜ`), and `memo`, which remembers a decider as a
   table over the enumeration (the same subgroup, up to `≐`).
+  **Generated subgroups** (`Spike.Generated`), as GAP gives them.  x lies
   in ⟨A⟩ when a word in the generators and their inverses evaluates to x
   (`InGen A`).  The decider reads a Schreier vector, which a
   breadth-first search computes and three decided checks certify
   (`Cert`): the identity is reached, the reached indices are closed under
   every letter, and every word evaluates to its index.  The universal
   property (`gen⊆`: a subgroup holding A holds ⟨A⟩) gives decisions by
   the generators alone: inclusion (`gen⊆?`), the normalizer
   (`normalizer⟪⟫`, the textbook predicate decided by 2|A| conjugates),
   the equality of two conjugates (`conjGen≐?`), and the cyclic subgroups
   of a given order (`cyclicOfOrder`).  The records `Generators` and
   `Adjoined` hold the certificates, so that Agda compares their types by
   name and never evaluates a certificate again at a call.
+  **The examples** (`Spike.A5.Setoid`, `Spike.A5.SetoidNaive`,
   `Spike.A5.Cyclic`).  The checks of `Spike.A5.Given` on the setoid
   route, each subgroup given by the decider of its table and by
   generators, and A₄'s counts inside A₅ with no group built on A₄; two of
   them again with the deciders composed and never remembered; and the
   classical counts |Syl₅(A₅)| = 6 and |Syl₃(A₅)| = 10, by a search of the
   cyclic subgroups.
+  **The two rules on the setoid route** (`Spike.SetoidRules`,
   `Spike.SetoidRulesExamples`).  Equality of subgroups is `≐`, decided.
   From a condition on generators that a search decides (each element of
   K outside H = ⟨B⟩ generates K together with B), every decidable
   subgroup between H and K is H or K: a disjunction over every
   `DecSubgroup`, proved constructively, and conversely.  Decided on S₃
   (between 1 and A₃, and its failure between 1 and S₃, with S₃'s
   classical counts n₂ = 3 and n₃ = 1) and on A₅ (⟨t⟩ is a maximal
   subgroup of A₄), where a search of the tables would run over 2⁶⁰
   subsets.

## What was measured

The record run is `bash spike/check.sh` on 2026-11-26 in the dev shell
(Agda 2.9.0 and agda-stdlib 2.4.1 from the pinned agda-algebras,
`66c324f8`, on a 12th Gen Intel Core i9-12900H): all 17 modules checked
from scratch in 1 minute 22 seconds.  The times are those of
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

A blank cell was not measured.  Through the deduplicated enumeration the
checks of `Spike.A5.Given` were not measured at all: `Spike.A5.Derived`,
which makes them, was stopped by `timeout 1200` after 20 minutes with no
result, and `spike/check.sh` leaves it out.  In three earlier runs the
same day, one lookup took 194, 195 and 182 ms, and the 60 lookups 23,621,
23,641 and 20,960 ms.

## The setoid route, measured

The record run of all 24 modules is `bash spike/check.sh` later on
2026-11-26, on the same machine and toolchain: 1 minute 50 seconds, and
the options check of M1-1 passed over all 25 modules of `spike/`.  The
times are those of `--profile=definitions` in that run, on A₅ unless
the row says otherwise.  A blank cell was not measured, and "under 10 ms"
marks a check the profile did not list (it listed no entry under 10 ms in
any run).  The columns are as follows:

+  **Tables**: the earlier modules, rerun in the same run.
+  **Deciders composed**: subgroups by the deciders of their tables
   (`toDec`), with conjugates and normalizers built from them by
   `Spike.Setoid` and never remembered (`Spike.A5.Setoid` and
   `Spike.A5.SetoidNaive`), or remembered as tables by `memo` where the
   row says so.
+  **Generators**: subgroups by generators with a checked Schreier vector
   (`Spike.Generated`), every decision made by the generators alone.

| Check | Tables | Deciders composed | Generators |
| --- | ---: | ---: | ---: |
| Building ⟨s⟩, ⟨t⟩, V and A₄: the closure check, or the certificate | 151, 142, 163, 170 ms | | under 10, under 10, under 10, 12 ms |
| The distinct conjugates of the Sylow 5-, 3- and 2-subgroups (6, 10, 5) | 644, 649, 635 ms | 2,314 ms (the first) | 167, 206, 169 ms |
| The orders of their normalizers (10, 6, 12) | 190 ms (the three), after 242, 246, 297 ms of closure checks | 90, 61, 81 ms | 21, 12, 22 ms |
| The indices of the normalizers, by agda-algebras' coset space (6, 10, 5) | 114, 129, 92 ms | 388 ms (the first); remembered, 115, 109, 93 ms | 94, 130, 74 ms |
| The same indices, as distinct coset tables, or as cosets counted by first members | 613, 562, 595 ms | | 61, 161, 95 ms |
| A₄ in A₅: n₃(A₄) = 4 and V normal in A₄, by conjugates | 1,044 ms (A₄ by positions); 2,041 ms (A₄ on `Fin 12`) | | 36 ms, with no group built on A₄ |
| The classical counts \|Syl₅(A₅)\| = 6 and \|Syl₃(A₅)\| = 10 | out of reach (2⁶⁰ subsets) | | 308, 204 ms, after 632 ms for the 60 certificates of the ⟨x⟩ |
| S₃: the classical counts n₂ = 3 and n₃ = 1 | 21 ms (64 subsets) | | under 10 ms |
| S₃: every subgroup between 1 and A₃ is 1 or A₃, decided | 22 ms (64 subsets) | | under 10 ms |
| A₅: every subgroup between ⟨t⟩ and A₄ is ⟨t⟩ or A₄, decided | out of reach (2⁶⁰ subsets) | | 93 ms, after 3,982 ms for the 60 certificates of the ⟨x, t⟩ |

Two findings came with the numbers, as follows:

+  **A decider is a function, and Agda does not remember what it has
   answered.**  Deduplicated under `≐` over the enumeration, the 60
   conjugates of the Sylow 5-subgroup ask their deciders, each built from
   another decider, about every element of the group at each comparison:
   2,314 ms against the tables' 644.  Asking only about the generators
   (`conjGen≐?`, 2|A| questions a comparison), or remembering a decider as
   a table (`memo`), removes the cost.
+  **A certificate in a type at a call is evaluated again, and under a
   bound variable it is evaluated symbolically.**  A module opened with
   arguments (`open Generated a5-group a5-given`) defines copies of its
   names, and Agda compares a copy with the original by evaluating both.
   Passed as `∀ i → Cert (e[ i ] ∷ t ∷ []) (schreier (e[ i ] ∷ t ∷ []))`
   where the parameter's type named `Generators.gens 𝔾₃` for `t ∷ []`, the
   60 certificates exhausted the 6 GB heap in 49 s; passed as a value of
   the record `Adjoined (t ∷ [])`, which Agda compares by name, they cost
   the 3,982 ms of their own check.  So `Generators` and `Adjoined` hold
   every certificate.

[ADR 0001]: ../docs/adr/0001-finite-groups.md
