<!-- File: spike/README.md -->

# The spike for ADR 0001

Scratch modules for [ADR 0001] (issue 5): the evidence for its decisions,
not library code.  The library file does not include `spike/`, and the
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

[ADR 0001]: ../docs/adr/0001-finite-groups.md
