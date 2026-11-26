<!-- File: README.md -->

# agda-groups

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](./LICENSE)

Finite group theory in [Agda][], on the group theory of the [Agda Universal
Algebra Library][agda-algebras], as [agda-lattices][] is lattice theory on
it.

The Agda Universal Algebra Library develops groups as algebras of a
signature: subgroups and their lattice, cosets, conjugation, normal
subgroups as congruences, minimal normal subgroups, complements and
permuting subgroups, Dedekind's rule, centralizers, commutators, G-sets and
the regular and coset actions, products, wreath products, simple groups,
and groups given by their tables.  It has no Lagrange's theorem, no class
equation, and neither Cauchy's theorem nor Sylow's.  This library imports
those modules, rather than copying them, and adds the counting of finite
group theory and the theorems that rest on it, as follows:

+  finite groups, their subgroups and their orders, and Cayley's theorem;
+  cosets, the index and Lagrange's theorem; group actions and the
   orbit-stabilizer theorem; the product formula; normalizers,
   centralizers and the center; conjugacy classes and the class equation;
   quotient groups and the correspondence theorem;
+  p-groups and their centers, Cauchy's theorem, and Sylow's three
   theorems in full;
+  fixed-point-free automorphisms (Gorenstein, *Finite Groups*, Theorem
   10.1.2); abelian minimal normal subgroups, which are elementary
   abelian; the commutator subgroup and perfect groups; and the
   complements of an abelian normal subgroup and their 1-cocycles.

Every module will be checked by Agda under `--without-K --exact-split
--safe`, with no postulate, and each result cites its source by theorem
number in the textbooks that state it.

## Status

The repository holds its plan and no Agda yet.  The plan,
[`docs/GITHUB_PROJECT.md`](docs/GITHUB_PROJECT.md), has six milestones, as
follows:

1.  the repository and its toolchain;
2.  finite groups and counting, beginning with ADR 0001, the decision on
    how a finite group and its subgroups are represented so that they can
    be counted;
3.  cosets and actions;
4.  p-groups and Sylow's theorems;
5.  further textbook results;
6.  the release, with a documentation site and a Zenodo DOI.

Each milestone and issue is defined in the plan, and the issues are on
GitHub once the plan is populated.

## The toolchain

The library is to be checked with Agda 2.9.0 and the [Agda standard
library][agda-stdlib] 2.4.1, both taken from the [Agda Universal Algebra
Library][agda-algebras]'s own Nix flake, together with that library itself,
pinned by `flake.lock`; it does not depend on agda-lattices.  The first
issue of the plan, M1-1, adds the flake, the library file, an options check
that every module carries those flags and no postulate, and
`nix develop --command make check`.

## The plan and its commands

The plan is one Markdown file in the format of [github-project][]: the
milestones, the labels, and every issue's text, with a graph of the
dependencies among the issues of each milestone.  Its engine is a pinned
input of this repository's flake, so `nix develop` puts it on `PATH`, and
`make help` lists the commands.  The ones in use are as follows:

+  `make lint` checks the plan's structure, offline;
+  `make populate-dry` shows what `make populate` would create on GitHub;
+  `make populate` creates the labels, the milestones and the issues;
+  `make update` brings the plan's generated regions up to date with the
   issues on GitHub.

After the first populate, an issue's text is edited on GitHub, and
`make update` mirrors it into the plan.

## License

The library is licensed under the Apache License 2.0 (`LICENSE`).

## Acknowledgment

The plan and the formal development in this repository are produced with
the assistance of large language models, chiefly Claude (Anthropic), used
as tools under the author's direction; the author takes full
responsibility for every definition, statement and proof.

[Agda]: https://wiki.portal.chalmers.se/agda/
[agda-algebras]: https://github.com/ualib/agda-algebras
[agda-lattices]: https://github.com/ualib/agda-lattices
[agda-stdlib]: https://github.com/agda/agda-stdlib
[github-project]: https://github.com/williamdemeo/github-project
