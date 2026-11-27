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

Every module is checked by Agda under `--without-K --exact-split --safe`,
with no postulate, and each result cites its source by theorem number in
the textbooks that state it.

## Status

The repository holds its plan, its toolchain, ADR 0001 (how a finite
group and its subgroups are represented) and its first modules, as
follows:

+  the counting of finite setoids that later modules use:
   `Groups.Finite.Setoid`, `Groups.Finite.Subset` and `Groups.Finite.Sum`,
   with their evaluations in `Groups.Finite.Examples`;
+  finite groups and their subgroups, the types every later issue states
   its theorems over: `Groups.Finite.Group` (finite groups and their
   orders), `Groups.Subgroup` (decidable subgroups, their orders, and the
   subgroups built from them), `Groups.Subgroup.Generated` (subgroups
   given by generators), `Groups.Subgroup.Group` (a subgroup as a finite
   group) and `Groups.Subgroup.Notions` (normal subgroups, abelian and
   elementary abelian groups, the subgroups between two, complements and
   minimal normal subgroups), with V₄, S₃ and A₅ as finite groups in
   `Groups.Examples.Small` and the evaluations in
   `Groups.Subgroup.Examples`.

The plan, [`docs/GITHUB_PROJECT.md`](docs/GITHUB_PROJECT.md), has six
milestones, as follows:

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

## Checking the library

The toolchain is a [Nix][] flake, so a machine with Nix 2.28 or later, with
flakes enabled, needs nothing else:

    git clone https://github.com/ualib/agda-groups.git
    cd agda-groups
    nix develop --command make check

`make check` first runs the options check, `scripts/check-safety.sh`
(below), then generates `src/EverythingGroups.agda`, which imports every
module under `src/`, and type-checks it with a heap limit of 6 GiB
(`+RTS -M6G -A128M`), and last checks the plan's structure (`make lint`).
It exits 0 when every module checks.  There is no separate test step:
type-checking is the test.

`make check-lean` runs the options check, its cases
(`scripts/test-check-safety.sh`) and the plan's lint, with no Agda, in a
few seconds.  The shell `.#lean` holds everything but Agda, so
`nix develop .#lean --command make check-lean` fetches no Agda at all.

The Agda is the released Agda 2.9.0, which Nix builds from source in about
an hour unless it can fetch it from the public binary cache
`formalverification` on [Cachix][], where the Agda Universal Algebra
Library's CI puts it.  To fetch it, run `cachix use formalverification`
once, or add the following lines to your Nix configuration
(`/etc/nix/nix.conf`, or the `nix.conf` in your user's Nix configuration
directory if you are a trusted user):

    extra-substituters = https://formalverification.cachix.org
    extra-trusted-public-keys = formalverification.cachix.org-1:KG/AJuuli2F4/bA56rUYC9V8ZE/Zw6iZjxJEf40cQOo=

When a module first imports a module of the Agda Universal Algebra
Library, the next `make check` also checks that module and the modules it
imports, and keeps their interface files under `.deps/`, so later runs
check this library alone.

### On GitHub

Two workflows run on every push to a pull request and to `main`, as
follows:

+  `check.yml` runs `nix develop --command make check`, reading the Agda
   from the cache `formalverification` and pushing to no cache, and keeps
   `_build/` and `.deps/` between runs, so that a run checks only what
   changed.  A pull request whose files are all Markdown, other than
   literate Agda and the plan, passes it without running Agda.
+  `lean.yml` runs `nix develop .#lean --command make check-lean`, with no
   Agda, and reports in about a minute.

Each workflow's header says how it is built and why.

### What the options check holds

Under `--safe` Agda refuses postulates, unsafe options and the pragmas
that switch a check off, so every theorem is proved from the type theory
alone.  `scripts/check-safety.sh` (`make safety`) makes that claim visible
without running Agda, and is what holds a module to `--exact-split`, which
no importing module enforces.  It fails, naming the file, on each of the
following:

+  a module (`.agda` or `.lagda.md`) whose code does not carry exactly
   `{-# OPTIONS --without-K --exact-split --safe #-}`, once, ahead of its
   first declaration;
+  a `postulate`, or one of the pragmas `TERMINATING`, `NON_TERMINATING`,
   `NO_TERMINATION_CHECK`, `NO_POSITIVITY_CHECK`, `NO_UNIVERSE_CHECK`,
   `NON_COVERING`, `INJECTIVE`, `INJECTIVE_FOR_INFERENCE`, `POLARITY` or
   `COMPILE`, in a module's code (the word in prose, in a comment or in a
   string is no failure);
+  a module in another literate format, which neither the check nor the
   aggregator reads;
+  a `flags` field in `agda-groups.agda-lib`, which would add options to
   every module without any pragma showing them.

No module may add `--lossy-unification`, which `--safe` accepts: no
module of the Agda Universal Algebra Library uses it, and a module that
needs it is a decision to record first.

### The toolchain

`flake.lock` pins every input, as follows:

+  the [Agda Universal Algebra Library][agda-algebras] at commit
   [`66c324f8`][algebras-pin] of its master branch, pinned in `flake.nix`
   itself as well;
+  Agda 2.9.0 and the [Agda standard library][agda-stdlib] 2.4.1, both
   taken from that library's flake, so the one pin moves the library, the
   compiler and the standard library together;
+  nixpkgs, which follows that library's own pin;
+  the plan's engine, [github-project][].

`nix develop` writes a project-local Agda configuration (`.agda/`) and an
`agda` wrapper that names the standard library, the Agda Universal Algebra
Library and this library explicitly, so nothing in your own Agda
configuration takes part.  The library does not depend on agda-lattices.

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

## Contributing and citing

[`CONTRIBUTING.md`](CONTRIBUTING.md) says how a contribution is checked,
how a module is written and cited, and how its types are stated over the
library's finite groups and subgroups.  To cite the library, use the
metadata in [`CITATION.cff`](CITATION.cff); a DOI comes with the first
release.

## License

The library is licensed under the Apache License 2.0 (`LICENSE`).

## Acknowledgment

The plan and the formal development in this repository are produced with
the assistance of large language models, chiefly Claude (Anthropic), used
as tools under the author's direction; the author takes full
responsibility for every definition, statement and proof.

[Agda]: https://wiki.portal.chalmers.se/agda/
[agda-algebras]: https://github.com/ualib/agda-algebras
[algebras-pin]: https://github.com/ualib/agda-algebras/tree/66c324f89de176c2d5b4d3513d76034e4ffff2dd
[Cachix]: https://www.cachix.org/
[agda-lattices]: https://github.com/ualib/agda-lattices
[agda-stdlib]: https://github.com/agda/agda-stdlib
[github-project]: https://github.com/williamdemeo/github-project
[Nix]: https://nixos.org/
