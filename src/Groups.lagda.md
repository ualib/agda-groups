---
layout: default
file: "src/Groups.lagda.md"
title: "Groups module"
date: "2026-11-25"
author: "the agda-groups development team"
---

### Groups

This is the `Groups` module of the agda-groups library: finite group theory
in Agda, on the group theory of the [Agda Universal Algebra Library][].

It is a barrel module: it declares nothing of its own and re-exports the
barrels of the directories under `Groups/`, each of which lists and
re-exports the modules of its directory, as follows:

+  `Groups.Finite`: finite setoids, decidable subsets and their sizes,
   sums and partitions, and finite groups with their orders;
+  `Groups.Subgroups`: the subgroups of a finite group, decided and
   counted, the subgroups given by generators, a subgroup as a finite
   group, and the notions about subgroups that later modules state;
+  `Groups.Examples`: the small groups V₄, S₃ and A₅ as finite groups.

The examples modules of each directory, which evaluate its lemmas, are
listed in its barrel and imported by none.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups where

open import Groups.Finite     public
open import Groups.Subgroups  public
open import Groups.Examples   public
```

[Agda Universal Algebra Library]: https://github.com/ualib/agda-algebras
