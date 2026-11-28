---
layout: default
file: "src/Groups/Finite.lagda.md"
title: "Groups.Finite module"
date: "2026-11-27"
author: "the agda-groups development team"
---

### Finite setoids, counting and finite groups

This is the `Groups.Finite` module of the agda-groups library.

It is a barrel module: it declares nothing of its own and re-exports the
modules under `Groups/Finite/`, which give the finite setoids that the
library counts and the finite groups that it is about.  They are the
following:

+  `Groups.Finite.Setoid`: finite setoids, each a setoid with an
   irredundant enumeration, with the index map, decidable equality, the
   size's invariance under bijections, and the pigeonhole principle;
+  `Groups.Finite.Subset`: decidable subsets of a finite setoid, their
   tables and sizes, inclusion and equality decided, and a subset as a
   finite setoid in its own right;
+  `Groups.Finite.Sum`: sums and products of finite setoids, the classes
   of a decidable equivalence relation and their count, and sums modulo
   p;
+  `Groups.Finite.Group`: finite groups, the Agda Universal Algebra
   Library's groups with an irredundant enumeration of the carrier, their
   order, and the passage to and from that library's `FiniteAlgebra`.

`Groups.Finite.Examples` evaluates every public lemma of the first three
on `Fin 6` and its quotient by congruence modulo 3.  No barrel imports
it, so a module that imports this one neither checks the examples nor
takes their names.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Finite where

open import Groups.Finite.Setoid  public
open import Groups.Finite.Subset  public
open import Groups.Finite.Sum     public
open import Groups.Finite.Group   public
```
