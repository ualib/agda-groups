---
layout: default
file: "src/Groups/Examples.lagda.md"
title: "Groups.Examples module"
date: "2026-11-27"
author: "the agda-groups development team"
---

### Examples of finite groups

This is the `Groups.Examples` module of the agda-groups library.

It is a barrel module: it declares nothing of its own and re-exports the
modules under `Groups/Examples/`, the concrete finite groups that the
library's evaluations use, as follows:

+  `Groups.Examples.Small`: the Klein four-group V₄, the symmetric group
   S₃ and the alternating group A₅, from the Agda Universal Algebra
   Library's `Examples.Classical.Groups`, as finite groups with the
   identity enumeration; and A₅'s generators s and t, of orders 5 and 3,
   with two double transpositions that generate a Klein four-group.

The evaluations are in each topic's own examples module,
`Groups.Finite.Examples` and `Groups.Subgroups.Examples`, which no barrel
imports.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Examples where

open import Groups.Examples.Small  public
```
