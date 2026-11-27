---
layout: default
file: "src/Groups/Broken.lagda.md"
title: "Groups.Broken (throwaway)"
date: "2026-11-26"
author: "the agda-groups development team"
---

A module broken on purpose, to see the full check fail.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Groups.Broken where

open import Data.Nat using (ℕ; zero)
open import Data.Bool using (Bool)

broken : ℕ
broken = Bool.true
```
