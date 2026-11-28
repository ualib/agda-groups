
<!-- File: src/README.md -->

# src/

The library's Agda modules, under `src/Groups/` (the namespace `Groups.*`),
each a literate Agda file (`.lagda.md`) that opens with
`{-# OPTIONS --without-K --exact-split --safe #-}` and has no postulate.
`agda-groups.agda-lib` names this directory as the library's `include`.

The modules are arranged as follows:

+  `Groups` (`Groups.lagda.md`) is the root barrel: it declares nothing
   and re-exports the barrel of each directory under `Groups/`.
+  Each directory `Groups/X/` has a barrel `Groups.X` beside it
   (`Groups/X.lagda.md`), which lists the modules of the directory with
   a line or two on each and re-exports them; the directory's first
   module, which the others build on, is `Groups.X.Basic` where it has
   one.  The barrels now are `Groups.Finite`, `Groups.Subgroups` and
   `Groups.Examples`.
+  An examples module, `Groups/X/Examples.lagda.md`, evaluates the lemmas
   of its directory.  Its barrel lists it and does not import it.

`make check` writes the aggregator `EverythingGroups.agda` here, which
imports every module, examples included, and is not tracked.  The plan,
`docs/GITHUB_PROJECT.md`, says what fills the rest, as follows:

+  ADR 0001 (M2-1) names the modules of finite groups and counting, and
   M2-2 to M2-4 write them.
+  Milestones 3 to 5 add cosets, actions and quotients (M3-1 to M3-6),
   p-groups and Sylow's theorems (M4-1 to M4-6), and the further results
   (M5-1 to M5-4); M6-1 adds the module of statements.
