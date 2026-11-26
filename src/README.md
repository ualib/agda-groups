<!-- File: src/README.md -->

# src/

The library's Agda modules, under `src/Groups/` (the namespace `Groups.*`),
each a literate Agda file (`.lagda.md`) that opens with
`{-# OPTIONS --without-K --exact-split --safe #-}` and has no postulate.
`agda-groups.agda-lib` names this directory as the library's `include`.

The directory holds no module yet.  The plan, `docs/GITHUB_PROJECT.md`,
says what fills it, as follows:

+  M1-1 adds the first module, `Groups`, with nothing in it but its
   header, so that `make check` has a module to check.
+  ADR 0001 (M2-1) names the modules of finite groups and counting, and
   M2-2 to M2-4 write them.
+  Milestones 3 to 5 add cosets, actions and quotients (M3-1 to M3-6),
   p-groups and Sylow's theorems (M4-1 to M4-6), and the further results
   (M5-1 to M5-4); M6-1 adds the module of statements.
