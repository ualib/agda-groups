<!-- File: scripts/README.md -->

# scripts/

The repository's scripts, as follows:

+  `ci/project-plan-update.sh`, from the github-project template: the
   weekly check, run by `.github/workflows/project-plan-update.yml`, that
   the plan's generated regions still match GitHub.  M1-2 keeps or
   removes it.
+  The options check, which M1-1 adds: every module under `src/` carries
   `--without-K --exact-split --safe` and no postulate.
