<!-- File: scripts/README.md -->

# scripts/

The repository's scripts, as follows:

+  `check-safety.sh`, the options check (`make safety`): every module
   under `src/` carries `--without-K --exact-split --safe` as its one
   OPTIONS pragma, and its code holds no postulate and no pragma that
   switches a check off; the library file adds no flags.  Its header
   states the rules and how it reads a module.
+  `test-check-safety.sh`, the cases of that check (`make safety-test`):
   modules that it must pass, and modules that it must fail with a named
   message.
