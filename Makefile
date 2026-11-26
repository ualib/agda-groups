# File: Makefile
#
# Two jobs: checking the library, and keeping the plan.  `make help` (the
# default) lists the targets.
#
# Checking the library, from the repository root inside `nix develop`, so
# that `agda` is the wrapper that knows the pinned standard library and
# agda-algebras (see flake.nix), as follows:
#
#   make check         The options check (make safety), then Agda on the
#                      aggregator with a heap limit, then the plan's lint.
#   make check-lean    The options check, its cases (make safety-test) and
#                      the plan's lint, with no Agda; `nix develop .#lean`
#                      is the shell without Agda.
#   make safety        scripts/check-safety.sh on src/ and the library file.
#   make safety-test   scripts/test-check-safety.sh, the check's cases.
#   make clean         Remove this library's interface files and the
#                      aggregator (the copy of agda-algebras under .deps/
#                      and its interface files stay).
#
# The aggregator, src/EverythingGroups.agda, imports every module under
# src/.  It is generated and gitignored, so that one run of Agda checks the
# whole library; it is a PHONY target, always regenerated, so that a module
# added or removed is picked up; and it is listed by `find` rather than by
# git, so that an untracked module is checked too.
#
# Keeping the plan: `make populate` and `make update` are the two
# directions of the contract stated in the README.
#
# The engine (gh_project_*.py) has exactly one home — the
# williamdemeo/github-project repository — and this Makefile finds it
# through whichever channel is available, in order:
#
#   local     scripts/gh_project_populate.py exists in THIS tree — the
#             engine repository itself, or a template copy that has not
#             yet run `make init`
#   path      gh-project-* CLIs on PATH — a Nix dev shell with the
#             engine package (see templates/consumer/flake.nix), a
#             `nix profile install`, or a future pipx install
#   checkout  GHPROJECT_DIR points at a checkout of the engine repo
#
# Variables:
#   AGDA           the agda to run      (default: the one on PATH)
#   AGDA_OPTS      extra agda flags
#   PLAN           plan file            (default: docs/GITHUB_PROJECT.md)
#   REPO           owner/name override  (default: the plan file's
#                                        **Repository**: header)
#   PYTHON         interpreter          (default: python3)
#   GHPROJECT_DIR  engine checkout path (checkout channel only)
#   NO_ENV_PREFIX  set (to anything) wherever gh authenticates *through*
#                  GH_TOKEN/GITHUB_TOKEN — GitHub Actions included; by
#                  default the engine strips those variables so they
#                  cannot shadow a keychain-stored token.

PYTHON ?= python3
PLAN   ?= docs/GITHUB_PROJECT.md
SRCDIR := src
AGDA   ?= agda
AGDA_OPTS ?=
# A heap limit of 6 GiB, as in agda-lattices: a check that needs more
# fails rather than taking the machine.
RTS_OPTS := +RTS -M6G -A128M -RTS
AGGREGATOR := $(SRCDIR)/EverythingGroups.agda
REPO   ?=
GHPROJECT_DIR ?=

FLAGS := $(if $(REPO),--repo $(REPO)) $(if $(NO_ENV_PREFIX),--no-env-prefix)

ifneq (,$(wildcard scripts/gh_project_populate.py))
  ENGINE_MODE := local
  POPULATE := $(PYTHON) scripts/gh_project_populate.py
  UPDATE   := $(PYTHON) scripts/gh_project_update.py
  LINT     := $(PYTHON) scripts/gh_project_lint.py
else ifneq (,$(shell command -v gh-project-update 2>/dev/null))
  ENGINE_MODE := path
  POPULATE := gh-project-populate
  UPDATE   := gh-project-update
  LINT     := gh-project-lint
else ifneq (,$(wildcard $(GHPROJECT_DIR)/scripts/gh_project_populate.py))
  ENGINE_MODE := checkout
  POPULATE := $(PYTHON) $(GHPROJECT_DIR)/scripts/gh_project_populate.py
  UPDATE   := $(PYTHON) $(GHPROJECT_DIR)/scripts/gh_project_update.py
  LINT     := $(PYTHON) $(GHPROJECT_DIR)/scripts/gh_project_lint.py
else
  ENGINE_MODE := missing
endif

.PHONY: help check check-lean safety safety-test clean $(AGGREGATOR) \
        populate-dry populate update update-check lint test init \
        guard-gh guard-engine engine-mode
.DEFAULT_GOAL := help

# In `path` mode the resolved CLI is (typically) a Nix wrapper carrying
# its own `gh` on a wrapped PATH, so probing the caller's ambient PATH
# would fail a `nix profile install` user whose tooling actually works;
# the CLI reports its own error if gh is genuinely absent.  local and
# checkout modes run bare python3 scripts and do need ambient gh.
ifeq ($(ENGINE_MODE),path)
GH_GUARD :=
else
GH_GUARD := guard-gh
endif

help: ## Show this help
	@grep -hE '^[a-zA-Z][a-zA-Z0-9_-]*:.*## ' $(MAKEFILE_LIST) \
	  | awk 'BEGIN {FS = ":.*## "} {printf "  \033[1m%-14s\033[0m %s\n", $$1, $$2}'

# -- Checking the library ------------------------------------------------

check: safety $(AGGREGATOR) ## Check the options, type-check every module, then lint the plan
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) $(AGGREGATOR)
	@$(MAKE) --no-print-directory lint

check-lean: safety safety-test lint ## The options check, its cases and the plan's lint, with no Agda

safety: ## Every module has the one pragma, no postulate and no unsafe pragma
	bash scripts/check-safety.sh $(SRCDIR) agda-groups.agda-lib

safety-test: ## Run the cases of the options check
	bash scripts/test-check-safety.sh

# `--exact-split` is absent from the aggregator's pragma: it constrains
# definitions, and the aggregator holds nothing but imports.  Each module
# carries it in its own pragma (make safety).
$(AGGREGATOR): ## Regenerate the aggregator from the current tree
	@{ \
	  echo "{-# OPTIONS --without-K --safe #-}"; \
	  echo ""; \
	  echo "module EverythingGroups where"; \
	  echo ""; \
	  find $(SRCDIR) \( -name '*.lagda.md' -o -name '*.agda' \) \
	      ! -path '$(AGGREGATOR)' \
	    | sed -e 's|^$(SRCDIR)/||' \
	          -e 's|\.lagda\.md$$||' \
	          -e 's|\.agda$$||' \
	          -e 's|/|.|g' \
	          -e 's|^|import |' \
	    | LC_ALL=C sort; \
	} > $(AGGREGATOR)
	@echo "wrote $(AGGREGATOR) ($$(grep -c '^import' $(AGGREGATOR)) modules)"

clean: ## Remove this library's interface files and the aggregator
	rm -rf _build
	find $(SRCDIR) -name '*.agdai' -delete
	rm -f $(AGGREGATOR)

# -- Keeping the plan -----------------------------------------------------

populate-dry: guard-engine $(GH_GUARD) ## Preview what populate would create (no mutations)
	$(POPULATE) $(PLAN) $(FLAGS) --dry-run

populate: guard-engine $(GH_GUARD) ## Create labels, milestones, issues on GitHub from $(PLAN)
	$(POPULATE) $(PLAN) $(FLAGS)

update: guard-engine $(GH_GUARD) ## Rewrite $(PLAN)'s generated regions from live GitHub state
	$(UPDATE) $(PLAN) $(FLAGS)

update-check: guard-engine $(GH_GUARD) ## Report whether $(PLAN) is stale without writing
	$(UPDATE) $(PLAN) $(FLAGS) --check

lint: guard-engine ## Validate $(PLAN)'s structure (no network)
	$(LINT) $(PLAN)

test: ## Run the engine test suite (offline; engine repo / pre-init copies only)
ifneq (,$(wildcard scripts/tests))
	$(PYTHON) -m unittest discover -s scripts/tests
else
	@echo "No local engine copy: the engine's tests run in its own repository"
	@echo "(https://github.com/williamdemeo/github-project)."
endif

init: ## Detach this template copy from the engine (one-time, consumer projects)
ifneq ($(ENGINE_MODE),local)
	@echo "Nothing to do: this tree carries no local engine copy."
else
	@echo "This removes the copied engine from this tree.  The engine's home is"
	@echo "https://github.com/williamdemeo/github-project; after this, make"
	@echo "resolves it from PATH (Nix dev shell) or GHPROJECT_DIR (checkout)."
	@if [ -z "$(INIT_YES)" ]; then \
	  printf 'Continue? [y/N] '; read ans; \
	  case "$$ans" in y|Y|yes) ;; *) echo "Aborted."; exit 1;; esac; \
	fi
	rm -f scripts/gh_project_populate.py scripts/gh_project_update.py \
	      scripts/gh_project_lint.py scripts/_gh_project_lib.py \
	      scripts/VERSION
	rm -rf scripts/_utils scripts/tests scripts/__pycache__
	@if [ -f templates/consumer/flake.nix ]; then \
	  mv templates/consumer/flake.nix flake.nix; \
	  rm -f flake.lock; \
	  rm -rf templates; \
	  echo "Installed the consumer flake (engine as a pinned input)."; \
	fi
	@echo
	@echo "Done.  Next steps:"
	@echo "  1. nix flake lock       # pin the engine (Nix channel), or set"
	@echo "     GHPROJECT_DIR to an engine checkout instead"
	@echo "  2. edit $(PLAN), then: make lint && make populate-dry"
	@echo "  3. commit the result"
endif

engine-mode: ## Print which engine channel this invocation resolved (debugging)
	@echo "$(ENGINE_MODE)"

guard-engine:
ifeq ($(ENGINE_MODE),missing)
	@echo "error: the github-project engine was not found.  Provide it via one of:"; \
	echo "  - Nix: enter the dev shell (nix develop) wired by your flake's"; \
	echo "    github-project input, so the gh-project-* CLIs are on PATH"; \
	echo "  - checkout: clone https://github.com/williamdemeo/github-project"; \
	echo "    and pass GHPROJECT_DIR=/path/to/that/clone"; \
	exit 1
endif

guard-gh:
	@command -v gh >/dev/null || { \
	  echo "error: the GitHub CLI (gh) is required for this target."; \
	  echo "       https://cli.github.com/  (or: nix develop)"; \
	  exit 1; \
	}
