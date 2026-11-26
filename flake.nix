# =============================================================================
# agda-groups: Nix flake
#
# File: flake.nix
#
# `nix develop` drops you in a shell with exactly the Agda, standard library
# and Agda Universal Algebra Library (agda-algebras) this library is checked
# against, and the roadmap engine that keeps the plan.  `nix develop .#lean`
# drops you in a shell without Agda, for the checks that need none
# (`make check-lean`).
#
# Pinning:
#
#   +  agda-algebras, the library this one builds on, is a flake input,
#      pinned in its URL at commit 66c324f8 of its master branch (the merge
#      of its pull request 642, which moved it to the released Agda 2.9.0
#      and standard library 2.4.1) and by flake.lock at that commit.  Since
#      the URL names the commit, `nix flake update` cannot move it; to move
#      it, edit the URL, run `nix flake lock`, and check.
#   +  The Agda is the environment agda-algebras exports
#      (`packages.<system>.default`): the released Agda 2.9.0, built from
#      agda/agda at the tag v2.9.0 by Agda's own flake, with the released
#      standard library 2.4.1.  Neither comes from nixpkgs, so the one pin
#      above fixes the library, the compiler and the standard library
#      together.  Building that Agda from source takes about an hour; the
#      public Cachix cache `formalverification` holds it (see the README).
#   +  nixpkgs follows agda-algebras' own pin and supplies the rest of the
#      shell: make, git and gh.
#   +  The roadmap engine (williamdemeo/github-project) is an input of its
#      own, pinned by flake.lock, with its own nixpkgs; `nix flake update
#      github-project` moves it.
#
# Library resolution:
#
#   +  Agda writes interface files beside a library's .agda-lib, and the Nix
#      store is read-only, so the shell copies the pinned sources of
#      agda-algebras to .deps/agda-algebras/ (once per pin, with the store
#      path it came from in .deps/agda-algebras/.source) and registers that
#      copy.  To use another copy (one whose interfaces are already built,
#      say), enter the shell with AGDA_ALGEBRAS_DIR set to its root; the
#      shell does not check that it matches the pin.
#   +  The shell writes a project-local AGDA_DIR (.agda/), so nothing in the
#      user's Agda configuration directory is consulted.  The standard
#      library's .agda-lib is read from the Agda environment's own library
#      file (its `libraryFile` attribute), so this flake never names the
#      standard library's store path or version itself; the library file
#      agda-groups.agda-lib asks for `standard-library-2.4`, which resolves
#      only to a 2.4 release.
#   +  The wrapper at .agda/bin/agda execs the environment's store path,
#      never `command -v agda`, which can resolve to the wrapper itself and
#      loop.  It passes --library-file after the Nix wrapper's own (Agda's
#      last flag wins) and --no-default-libraries, so a user's own defaults
#      file cannot contribute.
#
# This flake needs Nix 2.28 or later, as agda-algebras' does: the agda/agda
# tree it locks holds empty directories that an older Nix drops when hashing.
# =============================================================================
{
  description = "agda-groups: finite group theory in Agda, on the Agda Universal Algebra Library";

  inputs = {
    # Commit 66c324f8 of agda-algebras' master: the merge of its pull request
    # 642 (the released Agda 2.9.0 and standard library 2.4.1).
    agda-algebras.url = "github:ualib/agda-algebras/66c324f89de176c2d5b4d3513d76034e4ffff2dd";
    nixpkgs.follows = "agda-algebras/nixpkgs";
    github-project.url = "github:williamdemeo/github-project";
  };

  outputs = { self, nixpkgs, agda-algebras, github-project }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      forAllSystems = f:
        nixpkgs.lib.genAttrs systems (system:
          f { inherit system; pkgs = import nixpkgs { inherit system; }; });

      # The Agda environment agda-algebras exports: Agda 2.9.0 with the
      # standard library 2.4.1 registered in its own library file.
      mkAgdaEnv = system: agda-algebras.packages.${system}.default;

      # What both shells hold besides Agda: make, git, gh and the engine.
      mkBasePackages = system: pkgs: [
        pkgs.gnumake
        pkgs.git
        pkgs.gh
        github-project.packages.${system}.gh-project-engine
      ];

      # Project-local AGDA_DIR, the copy of agda-algebras, and an agda
      # wrapper that passes --library-file again after the Nix wrapper's own
      # (Agda's last-flag-wins rule), with --no-default-libraries so a user's
      # own defaults file cannot contribute.
      mkAgdaShellSetup = agdaEnv: ''
        ROOT="$PWD"
        if command -v git >/dev/null 2>&1 && git rev-parse --show-toplevel >/dev/null 2>&1; then
          ROOT="$(git rev-parse --show-toplevel)"
        fi

        export AGDA_DIR="$ROOT/.agda"
        mkdir -p "$AGDA_DIR"

        if [ -n "''${AGDA_ALGEBRAS_DIR:-}" ]; then
          ALGEBRAS="$AGDA_ALGEBRAS_DIR"
        else
          ALGEBRAS="$ROOT/.deps/agda-algebras"
          if [ "$(cat "$ALGEBRAS/.source" 2>/dev/null)" != "${agda-algebras}" ]; then
            rm -rf "$ALGEBRAS"
            mkdir -p "$ALGEBRAS"
            cp "${agda-algebras}/agda-algebras.agda-lib" "$ALGEBRAS/"
            cp -r "${agda-algebras}/src" "$ALGEBRAS/"
            chmod -R u+w "$ALGEBRAS"
            echo "${agda-algebras}" > "$ALGEBRAS/.source"
          fi
        fi
        export ALGEBRAS

        {
          cat "${agdaEnv.libraryFile}"
          echo "$ALGEBRAS/agda-algebras.agda-lib"
          echo "$ROOT/agda-groups.agda-lib"
        } > "$AGDA_DIR/libraries"
        echo "standard-library" > "$AGDA_DIR/defaults"

        mkdir -p "$AGDA_DIR/bin"
        cat > "$AGDA_DIR/bin/agda" <<EOF
#!/usr/bin/env bash
exec "${agdaEnv}/bin/agda" \\
  --no-default-libraries \\
  --library-file "$AGDA_DIR/libraries" \\
  --library standard-library \\
  --library agda-algebras \\
  --library agda-groups \\
  "\$@"
EOF
        chmod +x "$AGDA_DIR/bin/agda"
        export PATH="$AGDA_DIR/bin:$PATH"
      '';
    in
    {
      formatter = forAllSystems ({ pkgs, ... }: pkgs.nixpkgs-fmt);

      devShells = forAllSystems ({ system, pkgs }:
        let
          agdaEnv = mkAgdaEnv system;
        in
        {
          default = pkgs.mkShell {
            name = "agda-groups-dev";

            packages = [ agdaEnv ] ++ mkBasePackages system pkgs;

            LANG = "C.UTF-8";
            LC_ALL = "C.UTF-8";

            shellHook = ''
              ${mkAgdaShellSetup agdaEnv}

              echo ""
              echo "agda-groups dev shell"
              echo "   Agda          : ${agdaEnv.version}    ($(agda --version 2>/dev/null | head -n1))"
              echo "   stdlib        : $(cat "${agdaEnv.libraryFile}")"
              echo "   agda-algebras : $ALGEBRAS"
              echo "   AGDA_DIR      : $AGDA_DIR"
              echo ""

              case "${agdaEnv.version}" in
                2.9.*) : ;;
                *) echo "warning: expected Agda 2.9.x, got ${agdaEnv.version}" ;;
              esac
            '';
          };

          # The shell without Agda, for `make check-lean`: the options check,
          # its cases and the plan's lint.
          lean = pkgs.mkShell {
            name = "agda-groups-lean";
            packages = mkBasePackages system pkgs;
            LANG = "C.UTF-8";
            LC_ALL = "C.UTF-8";
          };
        });

      # `nix run .#update -- docs/GITHUB_PROJECT.md`, pinned by this
      # project's own flake.lock.
      apps = forAllSystems ({ system, ... }: github-project.apps.${system});
    };
}
