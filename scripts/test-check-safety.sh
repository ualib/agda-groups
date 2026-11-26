#!/usr/bin/env bash
# File: scripts/test-check-safety.sh
#
# The cases of scripts/check-safety.sh.  Each writes one module (and, for the
# cases of the library file, one library file) into a fresh directory and
# says what the check must make of it: `pass` (exit 0), or the failure it
# must report (exit 1, and a line naming the file with that message), so
# that a case cannot pass by failing for some other reason.  The last case
# runs the check on src/ and agda-groups.agda-lib.
#
# Each case is how the pinned Agda 2.9.0 reads the module: which lines are
# code (bare, indented and prose-prefixed fences open code; a fence naming
# another language does not; `agda` after a space or with more text after
# it is prose; a block inside an HTML comment is still code), and which
# pragmas are active (not those in a block comment, and an OPTIONS pragma
# only ahead of the first declaration); string and character literals may
# run over several lines and hold string gaps.  Set FIXTURES to a directory
# to keep the modules there.
#
#   bash scripts/test-check-safety.sh
set -u
CHECK=${CHECK:-scripts/check-safety.sh}
PRAGMA='{-# OPTIONS --without-K --exact-split --safe #-}'
F='```'
work=${FIXTURES:-$(mktemp -d)}
[ -n "${FIXTURES:-}" ] || trap 'rm -rf "$work"' EXIT
failures=0
CLEANLIB=("name: m" "depend: standard-library-2.4 agda-algebras" "include: .")

# judge NAME WANT DIR FILE: run the check on DIR (with the library file
# DIR/m.agda-lib) and compare with WANT, which is `pass` or the message the
# check must print for FILE.
judge() {
  local name=$1 want=$2 dir=$3 file=$4 got ok=0
  bash "$CHECK" "$dir" "$dir/m.agda-lib" > "$dir/out" 2>&1
  got=$?
  if [ "$want" = pass ]; then
    [ "$got" -eq 0 ] && ok=1
  else
    [ "$got" -eq 1 ] && grep -qxF -- "$dir/$file: $want" "$dir/out" && ok=1
  fi
  if [ "$ok" -eq 1 ]; then
    echo "ok    $name"
  else
    echo "FAIL  $name: exit $got, expected $( [ "$want" = pass ] && echo 0 || echo "1 with \"$file: $want\"" )"
    sed 's/^/      /' "$dir/out"
    failures=$((failures + 1))
  fi
}

# expect NAME WANT LINE...: the module made of the lines, with a clean
# library file, must give WANT.  EXPECT_AT, if set, is the module's path
# under the case's directory.
expect() {
  local name=$1 want=$2 dir="$work/$1" at=${EXPECT_AT:-M.lagda.md}
  mkdir -p "$(dirname "$dir/$at")"
  printf '%s\n' "${@:3}" > "$dir/$at"
  printf '%s\n' "${CLEANLIB[@]}" > "$dir/m.agda-lib"
  judge "$name" "$want" "$dir" "$at"
}

# expect_lib NAME WANT LINE...: the library file made of the lines, with a
# clean module, must give WANT.
expect_lib() {
  local name=$1 want=$2 dir="$work/$1"
  mkdir -p "$dir"
  printf '%s\n' "${HEAD[@]}" > "$dir/M.lagda.md"
  printf '%s\n' "${@:3}" > "$dir/m.agda-lib"
  judge "$name" "$want" "$dir" m.agda-lib
}

# Lines 1 to 8 of most modules below; a case's own lines start at 9.
HEAD=("# M" "" "${F}agda" "$PRAGMA" "module M where" "$F" "" "Prose may say postulate.")
POST="postulate A : Set"
MISSING="missing the pragma $PRAGMA in its code"

# Which lines are code.
expect clean                pass "${HEAD[@]}"
expect bare-fence           "line 11: postulate" "${HEAD[@]}" "" "$F" "$POST" "$F"
expect indented-fence       "line 11: postulate" "${HEAD[@]}" "" "  ${F}agda" "$POST" "  $F"
expect prose-before-fence   "line 11: postulate" "${HEAD[@]}" "" "Example: ${F}agda" "$POST" "$F"
expect prose-before-bare    "line 11: postulate" "${HEAD[@]}" "" "Example: $F" "$POST" "$F"
expect hidden-block         "line 12: postulate" "${HEAD[@]}" "" "<!--" "${F}agda" "$POST" "$F" "-->"
expect indented-close       pass "${HEAD[@]}" "" "  ${F}agda" "-- code" "  $F" "Then prose: postulate."
expect other-language       pass "${HEAD[@]}" "" "${F}haskell" "postulate = 1" "$F" "" "Then prose: postulate."
expect space-agda           pass "${HEAD[@]}" "" "$F agda" "$POST" "$F"
expect tagged-then-code     "line 13: postulate" "${HEAD[@]}" "" "${F}agda title" "prose for Agda" "$F" "$POST" "$F"
expect front-matter         pass "---" "title: \"postulate {-# TERMINATING #-}\"" "---" "${HEAD[@]}"
expect pragma-in-prose      "$MISSING" "# M" "" "$PRAGMA" "" "${F}agda" "module M where" "$F"
expect options-in-prose     pass "${HEAD[@]}" "" "Prose may show {-# OPTIONS --with-K #-}."

# Comments, literals and names inside the code.
expect line-comment         pass "${HEAD[@]}" "" "${F}agda" "-- postulate is not used here" "$F"
expect block-comment        pass "${HEAD[@]}" "" "${F}agda" "{- postulate A : Set" "   {-# TERMINATING #-} -}" "$F"
expect pragma-in-comment    "$MISSING" "# M" "" "${F}agda" "{-" "$PRAGMA" "-}" "module M where" "$F"
expect pragma-in-nested     "$MISSING" "# M" "" "${F}agda" "{- {- -}" "$PRAGMA" "-}" "module M where" "$F"
expect string-not-comment   "line 14: postulate" "${HEAD[@]}" "" "${F}agda" "open import Agda.Builtin.String" "s : String" "s = \"{-\"" "$POST" "$F"
expect char-not-string      "line 12: postulate" "${HEAD[@]}" "" "${F}agda" "open import Agda.Builtin.Char" "c : Char ; c = '\"' ; $POST" "$F"
expect multiline-string     "line 15: postulate" "${HEAD[@]}" "" "${F}agda" "open import Agda.Builtin.String" "s : String" "s = \"first line" "{-\"" "$POST" "$F"
expect string-gap           "line 14: postulate" "${HEAD[@]}" "" "${F}agda" "open import Agda.Builtin.String" "s : String" "s = \"first\\" "  \\\" ; $POST" "$F"
expect char-gap             "line 14: postulate" "${HEAD[@]}" "" "${F}agda" "open import Agda.Builtin.Char" "c : Char" "c = '\\" "  \\\"' ; $POST" "$F"
expect string-escape        "line 12: postulate" "${HEAD[@]}" "" "${F}agda" "open import Agda.Builtin.String" "s : String ; s = \"a\\\"\" ; $POST" "$F"
expect postulate-in-string  pass "${HEAD[@]}" "" "${F}agda" "open import Agda.Builtin.String" "s : String" "s = \"first line" "postulate\"" "$F"
expect postulate-in-name    pass "${HEAD[@]}" "" "${F}agda" "postulates : Set₁" "postulates = Set" "$F"

# Which OPTIONS pragmas are active, and which flags they may carry.
expect pragma-two-lines     pass "# M" "" "${F}agda" "{-#  OPTIONS --without-K" "    --exact-split  --safe #-}" "module M where" "$F"
expect without-K-missing    "line 4: another OPTIONS pragma: {-# OPTIONS --exact-split --safe #-}" "# M" "" "${F}agda" "{-# OPTIONS --exact-split --safe #-}" "module M where" "$F"
expect exact-split-missing  "line 4: another OPTIONS pragma: {-# OPTIONS --without-K --safe #-}" "# M" "" "${F}agda" "{-# OPTIONS --without-K --safe #-}" "module M where" "$F"
expect safe-missing         "line 4: another OPTIONS pragma: {-# OPTIONS --without-K --exact-split #-}" "# M" "" "${F}agda" "{-# OPTIONS --without-K --exact-split #-}" "module M where" "$F"
expect unsafe-flag-added    "line 4: another OPTIONS pragma: {-# OPTIONS --without-K --exact-split --safe --type-in-type #-}" "# M" "" "${F}agda" "{-# OPTIONS --without-K --exact-split --safe --type-in-type #-}" "module M where" "$F"
expect flags-reordered      "line 4: another OPTIONS pragma: {-# OPTIONS --safe --without-K --exact-split #-}" "# M" "" "${F}agda" "{-# OPTIONS --safe --without-K --exact-split #-}" "module M where" "$F"
expect extra-same-line      "2 OPTIONS pragmas, where one is allowed" "# M" "" "${F}agda" "$PRAGMA {-# OPTIONS --no-exact-split #-}" "module M where" "$F"
expect extra-own-line       "line 5: another OPTIONS pragma: {-# OPTIONS --no-exact-split #-}" "# M" "" "${F}agda" "$PRAGMA" "{-# OPTIONS --no-exact-split #-}" "module M where" "$F"
expect duplicate-pragma     "2 OPTIONS pragmas, where one is allowed" "# M" "" "${F}agda" "$PRAGMA" "$PRAGMA" "module M where" "$F"
expect pragma-after-header  "line 5: an OPTIONS pragma after the first declaration, where Agda ignores it" "# M" "" "${F}agda" "module M where" "$PRAGMA" "$F"

# --lossy-unification: allowed nowhere, a worked example included.
LOSSY='{-# OPTIONS --without-K --exact-split --safe --lossy-unification #-}'
expect lossy-in-theory      "line 4: another OPTIONS pragma: $LOSSY" "# M" "" "${F}agda" "$LOSSY" "module M where" "$F"
EXPECT_AT=Examples/M.lagda.md expect lossy-in-example "line 4: another OPTIONS pragma: $LOSSY" "# M" "" "${F}agda" "$LOSSY" "module M where" "$F"

# The pragmas that switch a check off, one case each, and pragmas that do not.
for p in TERMINATING NON_TERMINATING NO_TERMINATION_CHECK NO_POSITIVITY_CHECK NO_UNIVERSE_CHECK NON_COVERING; do
  expect "pragma-$p" "line 11: the pragma $p" "${HEAD[@]}" "" "${F}agda" "{-# $p #-}" "f : Set" "f = f" "$F"
done
expect pragma-INJECTIVE     "line 12: the pragma INJECTIVE" "${HEAD[@]}" "" "${F}agda" "postulat : Set → Set" "{-# INJECTIVE postulat #-}" "$F"
expect pragma-INJECTIVE_FOR_INFERENCE "line 12: the pragma INJECTIVE_FOR_INFERENCE" "${HEAD[@]}" "" "${F}agda" "g : Set → Set" "{-# INJECTIVE_FOR_INFERENCE g #-}" "$F"
expect pragma-POLARITY      "line 12: the pragma POLARITY" "${HEAD[@]}" "" "${F}agda" "g : Set → Set" "{-# POLARITY g ++ #-}" "$F"
expect pragma-COMPILE       "line 12: the pragma COMPILE" "${HEAD[@]}" "" "${F}agda" "g : Set → Set" "{-# COMPILE GHC g = \"postulate\" #-}" "$F"
expect foreign-quote        "line 12: postulate" "${HEAD[@]}" "" "${F}agda" "{-# FOREIGN GHC c = '\"' #-}" "$POST" "$F"
expect terminating-comment  pass "${HEAD[@]}" "" "${F}agda" "-- {-# TERMINATING #-}" "$F"
expect safe-pragmas         pass "${HEAD[@]}" "" "${F}agda" "g : Set → Set" "g A = A" "{-# INLINE g #-}" "{-# BUILTIN LEVEL Level #-}" "$F"

# Plain .agda modules, read whole.
EXPECT_AT=M.agda expect agda-clean     pass "$PRAGMA" "module M where" "-- postulate is not used here"
EXPECT_AT=M.agda expect agda-postulate "line 3: postulate" "$PRAGMA" "module M where" "$POST"
EXPECT_AT=M.agda expect agda-missing   "$MISSING" "module M where" "-- {-# OPTIONS --without-K --exact-split --safe #-}"
EXPECT_AT=Sub/M.agda expect agda-nested "line 3: the pragma TERMINATING" "$PRAGMA" "module Sub.M where" "{-# TERMINATING #-}"

# The aggregator at the top is skipped; a file of its name elsewhere is not.
dir="$work/aggregator-skipped"
mkdir -p "$dir"
printf '%s\n' "${HEAD[@]}" > "$dir/M.lagda.md"
printf '%s\n' "{-# OPTIONS --without-K --safe #-}" "module EverythingGroups where" "import M" > "$dir/EverythingGroups.agda"
printf '%s\n' "${CLEANLIB[@]}" > "$dir/m.agda-lib"
judge aggregator-skipped pass "$dir" EverythingGroups.agda
EXPECT_AT=Sub/EverythingGroups.agda expect aggregator-elsewhere "line 3: postulate" "$PRAGMA" "module Sub.EverythingGroups where" "$POST"

# A module in a literate format the check does not read, beside a clean one.
for ext in lagda lagda.tex lagda.rst lagda.org lagda.typ lagda.tree; do
  dir="$work/format-$ext"
  mkdir -p "$dir"
  printf '%s\n' "${HEAD[@]}" > "$dir/M.lagda.md"
  printf '%s\n' "$PRAGMA" "module N where" > "$dir/N.$ext"
  printf '%s\n' "${CLEANLIB[@]}" > "$dir/m.agda-lib"
  judge "format-$ext" "a module in a literate format this check does not read (write it as .lagda.md)" "$dir" "N.$ext"
done

# The library file.
expect_lib lib-clean        pass "${CLEANLIB[@]}"
expect_lib lib-flags        "a flags field, which would add options to every module" "${CLEANLIB[@]}" "flags: --lossy-unification"
expect_lib lib-flags-spaced "a flags field, which would add options to every module" "flags : --no-exact-split" "${CLEANLIB[@]}"
expect_lib lib-flags-comment pass "${CLEANLIB[@]}" "-- flags: --lossy-unification"
dir="$work/lib-missing"
mkdir -p "$dir"
printf '%s\n' "${HEAD[@]}" > "$dir/M.lagda.md"
judge lib-missing "no such library file" "$dir" m.agda-lib

# A directory with no modules.
mkdir -p "$work/empty"
if bash "$CHECK" "$work/empty" "$work/empty/m.agda-lib" > "$work/empty.out" 2>&1; then got=0; else got=$?; fi
if [ "$got" -eq 2 ]; then echo "ok    empty"; else echo "FAIL  empty: exit $got, expected 2"; failures=$((failures + 1)); fi

# The library itself.
if bash "$CHECK" src agda-groups.agda-lib > "$work/src.out" 2>&1; then
  echo "ok    src"
else
  echo "FAIL  src"; sed 's/^/      /' "$work/src.out"; failures=$((failures + 1))
fi

[ "$failures" -eq 0 ] || { echo "test-check-safety: $failures failures"; exit 1; }
echo "test-check-safety: all cases pass"
