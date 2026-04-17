#!/usr/bin/env bash
# Report stale deprecations in the lean4 source tree.
#
# This is a *read-only* discovery tool — it never edits files. For each of the
# supported deprecation kinds it prints the source locations and any remaining
# references that a human will need to rewrite before the deprecation can be
# removed.
#
#   CUTOFF=YYYY-MM-DD  override the cutoff (default: 6 months ago, GNU date)
#   ROOT=<path>        lean4 checkout (default: git toplevel)
#   LEAN=<path>        lean binary to run the discovery scripts with
#                      (default: build/release/stage1/bin/lean)
#
# Handlers:
#
#   @[deprecated_arg ...]  or  attribute [deprecated_arg ...] ...
#       Discovery delegated to script/find_deprecated_args.lean. Reports each
#       match for manual review — the no-replacement form may leave a dead
#       binder in the signature, and the script's syntactic scan can't tell
#       which variant a given attribute belongs to.
#
#   register_builtin_option ... := { ... deprecation? := some { since := "..." } ... }
#       Discovery delegated to script/find_deprecated_options.lean, which reads
#       `optionDeclsRef` + `declRangeExt` directly. Each hit prints the block
#       range plus any remaining references to the option name.
#
#   deprecated_syntax <kind> ... (since := "...")
#       Discovery delegated to script/find_deprecated_syntax.lean, which reads
#       `deprecatedSyntaxExt` per-module and resolves the *syntax declaration's*
#       source location via `declRangeExt`.
#
#   deprecated_module "..." (since := "...")
#       Discovery delegated to script/find_deprecated_modules.lean. Each hit
#       prints the deprecated file plus any remaining importers.

set -euo pipefail

ROOT="${ROOT:-$(git rev-parse --show-toplevel)}"
CUTOFF="${CUTOFF:-$(date -d '6 months ago' +%Y-%m-%d 2>/dev/null \
                  || date -v-6m +%Y-%m-%d)}"

cd "$ROOT"
echo "cutoff: $CUTOFF   root: $ROOT   (read-only)"
echo

LEAN="${LEAN:-build/release/stage1/bin/lean}"
if [[ ! -x "$LEAN" ]]; then
  echo "error: lean binary not found at $LEAN; set LEAN=<path>" >&2
  exit 1
fi
# Silence the import-time `deprecated_module` warning: each discovery script
# does `import Lean` in its header, and if some `Lean.*` module in the
# transitive import closure is itself marked `deprecated_module`, the header
# check fires against the script's own import rather than being caught by
# the script's own scan.
LEAN_ARGS=(-Dlinter.deprecated.module=false)

# ---- deprecated_arg: delegate to Lean (handles @[...] and attribute [...]) --
# Output columns: file, line, column, since, form ("attr" | "attribute"), content.
# Both forms are reported together; removing either requires human review since
# dropping a parameter (no-replacement case) has non-local effects.
echo "== deprecated_arg (attribute uses, manual review)"
arg_records=$("$LEAN" "${LEAN_ARGS[@]}" --run script/find_deprecated_args.lean --cutoff "$CUTOFF")
if [[ -z "$arg_records" ]]; then
  echo "  (none)"
else
  while IFS=$'\t' read -r file line col since form content; do
    echo "  $file:$line:$col  ($form, since $since)"
    echo "    $content"
  done <<<"$arg_records"
fi
echo

# ---- deprecated_option: delegate discovery to Lean --------------------------
# Output columns: file, option, since, startLine, startCol, endLine, endCol.
echo "== deprecated_option (register_builtin_option blocks)"
option_records=$("$LEAN" "${LEAN_ARGS[@]}" --run script/find_deprecated_options.lean --cutoff "$CUTOFF")
if [[ -z "$option_records" ]]; then
  echo "  (none)"
else
  while IFS=$'\t' read -r file name since start _startCol end _endCol; do
    echo "  $file:$start-$end: option \`$name\` (since $since)"
  done <<<"$option_records"
  echo
  echo "== remaining references to deprecated options (rewrite before removing)"
  awk -F'\t' '{print $2}' <<<"$option_records" | sort -u | while read -r name; do
    hits=$(grep -rHnF "$name" --include='*.lean' src 2>/dev/null \
      | grep -v "register_builtin_option $name" || true)
    if [[ -n "$hits" ]]; then
      echo "  $name:"
      echo "$hits" | sed 's/^/    /'
    fi
  done
fi
echo

# ---- deprecated_syntax: delegate discovery to Lean --------------------------
# Output columns: file, kind, since, startLine, startCol, endLine, endCol, text,
# cmdLocation. `file`/line range point at the `syntax`/`leading_parser`
# declaration (via `declRangeExt`); `cmdLocation` points at the
# `deprecated_syntax` command itself (via a syntactic scan of `src/`).
echo "== deprecated_syntax (syntax kind declarations)"
syntax_records=$("$LEAN" "${LEAN_ARGS[@]}" --run script/find_deprecated_syntax.lean --cutoff "$CUTOFF")
if [[ -z "$syntax_records" ]]; then
  echo "  (none)"
else
  while IFS=$'\t' read -r file kind since start _startCol end _endCol _text cmdLoc; do
    echo "  $file:$start-$end: kind \`$kind\` (since $since)"
    if [[ -n "$cmdLoc" && "$cmdLoc" != "-" ]]; then
      echo "    command:  $cmdLoc"
    else
      echo "    command:  (not located — manual review)"
    fi
  done <<<"$syntax_records"
  echo
  echo "== remaining references to deprecated syntax kinds"
  echo "   (includes the kind declaration, the deprecated_syntax command,"
  echo "    and any @[builtin_*_elab], macro_rules, or elab_rules keyed by the kind)"
  awk -F'\t' '{print $2}' <<<"$syntax_records" | sort -u | while read -r kind; do
    hits=$(grep -rHnF "$kind" --include='*.lean' src 2>/dev/null || true)
    if [[ -n "$hits" ]]; then
      echo "  $kind:"
      echo "$hits" | sed 's/^/    /'
    fi
  done
fi
echo

# ---- deprecated_module: delegate discovery to Lean --------------------------
echo "== deprecated_module (file-level)"
mod_records=$("$LEAN" "${LEAN_ARGS[@]}" --run script/find_deprecated_modules.lean --cutoff "$CUTOFF")
if [[ -z "$mod_records" ]]; then
  echo "  (none)"
else
  while IFS=$'\t' read -r file module since message; do
    echo "  $file  (module $module, since $since)"
    [[ -n "$message" ]] && echo "    message: $message"
  done <<<"$mod_records"
fi
