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
#   @[deprecated_arg old new (since := "...")]
#       Reports the `file:line` of each matching attribute (grep-based).
#
#   @[deprecated_arg old (since := "...")]       (no replacement)
#       Reports each match for manual review — the parameter may still be in
#       the signature, so removing the attribute has non-local effects.
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

# ---- @[deprecated_arg] (rename form): report file positions -----------------
echo "== deprecated_arg (rename form)"
pattern='^[[:space:]]*@\[deprecated_arg [^ ,"]+ [^ ,"]+.*\(since := "[0-9]{4}-[0-9]{2}-[0-9]{2}"\)\][[:space:]]*$'
# `grep` returns 1 when there are no matches; `|| true` keeps `pipefail` happy.
{ grep -rHnE "$pattern" --include='*.lean' src 2>/dev/null || true; } \
  | awk -F: -v c="$CUTOFF" '
      {
        match($0, /\(since := "[0-9-]+"\)/); since = substr($0, RSTART+12, 10)
        if (since <= c) print $1 ":" $2
      }' \
  | sort -t: -k1,1 -k2,2n \
  | sed 's/^/  /'
echo

# ---- @[deprecated_arg] (no-replacement form): manual review -----------------
echo "== deprecated_arg (no-replacement form, manual review)"
{ grep -rHnE '^[[:space:]]*@\[deprecated_arg [^ ,"]+[[:space:]]*(".+")?[[:space:]]*\(since := "[0-9]{4}-[0-9]{2}-[0-9]{2}"\)\][[:space:]]*$' \
       --include='*.lean' src 2>/dev/null || true; } \
  | awk -F: -v c="$CUTOFF" '
      {
        match($0, /\(since := "[0-9-]+"\)/); since = substr($0, RSTART+12, 10)
        # skip rename form (two identifiers before the optional string / since)
        if (match($0, /@\[deprecated_arg [^ ,"]+ [^ ,"]+/)) next
        if (since <= c) print "  " $0
      }'
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
  echo
  echo "== remaining imports of deprecated modules (rewrite before removing)"
  awk -F'\t' '{print $2}' <<<"$mod_records" | sort -u | while read -r module; do
    hits=$(grep -rHnE "^[[:space:]]*(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+${module}(\$|[[:space:]])" \
               --include='*.lean' src 2>/dev/null || true)
    if [[ -n "$hits" ]]; then
      echo "  $module:"
      echo "$hits" | sed 's/^/    /'
    fi
  done
fi
