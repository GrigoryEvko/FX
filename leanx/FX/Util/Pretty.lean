-- FX.Util.Pretty — pretty-printing helpers.
--
-- Role: shared formatting primitives used by the CLI (`fxi help`,
-- `fxi dump`) and the future diagnostic emitter.  Sibling of
-- `FX.Util.Basic` — a leaf, must not import anything heavier than
-- `FX.Util.Basic` so that kernel-level modules can stay off its
-- dependency cone.
--
-- Phase-1 surface (stable today):
--   * `indent n s`    — per-line indentation for nested diagnostics
--   * `bullets xs`    — `- item` list rendering for `--help` screens
--   * `formatError e` — human-readable projection of `FX.Util.Error`
--
-- Deferred (lands with later phases, NOT in scope for Phase 1):
--   * Wadler-Leijen style `Doc` combinator (flatten, nest, `<$>`,
--     `<+>`) — needed once kernel terms and elaboration traces are
--     printed (Phase 2+).
--   * Source-span highlighting with the `|---^` caret format from
--     `fx_design.md` §10.10 — needed when `fxi check` starts
--     surfacing refinement errors (Phase 2+).
--   * ANSI colouring gated on `isatty(stderr)` — cosmetic; lands
--     alongside the `--color {auto,never,always}` CLI flag.
--   * Structured-JSON rendering of diagnostics — belongs with the
--     agent-facing daemon (fx_design.md §24), not here.

import FX.Util.Basic

namespace FX.Util.Pretty

/-- Indent every line of `s` by `n` spaces.  Handy for nested
    diagnostic output.  Preserves the final newline (or absence of
    one) verbatim. -/
def indent (indentWidth : Nat) (textBlock : String) : String :=
  let indentPadding := "".pushn ' ' indentWidth
  let textLines := textBlock.splitOn "\n"
  String.intercalate "\n" (textLines.map
    (fun line => if line.isEmpty then line else indentPadding ++ line))

/-- Bullet-list rendering of an array of strings, one per line,
    prefixed with a leading `- `.  Empty arrays render as empty. -/
def bullets (items : Array String) : String :=
  String.intercalate "\n" (items.toList.map (fun item => "- " ++ item))

/-- Format an `FX.Util.Error` for human-readable output.  Mirrors
    the `ToString` instance but exposed as a reusable function so
    callers (e.g. `fxi`) can pre-format without a type ascription. -/
def formatError (error : FX.Util.Error) : String := toString error

end FX.Util.Pretty
