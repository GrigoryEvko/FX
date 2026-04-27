import FX.Syntax.Ast
import FX.Kernel.Env

/-!
# B12 — Named-argument routing

`reorderNamedCallArgs?` rewrites a call-site `CallArg` array so
that named arguments land in the positional slots declared by
the callee.  The kernel's `Term.pi` carries no parameter names,
so this reorder is an elaboration-only concern — named calls
compile to the same `app … (app … arg)` chain as positional
calls.

## Scope (Phase 2.2)

Supports three shapes:

  1. **All positional**: `f(1, 2, 3)` — unchanged, returned as-is.
  2. **All named (+ optional implicits)**: `f(b: 2, a: 1)` —
     reordered into the positional order declared by the
     callee.  Implicit args `#T` are normalized to the FRONT of
     the result (before the reordered named args), regardless
     of their source position.  This matches the typical FX
     convention `f(#T, a: x, b: y)` where implicits precede
     explicit args.  Users who interleave implicits in source
     order (`f(a: x, #T, b: y)`) get the normalized form and
     any resulting elaboration issue surfaces from the kernel's
     positional Pi application — not from B12 itself.
  3. **Mixed named + positional**: rejected with `E011`.  The
     §4.1 "≥2 positional args must be named" rule is the
     natural rationale; we enforce the stronger all-or-nothing
     invariant which captures the spirit without the argument
     counting.

Requires the callee to be a direct unqualified `.var` reference
to a registered fn decl in `globalEnv` — we need `paramNames`
to know where each named arg belongs.  Indirect calls
(`(lam _ _ _)(named: x)`, pipe chains, etc.) with named args
are rejected with `E012` — the caller must spell out
positional order.

Duplicates (`f(a: 1, a: 2)`) are `E013`.
Unknown names (`f(xyz: v)` where `xyz` isn't a param) are `E014`.
Missing names (some declared param has no arg) are `E015`.
Duplicate DECL-side param names (`fn f(x, x)`) are `E016` —
B12 cannot safely route a named arg to a specific position
when two positions share a name; the parser / elabFnDecl
should have rejected this earlier, so reaching this branch
indicates a bug in a prior phase.

## Error codes reserved

  * `E011` — mixed positional + named
  * `E012` — named args on indirect call / unregistered name
  * `E013` — duplicate named arg (call-side)
  * `E014` — unknown parameter name
  * `E015` — missing parameter
  * `E016` — duplicate declared parameter name (decl-side)
-/

namespace FX.Elab

open FX.Kernel
open FX.Syntax
open FX.Syntax.Ast

/-- An elaboration diagnostic.  Span is included so `fxi check`
    can point at the offending source line.  Kept here so this
    helper module can throw its own errors without a dependency
    on `FX/Elab/Elaborate.lean`.  Re-exported by Elaborate via
    `open FX.Elab`. -/
structure ElabError where
  code    : String
  message : String
  span    : Span
  deriving Repr

namespace ElabError

def make (code message : String) (span : Span := Span.zero) : ElabError :=
  { code := code, message := message, span := span }

end ElabError

/-- Classify a `CallArg` array into three categories for B12's
    reorder logic: has-positional (explicit `.pos`), has-named
    (`.named`).  Implicits are treated as neither (they keep
    their positions regardless).  Returns `(hasPos, hasNamed)`. -/
private def classifyCallArgs (callArgs : Array Ast.CallArg) : Bool × Bool :=
  callArgs.foldl (init := (false, false)) fun acc callArg =>
    match callArg with
    | .pos _     => (true, acc.2)
    | .named _ _ => (acc.1, true)
    | .implicit _ => acc

/-- If `fnExpr` is a direct unqualified `.var` reference, return
    the bare name.  `Qualified.name` paths return `none` — Phase
    2.2 doesn't support named args on module-qualified calls
    (would need scope-resolution of the qualified path, reserved
    for B13 module work). -/
private def directCalleeName? (fnExpr : Ast.Expr) : Option String :=
  match fnExpr with
  | .var qualIdent =>
    if qualIdent.parts.isEmpty then some qualIdent.final else none
  | _              => none

/-- B12: reorder named call arguments into the positional slots
    declared by the callee.  See the section docstring above for
    the three shapes and five error codes this handles. -/
def reorderNamedCallArgs? (globalEnv : GlobalEnv) (fnExpr : Ast.Expr)
    (callArgs : Array Ast.CallArg) (span : Span)
    : Except ElabError (Array Ast.CallArg) := do
  let (hasPos, hasNamed) := classifyCallArgs callArgs
  -- Shape 1: all positional — pass through unchanged.
  if !hasNamed then
    return callArgs
  -- Shape 3: mixed positional + named — reject per §4.1 "no
  -- positional multi-arg syntax — call sites are self-
  -- documenting".  The pipe `|>` idiom (§4.2 rule 5, "pipe
  -- fills the unnamed parameter") does its own single-positional
  -- → named-slot promotion inside the `.pipe` elab case before
  -- it reaches here, so by the time a call arrives with mixed
  -- args, either the user wrote mixed directly (reject) or
  -- pipe's promotion couldn't find a unique free slot
  -- (ambiguous, reject).  Both fail through E011 here.
  if hasPos then
    throw (ElabError.make "E011"
      "cannot mix positional and named arguments in one call — use all-positional or all-named"
      span)
  -- Shape 2: all named (+ implicits).  Requires direct callee.
  let calleeName ← match directCalleeName? fnExpr with
    | some name => pure name
    | none      =>
      throw (ElabError.make "E012"
        "named arguments require a direct reference to a registered fn decl"
        span)
  let paramNames ← match globalEnv.lookupParamNames? calleeName with
    | some names => pure names
    | none       =>
      throw (ElabError.make "E012"
        s!"named arguments require '{calleeName}' to be a registered fn decl"
        span)
  -- Reject duplicate decl-side param names — the reorder is
  -- ambiguous when `paramNames = [x, x]` (the named arg `x: v`
  -- would get routed to both positions, silently replicating
  -- `v`).  A well-formed decl has distinct param names; failing
  -- here means a prior phase (parser / elabFnDecl) let through
  -- a malformed signature.
  let mut seenDeclNames : List String := []
  for declaredName in paramNames do
    if seenDeclNames.contains declaredName then
      throw (ElabError.make "E016"
        s!"'{calleeName}' has duplicate parameter name '{declaredName}' — cannot route named args unambiguously"
        span)
    seenDeclNames := declaredName :: seenDeclNames
  -- Extract named args as a (name, expr) list and implicits as-is.
  -- Check for duplicate names first.
  let mut seenNames : List String := []
  for callArg in callArgs do
    match callArg with
    | .named argName _ =>
      if seenNames.contains argName then
        throw (ElabError.make "E013"
          s!"duplicate named argument '{argName}:'" span)
      seenNames := argName :: seenNames
    | _ => pure ()
  -- Reject unknown names BEFORE checking for missing — an "unknown
  -- param" diagnostic is more actionable than "missing param"
  -- when both are true (user typo'd a param name, now the mapping
  -- reports BOTH what they wrote wrong AND that the real param
  -- lacks an arg; the former is the root cause).
  for callArg in callArgs do
    match callArg with
    | .named argName _ =>
      if !paramNames.contains argName then
        throw (ElabError.make "E014"
          s!"'{calleeName}' has no parameter named '{argName}' (declared: {paramNames})"
          span)
    | _ => pure ()
  -- Build the reordered array by walking paramNames in order.
  let mut reordered : Array Ast.CallArg := #[]
  for paramName in paramNames do
    let found := callArgs.findSome? fun callArg =>
      match callArg with
      | .named argName argExpr =>
        if argName == paramName then some argExpr else none
      | _ => none
    match found with
    | some argExpr => reordered := reordered.push (.pos argExpr)
    | none         =>
      throw (ElabError.make "E015"
        s!"missing argument for parameter '{paramName}' in call to '{calleeName}'"
        span)
  -- Append implicits in their original order.  Implicits are
  -- orthogonal to the explicit-arg reorder — they apply before
  -- the positional args at elab time.  Keeping them at the end
  -- preserves the current elab ordering (implicits first, then
  -- positionals) — wait: implicits appear BEFORE positionals in
  -- the source, so we prepend them to match.
  let implicits := callArgs.filter fun callArg =>
    match callArg with | .implicit _ => true | _ => false
  return implicits ++ reordered

end FX.Elab
