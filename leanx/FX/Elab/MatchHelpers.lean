import FX.Elab.Scope
import FX.Elab.NamedArgs
import FX.Syntax.Ast
import FX.Kernel.Inductive
import FX.Kernel.Substitution
import FX.Kernel.Env

/-!
# B7 — Match-expression elaboration helpers

Pattern-match elaboration dispatches over an `IndSpec` registered
in `FX/Kernel/Inductive.lean`.  The elaborator:

  1. Scans arm patterns to find the governing spec (first arm
     whose pattern resolves to a known constructor).
  2. Checks exhaustiveness — every ctor in the spec has an arm.
  3. For each ctor in `spec.ctors` order, builds a method term
     whose lambda chain matches what the kernel's `iotaArgs`
     rule feeds in: one lambda per ctor arg, plus an extra
     unused lambda after each self-referential arg for the
     auto-supplied recursive result.  This shape is the
     contract the kernel's `indRec` reduction relies on (see
     `FX/Kernel/Reduction.lean` `iotaArgs`).
  4. Emits `Term.indRec specName motive methods scrutinee`.

Scope extension during body elaboration mirrors the method's
binder shape — each pattern-supplied name gets an index, and
each self-reference adds an unused `"_"` binder between.

Phase-2.2 limitations (relaxed in later milestones):

  * Nested patterns (`Some(Ok(x))`): arg patterns must be
    identifier or wildcard.
  * Guards: rejected.
  * Parameterized specs: rejected (Bool / Nat / Unit only).
  * Variable or wildcard catch-all arms: rejected.  Every arm
    must reference a concrete ctor, and every ctor must appear.

## Extraction from Elaborate.lean

Moved here so `Elaborate.lean` stays focused on the `elabExpr`
mutual block and decl-level driving logic.  These helpers are
structural — pure data operations on `IndSpec` + surface `Pattern`
nodes — and don't participate in any mutual recursion with
`elabExpr`.
-/

namespace FX.Elab

open FX.Kernel
open FX.Syntax
open FX.Syntax.Ast

/-- Resolve a qualified identifier against user-declared ADT
    specs (from `globalEnv.userSpecs`) and the hardcoded prelude
    registry.  Returns `some (specName, ctorIndex, ctorSpec)`
    when the last parts element names a registered `IndSpec`
    AND `q.final` is one of its constructors.  Returns `none`
    otherwise (unqualified, unknown type, or not-a-constructor).
    Used by `elabExpr`'s `.var` and `.app` cases to map surface
    `Nat.Zero` / `Bool.True` / user `color.Red` onto `Term.ctor`
    nodes.

    Kept here rather than hoisted separately so it's
    co-located with the match-helper callers that depend on it. -/
def resolveQualCtor? (globalEnv : GlobalEnv) (qualIdent : QualIdent)
    : Option (String × Nat × IndCtor) :=
  if qualIdent.parts.size = 0 then none
  else
    let specName := qualIdent.parts[qualIdent.parts.size - 1]!
    match Inductive.specByName? specName globalEnv.userSpecs with
    | some spec =>
      match spec.findCtor? qualIdent.final with
      | some (ctorIndex, ctorSpec) => some (specName, ctorIndex, ctorSpec)
      | none => none
    | none => none

/-- Resolve an unqualified ctor reference by sweeping all
    registered specs (user first, then prelude) for a
    constructor with that name.  Returns `(specName, ctorIndex,
    IndCtor)` of the FIRST match.  `none` otherwise.  Used at
    surface call sites where the user writes `Node(...)` as
    shorthand for `tree.Node(...)`. -/
def resolveUnqualCtor? (globalEnv : GlobalEnv) (ctorName : String)
    : Option (String × Nat × IndCtor) :=
  let allSpecs := globalEnv.userSpecs ++ Inductive.preludeSpecs
  allSpecs.findSome? fun spec =>
    match spec.findCtor? ctorName with
    | some (ctorIndex, ctorSpec) =>
      some (spec.name, ctorIndex, ctorSpec)
    | none => none

/-- Resolve either form of ctor reference (qualified or
    unqualified) from a QualIdent.  Tries qualified first
    (`Nat.Succ`, `color.Red`), then falls through to unqualified
    sweep (`Succ`, `Red`). -/
def resolveCtorRef? (globalEnv : GlobalEnv) (qualIdent : QualIdent)
    : Option (String × Nat × IndCtor) :=
  match resolveQualCtor? globalEnv qualIdent with
  | some triple => some triple
  | none        =>
    if qualIdent.parts.isEmpty then
      resolveUnqualCtor? globalEnv qualIdent.final
    else
      none

/-- B8 record-literal sugar: a TYPE NAME with exactly one
    constructor resolves to that constructor.  Used at the
    record-literal-desugar call site `config { f: v }`, which
    parses as `Expr.app (.var "config") [named-args]`; this
    helper routes the `config` head to the spec's sole ctor so
    the existing named-arg-reorder path takes over.

    Separate from `resolveCtorRef?` because the latter is called
    in non-App positions (bare var, match arm pattern) where
    this fallback would mis-resolve `Pair(Nat, Nat)` as a
    mkPair ctor call when the user means a type application.
    At the App site we gate on "all args named" to distinguish
    record-literal from positional-type-application. -/
def resolveRecordCtor? (globalEnv : GlobalEnv) (qualIdent : QualIdent)
    : Option (String × Nat × IndCtor) :=
  if qualIdent.parts.isEmpty then
    match globalEnv.specByName? qualIdent.final with
    | some spec =>
      match spec.ctors with
      | [soleCtor] => some (spec.name, 0, soleCtor)
      | _          => none
    | none => none
  else
    none

/-- Resolve an arm pattern's top-level constructor to
    `(specName, ctorIndex, ctorSpec)`.  Handles both qualified
    (`Nat.Succ`) and unqualified (`Succ`) ctor references.
    Returns `none` for non-ctor patterns (wildcard, var,
    literal, tuple). -/
partial def resolveArmCtor? (globalEnv : GlobalEnv) : Pattern → Option (String × Nat × IndCtor)
  | .ctor qualIdent _ _ =>
    if qualIdent.parts.size > 0 then
      resolveQualCtor? globalEnv qualIdent
    else
      -- Unqualified ctor: scan user specs first, then prelude
      -- specs in declaration order.  First match wins — if two
      -- specs declare the same ctor name (e.g., user `Red`
      -- shadowing a hypothetical prelude `Red`), the user decl
      -- wins.
      let allSpecs := globalEnv.userSpecs ++ Inductive.preludeSpecs
      allSpecs.findSome? fun spec =>
        match spec.findCtor? qualIdent.final with
        | some (ctorIdx, ctorSpec) => some (spec.name, ctorIdx, ctorSpec)
        | none => none
  | .asPattern inner _ _ =>
    -- Q84: `as`-patterns don't change which ctor the arm matches
    -- — they just bind the scrutinee to an extra name.  Peek
    -- through to let ctor-specific classification find the real
    -- pattern underneath.
    resolveArmCtor? globalEnv inner
  | _ => none

/-- Q85: detect whether a ctor-arg pattern is itself a nested
    ctor pattern (needs destructuring).  Looks through a
    top-level `as` wrapper so `Cons(h, t) as inner` still
    counts as nested.  Returns `false` for `var`, `wildcard`,
    `literal`, `tuple` — nested destructuring only triggers on
    nested constructors.  -/
partial def isNestedCtorArg : Pattern → Bool
  | .ctor _ _ _              => true
  | .asPattern inner _ _     => isNestedCtorArg inner
  | _                        => false

/-- Q85: given an arm pattern (possibly a ctor with nested
    ctor-arg patterns), rewrite into:
      * `newOuterPattern` — ctor with the nested arg replaced
        by a fresh var binder.
      * `newArmBody` — an inner `match` expression on the fresh
        binder with two arms: the original nested pattern →
        original arm body, and wildcard → `catchAllBody`.

    For arms without nested args, returns `(armPattern,
    armBody)` unchanged.

    Scope:
      * At most ONE nested position per arm.  Multiple nested
        positions in the same arm are E010 — combine into one
        or use explicit nested match.
      * The arm pattern is expected to be `.ctor` (top-level
        `as` stripped by `stripArmAsPattern` upstream).  For
        non-ctor patterns the function is a no-op. -/
def rewriteNestedArgs (armPattern : Pattern) (armBody : Expr)
    (armSpan : Span) (armGuard : Option Expr) (catchAllBody : Expr)
    : Except ElabError (Pattern × Expr × Option Expr) := do
  match armPattern with
  | .ctor qualIdent args _ =>
    match args.findIdx? isNestedCtorArg with
    | none =>
      -- No nested args.  Pass through unchanged.
      pure (armPattern, armBody, armGuard)
    | some idx =>
      -- Reject multiple nested positions in the same arm —
      -- would need a sequence of inner matches and is deferred.
      let remainingArgs := args.extract (idx + 1) args.size
      if remainingArgs.any isNestedCtorArg then
        throw (ElabError.make "E010"
          s!"multiple nested ctor-arg positions in '{qualIdent.final}' pattern — only one level of nested destructuring per arm supported (combine into one nested match inside the arm body)"
          armSpan)
      let nestedArg := args[idx]!
      let freshName := s!"__nested_arg_{idx}"
      let freshPat : Pattern := .var freshName armSpan
      let newArgs := args.set! idx freshPat
      let newOuterPattern : Pattern := .ctor qualIdent newArgs armSpan
      let freshQ : QualIdent :=
        { parts := #[], final := freshName, span := armSpan }
      let freshExpr : Expr := .var freshQ
      -- Guard moves INTO the inner arm so references to nested
      -- bindings (e.g., `Succ(p) if p > 5` nested inside) resolve
      -- — the inner arm has `p` in scope.  Outer ctor args are
      -- also in scope inside the inner match, so moving the
      -- guard inward doesn't break outer-only guards either.
      -- With the guard inside, Q83's guard handling fires at the
      -- inner match level when the inner arm is processed.
      let innerArm1 : MatchArm :=
        MatchArm.mk nestedArg armGuard armBody armSpan
      let innerArm2 : MatchArm :=
        MatchArm.mk (.wildcard armSpan) none catchAllBody armSpan
      let innerMatch : Expr :=
        .match_ freshExpr #[innerArm1, innerArm2] armSpan
      pure (newOuterPattern, innerMatch, none)
  | _ =>
    -- Non-ctor top-level (catch-all paths came through with a
    -- synthesized ctor pattern in Q81/Q82 — we shouldn't see
    -- raw wildcard/var here).  Pass through; the outer code
    -- handles non-ctor patterns separately.
    pure (armPattern, armBody, armGuard)

/-- Strip a top-level `as` binding off an arm, returning the arm
    with the inner pattern substituted and the bound name.  Q84.

    Arms without a top-level `as` return themselves plus `none`.
    Nested `as` bindings (inside ctor args, e.g., `Some(x as
    inner)`) are NOT stripped here — the elaborator processes
    them separately if/when it lands support for nested-`as`
    bindings on ctor-arg patterns.  The top-level form
    (`Succ(p) as n => body`) is the only one Q84 supports. -/
def stripArmAsPattern (arm : MatchArm) : MatchArm × Option String :=
  match arm with
  | .mk (.asPattern inner asName _) guard body span =>
    (.mk inner guard body span, some asName)
  | _ => (arm, none)

/-- Determine which `IndSpec` a match dispatches over by scanning
    arm patterns for the first resolvable constructor reference.
-/
def resolveMatchSpec? (globalEnv : GlobalEnv) (matchArms : Array MatchArm)
    : Option IndSpec :=
  matchArms.toList.findSome? fun matchArm =>
    match matchArm with
    | .mk armPattern _ _ _ =>
      match resolveArmCtor? globalEnv armPattern with
      | some (specName, _, _) =>
        Inductive.specByName? specName globalEnv.userSpecs
      | none => none

/-- Walk a ctor's arg telescope ONCE and produce both
    (extendedScope, totalDepth) — the scope has each
    user-supplied name pushed (plus an auto-`"_"` binder after
    every self-referential arg for the recursive-result slot),
    and the depth is the total binder count the method's lambda
    chain introduces.

    A single walk keeps the self-ref bookkeeping honest against
    drift — earlier we had two parallel walks (one produced the
    scope, one produced the depth) that could get out of sync
    if the self-ref rule changed on only one side. -/
def scopeAndDepthForCtor (specName : String) (baseScope : Scope)
    : List Term → List String → (Scope × Nat)
  | [],                            _                       => (baseScope, 0)
  | _,                             []                      => (baseScope, 0)
  | argType :: restArgTypes,       argName :: restArgNames =>
    let scopeAfterArg := baseScope.push argName
    let isSelfRef :=
      match argType with
      | .ind referencedName _ => referencedName == specName
      | _                     => false
    let scopeAfterRec := if isSelfRef then scopeAfterArg.push "_" else scopeAfterArg
    let selfRefExtra := if isSelfRef then 1 else 0
    let (finalScope, restDepth) :=
      scopeAndDepthForCtor specName scopeAfterRec restArgTypes restArgNames
    (finalScope, 1 + selfRefExtra + restDepth)

/-- Variant of `scopeAndDepthForCtor` that registers ctor-arg
    type hints in the scope (Q78) while preserving the
    self-reference detection on the original (unsubstituted)
    arg types.

    Split into a separate function because the self-ref check
    MUST happen on the unsubstituted `.var i` placeholders —
    after substitution, a `var 0 → ind "Option" [Nat]` change
    makes an `Option(Option(Nat))` arg LOOK like a self-reference
    to `Option`, which adds a spurious `rec` binder and breaks
    the depth math.

    Params:
      * `originalArgTypes` — ctor spec's declared arg types,
        used for self-ref detection.
      * `substitutedArgTypes` — same list after `substParams
        scrutineeTypeArgs`, used as the pushed type hint.

    Both lists must have the same length; the caller enforces
    that by substituting once per arg.  The original function
    is retained for callsites that don't have typeArgs (for-loop
    elaboration, where the spec is always `Nat`). -/
def scopeAndDepthForCtorTyped (specName : String) (baseScope : Scope)
    : List Term → List Term → List String → (Scope × Nat)
  | [],                             _,                           _              => (baseScope, 0)
  | _,                              [],                          _              => (baseScope, 0)
  | _,                              _,                           []             => (baseScope, 0)
  | origArgType :: restOrigArgTypes, substArgType :: restSubstArgTypes, argName :: restArgNames =>
    let scopeAfterArg := baseScope.pushWithType argName substArgType
    let isSelfRef :=
      match origArgType with
      | .ind referencedName _ => referencedName == specName
      | _                     => false
    let scopeAfterRec := if isSelfRef then scopeAfterArg.push "_" else scopeAfterArg
    let selfRefExtra := if isSelfRef then 1 else 0
    let (finalScope, restDepth) :=
      scopeAndDepthForCtorTyped specName scopeAfterRec
        restOrigArgTypes restSubstArgTypes restArgNames
    (finalScope, 1 + selfRefExtra + restDepth)

/-- Wrap an elaborated arm body in the lambda chain a ctor
    method needs to match the kernel's iota-reduction arg order.

    Lambdas nest outermost-first in pattern-arg order.  Each
    self-referential ctor arg contributes TWO lambdas: one for
    the arg itself, one for the recursive-result value.  The
    recursive result's domain is `returnType` shifted to the
    depth at which that binder sits — for a non-dependent motive
    (`\_ : ind spec []. shift 0 1 returnType`) the recursive
    call `indRec spec motive methods argVal` computes to
    `shift 0 1 returnType` up to beta, which at the recursive
    binder's scope depth is exactly the shifted return type we
    bind.

    `depthSoFar` tracks the binder count emitted so far (starts
    at 0 at the outermost ctor-arg lambda).  `returnType` is
    the match-expression result type in the OUTER elaboration
    scope — it's shifted by `depthSoFar` when used as a
    recursive binder's domain. -/
def wrapCtorMethod (specName : String) (returnType : Term)
    (armBody : Term) : Nat → List (Term × String) → Term
  | _,          []                                 => armBody
  | depthSoFar, (argType, _argName) :: restPairs  =>
    let isSelfRef :=
      match argType with
      | .ind referencedName _ => referencedName == specName
      | _                     => false
    if isSelfRef then
      let recResultType := Term.shift 0 (depthSoFar + 1) returnType
      let innerAfterRec :=
        wrapCtorMethod specName returnType armBody (depthSoFar + 2) restPairs
      Term.lam Grade.default (Term.shift 0 depthSoFar argType)
        (Term.lam Grade.default recResultType innerAfterRec)
    else
      let innerAfterArg :=
        wrapCtorMethod specName returnType armBody (depthSoFar + 1) restPairs
      Term.lam Grade.default (Term.shift 0 depthSoFar argType) innerAfterArg

/-- Compute the de Bruijn indices each ctor argument occupies
    inside the method's lambda chain, measured from the bottom
    (innermost) of the chain.  Used by Q82's var-pattern catch-all
    synthesis — the synthesized method body reconstructs the ctor
    value (`Ctor(arg_0, ..., arg_{k-1})`) and needs each `arg_i`'s
    de Bruijn index at the depth just below the chain.

    The computation mirrors `scopeAndDepthForCtor`'s push discipline:
    one binder per arg, plus one extra `_rec` binder after every
    self-referential arg.  The total depth is the sum of those per-
    arg push counts; each arg's final index is `totalDepth -
    priorPushSum - 1` (the arg sits one slot above everything pushed
    after it).

    Example — `List.Cons(h: a, t: List(a))`:
      * pushCounts = `[1, 2]` (h plain; t self-ref)
      * totalDepth = 3
      * indices = `[2, 1]` — h at idx 2, t at idx 1 below the chain.
      (The `_rec_t` binder sits at idx 0 but is never referenced by
      the reconstruction.) -/
def argDeBruijnIndicesForCtor (specName : String)
    (ctorArgs : List Term) : List Nat :=
  let pushCounts : List Nat := ctorArgs.map fun argType =>
    match argType with
    | .ind referencedName _ => if referencedName == specName then 2 else 1
    | _                     => 1
  let totalDepth : Nat := pushCounts.foldl (· + ·) 0
  let rec walk (priorPushSum : Nat)
      : List Nat → List Nat
    | []              => []
    | pushCount :: restCounts =>
      (totalDepth - priorPushSum - 1)
        :: walk (priorPushSum + pushCount) restCounts
  walk 0 pushCounts

/-- Build a non-dependent motive for a `Term.indRec` on a Bool
    scrutinee — `lambda (_ :_default ind "Bool" []). shift 0 1
    X`.

    Used by the if-expr desugar (B6): `if cond; t else e end if`
    emits `indRec "Bool" (boolMotive resultType) [e, t] cond`.
    The motive body lives under one extra binder (the ctor-
    scrutinee binding), so free vars in `resultType` shift up
    by 1 — closed types are no-ops, dependent types carry
    through correctly.  Two if-expr elab sites share this so a
    motive tweak (e.g., making the binder grade ghost when
    refinements land) happens in one place. -/
def boolMotive (resultType : Term) : Term :=
  Term.lam Grade.default (.ind "Bool" []) (Term.shift 0 1 resultType)

end FX.Elab
