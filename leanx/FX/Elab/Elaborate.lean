import FX.Elab.Scope
import FX.Elab.EffectInference
import FX.Elab.MatchHelpers
import FX.Elab.NamedArgs
import FX.Syntax.Ast
import FX.Kernel.Typing
import FX.Kernel.Env
import FX.Derived.Session.Binary
import FX.Derived.Session.Translate

/-!
# Elaboration — surface AST → kernel Term

Per `fx_design.md` §6 (type system) and §31.7 (how surface
constructs desugar to the kernel terms).

## Current scope (Phase 2.2 — M1 complete, M2 in progress)

Handles the subset of `FX.Syntax.Ast` wired end-to-end through
parser + elaborator + kernel check + eval:

  * **Declarations**: `fnDecl` (both one-liner `= expr;` and
    block `begin fn ... end fn` bodies).  `moduleDecl`,
    `openDecl`, `constDecl`, `sorryDecl` recognized but stubbed
    (E020).
  * **Expressions**: `var` (local scope → `Term.var`, global
    scope → `Term.const`), `app` with implicit `#T` args,
    `lam`, `arrow`, `literal` for `type`/`true`/`false`/
    unsuffixed `int` (unary-Nat), `letBind`/`block` statements,
    `ifExpr` (B6 — compiles to indRec on Bool), `match_` (B7 —
    compiles to indRec on any preludeSpec with per-ctor
    methods).
  * **Function parameters**: type parameters `<a: type, ...>`
    (B2 — ghost-moded FnParams prepended to regular params);
    regular params with `ParamMode` prefix mapping to kernel
    grades via `modeToGrade`.
  * **Cross-decl resolution (two-pass `checkFile`)**: pass 1
    elabs every signature and pre-registers types in
    `GlobalEnv`; pass 2 elabs bodies with full env visibility.
    Self- and forward references compile to `Term.const`,
    resolved at eval time against the real body.

## Pipeline shape

```
File  ─elabFile / checkFile─▶  Array DeclResult
Decl  ─elabDeclE / elabAndCheckE─▶  ElabDecl | elabFail | typeFail
```

`elabAndCheckE` chains elab → kernel `inferType` on the
declared type → kernel `check` of the body against that type.
All with the ambient `GlobalEnv` for const resolution.

## De Bruijn discipline

Elaborate introduces binders left-to-right; each new binder
gets de Bruijn index 0 and shifts every older binder up by 1.
A `Scope` (from `FX.Elab.Scope`) mirrors this so named-identifier
resolution returns the right index.

Match-arm self-referential ctor args introduce TWO binders per
user-visible pattern name: the arg itself, then an unused
recursive-result binder matching what the kernel's iota rule
supplies.  `scopeAndDepthForCtor` produces both the extended
scope and the total binder depth in one walk.

## Error taxonomy

Error codes prefix `E` (for elaboration), distinct from the
kernel's `T` and parser's `P`:

  * `E001` unknown identifier (neither in scope nor a prelude)
  * `E010` unsupported expression form for the current phase
  * `E020` unsupported declaration form for the current phase
  * `E030` block-form function body not yet handled
  * `E100` internal: impossible branch reached
-/

namespace FX.Elab

open FX.Kernel
open FX.Syntax
open FX.Syntax.Ast

-- `ElabError` is defined in `FX/Elab/NamedArgs.lean` so that
-- helper module can throw its own diagnostics without a
-- dependency cycle.  Re-exported here via the shared
-- `namespace FX.Elab`.

/-- One elaborated spec clause: the surface kind plus the
    elaborated predicate/measure/constraint Term.  For
    `postCond` the predicate was elaborated under the fn's
    scope extended with the return-binder (at de Bruijn 0);
    for the other three kinds, under the fn's parameter scope
    only.  Stream E consumes this list to emit SMT queries. -/
inductive ElabSpecClause : Type where
  | whereCstr (constraintTerm : Term)
  | preCond   (predicateTerm : Term)
  | postCond  (returnBinder : String) (predicateTerm : Term)
  | decreases (measureTerm : Term)
  deriving Repr

/-- A successfully elaborated top-level declaration. -/
structure ElabDecl where
  /-- The source-level name. -/
  name : String
  /-- The kernel term representing the declaration body. -/
  body : Term
  /-- The kernel term representing the declaration type. -/
  type : Term
  /-- Whether the `@[transparent]` attribute was present on the
      source decl (§10.15 body-visibility).  Transparent bodies
      unfold at `whnf` / `convEq` via `GlobalEnv.unfold?`; opaque
      bodies (the default) stay as `.const` heads.  Runtime
      evaluation unfolds both — transparency is a
      typing/conversion discipline, not an execution policy. -/
  transparent : Bool := false
  /-- B4: specification clauses (pre/post/decreases/where) with
      predicates elaborated under the fn's parameter scope (and
      the return-value binder for `post`).  §5.1 ordering was
      checked at elab time.  Stream E (E1-E4) consumes this
      list to emit SMT discharge queries; until then the
      predicates are carried through as erased-at-codegen
      metadata (ghost grade per §1.5). -/
  specs : Array ElabSpecClause := #[]
  deriving Repr

/-- Scan a decl's `@[...]` attribute array for a bare
    `transparent` identifier.  Returns `true` when the attribute
    is present.  Matches only the plain identifier form
    (`@[transparent]`) — attribute-application forms
    (`@[transparent(...)]`) are not expected and would not
    match.  Per fx_design.md §10.15 transparent + no_inline are
    orthogonal; this helper covers the SMT / conversion side. -/
def hasTransparentAttr (attrs : Array Ast.Expr) : Bool :=
  attrs.any fun attrExpr =>
    match attrExpr with
    | .var qualIdent => qualIdent.parts.isEmpty && qualIdent.final == "transparent"
    | _              => false

-- Ctor-resolution helpers (`resolveQualCtor?`, `resolveUnqualCtor?`,
-- `resolveCtorRef?`) and B7 match-compilation helpers
-- (`resolveArmCtor?`, `resolveMatchSpec?`, `scopeAndDepthForCtor`,
-- `wrapCtorMethod`, `boolMotive`) live in `FX/Elab/MatchHelpers.lean`.
-- Re-exported via the shared `namespace FX.Elab`.

/-- Build a unary-`Nat` kernel term representing `n` — a chain of
    `Nat.Succ` around `Nat.Zero`.  `buildNatLit 0 = ctor "Nat" 0 [] []`;
    `buildNatLit (n+1) = ctor "Nat" 1 [] [buildNatLit n]`.  Used by the
    integer-literal elaboration path (D2). -/
def buildNatLit : Nat → Term
  | 0     => Term.ctor "Nat" 0 [] []
  | n + 1 => Term.ctor "Nat" 1 [] [buildNatLit n]

/-- Convert a single character to a digit value in the given base.
    Returns `none` if the character is not a valid digit for the base.
    Handles `0-9`, `a-z`, `A-Z`. -/
def charToDigit? (base : Nat) (digitChar : Char) : Option Nat :=
  let digitValue : Nat :=
    if digitChar.isDigit then digitChar.toNat - '0'.toNat
    else if 'a' ≤ digitChar ∧ digitChar ≤ 'z' then
      10 + (digitChar.toNat - 'a'.toNat)
    else if 'A' ≤ digitChar ∧ digitChar ≤ 'Z' then
      10 + (digitChar.toNat - 'A'.toNat)
    else 255
  if digitValue < base then some digitValue else none

/-- Parse a digit string as a `Nat` in the given base.  Returns
    `none` on any invalid digit or empty input.  Lexer guarantees
    `text` contains only valid digits for the declared base (per
    `fx_lexer.md` §4) — this function mostly tolerates the lexer's
    invariant but stays safe against malformed input. -/
def parseInBase? (base : Nat) (digitText : String) : Option Nat :=
  if digitText.isEmpty then none
  else
    digitText.toList.foldlM (init := 0) fun accumulator nextChar =>
      match charToDigit? base nextChar with
      | some digitValue => some (accumulator * base + digitValue)
      | none            => none

/-- Parse a lexer-produced integer-literal `text` (digits only, no
    underscores, no base prefix — the lexer canonicalizes) under its
    recorded `IntBase`.  Returns `none` on malformed input. -/
def parseIntText? (text : String) (base : IntBase) : Option Nat :=
  match base with
  | .dec => text.toNat?
  | .hex => parseInBase? 16 text
  | .oct => parseInBase? 8 text
  | .bin => parseInBase? 2 text

-- B7 match-compilation helpers (`resolveArmCtor?`,
-- `resolveMatchSpec?`, `scopeAndDepthForCtor`, `wrapCtorMethod`,
-- `boolMotive`) plus ctor-resolution (`resolveQualCtor?`,
-- `resolveUnqualCtor?`, `resolveCtorRef?`) live in
-- `FX/Elab/MatchHelpers.lean`.  Re-exported via the shared
-- `namespace FX.Elab`.
--
-- B12 named-argument routing (`reorderNamedCallArgs?` and
-- helpers) lives in `FX/Elab/NamedArgs.lean`.

/-! ## Synthesis-mode let-RHS type inference (partial §4.6)

`inferLetRhsType?` returns the declared type of a let-RHS for the
subset of surface shapes that are *synthesis-mode* per §4.6 — the
shapes whose type is determined purely by the RHS without needing
an expected type from the surrounding context.

Supported shapes:
  * Nullary ctor (`Red`, `Nat.Zero`) → `ind specName []`
  * Applied ctor (`Nat.Succ(n)`, `Config(h, p)`) → `ind specName []`
  * Boolean keyword literal (`true`, `false`) → `ind "Bool" []`
  * Integer literal (unsuffixed `42`, `0xFF`) → `ind "Nat" []`
  * Global name referencing a registered fn/const → registered type
  * Field access `obj.fieldname` where `fieldname` appears in a
    registered record spec → field's declared type

Unsupported (caller must fall back to `typeAnnotation`):
  * Polymorphic calls without type args
  * Empty collections `[]`, `{}`
  * Local variable references (need local typing context)
  * Lambda values (need expected Pi)
  * Arithmetic / comparison (no Phase-2 numeric type class)

Returns `none` when the RHS shape isn't in the synthesis-mode
subset, signaling the caller to require an ascription. -/

/-- Peel Pi binders off a type, returning the final codomain when
    the codomain is non-dependent (var 0 isn't used inside).
    Conservative — only returns `some` when the result is a ground
    type safely usable outside the peeled-away binders. -/
partial def peelPiReturn? : Term → Option Term
  | .pi _ _ body _ => peelPiReturn? body
  | result       =>
    match Term.countVarAt 0 result with
    | Usage.zero => some result
    | _          => none

def inferLetRhsType? (globalEnv : GlobalEnv) (rhs : Ast.Expr) : Option Term :=
  match rhs with
  -- Nullary ctor or global name reference.
  | .var qualIdent =>
    match resolveCtorRef? globalEnv qualIdent with
    | some (specName, _ctorIndex, ctorSpec) =>
      if ctorSpec.args.isEmpty then some (Term.ind specName [])
      else none  -- partial-ctor: user must use application syntax
    | none =>
      if qualIdent.parts.isEmpty then
        match globalEnv.lookupType? qualIdent.final with
        | some registeredType => some registeredType
        | none                =>
          -- Fall back to type name: `let x = color;` where `color`
          -- is a registered type → type of x is Type<0>.
          match Inductive.specByName? qualIdent.final globalEnv.userSpecs with
          | some _  => some (Term.type .zero)
          | none    => none
      else
        none  -- qualified non-ctor: out of scope
  -- Applied ctor or fn call.
  | .app fnExpr _callArgs _span =>
    match fnExpr with
    | .var qualIdent =>
      match resolveCtorRef? globalEnv qualIdent with
      | some (specName, _, _) => some (Term.ind specName [])
      | none =>
        -- Global fn call: look up declared type's return.  The
        -- registered type is `Π ... → T` per `elabFnType`; peel
        -- Pis and return the codomain when non-dependent.
        if qualIdent.parts.isEmpty then
          match globalEnv.lookupType? qualIdent.final with
          | some registeredType => peelPiReturn? registeredType
          | none                => none
        else
          none
    | _ => none
  -- Integer / bool literal.
  | .literal (.intLit _ _) _  => some (Term.ind "Nat" [])
  | .literal (.kw .trueKw) _  => some (Term.ind "Bool" [])
  | .literal (.kw .falseKw) _ => some (Term.ind "Bool" [])
  | .literal (.kw .typeKw) _  => some (Term.type (.succ .zero))
  -- Kind literal `effect` in type-param position — same shape as
  -- `type` for kind-checking purposes (both inhabit Type-of-types).
  -- The full kind distinction (§5.5 grammar: TYPE vs EFFECT vs
  -- NAT vs REGION) is deferred; for now all kinds collapse to
  -- `Type(succ 0)` since the elaborator treats every type-param
  -- as a ghost-graded binder regardless of kind.
  | .literal (.kw .effectKw) _ => some (Term.type (.succ .zero))
  -- Field access — look up the field in registered specs.
  | .field _receiver fieldName _span =>
    let allSpecs := globalEnv.userSpecs ++ Inductive.preludeSpecs
    allSpecs.findSome? fun spec =>
      match IndSpec.findFieldIndex? spec fieldName with
      | some fieldIndex =>
        match spec.ctors with
        | firstCtor :: _ => firstCtor.args[fieldIndex]?
        | []              => none
      | none => none
  -- §4.2 pipe `x |> rhs` has the same inferred type as the
  -- call the elab case synthesizes.  When rhs is already an
  -- application `f(args)`, we look up `f`'s return type — the
  -- pipe only prepends an arg, so the codomain is unchanged.
  -- When rhs is a bare callable (a var like `f`), pipe makes
  -- it `f(x)`; its type is `f`'s codomain.  Anything else
  -- (`x |> (fn(y) => …)`, `x |> 42`, etc.) is too polymorphic
  -- for synthesis mode — user must ascribe.
  | .pipe _lhsExpr rhsExpr _span =>
    match rhsExpr with
    | .app (.var qualIdent) _ _ =>
      match resolveCtorRef? globalEnv qualIdent with
      | some (specName, _, _) => some (Term.ind specName [])
      | none =>
        if qualIdent.parts.isEmpty then
          match globalEnv.lookupType? qualIdent.final with
          | some registeredType => peelPiReturn? registeredType
          | none                => none
        else
          none
    | .var qualIdent =>
      match resolveCtorRef? globalEnv qualIdent with
      | some (specName, _, _) => some (Term.ind specName [])
      | none =>
        if qualIdent.parts.isEmpty then
          match globalEnv.lookupType? qualIdent.final with
          | some registeredType => peelPiReturn? registeredType
          | none                => none
        else
          none
    | _ => none
  | _ => none

/-! ## Surface→kernel Grade + Pi/lam chain builders

Pure Term operations hoisted above the expression mutual block
so `elabStmtChain`'s local-fn case (E-7) can call them — Lean 4
`partial def` forward references across a mutual boundary don't
resolve, so helpers used inside the mutual must be declared
before it.  These have no elaborator dependencies — just grade
arithmetic and Term construction. -/

/-- Map surface parameter modes to the kernel `Grade` used on the
    corresponding `Pi`/`lam` binder.

    Current mapping (Q53 refinement of the A9 promise at §6.1):

      * `.ghost`               → `Grade.ghost`   (usage 0, erased)
      * `.ref_`                → `Grade.shared`  (usage ω — §7.1
                                  "shared borrow, duplicable")
      * `.affine`              → `Grade.shared`  (usage ω — affine
                                  allows ≤ 1 uses, and ω safely
                                  over-approximates; tightened to a
                                  proper `≤ 1` lattice element when
                                  the Usage semiring grows a fourth
                                  atom, tracked separately)
      * `.own`, `.refMut`,
        `.linear`, `.secret`,
        `.default_`            → `Grade.default` (usage 1, linear)

    `.secret` currently collapses to linear alongside the other
    exclusive modes — the security-dimension signaling ("this
    binder carries classified data") lives on the type, not the
    grade, so the usage dim is linear regardless.  Security
    enforcement fires through `Grade.security` at the value side.

    Single source of truth for surface→kernel grade mapping.  -/
def modeToGrade : ParamMode → Grade
  | .ghost  => Grade.ghost
  | .ref_   => Grade.shared
  | .affine => Grade.shared
  | _       => Grade.default

/-- Q54: context-aware refinement of `modeToGrade`.  The base
    mapping decides grade from surface mode alone; this variant
    consults the parameter's elaborated type so that a default-
    mode binding of a `@[copy]`-marked user type gets grade
    `Grade.shared` (usage = ω) without requiring an explicit
    `ref` on the surface.

    Precedence: surface mode wins.  `ghost x: copyable_type`
    stays ghost-graded; `ref x: copyable_type` stays shared (no
    change).  Only default / linear / own / refMut / secret
    bindings — whose `modeToGrade` would otherwise produce
    `Grade.default` (usage = 1) — get upgraded when the type
    head resolves to a copy-marked `IndSpec`.

    Resolution of the type head is deliberately syntactic:
    walk past `Term.app` spines to find the underlying
    `Term.ind` head (for parameterized types like `option(Nat)`),
    then look up the spec.  If the head isn't an `Ind` or the
    spec lookup fails, fall back to `modeToGrade` unchanged.
    Other Term shapes (`Pi`, `Sigma`, `Const`, primitives) are
    not copy-able in this Phase-2 mapping.
-/
def gradeForParam (paramMode : ParamMode) (paramType : Term)
    (globalEnv : GlobalEnv) : Grade :=
  let baseGrade := modeToGrade paramMode
  -- Surface mode already produces Grade.shared or Grade.ghost —
  -- no room to upgrade further.  Equivalent check against the
  -- usage dimension keeps this robust if a future mode-arm adds
  -- another shared-valued grade.
  if baseGrade.usage != Usage.one then baseGrade
  else
    -- Peel Term.app chain to find the head.
    let rec peelHead : Term → Term
      | Term.app headTerm _ => peelHead headTerm
      | other               => other
    match peelHead paramType with
    | Term.ind typeName _ =>
      -- `GlobalEnv.specByName?` unifies user-declared and prelude
      -- specs (§A11 / Env.lean:145).  Prelude Nat/Bool/Unit aren't
      -- marked `@[copy]` today — the lookup still fires the flag
      -- if a future prelude refresh sets it.
      match globalEnv.specByName? typeName with
      | some resolvedSpec =>
        if resolvedSpec.isCopy then Grade.shared else baseGrade
      | none => baseGrade
    | _ => baseGrade

/-- Wrap a pre-elaborated return `Term` with a chain of `Pi`
    binders for the given `params`.  The return term already lives
    in the innermost scope (all params pushed); the Pi chain wraps
    from outer to inner.

    **Innermost-effect convention.**  Only the INNERMOST arrow
    carries the declared effect — the one whose call actually
    performs it.  Outer curried arrows are pure applications that
    produce a smaller fn.  This matches §9 Curry semantics:
    `fn f(a, b): C with IO` ≡ `Π (a:A). Π (b:B) →{IO} C`.
    Partial application `f(a)` returns a `Π (b:B) →{IO} C` value
    without firing IO; the effect fires when the final arg is
    applied.  An earlier draft put the effect on ALL arrows,
    which broke this partial-application invariant. -/
def piFromTerm (globalEnv : GlobalEnv)
    (params : List (ParamMode × String × Term)) (returnTerm : Term)
    (returnEffect : Effect := Effect.tot) : Term :=
  let rec build : List (ParamMode × String × Term) → Term
    | [] => returnTerm
    | [(paramMode, _, paramType)] =>
      Term.pi (gradeForParam paramMode paramType globalEnv)
              paramType returnTerm returnEffect
    | (paramMode, _, paramType) :: remainingParams =>
      Term.pi (gradeForParam paramMode paramType globalEnv)
              paramType (build remainingParams) Effect.tot
  build params

/-- Analog of `piFromTerm` for lambdas — wrap a pre-elaborated
    body term with a `lambda`-chain.  The grade on each binder
    tracks the corresponding parameter's surface mode so that
    ghost type parameters carry `Grade.ghost` through Pi-intro
    (Wood-Atkey context division, §27.1) AND the Q54 copy-type
    upgrade stays consistent between the Pi and its lambda
    (otherwise a mismatch would make the decl's body type-check
    against a slightly different Pi than was declared). -/
def lamFromTerm (globalEnv : GlobalEnv)
    : List (ParamMode × String × Term) → Term → Term
  | [], bodyTerm => bodyTerm
  | (paramMode, _, paramType) :: remainingParams, bodyTerm =>
    Term.lam (gradeForParam paramMode paramType globalEnv) paramType
      (lamFromTerm globalEnv remainingParams bodyTerm)

/-- Pre-N11 guard: reject or-patterns at any depth in a match arm.

    The current Q81-Q85 elaborator has no or-pattern support; silently
    passing would either drop the arm (no ctor resolution) or trigger
    Q85+Q86-style composition bugs.  N11 wires Maranget in (whose N5
    pre-pass expands or-patterns structurally).  Until then, or-
    patterns are fatal with a diagnostic pointing at the landing task. -/
partial def patternContainsOrPattern : Ast.Pattern → Bool
  | .orPattern _ _       => true
  | .ctor _ args _       => args.any patternContainsOrPattern
  | .tuple items _       => items.any patternContainsOrPattern
  | .ascribed inner _ _  => patternContainsOrPattern inner
  | .asPattern inner _ _ => patternContainsOrPattern inner
  | .wildcard _          => false
  | .var _ _             => false
  | .literal _ _         => false

/-! ## Expression elaboration -/

mutual

/-- Elaborate a surface expression to a kernel term under `scope`,
    falling back to `globalEnv` for unqualified names that don't match a
    local binder — the name resolves to an inlined copy of the
    referenced decl's body, shifted to account for any binders
    introduced since the decl was elaborated.  Phase 2.2's inlining
    approach replaces a future `Term.const` kernel form (deferred;
    see AXIOMS.md status).

    **Expected-type threading (B6).**  The optional `expected`
    parameter carries the type the surrounding context wants this
    expression to produce (e.g., a function's declared return type
    for its body, or the outer if/else's return type for a branch).
    Most expression forms ignore `expected` and synthesize their
    term structurally.  `if`-expressions (B6) REQUIRE `expected`
    because the `indRec` motive needs to name the if-expr's
    result type and Phase-2.2 has no mechanism to infer it from
    the branches without a typing context. -/
partial def elabExpr (globalEnv : GlobalEnv) (scope : Scope)
    (expected : Option Term := none)
    : Ast.Expr → Except ElabError Term
  -- Variable.  Resolution cascade:
  --   Qualified `Mod.name`: must be a registered ctor-ref or unknown.
  --   Unqualified `name`:
  --     1. Local scope → `Term.var i`
  --     2. Global globalEnv body → inlined + shifted
  --     3. Prelude type spec → `Term.ind name []` (nullary types only)
  --     4. E001 unbound
  | .var q => do
    let name := q.final
    if q.parts.size > 0 then
      -- Qualified name: the only valid shape in M1 is a ctor
      -- reference like `Nat.Zero` / `Bool.True`.  Nullary ctors
      -- elaborate to `Term.ctor name ctorIndex [] []`; ctors
      -- requiring args must be applied (§4.1) — bare references
      -- emit E010.
      match resolveQualCtor? globalEnv q with
      | some (specName, ctorIndex, ctorSpec) =>
        if ctorSpec.args.isEmpty then
          -- B9: a qualified nullary ctor of a parameterized spec
          -- (e.g. `Option.None` in a `Option(Nat)` position)
          -- needs to thread the expected type args into the
          -- emitted Term or the kernel rejects with T111
          -- "expects N type params".  Mirrors the same inference
          -- at the unqualified ctor path (line ~573) and at the
          -- applied-ctor path in the `.app` case.
          let inferredTypeArgs : List Term :=
            match expected with
            | some (.ind expectedName expectedArgs) =>
              if expectedName == specName then expectedArgs else []
            | _ => []
          return Term.ctor specName ctorIndex inferredTypeArgs []
        else
          throw (ElabError.make "E010"
            s!"constructor '{specName}.{ctorSpec.name}' expects {ctorSpec.args.length} arg(s) — use application syntax '{specName}.{ctorSpec.name}(...)'"
            q.span)
      | none =>
        -- B13 impl-block method reference: `TypeName.methodName`
        -- is the name under which `flattenImplDecls` registered
        -- the method.  Try the globalEnv as a fully-qualified
        -- global fn name before rejecting.
        let fullyQualifiedName := String.intercalate "." (q.parts.toList ++ [name])
        if globalEnv.contains fullyQualifiedName then
          return Term.const fullyQualifiedName
        else
          let specName := q.parts[q.parts.size - 1]!
          throw (ElabError.make "E001"
            s!"unknown qualified name '{specName}.{name}' (no such ctor, type, or impl method)"
            q.span)
    else
      match scope.resolve? name with
      | some i => return Term.var i
      | none =>
        if globalEnv.contains name then
          -- Global reference.  Emit `Term.const` rather than inline
          -- the body — this ties the knot for recursion (a decl's
          -- body may reference itself when `elabFile` has pre-
          -- registered the name) and preserves §10.15 opaque-by-
          -- default body visibility.  The evaluator resolves
          -- `Term.const` lazily against `EvalEnv.globals`; the type
          -- checker resolves against the same env at typing.
          return Term.const name
        else
          -- Prelude-type fallback: unqualified names that match a
          -- registered `IndSpec` with zero params elaborate to the
          -- applied inductive type `Term.ind name []`.  Parameterized
          -- specs (Option, List, Pair) are kept out of the prelude
          -- registry until the typing layer threads type-args; see
          -- `FX/Kernel/Inductive.lean` `Experimental` namespace.
          match Inductive.specByName? name globalEnv.userSpecs with
          | some spec =>
            if spec.paramCount = 0 then
              return Term.ind name []
            else
              throw (ElabError.make "E001"
                s!"type '{name}' expects {spec.paramCount} type parameter(s)"
                q.span)
          | none =>
            -- Unqualified ctor lookup: sweep all registered specs
            -- (user first, then prelude) for a nullary ctor with
            -- this name.  This is what makes `Red` work as
            -- shorthand for `color.Red` after `type color Red;
            -- Green; Blue; end type;`.  Ctors with args must go
            -- through the `.app` case (application handles them
            -- via `resolveQualCtor?` + arg elab).
            let allSpecs := globalEnv.userSpecs ++ Inductive.preludeSpecs
            let ctorMatch := allSpecs.findSome? fun spec =>
              match spec.findCtor? name with
              | some (ctorIndex, ctorSpec) =>
                if ctorSpec.args.isEmpty then
                  some (spec.name, ctorIndex)
                else
                  none
              | none => none
            match ctorMatch with
            | some (specName, ctorIndex) =>
              -- B9: same type-arg inference as the applied-ctor
              -- branch in `.app`.  When a bare nullary ctor
              -- reference (e.g. `None`) appears in a position
              -- with known expected type `option(Nat)`, pull the
              -- type args off the expected and thread them into
              -- the emitted `Term.ctor` so the kernel's T111
              -- arity check passes.
              let inferredTypeArgs : List Term :=
                match expected with
                | some (.ind expectedName expectedArgs) =>
                  if expectedName == specName then expectedArgs else []
                | _ => []
              return Term.ctor specName ctorIndex inferredTypeArgs []
            | none =>
              throw (ElabError.make "E001"
                s!"unknown identifier '{name}'" q.span)
  -- `type` keyword (as literal): universe 0
  | .literal (.kw .typeKw) _ =>
    return Term.type .zero
  -- `effect` keyword (as literal) — kind marker for effect-row
  -- type parameters `<eff: effect>` per §9.2.  Elaborates to
  -- universe 0 for the same reason `type` does: it's a ghost-
  -- graded kind that carries no runtime content.  Full kind
  -- distinction lives in a later phase; for now `effect` and
  -- `type` are interchangeable at the elaboration boundary.
  | .literal (.kw .effectKw) _ =>
    return Term.type .zero
  -- Boolean keyword literals: desugar to `Term.ctor "Bool" k [] []`
  -- where `k` is the constructor index in `Inductive.boolSpec`.
  -- D1: surface access to the `Bool` prelude inductive.
  | .literal (.kw .trueKw) _ =>
    return Term.ctor "Bool" 1 [] []
  | .literal (.kw .falseKw) _ =>
    return Term.ctor "Bool" 0 [] []
  -- Unsuffixed integer literal: elaborate to a unary-`Nat` chain
  -- `Nat.Succ^n Nat.Zero` per `fx_design.md` §3.1.  Fixed-width
  -- suffixes (`u8`, `i64`, etc.) wait on D2's primitive numerics.
  | .literal (.intLit text base) span =>
    match parseIntText? text base with
    | some n => return buildNatLit n
    | none =>
      throw (ElabError.make "E010"
        s!"malformed integer literal '{text}'" span)
  -- Unit
  | .unit span =>
    -- Phase 2.1 has no unit type in the kernel.  Reject.
    throw (ElabError.make "E010"
      "unit expression — kernel has no unit type in Phase 2.1" span)
  -- Application.  Two cases:
  --   (1) `f` is a qualified ctor ref — `Nat.Succ(x)` → one
  --       `Term.ctor` node with elaborated args.
  --   (2) Generic: `f(a, b, c)` → `app (app (app f a) b) c`.
  | .app fnExpr callArgs span => do
    -- Record-literal sugar (B8): `TypeName { f: v, g: v }`
    -- parses as `Expr.app (.var "TypeName") [named-args]`.  We
    -- route the TypeName head to the sole ctor ONLY when every
    -- call-arg is `.named _ _` — positional args like
    -- `Pair(Nat, Nat)` are type application, not record
    -- construction, and must fall through to the parameterized-
    -- type-app branch.
    let allNamed : Bool :=
      !callArgs.isEmpty && callArgs.toList.all fun ca =>
        match ca with | .named _ _ => true | _ => false
    let maybeCtor : Option (String × Nat × IndCtor) :=
      match fnExpr with
      | .var qualIdent =>
        match resolveCtorRef? globalEnv qualIdent with
        | some triple => some triple
        | none        =>
          if allNamed then resolveRecordCtor? globalEnv qualIdent
          else none
      | _              => none
    match maybeCtor with
    | some (specName, ctorIndex, ctorSpec) =>
      if callArgs.size ≠ ctorSpec.args.length then
        throw (ElabError.make "E010"
          s!"ctor '{specName}.{ctorSpec.name}' expects {ctorSpec.args.length} arg(s), got {callArgs.size}"
          span)
      else
        -- Detect whether the caller used named args.  B8 record
        -- literals `Config { host: h, port: p }` desugar to a
        -- call with all-named args; we reorder them against the
        -- ctor's `argNames` before feeding positional slots.
        -- Mixed named + positional is a compile error (all-or-
        -- nothing, same discipline as B12 for fn calls).
        let namedCount := callArgs.toList.foldl (init := 0) fun acc ca =>
          match ca with | .named _ _ => acc + 1 | _ => acc
        let reorderedArgs : Except ElabError (List Ast.Expr) :=
          if namedCount = 0 then
            -- All positional — simple case.
            callArgs.toList.mapM fun ca =>
              match ca with
              | .pos argExpr => .ok argExpr
              | .named _argName _ =>
                .error (ElabError.make "E010"
                  s!"ctor '{specName}.{ctorSpec.name}': mixed positional / named args"
                  span)
              | .implicit _ =>
                .error (ElabError.make "E010"
                  s!"ctor '{specName}.{ctorSpec.name}' does not support implicit args"
                  span)
          else if namedCount ≠ callArgs.size then
            .error (ElabError.make "E010"
              s!"ctor '{specName}.{ctorSpec.name}': mixed positional / named args — use all of one form"
              span)
          else if ctorSpec.argNames.length = 0 then
            .error (ElabError.make "E010"
              s!"ctor '{specName}.{ctorSpec.name}' has no declared field names — use positional args"
              span)
          else do
            -- Reorder: for each ctor field name in declared order,
            -- find the matching named arg.  Missing or extra args
            -- emit E015 (same code family as B12 fn named-arg
            -- reorder).
            ctorSpec.argNames.mapM fun fieldName => do
              let found := callArgs.toList.findSome? fun ca =>
                match ca with
                | .named name expr =>
                  if name = fieldName then some expr else none
                | _ => none
              match found with
              | some expr => .ok expr
              | none      =>
                .error (ElabError.make "E015"
                  s!"ctor '{specName}.{ctorSpec.name}': missing field '{fieldName}'"
                  span)
        let orderedArgExprs ← reorderedArgs
        -- B9: for a parameterized spec, extract typeArgs from the
        -- expected type when it's `Term.ind specName [...]`.  This
        -- is the type-arg inference for the common case where a
        -- ctor call appears in a position with a known expected
        -- type (fn return, let binding, match arm body).  When
        -- expected is `none` or a non-matching shape, typeArgs
        -- stay empty and the kernel rejects with T111 — a clean
        -- "need explicit type arg" signal to the caller.
        let inferredTypeArgs : List Term :=
          match expected with
          | some (.ind expectedName expectedArgs) =>
            if expectedName == specName then expectedArgs else []
          | _ => []
        -- Q75: thread the ctor's declared arg types (after
        -- substituting `typeArgs`) through as expected types for
        -- each argument's own elaboration.  This matters for
        -- nested parameterized ctors like
        -- `Option.Some(Option.Some(Nat.Zero))` — the inner Some
        -- needs to see `Option(Nat)` as its expected type to
        -- thread `[Nat]` into its own emitted ctor term.  Without
        -- this, the inner Some elabs with `expected=none`, empty
        -- typeArgs, and kernel rejects with T111.
        let substitutedArgTypes : List Term :=
          ctorSpec.args.map (FX.Kernel.Term.substParams inferredTypeArgs)
        let argTerms ←
          (orderedArgExprs.zip substitutedArgTypes).mapM fun (argExpr, argType) =>
            elabExpr globalEnv scope (some argType) argExpr
        return Term.ctor specName ctorIndex inferredTypeArgs argTerms
    | none =>
      -- B9: parameterized-type application.  If `fnExpr` names a
      -- registered spec with paramCount > 0, treat this as a type
      -- application `spec(typeArg, ...)` → `Term.ind spec.name
      -- typeArgs` per §H.4 Ind-form.  This MUST precede the
      -- fn-call fallthrough because a parameterized-spec reference
      -- like `box` has no registered type in `globalEnv.entries`
      -- (it lives in `userSpecs`) — if we fell through, the fn
      -- path would emit E001 for missing fn.
      let maybeTypeApp : Option IndSpec :=
        match fnExpr with
        | .var qualIdent =>
          if qualIdent.parts.isEmpty && scope.resolve? qualIdent.final = none then
            globalEnv.specByName? qualIdent.final
          else
            none
        | _ => none
      match maybeTypeApp with
      | some spec =>
        if spec.paramCount > 0 then
          if callArgs.size ≠ spec.paramCount then
            throw (ElabError.make "E001"
              s!"type '{spec.name}' expects {spec.paramCount} type parameter(s), got {callArgs.size}"
              span)
          else
            let typeArgTerms ← callArgs.toList.mapM fun ca =>
              match ca with
              | .pos argExpr =>
                elabExpr globalEnv scope (some (Term.type .zero)) argExpr
              | .implicit argExpr =>
                elabExpr globalEnv scope (some (Term.type .zero)) argExpr
              | .named _ _ =>
                throw (ElabError.make "E010"
                  s!"type '{spec.name}': type application requires positional args"
                  span)
            return Term.ind spec.name typeArgTerms
        else
          -- Non-parameterized spec applied like `Bool()` — fall
          -- through and let the 0-arg Unit branch handle it (the
          -- caller probably meant to write bare `Bool`).
          pure ()
      | none => pure ()
      -- §31.7 zero-arg uniformity: a 0-arg call `f()` applies the
      -- fn to a synthetic Unit-ctor argument, mirroring the Unit
      -- parameter injected at `elabFnSignature`.  `f` elaborates
      -- with declared type `Π (_ :_ghost Unit) → T @ eff`; the
      -- call site supplies `Unit.tt` to fire the effect via
      -- Pi-elim and get back `T`.  Before this fix, 0-arg calls
      -- left `f` un-applied, which required a hack in effect
      -- inference to fire the declared effect off the bare name.
      if callArgs.isEmpty then
        let fnTerm ← elabExpr globalEnv scope none fnExpr
        return Term.app fnTerm (Term.ctor "Unit" 0 [] [])
      -- B12: when the caller uses named args, reorder them into the
      -- positional slots declared by the callee.  Requires the
      -- callee to be a direct unqualified reference to a registered
      -- fn decl so we can look up `paramNames`.  Mixed positional /
      -- named is rejected (all-or-nothing keeps the algorithm
      -- simple; implicits `#T` are orthogonal and preserved in
      -- position).
      let reorderedArgs ← reorderNamedCallArgs? globalEnv fnExpr callArgs span
      let fnTerm ← elabExpr globalEnv scope none fnExpr
      -- B11: thread the callee's declared type through the fold so
      -- each arg elaborates with its expected-domain known.  This
      -- unlocks typed-position-dependent forms at the call site —
      -- wildcard lambdas (`fn(_) => body`), type-arg inference for
      -- ctors like `None`, and anywhere else bidirectional
      -- elaboration needs a hint.  When the callee's type can't be
      -- looked up (lambda at call site, indirect fn), the expected
      -- falls back to `none` — the pre-B11 behavior.
      let initialDeclaredType : Option Term :=
        match fnExpr with
        | .var qualIdent =>
          if qualIdent.parts.isEmpty then
            globalEnv.lookupType? qualIdent.final
          else none
        | _ => none
      -- §4.2 rule 25 lift: when the formal param is a Pi and the
      -- call-arg is a composable expression carrying at least one
      -- `.dotShorthand` deep inside (but not a bare dot — Q61
      -- handles that — and not an explicit `.lam` — the user
      -- already wrote their own lambda), wrap the arg in
      -- `fn(it) => subst(arg)` so the single lambda's `it` binder
      -- is shared by every `.field` the substitution inserts.
      let liftDotsOverPi (argExpected : Option Term) (argExpr : Ast.Expr)
          : Ast.Expr :=
        match argExpected with
        | some (.pi _ _ _ _) =>
          match argExpr with
          | .dotShorthand _ _ => argExpr  -- bare: Q61 path
          | .lam _ _ _        => argExpr  -- explicit user lambda
          | _ =>
            if argExpr.containsDotShorthand then
              let substituted := argExpr.substDotShorthand "it"
              .lam #[.plain "it"] substituted Span.zero
            else
              argExpr
        | _ => argExpr
      -- Fold state is (appliedSoFar, remainingDeclaredType) — each
      -- iteration peels one Pi to get that arg's domain.
      let (finalTerm, _) ← reorderedArgs.foldlM
        (init := (fnTerm, initialDeclaredType))
        fun ((appliedSoFar, remainingType) : Term × Option Term) callArg => do
          -- Peel one Pi: domain becomes this arg's expected type;
          -- codomain becomes the new remaining type for the next iter.
          let (argExpected, nextRemaining) : Option Term × Option Term :=
            match remainingType with
            | some (.pi _grade domain codomain _eff) =>
              (some domain, some codomain)
            | _ => (none, none)
          match callArg with
          | .pos argExpr => do
            let liftedArg := liftDotsOverPi argExpected argExpr
            let argTerm ← elabExpr globalEnv scope argExpected liftedArg
            return (Term.app appliedSoFar argTerm, nextRemaining)
          | .named argName _ =>
            -- After `reorderNamedCallArgs?`, every argument is either
            -- `.pos` or `.implicit` — `.named` is an elab-internal
            -- invariant violation at this point.
            throw (ElabError.make "E999"
              s!"internal: named arg '{argName}:' survived reorder" span)
          | .implicit argExpr => do
            -- Implicit type args (`#T`) apply identically to positional
            -- args at the kernel level — the callee's ghost-graded Pi
            -- binder matches the explicit `#` marker at the call site.
            -- Phase-2 typing verifies the kind/type alignment per the
            -- Pi-elim rule; grade enforcement (that the target param
            -- is actually ghost) follows in A12.  Dot-lifting doesn't
            -- apply to implicits (they receive types, not values).
            let argTerm ← elabExpr globalEnv scope argExpected argExpr
            return (Term.app appliedSoFar argTerm, nextRemaining)
      return finalTerm
  -- Function type `A -> B`.  B lives under one new binder but
  -- the user wrote a non-dependent arrow, so shift B up by 1
  -- when folding into a Pi.  Q55: the binder's grade is
  -- computed via `gradeForParam ParamMode.default_` so that
  -- `Nat -> Nat` (whose domain is a @[copy] prelude spec) uses
  -- `Grade.shared` — matching what a `fn (x: Nat)` declaration
  -- produces.  Without this, `val f : Nat -> Nat; fn f(x: Nat)
  -- = ...;` declares Pi-grade mismatching between the val
  -- signature (default) and the fn body (shared), firing T002.
  | .arrow domainExpr codomainExpr _ => do
    let domainTerm   ← elabExpr globalEnv scope none domainExpr
    let codomainTerm ← elabExpr globalEnv scope none codomainExpr
    -- Anonymous arrow `A -> B`: no effect annotation (Tot).
    -- Effect-annotated fn types come through fnDecl, which
    -- builds Pi with the explicit row — see elabFnType.
    let binderGrade := gradeForParam ParamMode.default_ domainTerm globalEnv
    return Term.pi binderGrade domainTerm (Term.shift 0 1 codomainTerm) Effect.tot
  -- Lambda `fn(params) => body`
  | .lam params body span => do
    elabLamChain globalEnv scope params.toList body span expected
  -- sorry — produces an ill-typed term placeholder; the kernel
  -- will reject it at check time.  We emit `type (var 0)` —
  -- guaranteed ill-typed — so `fxi check` highlights the
  -- sorry as the source of the error.  Phase-3 will add a
  -- dedicated `sorry` term form.
  | .sorryExpr span =>
    throw (ElabError.make "E010"
      "sorry not supported in Phase 2.1 kernel" span)
  -- Remaining literal kinds: Phase 2.2 ships only `type`,
  -- `true`/`false`, and unsuffixed integer literals (→ unary Nat
  -- chain).  Everything else is rejected here with a specific
  -- diagnostic naming the task that will land it, so error
  -- output reads like a work roadmap instead of a generic
  -- placeholder.  Extending the accepted set is a one-arm edit
  -- here plus the corresponding kernel support.
  | .literal (.typedInt text _ suffix) span =>
    throw (ElabError.make "E010"
      s!"suffixed integer literal '{text}{suffix}' — fixed-width primitives land with D2" span)
  | .literal (.decimalLit text) span =>
    throw (ElabError.make "E010"
      s!"decimal literal '{text}' — `decimal` / `dec*` primitives land with D2" span)
  | .literal (.typedDecimal text suffix) span =>
    throw (ElabError.make "E010"
      s!"suffixed decimal '{text}{suffix}' — fixed-width decimals land with D2" span)
  | .literal (.typedFloat text suffix) span =>
    throw (ElabError.make "E010"
      s!"float literal '{text}{suffix}' — `f32`/`f64` primitives land with D2" span)
  | .literal (.ternaryLit text) span =>
    throw (ElabError.make "E010"
      s!"ternary literal '{text}' — balanced-ternary primitives land with D2" span)
  | .literal (.typedTernary text suffix) span =>
    throw (ElabError.make "E010"
      s!"suffixed ternary '{text}{suffix}' — fixed-width ternary lands with D2" span)
  | .literal (.stringLit _) span =>
    throw (ElabError.make "E010"
      "string literal — `string` primitive lands with D2" span)
  | .literal (.fstringLit _) span =>
    throw (ElabError.make "E010"
      "format string — f-string expansion lands with D2 + transformer pass" span)
  | .literal (.rstringLit _) span =>
    throw (ElabError.make "E010"
      "raw string — `string` primitive lands with D2" span)
  | .literal (.bstringLit _) span =>
    throw (ElabError.make "E010"
      "byte string — byte-array primitive lands with D2" span)
  | .literal tok span =>
    -- Defensive: should be unreachable.  `parseAtom` builds
    -- `Expr.literal` only from tokens matching `Token.isLiteralAtom`,
    -- and every such shape has a dedicated arm above (including the
    -- three recognized keyword literals `type`/`true`/`false`).
    -- If this fires, it's an elaborator bug: an exotic token made
    -- it past the parser's literal check.
    throw (ElabError.make "E100"
      s!"internal: unexpected literal token past parseAtom check: {repr tok}" span)
  -- `let x : T = e; body` — desugars to `(lambda(x :_1 T). body) e`.
  -- Phase 2.2 requires an explicit type ascription on the let —
  -- bidirectional inference lands in M2.  Only the `Pattern.var name`
  -- and `Pattern.wildcard` pattern shapes are handled; destructuring
  -- lets are deferred to pattern compilation (task B7).
  | .letBind pattern typeAnnotation valueExpr bodyExpr span => do
    let boundName ← match pattern with
      | .var boundName _ => pure boundName
      | .wildcard _      => pure "_"
      | _ =>
        throw (ElabError.make "E010"
          "let binding pattern other than identifier or wildcard not yet supported" span)
    let typeTerm ← match typeAnnotation with
      | some typeExpr => elabExpr globalEnv scope none typeExpr
      | none =>
        -- Synthesis-mode RHS per §4.6: infer directly from the
        -- AST shape when possible.  Failing that, emit T045 with
        -- a concrete hint.
        match inferLetRhsType? globalEnv valueExpr with
        | some inferredType => pure inferredType
        | none =>
          throw (ElabError.make "T045"
            s!"let binding '{boundName}' cannot infer type — add ': T' or use a synthesis-mode RHS (ctor call, literal, global fn, field access)"
            span)
    -- Thread the declared let-value type as expected so RHS
    -- if-exprs (and similar) elaborate correctly.
    let valueTerm ← elabExpr globalEnv scope (some typeTerm) valueExpr
    -- The let body runs under one extra binder, so the expected
    -- type (if any) needs to shift up by 1 to preserve its
    -- outer-scope de Bruijn references.
    let bodyExpected := expected.map (Term.shift 0 1)
    -- Q77: register the let-bound name's type so `match m` with
    -- `m: Option(T)` let-bindings can recover the motive's
    -- typeArgs (Q76 only covered fn params).
    let bodyTerm ← elabExpr globalEnv (scope.pushWithType boundName typeTerm)
                             bodyExpected bodyExpr
    -- Q56: route the binder's grade through `gradeForParam` so
    -- a `let` over a @[copy] type (prelude Nat/Bool/primitive,
    -- or user-declared copy) matches the grade that a fn param
    -- of the same type produces.  Pre-Q56 the let's lam was
    -- hardcoded `Grade.default`, so re-binding a copyable
    -- value via `let` silently downgraded its multi-use
    -- admission — breaking the invariant that "if you can
    -- pass it to a fn, you can let-bind it and reference it
    -- the same way".
    let binderGrade := gradeForParam ParamMode.default_ typeTerm globalEnv
    return Term.app (Term.lam binderGrade typeTerm bodyTerm) valueTerm
  -- `begin stmts…; tail end` — fold stmts into a nested let chain
  -- culminating in `tail`.  Each `letStmt` is a let binding; each
  -- `exprStmt` is a side-effecting evaluation (treated as
  -- `let _ = e; rest` — but since the kernel is currently pure,
  -- the value is just dropped).
  | .block stmts tail _span =>
    elabStmtChain globalEnv scope stmts.toList tail expected
  -- B6: `if cond; then else elseIfs* else else_body end if` desugars
  -- to `indRec "Bool" motive [else_body, then_body] cond` — method[0]
  -- runs for Bool.False, method[1] runs for Bool.True, matching the
  -- ctor ordering in `boolSpec`.  `else if` chains fold right into
  -- nested indRec forms.
  | .ifExpr cond thenBr elseIfs elseOpt span => do
    match expected with
    | none =>
      throw (ElabError.make "E010"
        "if-expression needs a known result type; use it as the body of a fn with a declared return type"
        span)
    | some returnType =>
      -- The condition is a Bool — propagate so that a nested
      -- if-expr used as a condition elaborates (its own expected
      -- would otherwise be `none` and error).
      let condTerm ← elabExpr globalEnv scope (some (.ind "Bool" [])) cond
      let thenTerm ← elabExpr globalEnv scope (some returnType) thenBr
      let elseTerm ← foldElseChain globalEnv scope returnType elseIfs.toList
                                    elseOpt span
      return Term.indRec "Bool" (boolMotive returnType)
               [elseTerm, thenTerm] condTerm
  -- §2.6 logical operators.  Elaborate directly to
  -- `indRec "Bool"` — no AST-level desugaring was done at
  -- parse time so error messages and future tooling can
  -- refer to the `not` / `and` / `or` keyword by name.
  --
  -- Result type: `Bool`.  When `expected` is present we thread
  -- it so that downstream sites that want a specific Bool-valued
  -- refinement still validate; when absent we use plain `Bool`.
  -- Operand type: `Bool` always — the condition / both sides
  -- are propositions.  A non-Bool operand trips T002 at the
  -- kernel check, not here.
  | .logicalNot body span => do
    let boolTy := Term.ind "Bool" []
    let resultType := expected.getD boolTy
    let bodyTerm ← elabExpr globalEnv scope (some boolTy) body
    -- `not b` = `indRec Bool (λ _. Bool) [True, False] b`:
    -- method[0] runs on Bool.False -> True;
    -- method[1] runs on Bool.True  -> False.
    let _ := span
    let ctorTrue  := Term.ctor "Bool" 1 [] []
    let ctorFalse := Term.ctor "Bool" 0 [] []
    return Term.indRec "Bool" (boolMotive resultType)
             [ctorTrue, ctorFalse] bodyTerm
  | .logicalAnd lhs rhs span => do
    let boolTy := Term.ind "Bool" []
    let resultType := expected.getD boolTy
    let lhsTerm ← elabExpr globalEnv scope (some boolTy) lhs
    let rhsTerm ← elabExpr globalEnv scope (some boolTy) rhs
    -- `a and b` = `if a then b else False`:
    -- method[0] (False branch) = False; method[1] (True) = b.
    let _ := span
    let ctorFalse := Term.ctor "Bool" 0 [] []
    return Term.indRec "Bool" (boolMotive resultType)
             [ctorFalse, rhsTerm] lhsTerm
  | .logicalOr lhs rhs span => do
    let boolTy := Term.ind "Bool" []
    let resultType := expected.getD boolTy
    let lhsTerm ← elabExpr globalEnv scope (some boolTy) lhs
    let rhsTerm ← elabExpr globalEnv scope (some boolTy) rhs
    -- `a or b` = `if a then True else b`:
    -- method[0] (False branch) = b; method[1] (True) = True.
    let _ := span
    let ctorTrue := Term.ctor "Bool" 1 [] []
    return Term.indRec "Bool" (boolMotive resultType)
             [rhsTerm, ctorTrue] lhsTerm
  -- §2.6 propositional implies `a ==> b`.  Classical reading:
  -- `not a or b` — the result is True when `a` is False,
  -- otherwise it's `b`.  Directly emits the short-circuit
  -- `indRec "Bool"` shape the desugar would produce, so the
  -- kernel term is identical to what a user-written
  -- `not a or b` would produce post-Q63 — only the AST
  -- provenance differs (so diagnostics cite `==>`).  Q67.
  | .logicalImplies lhs rhs span => do
    let boolTy := Term.ind "Bool" []
    let resultType := expected.getD boolTy
    let lhsTerm ← elabExpr globalEnv scope (some boolTy) lhs
    let rhsTerm ← elabExpr globalEnv scope (some boolTy) rhs
    -- `a ==> b` = `if a then b else True`:
    -- method[0] (False branch) = True (vacuously satisfied);
    -- method[1] (True branch) = b.
    let _ := span
    let ctorTrue := Term.ctor "Bool" 1 [] []
    return Term.indRec "Bool" (boolMotive resultType)
             [ctorTrue, rhsTerm] lhsTerm
  -- §2.6 propositional iff `a <==> b`.  Result is True exactly
  -- when both operands have the same Bool value.  When `a` is
  -- True, the result is `b` (matches iff b is also True);
  -- when `a` is False, the result is `not b` (matches iff b is
  -- also False).  The inner `not b` is itself an `indRec Bool`
  -- with methods [True, False] on b.  Q67.
  | .logicalIff lhs rhs span => do
    let boolTy := Term.ind "Bool" []
    let resultType := expected.getD boolTy
    let lhsTerm ← elabExpr globalEnv scope (some boolTy) lhs
    let rhsTerm ← elabExpr globalEnv scope (some boolTy) rhs
    let _ := span
    let ctorTrue  := Term.ctor "Bool" 1 [] []
    let ctorFalse := Term.ctor "Bool" 0 [] []
    -- `not rhs` as a Term, computed under the same motive so
    -- both arms of the outer indRec have matching types.
    let notRhsTerm : Term :=
      Term.indRec "Bool" (boolMotive resultType)
        [ctorTrue, ctorFalse] rhsTerm
    return Term.indRec "Bool" (boolMotive resultType)
             [notRhsTerm, rhsTerm] lhsTerm
  -- §2.6 constructor-test `x is Ctor`.  Desugars at elab time
  -- to an exhaustive match — one arm per ctor of the
  -- scrutinee's spec — producing `Bool.True` for the arm whose
  -- ctor tag matches and `Bool.False` for every other ctor:
  --
  --   match x;
  --     Ctor1(_, ..., _) => Bool.False;
  --     ...
  --     TargetCtor(_, ..., _) => Bool.True;
  --     ...
  --     CtorN(_, ..., _) => Bool.False;
  --   end match
  --
  -- We enumerate every ctor rather than using a `_` catch-all
  -- because elabMatch checks exhaustiveness by ctor name, not
  -- by wildcard coverage — and every ctor already has its arm
  -- so no exhaustiveness warning can fire spuriously.  Reusing
  -- elabMatch means pattern compilation, payload-binder shifts,
  -- and indRec lowering all fire from one code path — no new
  -- kernel surface.  Q66.
  | .isCheck scrutinee ctorRef span => do
    match resolveCtorRef? globalEnv ctorRef with
    | none =>
      throw (ElabError.make "E010"
        s!"`is`: '{ctorRef.final}' is not a known constructor"
        span)
    | some (specName, targetCtorIndex, _targetCtor) =>
      match globalEnv.specByName? specName with
      | none =>
        throw (ElabError.make "E010"
          s!"`is`: constructor '{ctorRef.final}' belongs to unregistered spec '{specName}'"
          span)
      | some resolvedSpec =>
        -- Build one arm per ctor.  Bool.True when the ctor
        -- index matches the target, Bool.False otherwise.
        let boolTrueExpr : Ast.Expr :=
          .var { parts := #["Bool"], final := "True", span := span }
        let boolFalseExpr : Ast.Expr :=
          .var { parts := #["Bool"], final := "False", span := span }
        let armsList : List Ast.MatchArm :=
          (resolvedSpec.ctors.zipIdx).map fun (armCtor, armCtorIndex) =>
            let subPatterns := armCtor.args.toArray.map fun _ =>
              Ast.Pattern.wildcard span
            let armCtorRef : QualIdent :=
              { parts := #[specName], final := armCtor.name, span := span }
            let armPattern : Ast.Pattern :=
              .ctor armCtorRef subPatterns span
            let armBody : Ast.Expr :=
              if armCtorIndex == targetCtorIndex then
                boolTrueExpr
              else
                boolFalseExpr
            .mk armPattern none armBody span
        elabMatch globalEnv scope expected scrutinee armsList.toArray span
  -- §3.7 list literal `[a, b, c]`.  Elaborates to a right-fold
  -- `Cons(a, Cons(b, Cons(c, Nil)))` over the prelude `List`
  -- spec.  The element type is extracted from the expected
  -- `List(T)` Pi — without it we can't pick the type arg for
  -- `Nil` / `Cons` and emit E010 with a hint.  Q71.
  | .listLit items span => do
    -- Extract element type from expected `Term.ind "List" [T]`.
    let elementType? : Option Term :=
      match expected with
      | some (.ind "List" (headArg :: _)) => some headArg
      | _                                 => none
    match elementType? with
    | none =>
      throw (ElabError.make "E010"
        s!"list literal has no known element type — use it in a position expecting `list<T>` (e.g. a `let xs : list(Nat) = [..]`) so the elaborator can resolve the element type"
        span)
    | some elementType =>
      -- Elaborate each item with the extracted element type as
      -- expected, then right-fold into a Cons chain terminating
      -- at Nil.  Nil ctor = `Term.ctor "List" 0 [elementType] []`;
      -- Cons = `Term.ctor "List" 1 [elementType] [head, tail]`.
      let nilTerm : Term := Term.ctor "List" 0 [elementType] []
      let mut resultTerm : Term := nilTerm
      -- Right-fold: iterate items in REVERSE so the outermost
      -- Cons wraps the first item and innermost wraps the last.
      for i in [0 : items.size] do
        let reverseIndex := items.size - 1 - i
        let itemExpr := items[reverseIndex]!
        let itemTerm ← elabExpr globalEnv scope (some elementType) itemExpr
        resultTerm := Term.ctor "List" 1 [elementType] [itemTerm, resultTerm]
      let _ := span
      return resultTerm
  -- §4.2 pipe `x |> f(args)` elaborates by prepending `x` to
  -- the RHS's call-arg array and delegating to the generic
  -- `Expr.app` path.  The synthesized application reuses `span`
  -- so any downstream diagnostic points at the pipe position
  -- rather than a parse-time-erased call site.
  --
  -- Named-arg promotion (§4.2 rule 5 — "pipe fills the unnamed
  -- parameter"):  when the RHS is a call to a direct-registered
  -- fn that already carries named args, we look up the callee's
  -- declared param names; if exactly one slot is not yet named,
  -- we emit `lhsExpr` as `.named uniqueSlot lhsExpr` instead of
  -- positional.  This keeps the generated call all-named so
  -- `NamedArgs.reorderNamedCallArgs?` routes normally and the
  -- spec's "no mixed positional+named" rule (§4.1) stays
  -- enforced for non-pipe direct calls — the promotion is a
  -- pipe-local operation, not a generic mixed-arg allowance.
  --
  -- Fallbacks (all emit a positional `lhsExpr`):
  --   * RHS is a call without named args — `x |> f(y)` becomes
  --     `f(x, y)`, caught by the arg-count path naturally.
  --   * RHS is a bare callable (var, field, paren-lambda) —
  --     wraps in a single-arg app.
  --   * Multiple unfilled slots / indirect callee / unregistered
  --     fn — pipe can't pick a unique target; positional falls
  --     through to E011 with the pipe span intact.
  | .pipe lhsExpr rhsExpr span => do
    let promotedArgs? (funcExpr : Ast.Expr) (existingArgs : Array Ast.CallArg)
        : Option (Array Ast.CallArg) :=
      let hasNamed := existingArgs.any fun ca =>
        match ca with | .named _ _ => true | _ => false
      if !hasNamed then none
      else
        match funcExpr with
        | .var qualIdent =>
          if !qualIdent.parts.isEmpty then none
          else
            match globalEnv.lookupParamNames? qualIdent.final with
            | none => none
            | some declaredParamNames =>
              let namedInCall : List String := existingArgs.toList.filterMap fun ca =>
                match ca with | .named paramName _ => some paramName | _ => none
              let freeSlots := declaredParamNames.filter
                (fun paramName => !namedInCall.contains paramName)
              match freeSlots with
              | [uniqueSlot] =>
                some (#[Ast.CallArg.named uniqueSlot lhsExpr] ++ existingArgs)
              | _ => none
        | _ => none
    let synthesizedApp : Ast.Expr :=
      match rhsExpr with
      | .app funcExpr existingArgs _ =>
        match promotedArgs? funcExpr existingArgs with
        | some argsAllNamed => .app funcExpr argsAllNamed span
        | none              =>
          .app funcExpr (#[Ast.CallArg.pos lhsExpr] ++ existingArgs) span
      | _ =>
        .app rhsExpr #[Ast.CallArg.pos lhsExpr] span
    elabExpr globalEnv scope expected synthesizedApp
  -- B7: `match scrutinee; arm1; arm2; … end match` desugars to
  -- `indRec specName motive methods scrutinee`, where `specName` is
  -- determined from the arms' ctor references (§13.5's Ind-elim at
  -- the surface).
  | .match_ scrutinee matchArms span =>
    elabMatch globalEnv scope expected scrutinee matchArms span
  -- B10: `for LOOPVAR in 0..HI; BODY end for` desugars to
  --   indRec "Nat" (λ _. Unit) [Unit.tt, λ i. λ _rec. BODY] HI
  -- following the same shape if/else (B6) and match (B7) use.  The
  -- Succ method's `λ i. λ _rec.` lambda chain reuses
  -- `wrapCtorMethod` from MatchHelpers — Nat's recursive self-ref
  -- in Succ(Nat) contributes the two-binder expansion.  Execution
  -- order on `for i in 0..N; body end for;` is `body[0]; body[1];
  -- ...; body[N-1]; return unit` because indRec unfolds as
  -- `s (N-1) (s (N-2) (... (s 0 base) ...))`, and in each step the
  -- recursive result (`_rec : Unit`) is evaluated before the
  -- outer lambda body.
  -- V1 restrictions pinned at elab time:
  --   * `lo` must be a literal `0` — non-zero starts need Nat
  --     arithmetic at elab time (threading `lo + k` through the
  --     step is future work).
  --   * `body` must elaborate to `Unit` (side-effect-only
  --     loops).  Block-form bodies use `unit` as their tail.
  --   * No `break` / `continue` — needs control-flow effects
  --     (tasks E-3, E-5).
  | .forRange loopVar loExpr hiExpr bodyExpr span => do
    let isLiteralZero : Bool :=
      match loExpr with
      | .literal (.intLit text base) _ =>
        match parseIntText? text base with
        | some 0 => true
        | _      => false
      | _ => false
    if !isLiteralZero then
      throw (ElabError.make "E013"
        "for-loop lower bound must be the literal `0` in this phase; non-zero starts need Nat addition at elab time (task B10 v1 restriction)"
        span)
    let natInd  := Term.ind "Nat" []
    let unitInd := Term.ind "Unit" []
    let unitTt  := Term.ctor "Unit" 0 [] []
    let hiTerm ← elabExpr globalEnv scope (some natInd) hiExpr
    -- Extend scope for the Succ method's binders per the ctor's
    -- self-referential shape: pushes `loopVar` then `_rec`, depth 2.
    let (loopScope, loopDepth) :=
      scopeAndDepthForCtor "Nat" scope [natInd] [loopVar]
    -- Body expected type is `Unit`, shifted into the loop scope.
    -- Unit is closed so `shift 0 loopDepth unitInd = unitInd`, but
    -- we keep the shift explicit to match the match-elaboration
    -- pattern and stay future-proof against dependent motives.
    let shiftedUnit := Term.shift 0 loopDepth unitInd
    let bodyTerm ← elabExpr globalEnv loopScope (some shiftedUnit) bodyExpr
    -- Succ method: `wrapCtorMethod` emits `λ loopVar : Nat. λ _rec :
    -- Unit. bodyTerm`, with the self-ref rec lambda discovered from
    -- Succ's arg shape `[.ind "Nat" []]`.
    let succMethod :=
      wrapCtorMethod "Nat" unitInd bodyTerm 0 [(natInd, loopVar)]
    -- Non-dependent motive `λ _ : Nat. Unit`, matching the shape
    -- `boolMotive` uses for if-expressions.
    let motive := Term.lam Grade.default natInd (Term.shift 0 1 unitInd)
    return Term.indRec "Nat" motive [unitTt, succMethod] hiTerm
  -- B10 part 2: `while COND; BODY end while` — parse surface
  -- recognized, but elab refuses until the `Div` effect and its
  -- termination discipline land (tasks E-3 for control-flow-vs-
  -- enabling effect split, and E-6 for the runtime).  Once those
  -- close, `while` desugars to a rec fn with `with Div` — no
  -- kernel changes beyond those effect rows.  Error E013 keeps the
  -- current landing under a single code shared with non-zero-start
  -- `for` so `fxi --explain E013` documents both together.
  | .whileLoop _cond _body span =>
    throw (ElabError.make "E013"
      "while-loop elab pending `with Div` effect wiring (tasks E-3 / E-6); for bounded iteration, use `for i in 0..N; ... end for;`"
      span)
  | .field receiver fieldName span => do
    -- B8 record field access: `receiver.field`.  Translated into
    -- `indRec[SpecName] (λ _ : SpecTy. FieldTy) [projection] receiver`
    -- where `projection` is a curried method that picks the
    -- field-index-th argument out of the ctor's arg telescope.
    --
    -- Phase-2 heuristic for disambiguation: search user specs +
    -- prelude specs for a single-ctor spec whose first ctor has a
    -- field named `fieldName`.  Unique match wins.  Multiple
    -- matches → E010 ambiguity; zero → E010 unknown.  Future
    -- work: thread `receiver`'s inferred type so the lookup is
    -- precise.
    let allSpecs := globalEnv.userSpecs ++ Inductive.preludeSpecs
    let specMatches := allSpecs.filterMap fun spec =>
      match IndSpec.findFieldIndex? spec fieldName with
      | some fieldIndex =>
        match spec.ctors with
        | firstCtor :: _ => some (spec, fieldIndex, firstCtor)
        | []              => none
      | none => none
    match specMatches with
    | [(targetSpec, fieldIndex, firstCtor)] => do
      let receiverTerm ← elabExpr globalEnv scope
        (some (Term.ind targetSpec.name [])) receiver
      let argCount := firstCtor.args.length
      -- The field's declared type may reference earlier args via
      -- `var i` (de Bruijn under the ctor arg telescope).  For
      -- non-dependent record fields (all Phase-2 records) the type
      -- has no `var` references; for dependent records we'd need
      -- more careful shifting.  Phase-2 uses the stored arg type
      -- directly — works for concrete field types.
      let fieldType := firstCtor.args[fieldIndex]!
      -- Non-dependent motive: `λ _ : ind specName []. fieldType`.
      -- The motive's body runs at depth 1 under the `_` binder.
      -- `fieldType` was elaborated at depth 0 (outside all ctor
      -- arg binders).  Shift by 1 to account for the `_` binder.
      let shiftedFieldType := Term.shift 0 1 fieldType
      let motive := Term.lam Grade.default
        (Term.ind targetSpec.name []) shiftedFieldType
      -- Build the curried projection method:
      --   λ arg_0 : T_0. ... λ arg_{n-1} : T_{n-1}. var (argCount - 1 - fieldIndex)
      -- The returned `var k` picks the field-index-th arg out of
      -- the telescope (rightmost = smallest index per de Bruijn).
      let rec buildProjection (argsRemaining : List Term) (depthSoFar : Nat)
          : Term :=
        match argsRemaining with
        | []                  =>
          Term.var (argCount - 1 - fieldIndex)
        | argType :: restArgs =>
          -- Shift argType into the current depth-sofar scope.
          let shiftedArgType := Term.shift 0 depthSoFar argType
          Term.lam Grade.default shiftedArgType
            (buildProjection restArgs (depthSoFar + 1))
      let projection := buildProjection firstCtor.args 0
      return Term.indRec targetSpec.name motive [projection] receiverTerm
    | []       =>
      throw (ElabError.make "E010"
        s!"unknown field '{fieldName}' — no registered record type declares it"
        span)
    | _matches =>
      throw (ElabError.make "E010"
        s!"ambiguous field '{fieldName}' — multiple registered types declare it; disambiguate via pattern match"
        span)
  | .tryPrefix body _span =>
    -- E-3 parser half (landed): `try EXPR` is a control-flow
    -- marker per §4.9.  The elaborator half (E042 emission when
    -- `body`'s callee has `Fail(E)` / `Exn(E)` in its effect row
    -- but no enclosing `try` is present) is a follow-on — needs
    -- the Fail effect wired in FX.Kernel.Effect first.  Until
    -- then: pass through.  The surface `try` is accepted but the
    -- kernel treats it as a no-op; semantic enforcement of the
    -- control-flow/enabling split lands with the full E-3.
    elabExpr globalEnv scope expected body
  | .handleExpr body _returnClause _arms _span =>
    -- E-5 parser half (landed): `handle EXPR ... end handle` is
    -- the effect-handler form per §9.6.  The elaborator half
    -- (typing rule per §9.6 + desugaring into delimited-
    -- continuation handler applications) is a follow-on — needs
    -- the user-effect registry from E-4's elaborator half plus
    -- a kernel representation for resumable continuations.
    -- Until then: pass through to the body.  The surface arms
    -- are parsed and available for tooling but are not yet
    -- dispatched at runtime.
    elabExpr globalEnv scope expected body
  | .dotShorthand fieldName span =>
    -- §4.2 dot-shorthand: `.field` without left operand in a
    -- function-argument position elaborates to `fn(it) => it.field`.
    -- Q61: implemented by reading the expected Pi's domain (the
    -- value `.field` will be applied to), looking up the record
    -- spec with a field named `fieldName`, and building a lam
    -- whose body is the same `indRec`-projection shape as the
    -- explicit `x.field` case at line ~1003.  Without an
    -- expected Pi or without a matching field, emits E010 with
    -- a helpful suggestion.
    match expected with
    | some (.pi _expectedGrade expectedDomain _expectedCodomain _expectedEffect) =>
      let rec peelAppHead : Term → Term
        | Term.app headTerm _ => peelAppHead headTerm
        | other               => other
      match peelAppHead expectedDomain with
      | .ind indTypeName _ =>
        match globalEnv.specByName? indTypeName with
        | some resolvedSpec =>
          match IndSpec.findFieldIndex? resolvedSpec fieldName with
          | some fieldIndex =>
            match resolvedSpec.ctors with
            | firstCtor :: _ =>
              let argCount := firstCtor.args.length
              let fieldType := firstCtor.args[fieldIndex]!
              -- Same motive + projection shape as the `.field`
              -- case.  The outer lam we wrap around it doesn't
              -- change the motive's self-contained de Bruijn —
              -- the motive's `_` binder provides its own depth.
              let shiftedFieldType := Term.shift 0 1 fieldType
              let motive := Term.lam Grade.default
                (Term.ind resolvedSpec.name []) shiftedFieldType
              let rec buildShorthandProjection (argsRemaining : List Term) (depthSoFar : Nat)
                  : Term :=
                match argsRemaining with
                | []                  =>
                  Term.var (argCount - 1 - fieldIndex)
                | argType :: restArgs =>
                  let shiftedArgType := Term.shift 0 depthSoFar argType
                  Term.lam Grade.default shiftedArgType
                    (buildShorthandProjection restArgs (depthSoFar + 1))
              let projection := buildShorthandProjection firstCtor.args 0
              -- Body: indRec on the lam's parameter (var 0).
              let accessBody := Term.indRec resolvedSpec.name motive
                                  [projection] (Term.var 0)
              -- Wrap in lam with binder grade routed through
              -- gradeForParam so a `.field` over a @[copy]-
              -- graded record inherits Grade.shared correctly.
              let binderGrade :=
                gradeForParam ParamMode.default_ expectedDomain globalEnv
              return Term.lam binderGrade expectedDomain accessBody
            | [] =>
              throw (ElabError.make "E010"
                s!"dot-shorthand '.{fieldName}': type '{indTypeName}' has no constructors"
                span)
          | none =>
            throw (ElabError.make "E010"
              s!"dot-shorthand '.{fieldName}': type '{indTypeName}' has no field named '{fieldName}'"
              span)
        | none =>
          throw (ElabError.make "E010"
            s!"dot-shorthand '.{fieldName}': type '{indTypeName}' not registered"
            span)
      | _ =>
        throw (ElabError.make "E010"
          s!"dot-shorthand '.{fieldName}' requires the expected Pi's domain to be an inductive type; got a non-inductive head"
          span)
    | _ =>
      throw (ElabError.make "E010"
        s!"dot-shorthand '.{fieldName}' has no known argument type — use it in a higher-order fn argument position (e.g. `map(.{fieldName})`) so the callee's parameter type threads through"
        span)
  -- §2.6 equality / inequality dispatch, Q68 + Q72.  `==` /
  -- `!=` are polymorphic over Bool and Nat: synthesis-elab
  -- each operand, inspect the emitted kernel Term for obvious-
  -- Bool shape, and dispatch accordingly.  Otherwise fall
  -- back to the Nat-forced path (Q68 baseline).
  --
  -- "Obvious-Bool" kernel shapes are `Term.ctor "Bool" ..` and
  -- `Term.indRec "Bool" ..` — the two ways a fully-elaborated
  -- term's head can be a Bool constructor or Bool eliminator.
  -- Covers all literal uses (`Bool.True`, `not e`, `a and b`,
  -- `a <==> b`, `a is Ctor`, `a < b`, etc.).  A scope-bound
  -- variable typed `Bool` is NOT caught — it elabs to
  -- `Term.var _`, whose type isn't visible to the elaborator
  -- without a typing-context walk.  For those, users can
  -- route through `<==>` (iff) or ascribe the comparison into
  -- a Bool context explicitly.
  --
  -- Bool shapes (both indRec "Bool" on lhs):
  --   a == b  →  [not rhs, rhs]   (iff)
  --   a != b  →  [rhs, not rhs]   (xor)
  -- Nat shapes (through `nat_eq` + optional `not`):
  --   a == b  →  nat_eq(a, b)
  --   a != b  →  not nat_eq(a, b)
  | .binop operator lhsExpr rhsExpr span => do
    -- Kernel-shape predicate: does `t` have a Bool head?  Used
    -- by both `==` and `!=` to pick dispatch.
    let looksBool : Term → Bool := fun t =>
      match t with
      | .ctor "Bool" _ _ _   => true
      | .indRec "Bool" _ _ _ => true
      | _                    => false
    -- Synthesis-elab probe.  Failure here is non-fatal: we
    -- just can't detect Bool, so we proceed to Nat where the
    -- real error (if any) will surface with the legacy-path
    -- diagnostic.
    let probedLhs := elabExpr globalEnv scope none lhsExpr
    let probedRhs := elabExpr globalEnv scope none rhsExpr
    let isBoolEq : Bool :=
      probedLhs.toOption.any looksBool ||
      probedRhs.toOption.any looksBool
    match operator with
    | Token.eqEq => do
      let boolTy := Term.ind "Bool" []
      let natTy  := Term.ind "Nat" []
      let resultType := expected.getD boolTy
      if isBoolEq then
        let lhsTerm ← elabExpr globalEnv scope (some boolTy) lhsExpr
        let rhsTerm ← elabExpr globalEnv scope (some boolTy) rhsExpr
        let _ := span
        let ctorTrue  := Term.ctor "Bool" 1 [] []
        let ctorFalse := Term.ctor "Bool" 0 [] []
        let notRhsTerm : Term :=
          Term.indRec "Bool" (boolMotive resultType)
            [ctorTrue, ctorFalse] rhsTerm
        return Term.indRec "Bool" (boolMotive resultType)
                 [notRhsTerm, rhsTerm] lhsTerm
      else
        let lhsTerm ← elabExpr globalEnv scope (some natTy) lhsExpr
        let rhsTerm ← elabExpr globalEnv scope (some natTy) rhsExpr
        let _ := span
        return Term.app (Term.app (Term.const "nat_eq") lhsTerm) rhsTerm
    | Token.neq => do
      let boolTy := Term.ind "Bool" []
      let natTy  := Term.ind "Nat" []
      let resultType := expected.getD boolTy
      if isBoolEq then
        let lhsTerm ← elabExpr globalEnv scope (some boolTy) lhsExpr
        let rhsTerm ← elabExpr globalEnv scope (some boolTy) rhsExpr
        let _ := span
        let ctorTrue  := Term.ctor "Bool" 1 [] []
        let ctorFalse := Term.ctor "Bool" 0 [] []
        let notRhsTerm : Term :=
          Term.indRec "Bool" (boolMotive resultType)
            [ctorTrue, ctorFalse] rhsTerm
        -- a != b  =  `if a then not b else b` — method[0]
        -- (False arm) runs rhs, method[1] (True arm) runs not
        -- rhs.  Differs from `==`'s [notRhsTerm, rhsTerm] by a
        -- method-array swap, nothing else.
        return Term.indRec "Bool" (boolMotive resultType)
                 [rhsTerm, notRhsTerm] lhsTerm
      else
        let lhsTerm ← elabExpr globalEnv scope (some natTy) lhsExpr
        let rhsTerm ← elabExpr globalEnv scope (some natTy) rhsExpr
        let _ := span
        let eqTerm := Term.app (Term.app (Term.const "nat_eq") lhsTerm) rhsTerm
        let ctorTrue  := Term.ctor "Bool" 1 [] []
        let ctorFalse := Term.ctor "Bool" 0 [] []
        return Term.indRec "Bool" (boolMotive resultType)
                 [ctorTrue, ctorFalse] eqTerm
    -- §2.6 Nat ordering — Q69.  All four operators share a
    -- single `nat_lt` prelude fn; three of them compose via
    -- arg-swap and/or `not` wrapping.  The `not` form reuses
    -- the `indRec "Bool" [True, False]` pattern from `!=`.
    --
    --   a <  b  =  nat_lt(a, b)
    --   a >  b  =  nat_lt(b, a)
    --   a <= b  =  not nat_lt(b, a)
    --   a >= b  =  not nat_lt(a, b)
    | Token.lt => do
      let natTy := Term.ind "Nat" []
      let lhsTerm ← elabExpr globalEnv scope (some natTy) lhsExpr
      let rhsTerm ← elabExpr globalEnv scope (some natTy) rhsExpr
      let _ := span
      return Term.app (Term.app (Term.const "nat_lt") lhsTerm) rhsTerm
    | Token.gt => do
      let natTy := Term.ind "Nat" []
      let lhsTerm ← elabExpr globalEnv scope (some natTy) lhsExpr
      let rhsTerm ← elabExpr globalEnv scope (some natTy) rhsExpr
      let _ := span
      -- Swap args: `a > b` ⟺ `b < a`.
      return Term.app (Term.app (Term.const "nat_lt") rhsTerm) lhsTerm
    | Token.leq => do
      let natTy := Term.ind "Nat" []
      let boolTy := Term.ind "Bool" []
      let resultType := expected.getD boolTy
      let lhsTerm ← elabExpr globalEnv scope (some natTy) lhsExpr
      let rhsTerm ← elabExpr globalEnv scope (some natTy) rhsExpr
      let _ := span
      -- `a <= b` ⟺ `not (b < a)`.
      let ltTerm := Term.app (Term.app (Term.const "nat_lt") rhsTerm) lhsTerm
      let ctorTrue  := Term.ctor "Bool" 1 [] []
      let ctorFalse := Term.ctor "Bool" 0 [] []
      return Term.indRec "Bool" (boolMotive resultType)
               [ctorTrue, ctorFalse] ltTerm
    | Token.geq => do
      let natTy := Term.ind "Nat" []
      let boolTy := Term.ind "Bool" []
      let resultType := expected.getD boolTy
      let lhsTerm ← elabExpr globalEnv scope (some natTy) lhsExpr
      let rhsTerm ← elabExpr globalEnv scope (some natTy) rhsExpr
      let _ := span
      -- `a >= b` ⟺ `not (a < b)`.
      let ltTerm := Term.app (Term.app (Term.const "nat_lt") lhsTerm) rhsTerm
      let ctorTrue  := Term.ctor "Bool" 1 [] []
      let ctorFalse := Term.ctor "Bool" 0 [] []
      return Term.indRec "Bool" (boolMotive resultType)
               [ctorTrue, ctorFalse] ltTerm
    -- §2.6 Nat arithmetic — Q70.  `+`, `-`, `*` each route
    -- through one prelude fn via `Term.const`.  Subtraction is
    -- saturating (max(0, n-m)); multiplication's body chains
    -- to `nat_add` at every Succ step of the outer induction.
    --
    --   a + b  =  nat_add(a, b)
    --   a - b  =  nat_sub(a, b)   (saturating)
    --   a * b  =  nat_mul(a, b)
    | Token.plus => do
      let natTy := Term.ind "Nat" []
      let lhsTerm ← elabExpr globalEnv scope (some natTy) lhsExpr
      let rhsTerm ← elabExpr globalEnv scope (some natTy) rhsExpr
      let _ := span
      return Term.app (Term.app (Term.const "nat_add") lhsTerm) rhsTerm
    | Token.minus => do
      let natTy := Term.ind "Nat" []
      let lhsTerm ← elabExpr globalEnv scope (some natTy) lhsExpr
      let rhsTerm ← elabExpr globalEnv scope (some natTy) rhsExpr
      let _ := span
      return Term.app (Term.app (Term.const "nat_sub") lhsTerm) rhsTerm
    | Token.star => do
      let natTy := Term.ind "Nat" []
      let lhsTerm ← elabExpr globalEnv scope (some natTy) lhsExpr
      let rhsTerm ← elabExpr globalEnv scope (some natTy) rhsExpr
      let _ := span
      return Term.app (Term.app (Term.const "nat_mul") lhsTerm) rhsTerm
    -- Q73: division and modulus on Nat.  Total — `a / 0 = 0`
    -- (the helper runs out of fuel before emitting a Succ).
    -- `a % b = a - (a/b)*b` composes the earlier prelude fns.
    --   a / b  =  nat_div(a, b)
    --   a % b  =  nat_mod(a, b)
    | Token.slash => do
      let natTy := Term.ind "Nat" []
      let lhsTerm ← elabExpr globalEnv scope (some natTy) lhsExpr
      let rhsTerm ← elabExpr globalEnv scope (some natTy) rhsExpr
      let _ := span
      return Term.app (Term.app (Term.const "nat_div") lhsTerm) rhsTerm
    | Token.percent => do
      let natTy := Term.ind "Nat" []
      let lhsTerm ← elabExpr globalEnv scope (some natTy) lhsExpr
      let rhsTerm ← elabExpr globalEnv scope (some natTy) rhsExpr
      let _ := span
      return Term.app (Term.app (Term.const "nat_mod") lhsTerm) rhsTerm
    | _ =>
      throw (ElabError.make "E010"
        s!"binary operator '{repr operator}' — §2.6 Nat ops wired: comparison (`==`/`!=`/`<`/`<=`/`>`/`>=`) and arithmetic (`+`/`-`/`*`/`/`/`%`); bitwise/shift ops are follow-on"
        span)
  | .index _ _ span
  | .prefix_ _ _ span
  | .tuple _ span
  | .unimplemented _ span =>
    throw (ElabError.make "E010"
      "expression form not supported in Phase 2.1 kernel" span)

/-- Elaborate a lambda-parameter chain `fn(p1, p2, …) => body`
    into a nested kernel `lam`.

    Param shapes supported (B11 partial):

      * `.typed name T` — explicit annotation; always accepted.
      * `.plain name` — **untyped**; accepted ONLY when the
        surrounding context provides an expected `Π`-type.
        The expected Pi's domain fills the binder's type; the
        expected's codomain is threaded into the recursive call
        so the rest-of-chain also benefits from inference.  No
        expected ⇒ `E010` with a hint.
      * `.wildcard` — `_` param; same inference rule as
        `.plain`, with an anonymous binder name.
      * `.destructure pattern` — still `E010`.  Destructuring
        desugar into `match` on the param is B11-followup.

    The `expected` parameter is `Option Term`; threading it
    via `let` through the recursion preserves de-Bruijn
    correctness (the Pi's codomain already lives under one
    binder in the outer scope and stays that way after we
    open it). -/
partial def elabLamChain (globalEnv : GlobalEnv) (scope : Scope)
    (params : List LamParam) (body : Ast.Expr) (span : Span)
    (expected : Option Term := none)
    : Except ElabError Term := do
  match params with
  | [] => elabExpr globalEnv scope expected body
  | .typed name typeExpr :: rest =>
    let typeTerm ← elabExpr globalEnv scope none typeExpr
    -- For the rest of the chain: if the expected was a Pi, strip
    -- its domain and recurse with the codomain as the new expected.
    -- Type checking will still enforce the annotation against the
    -- expected's domain at the kernel level.  Q55: inherit the
    -- expected Pi's binder grade when available so a typed lambda
    -- passed into a copy-graded position matches its expected
    -- type; otherwise compute from the annotation's type head via
    -- gradeForParam (matching §7.8 / Q54 copy propagation).
    let (innerExpected, binderGrade) := match expected with
      | some (.pi expectedGrade _dom codomain _eff) =>
        (some codomain, expectedGrade)
      | _ =>
        (none, gradeForParam ParamMode.default_ typeTerm globalEnv)
    let inner ← elabLamChain globalEnv (scope.push name) rest body
                  span innerExpected
    return Term.lam binderGrade typeTerm inner
  | .plain name :: rest =>
    match expected with
    | some (.pi expectedGrade domain codomain _eff) =>
      let inner ← elabLamChain globalEnv (scope.push name) rest body
                    span (some codomain)
      return Term.lam expectedGrade domain inner
    | _ =>
      throw (ElabError.make "E010"
        s!"lambda parameter '{name}' has no type annotation and no expected Pi-type in scope — either add `: T` or use the lambda in a typed position"
        span)
  | .wildcard :: rest =>
    match expected with
    | some (.pi expectedGrade domain codomain _eff) =>
      -- Anonymous binder pushes a sentinel name to Scope so de Bruijn
      -- positions stay aligned; the body can't reference it.
      let inner ← elabLamChain globalEnv (scope.push "_") rest body
                    span (some codomain)
      return Term.lam expectedGrade domain inner
    | _ =>
      throw (ElabError.make "E010"
        "wildcard lambda parameter requires an expected Pi-type — use `(_: T)` or call the lambda in a typed position"
        span)
  | .destructure destructurePattern :: rest =>
    -- Destructuring lambda: `fn((a, b)) => body` or
    -- `fn(MkPair(a, b)) => body`.  Requires an expected `Pi`
    -- whose domain is a registered inductive with a SINGLE
    -- constructor (Pair-like — a record or a product).  Compile
    -- to `λ _arg. indRec … _arg` with the constructor's args
    -- bound in the method.  Avoids re-implementing match logic
    -- by consuming the existing `scopeAndDepthForCtor` +
    -- `wrapCtorMethod` helpers from `FX/Elab/MatchHelpers.lean`.
    --
    -- Phase 2.2 scope: only (a) tuple patterns `(a, b)` desugar
    -- to the `Pair` prelude spec's `MkPair` constructor, and
    -- (b) single-ctor user ADTs accept a ctor pattern whose
    -- args are vars/wildcards (for record-destructuring of
    -- `type Config { host, port }` and similar).  Nested
    -- patterns (destructuring inside destructuring) are
    -- rejected — user rewrites as two lambdas.
    match expected with
    | some (.pi _grade domain codomain _eff) =>
      -- Extract the inductive spec from the expected domain.
      -- Destructuring only works when the param's expected
      -- type is a known inductive with a single constructor
      -- (a record, or a product like `Pair`).  This lets us
      -- use the ACTUAL ctor name — we can't guess `MkPair` if
      -- the user's signature says `my_record`.
      let (specName, ctorSpec) ←
        match domain with
        | .ind typeName _typeArgs =>
          -- Look up the spec in user decls first, then prelude.
          let lookupResult :=
            Inductive.specByName? typeName globalEnv.userSpecs
              |>.orElse (fun _ => Inductive.preludeSpecs.find? (·.name == typeName))
          match lookupResult with
          | some spec =>
            if spec.ctors.length ≠ 1 then
              throw (ElabError.make "E010"
                s!"destructuring lambda requires single-constructor spec, '{typeName}' has {spec.ctors.length} ctors — use `match` explicitly"
                span)
            else
              match spec.ctors with
              | [ctorSpec] => pure (typeName, ctorSpec)
              | _ => throw (ElabError.make "E010"
                     s!"destructuring lambda: spec '{typeName}' has unexpected ctor shape"
                     span)
          | none => throw (ElabError.make "E010"
                    s!"destructuring lambda: spec '{typeName}' not registered"
                    span)
        | _ => throw (ElabError.make "E010"
               "destructuring lambda requires an inductive type as the parameter's expected type"
               span)
      -- Resolve pattern-var names from the destructure pattern.
      -- For tuple patterns, the arg count must match the spec's
      -- ctor arg count.  For ctor patterns, the name must match
      -- the spec's sole ctor.
      let patternVarNames ←
        match destructurePattern with
        | .tuple patternItems _ =>
          if patternItems.size ≠ ctorSpec.args.length then
            throw (ElabError.make "E010"
              s!"destructuring tuple has {patternItems.size} elements, spec '{specName}' ctor takes {ctorSpec.args.length}"
              span)
          else
            patternItems.toList.mapM fun patternItem =>
              match patternItem with
              | .var varName _  => pure varName
              | .wildcard _     => pure "_"
              | _ => throw (ElabError.make "E010"
                     "nested destructuring patterns not supported — items must be identifiers or wildcards"
                     span)
        | .ctor qualIdent argPatterns _ =>
          if qualIdent.final ≠ ctorSpec.name then
            throw (ElabError.make "E010"
              s!"destructuring ctor '{qualIdent.final}' doesn't match spec's ctor '{ctorSpec.name}'"
              span)
          else
            argPatterns.toList.mapM fun argPattern =>
              match argPattern with
              | .var varName _  => pure varName
              | .wildcard _     => pure "_"
              | _ => throw (ElabError.make "E010"
                     "nested destructuring patterns not supported — args must be identifiers or wildcards"
                     span)
        | _ => throw (ElabError.make "E010"
               "destructuring lambda accepts only tuple or ctor patterns" span)
      -- Build scope for the body: outer + _arg + each pattern
      -- var (with auto-`_` binders for self-referential args;
      -- single-ctor records typically have none).
      let (bodyScope, _methodDepth) :=
        scopeAndDepthForCtor specName (scope.push "_arg")
                              ctorSpec.args patternVarNames
      -- Elaborate remaining lambda chain under the enriched
      -- scope; `rest` handles any further params.
      let innerBody ← elabLamChain globalEnv bodyScope rest body
                         span (some codomain)
      -- Wrap innerBody in the method's lambda chain (one lambda
      -- per ctor arg, shifted per position).  `wrapCtorMethod`
      -- produces the correctly-shifted method term.
      let argTypeNames := ctorSpec.args.zip patternVarNames
      let methodTerm := wrapCtorMethod specName codomain innerBody 0 argTypeNames
      -- Build a non-dependent motive:
      -- `λ (_ : domain). shift 0 1 codomain`.
      let motive := Term.lam Grade.default domain (Term.shift 0 1 codomain)
      -- Emit the outer lambda: `λ (_arg : domain). indRec … var0`.
      let indRecTerm :=
        Term.indRec specName motive [methodTerm] (Term.var 0)
      pure (Term.lam Grade.default domain indRecTerm)
    | _ => throw (ElabError.make "E010"
           "destructuring lambda parameter requires an expected Pi-type — use the lambda in a typed position"
           span)

/-- Fold an `else if` chain plus its final `else` body into a
    single kernel term.  Each `(cond_i, body_i)` pair becomes
    another `indRec "Bool"` wrapping the suffix chain.  The final
    `else` body (REQUIRED — B6 demands exhaustive if/else) becomes
    the innermost method[0].  Missing `else` is E010 with a
    suggestion to either add `else` or restructure into a match. -/
partial def foldElseChain (globalEnv : GlobalEnv) (scope : Scope)
    (resultType : Term) (elseIfChain : List (Ast.Expr × Ast.Expr))
    (maybeFinalElse : Option Ast.Expr) (span : Span)
    : Except ElabError Term := do
  match elseIfChain with
  | [] =>
    match maybeFinalElse with
    | some finalElseExpr => elabExpr globalEnv scope (some resultType) finalElseExpr
    | none =>
      throw (ElabError.make "E010"
        "if-expression must have an 'else' branch (Phase 2.2 requires exhaustive if/else)"
        span)
  | (condExpr, thenExpr) :: remainingElseIfs =>
    let condTerm ← elabExpr globalEnv scope (some (.ind "Bool" [])) condExpr
    let thenTerm ← elabExpr globalEnv scope (some resultType) thenExpr
    let elseTerm ← foldElseChain globalEnv scope resultType remainingElseIfs
                                  maybeFinalElse span
    return Term.indRec "Bool" (boolMotive resultType)
             [elseTerm, thenTerm] condTerm

/-- Fold a list of statements followed by a tail expression into a
    single elaborated term.  `letStmt name := value` becomes
    `(lambda(name :_1 T). <rest>) value`; `exprStmt e` becomes an
    ignored-value let `(lambda(_ :_1 T_e). <rest>) e` — M1 has no IO
    or mutation so `exprStmt` is pure dead code, but we preserve
    the evaluation site for future effect-tracking.

    Phase 2.2 requires every letStmt carry an explicit type
    ascription; exprStmt requires the expression's type to be
    inferable from the kernel (which in Phase 2.2 means the
    expression's elaborated term must be a literal `type`, a
    variable with known type in scope, or an Ind type — the
    kernel's `inferType` will catch unsupported shapes). -/
partial def elabStmtChain (globalEnv : GlobalEnv) (scope : Scope)
    (stmts : List Stmt) (tail : Ast.Expr)
    (expected : Option Term := none) : Except ElabError Term := do
  match stmts with
  | [] => elabExpr globalEnv scope expected tail
  | .letStmt pattern typeAnnotation valueExpr span :: remainingStmts =>
    let boundName ← match pattern with
      | .var boundName _ => pure boundName
      | .wildcard _      => pure "_"
      | _ =>
        throw (ElabError.make "E010"
          "let statement pattern other than identifier or wildcard not yet supported" span)
    let typeTerm ← match typeAnnotation with
      | some typeExpr => elabExpr globalEnv scope none typeExpr
      | none =>
        -- Synthesis-mode RHS per §4.6.
        match inferLetRhsType? globalEnv valueExpr with
        | some inferredType => pure inferredType
        | none =>
          throw (ElabError.make "T045"
            s!"let statement '{boundName}' cannot infer type — add ': T' or use a synthesis-mode RHS (ctor call, literal, global fn, field access)"
            span)
    -- Thread the declared let-value type as expected, so if-exprs
    -- (and other forms requiring an expected type) in the RHS
    -- elaborate under the correct context.
    let valueTerm ← elabExpr globalEnv scope (some typeTerm) valueExpr
    -- The body sees the binder; shift the expected type up by 1
    -- so its de Bruijn references (if any — typically closed
    -- types) still point to their original targets.
    let expectedShifted := expected.map (Term.shift 0 1)
    -- Q77: register the let-bound name's type (as we do for fn
    -- params in Q76) so downstream `match m` on `m: Option(T)`
    -- can recover the scrutinee's typeArgs for the motive.
    let bodyTerm ← elabStmtChain globalEnv
                                 (scope.pushWithType boundName typeTerm)
                                 remainingStmts tail expectedShifted
    -- Q56: grade routing — same rationale as the expression-
    -- level let above.  A block-form `let x : Nat = e; rest`
    -- produces a lam whose binder grade matches the type's
    -- copyability via `gradeForParam`.
    let binderGrade := gradeForParam ParamMode.default_ typeTerm globalEnv
    return Term.app (Term.lam binderGrade typeTerm bodyTerm) valueTerm
  | .exprStmt _droppedExpr span :: _rest =>
    -- `exprStmt` mid-block needs an inferred type for the
    -- discarded-value let.  Phase 2.2 doesn't do inference, so
    -- we reject with E010 and suggest the user write
    -- `let _ : T = e;` explicitly.  M2 unblocks this once the
    -- kernel's `inferType` is wired to elaborator-time inference.
    throw (ElabError.make "E010"
      "bare expression statement not yet supported — use `let _ : T = e;`"
      span)
  | .fnStmt fnName fnParams _fnRetType _fnEffects _fnSpecs fnBody span :: remainingStmts => do
    -- E-7 §4.7 rule 18: local fn inside a block.  Parsed form is
    -- restricted to `fn NAME(params): retType = expr;` — no `with`
    -- effects, no spec clauses, no type params (see Parser.lean
    -- `parseStmtsThenTailLoop`'s fnKw arm; parser rejects the
    -- fuller forms with P050/P051/P052 and suggests hoisting to
    -- a top-level fn).  Rule 18 is enforced by the parse
    -- restriction: a local fn has no declarable effects, so its
    -- effect row is `Tot` by construction and can't inherit the
    -- enclosing fn's row.
    --
    -- Desugar: `fn double(x:T):U = expr;\n<rest>` becomes
    -- `(λ (double :_1 Π x. U). <rest>) (λ x. expr)` at the kernel
    -- level — the enclosing block carries `double` as a let-bound
    -- closure addressable in subsequent stmts via Term.var 0.
    let _fnRetType := _fnRetType  -- silence unused warnings
    let _fnEffects := _fnEffects
    let _fnSpecs := _fnSpecs
    -- Elaborate params left-to-right in growing scope.  Each
    -- param's type expr may refer to earlier params (dependent
    -- param types work the same as top-level fn decls).
    let rec elabParams (sc : Scope)
        (acc : List (ParamMode × String × Term))
        : List FnParam → Except ElabError (Scope × List (ParamMode × String × Term))
      | [] => return (sc, acc.reverse)
      | .mk paramMode paramName paramTypeExpr _ :: rest => do
        let paramType ← elabExpr globalEnv sc none paramTypeExpr
        -- Q76: register the param's type alongside its name so
        -- `match m` in the body (with `m: Option(Nat)` etc.)
        -- can recover `[Nat]` for the motive's typeArgs.
        elabParams (sc.pushWithType paramName paramType)
                   ((paramMode, paramName, paramType) :: acc)
                   rest
    let (innerScope, elaboratedParams) ←
      if fnParams.isEmpty then
        -- §31.7 zero-arg uniform translation: same as top-level
        -- fns (see `elabFnSignature`), inject a ghost Unit param.
        pure (scope.push "_",
              [(ParamMode.ghost, "_", Term.ind "Unit" [])])
      else
        elabParams scope [] fnParams.toList
    let retTypeTerm ← elabExpr globalEnv innerScope none _fnRetType
    let declaredType := piFromTerm globalEnv elaboratedParams retTypeTerm Effect.tot
    let bodyInnerTerm ← match fnBody with
      | .oneLiner bodyExpr =>
        elabExpr globalEnv innerScope (some retTypeTerm) bodyExpr
      | .block _ _ =>
        throw (ElabError.make "E010"
          "local fn with block body not yet supported — use one-liner `= expr;`"
          span)
    let lamTerm := lamFromTerm globalEnv elaboratedParams bodyInnerTerm
    -- Let-desugar: wrap remainder in `(λ (name :_g fnType). rest) lamTerm`.
    -- Q56: the synthesized binder's grade routes through
    -- `gradeForParam` just like the expression-level let path
    -- above.  For a local fn the type is a Pi, which doesn't
    -- trigger the copy-upgrade (gradeForParam only peels
    -- through Term.app — Pi stays `Grade.default`), so this is
    -- a consistency fix rather than a behavioral change for
    -- typical E-7 usage.  It matters when a future refactor
    -- ever marks Pi types @[copy] (e.g., for pure-closure
    -- sharing) — the helper becomes the single point of
    -- truth.
    let expectedShifted := expected.map (Term.shift 0 1)
    let restTerm ← elabStmtChain globalEnv (scope.push fnName)
                                 remainingStmts tail expectedShifted
    let binderGrade := gradeForParam ParamMode.default_ declaredType globalEnv
    return Term.app
      (Term.lam binderGrade declaredType restTerm)
      lamTerm

/-- Elaborate a `match` expression to `Term.indRec`.

    1.  Scan arms for the governing `IndSpec` (first arm with a
        resolvable ctor pattern).
    2.  Elaborate the scrutinee against `ind specName []`.
    3.  For every ctor in `spec.ctors` order (not arm order), find
        the matching arm, elaborate its body in an extended scope,
        and wrap the body in the lambda chain the kernel's iota
        rule expects.
    4.  Emit `Term.indRec spec.name motive methods scrutineeTerm`
        with a non-dependent motive.

    Phase-2.2 limitations: guards rejected, nested patterns
    rejected, parameterized inductives rejected, wildcard / variable
    catch-all arms rejected.  Every ctor must have a dedicated arm. -/
partial def elabMatch (globalEnv : GlobalEnv) (scope : Scope)
    (expected : Option Term)
    (scrutinee : Ast.Expr) (matchArms : Array MatchArm)
    (matchSpan : Span)
    : Except ElabError Term := do
  -- Match needs a known result type to build the motive.  The
  -- same constraint if/else has (B6); inherited here.
  let returnType ← match expected with
    | some expectedType => pure expectedType
    | none =>
      throw (ElabError.make "E010"
        "match expression needs a known result type; use it as a fn body with a declared return type, or bind via 'let r : T = match ...'"
        matchSpan)
  -- Or-pattern rejection (pre-N11).  Maranget's N5 expansion handles
  -- these structurally; until N11 integrates Maranget, the legacy Q81-
  -- Q85 path would silently drop or-pattern arms via ctor-resolution
  -- misses.  Fail loudly instead.
  for candidateArm in matchArms do
    match candidateArm with
    | .mk armPattern _ _ armSpan =>
      if patternContainsOrPattern armPattern then
        throw (ElabError.make "E010"
          "or-patterns (`p1 | p2`) not yet supported by the legacy match elaborator — pending N11 Maranget integration; split into separate arms for now"
          armSpan)
  let spec ← match resolveMatchSpec? globalEnv matchArms with
    | some resolvedSpec => pure resolvedSpec
    | none =>
      throw (ElabError.make "E010"
        "match arms reference no known constructor — cannot infer scrutinee type from patterns alone"
        matchSpan)
  -- Q76: Parameterized-inductive match — recover typeArgs via
  -- Scope type hints (for variable scrutinees) or a synthesis
  -- probe (for direct ctor applications).  Scope-typed binders
  -- come from fn parameters (see `elabFnParamsInOrder` and the
  -- local-fn `elabParams`).  Sites that don't push with type
  -- (pattern-bound match args, bare lambda params without
  -- annotation) still hit the reject path below.
  let scrutineeTypeArgs : List Term :=
    if spec.params.length == 0 then []
    else
      -- Try 1: scope-var with registered type hint.
      let hintFromScope : Option (List Term) :=
        match scrutinee with
        | .var qualIdent =>
          if qualIdent.parts.isEmpty then
            match scope.typeOf? qualIdent.final with
            | some (.ind indName indArgs) =>
              if indName == spec.name then some indArgs else none
            | _ => none
          else none
        | _ => none
      match hintFromScope with
      | some typeArgsFromHint => typeArgsFromHint
      | none =>
        -- Try 2: probe the scrutinee in synthesis mode and
        -- inspect the head.  Works for direct ctor calls like
        -- `Option.Some(x)` when the outer context provides
        -- typeArgs (otherwise empty).  Non-fatal on error.
        match elabExpr globalEnv scope none scrutinee with
        | .ok (.ctor _ _ probeTypeArgs _) => probeTypeArgs
        | _ => []
  if spec.params.length ≠ 0 ∧ scrutineeTypeArgs.length ≠ spec.params.length then
    throw (ElabError.make "E010"
      s!"match against parameterized inductive '{spec.name}': couldn't recover typeArgs from the scrutinee.  Works today for: (a) fn parameters typed `{spec.name}(...)`, and (b) direct ctor applications in the scrutinee position.  Nested let-bindings and lambda params without annotation aren't yet scope-typed — use a named fn param as the scrutinee, or bind via a typed let."
      matchSpan)
  -- Elaborate the scrutinee with the recovered typeArgs threaded
  -- through.  For non-parameterized specs this reduces to the
  -- pre-Q76 behavior (`ind spec.name []`).
  let scrutineeExpectedType := Term.ind spec.name scrutineeTypeArgs
  let scrutineeTerm ← elabExpr globalEnv scope (some scrutineeExpectedType) scrutinee
  -- Build one method per ctor, in ctor-index order.  `buildMethods`
  -- walks the spec's ctor list and pulls the matching arm from
  -- `matchArms` by ctor-name resolution.
  let rec buildMethods (ctorIndex : Nat)
      : List IndCtor → Except ElabError (List Term)
    | []                     => return []
    | ctorSpec :: restCtors  => do
      -- Find the arm that references this ctor.  Q84: peek
      -- through top-of-arm `as` patterns so `Succ(p) as n => …`
      -- still resolves to the Succ ctor; the as-name is
      -- extracted below into `matchingArmAsName`.
      let matchingArmPair : Option (MatchArm × Option String) :=
        matchArms.toList.findSome? fun candidateArm =>
          let (stripped, asName) := stripArmAsPattern candidateArm
          match stripped with
          | .mk armPattern _ _ _ =>
            match resolveArmCtor? globalEnv armPattern with
            | some (armSpecName, armCtorIndex, _) =>
              if armSpecName == spec.name && armCtorIndex == ctorIndex then
                some (stripped, asName)
              else none
            | none => none
      -- Catch-all resolution.  Priority: ctor-specific arm first,
      -- then wildcard arm (`_ => body`, Q81), then var-pattern arm
      -- (`n => body`, Q82), with optional Q84 `as`-bindings
      -- layered on.  All catch-all shapes synthesize the same
      -- ctor pattern (`SpecName.CtorName(_, _, ..)`) so the
      -- existing arg-count / arg-names machinery works uniformly.
      -- `catchAllArm`'s `Option String` carries the bound name
      -- when the arm binds the scrutinee value (via `n =>`,
      -- `_ as n =>`, or `pat as n =>`); `none` when the arm
      -- doesn't bind anything (plain `_ =>`).  The downstream
      -- β-redex wrap (Q82) fires whenever the name is `some`,
      -- regardless of which surface form produced it.
      let catchAllArm : Option (MatchArm × Option String) :=
        matchArms.toList.findSome? fun candidateArm =>
          match candidateArm with
          | .mk (.wildcard _)                      _ _ _ => some (candidateArm, none)
          | .mk (.var varName _)                   _ _ _ => some (candidateArm, some varName)
          | .mk (.asPattern (.wildcard _) asName _) guard body span =>
            -- `_ as n` — catch-all + binding, equivalent to `n`.
            some (.mk (.wildcard span) guard body span, some asName)
          | _                                             => none
      -- Q83: guards on catch-all arms are not yet supported.  A
      -- guarded catch-all would need its own fallthrough — either
      -- another unguarded catch-all or a totality proof — which
      -- isn't worth the complexity for the first guard pass.  The
      -- 90% case (`Succ(p) if p > 5 => "big"; _ => "small";`) keeps
      -- the guard on the ctor-specific arm and the catch-all
      -- unguarded, so this restriction rarely bites.  Programs that
      -- need chained guards on a catch-all can write a nested
      -- `match` inside the catch-all body.
      match catchAllArm with
      | some (.mk _ (some _) _ catchSpan, _) =>
        throw (ElabError.make "E010"
          s!"guarded catch-all arm not yet supported in match on '{spec.name}' — put the guard on a ctor-specific arm and leave the catch-all unguarded, or use a nested match inside the catch-all body"
          catchSpan)
      | _ => pure ()
      let resolvedPair : Option (MatchArm × Option String) :=
        match matchingArmPair with
        | some existingPair => some existingPair
        | none =>
          match catchAllArm with
          | some (.mk _ armGuard armBody armSpan, maybeVarName) =>
            let wildcardArgs : Array Ast.Pattern :=
              Array.replicate ctorSpec.args.length (Ast.Pattern.wildcard armSpan)
            let ctorRef : QualIdent :=
              { parts := #[spec.name], final := ctorSpec.name, span := armSpan }
            let synthPattern : Ast.Pattern :=
              Ast.Pattern.ctor ctorRef wildcardArgs armSpan
            some (.mk synthPattern armGuard armBody armSpan, maybeVarName)
          | none => none
      let (.mk armPattern armGuard armBody armSpan, varCatchAllName) ←
        match resolvedPair with
        | some pair => pure pair
        | none =>
          throw (ElabError.make "E010"
            s!"non-exhaustive match: missing arm for '{spec.name}.{ctorSpec.name}' (add an explicit `{ctorSpec.name}(...) => ...` arm or a catch-all `_ => ...`)"
            matchSpan)
      -- Q83: guard on primary arm → needs catch-all as fallthrough.
      -- Since guarded catch-alls were rejected above, a primary arm
      -- with a guard must be ctor-specific (`varCatchAllName` is
      -- `none` in that branch).  The chain built later in this
      -- method references `catchAllArm`, which must therefore
      -- exist.  Check up-front so the error points at the arm
      -- rather than surfacing deep in the elaboration.
      if armGuard.isSome && catchAllArm.isNone then
        throw (ElabError.make "E010"
          s!"ctor-specific arm for '{spec.name}.{ctorSpec.name}' is guarded — add an unguarded catch-all `_ => ...` (or `n => ...`) to handle the fallthrough when the guard fails"
          armSpan)
      -- Q85: nested ctor-arg destructuring.  When the primary
      -- arm's ctor pattern has a ctor pattern at any arg
      -- position (e.g., `Some(Cons(h, _))`), `rewriteNestedArgs`
      -- replaces the nested position with a fresh var binder and
      -- synthesizes an inner `match` on that binder as the arm
      -- body — the nested pattern and the catch-all body become
      -- arms of the inner match.  The result is elaborated by
      -- the usual pipeline: the recursive `elabExpr`/`elabMatch`
      -- call processes the inner match end-to-end (Q81-Q84 all
      -- compose underneath).  Requires the outer catch-all to
      -- be an unguarded wildcard (`_ => body`) — a var-pattern
      -- or as-pattern catch-all would bind the scrutinee value
      -- which isn't in scope inside the synthesized inner match.
      let (armPattern, armBody, armGuard) ← do
        match armPattern with
        | .ctor _ ctorArgs _ =>
          if ctorArgs.any isNestedCtorArg then
            match catchAllArm with
            | none =>
              throw (ElabError.make "E010"
                s!"nested ctor-arg destructuring in '{spec.name}.{ctorSpec.name}' arm requires an unguarded wildcard catch-all `_ => ...` for inner fallthrough"
                armSpan)
            | some (.mk _ _ catchBodyExpr _, catchVarBinding) =>
              if catchVarBinding.isSome then
                throw (ElabError.make "E010"
                  s!"nested ctor-arg destructuring currently requires a wildcard catch-all `_ => ...` — var-pattern (`n => ...`) and as-pattern (`_ as n => ...`) catch-alls bind the scrutinee value, which isn't available inside the synthesized inner match"
                  armSpan)
              else
                rewriteNestedArgs armPattern armBody armSpan armGuard catchBodyExpr
          else
            pure (armPattern, armBody, armGuard)
        | _ =>
          pure (armPattern, armBody, armGuard)
      -- The arm's pattern must be a ctor pattern whose arg shapes
      -- line up with the spec's ctor arg count.
      let argPatterns ← match armPattern with
        | .ctor _ pats _ => pure pats
        | _ =>
          throw (ElabError.make "E010"
            s!"arm for '{spec.name}.{ctorSpec.name}' must use a constructor pattern"
            armSpan)
      if argPatterns.size ≠ ctorSpec.args.length then
        throw (ElabError.make "E010"
          s!"pattern '{spec.name}.{ctorSpec.name}' expects {ctorSpec.args.length} arg(s), got {argPatterns.size}"
          armSpan)
      -- Each arg pattern must be a bare identifier or wildcard
      -- in M2 — nested destructuring is deferred.
      let argNames : List String ←
        argPatterns.toList.mapM fun argPattern =>
          match argPattern with
          | .var boundName _ => pure boundName
          | .wildcard _       => pure "_"
          | _ =>
            Except.error (ElabError.make "E010"
              s!"ctor-arg pattern in '{spec.name}.{ctorSpec.name}' arm must be identifier or wildcard (nested patterns deferred)"
              armSpan)
      -- Extend scope to match the method's lambda chain, then
      -- elaborate the body under a correctly-shifted expected type.
      -- Q78: use the Typed variant so nested matches on a bound
      -- variable of parameterized type can recover its concrete
      -- typeArgs.  The self-ref walk uses the ORIGINAL arg types
      -- (`ctorSpec.args` with `.var i` placeholders) — substituting
      -- would turn an `Option(Option(Nat))` arg into a fake self-
      -- reference and break depth math.  The pushed type hint uses
      -- SUBSTITUTED types so nested matches see the concrete
      -- `Option(Nat)` instead of `.var 0`.
      let substitutedCtorArgs : List Term :=
        ctorSpec.args.map (FX.Kernel.Term.substParams scrutineeTypeArgs)
      let (bodyScope, bodyDepth) :=
        scopeAndDepthForCtorTyped spec.name scope
          ctorSpec.args substitutedCtorArgs argNames
      -- Q82: var-pattern catch-all arms bind the scrutinee value as
      -- `n`.  Implementation strategy: synthesize the method body
      -- as a β-redex `(λ n : scrutineeType. body) (Ctor args)` —
      -- the kernel reduces this during whnf, so `n` in the body
      -- sees the reconstructed ctor value with zero runtime cost
      -- beyond a standard β step the kernel already performs for
      -- iota.  Body elaboration happens under a scope where `n` is
      -- at index 0 (one deeper than ctor args); the outer β-redex
      -- sits at ctor-arg depth.
      let (extendedScope, extendedDepth) :=
        match varCatchAllName with
        | some varName =>
          let scrutineeIndType : Term := Term.ind spec.name scrutineeTypeArgs
          let shiftedScrutineeType : Term := Term.shift 0 bodyDepth scrutineeIndType
          (bodyScope.pushWithType varName shiftedScrutineeType, bodyDepth + 1)
        | none => (bodyScope, bodyDepth)
      let bodyExpectedType := Term.shift 0 extendedDepth returnType
      let armBodyTerm ←
        elabExpr globalEnv extendedScope (some bodyExpectedType) armBody
      -- When the arm came from a var-pattern catch-all, wrap the
      -- elaborated body in the β-redex described above.  Otherwise
      -- the elaborated body IS the method body.
      let methodBodyAtCtorDepth : Term :=
        match varCatchAllName with
        | some _ =>
          let scrutineeIndType : Term := Term.ind spec.name scrutineeTypeArgs
          let shiftedScrutineeType : Term := Term.shift 0 bodyDepth scrutineeIndType
          -- Reconstruct the ctor value at ctor-arg depth.  Type args
          -- live at outer scope (depth 0); shift them by bodyDepth
          -- so their free-var references match the inner context.
          -- Each ctor arg's de Bruijn index comes from
          -- `argDeBruijnIndicesForCtor`, which walks the same push
          -- counts `scopeAndDepthForCtorTyped` uses so the indices
          -- agree across self-ref and plain args.
          let shiftedTypeArgs : List Term :=
            scrutineeTypeArgs.map (Term.shift 0 bodyDepth)
          let argIndices : List Nat :=
            argDeBruijnIndicesForCtor spec.name ctorSpec.args
          let ctorArgVars : List Term := argIndices.map Term.var
          let ctorRecon : Term :=
            Term.ctor spec.name ctorIndex shiftedTypeArgs ctorArgVars
          Term.app (Term.lam Grade.default shiftedScrutineeType armBodyTerm) ctorRecon
        | none => armBodyTerm
      -- Q83: If the primary arm carries a guard, wrap the method
      -- body in `if guard; primaryBody else catchAllBody` via a
      -- `Term.indRec "Bool" (boolMotive _) [catchAll, primary]
      -- guardTerm` — same shape B6 uses for if/else.  The
      -- catch-all body is elaborated here under the same
      -- `bodyScope` as the primary (so both sit at ctor-arg
      -- depth); for var-pattern catch-alls, the body is wrapped in
      -- the same β-redex as in Q82.  Guards are elaborated in
      -- `bodyScope` directly (no var extension), matching the
      -- scope the ctor-specific arm's body sees.
      let finalMethodBodyAtCtorDepth : Term ← do
        match armGuard with
        | none => pure methodBodyAtCtorDepth
        | some guardExpr =>
          -- `catchAllArm` is non-none here (checked above).
          let (_, catchVarName, catchBody) :=
            match catchAllArm with
            | some (.mk _ _ catchBodyExpr catchSpan, maybeVar) =>
              (catchSpan, maybeVar, catchBodyExpr)
            | none =>
              -- Unreachable per the guard check above, but Lean's
              -- exhaustiveness doesn't know that.  Fall back to
              -- a dummy trio; the pure above fires on the `none`
              -- branch, not this one.
              (armSpan, none, armBody)
          let guardTerm ←
            elabExpr globalEnv bodyScope (some (Term.ind "Bool" [])) guardExpr
          -- Elaborate catch-all body at `bodyScope` (plain or
          -- extended with var binding for var-pattern catch-alls).
          let (catchScope, catchScopeDepth) :=
            match catchVarName with
            | some varName =>
              let shiftedType : Term :=
                Term.shift 0 bodyDepth (Term.ind spec.name scrutineeTypeArgs)
              (bodyScope.pushWithType varName shiftedType, bodyDepth + 1)
            | none => (bodyScope, bodyDepth)
          let catchExpectedType := Term.shift 0 catchScopeDepth returnType
          let catchBodyTerm ←
            elabExpr globalEnv catchScope (some catchExpectedType) catchBody
          -- β-redex wrap for var-pattern catch-all (same shape as
          -- the Q82 block above; Q82's path runs only when the
          -- primary arm is a var-pattern catch-all, which is a
          -- different case from Q83's guarded-primary path).
          let catchBodyAtCtorDepth : Term :=
            match catchVarName with
            | some _ =>
              let shiftedScrutineeType : Term :=
                Term.shift 0 bodyDepth (Term.ind spec.name scrutineeTypeArgs)
              let shiftedTypeArgs : List Term :=
                scrutineeTypeArgs.map (Term.shift 0 bodyDepth)
              let argIndices : List Nat :=
                argDeBruijnIndicesForCtor spec.name ctorSpec.args
              let ctorArgVars : List Term := argIndices.map Term.var
              let ctorRecon : Term :=
                Term.ctor spec.name ctorIndex shiftedTypeArgs ctorArgVars
              Term.app (Term.lam Grade.default shiftedScrutineeType catchBodyTerm) ctorRecon
            | none => catchBodyTerm
          -- Bool method order in `indRec` is `[False, True]`; the
          -- `True` branch returns `primaryBody`, the `False` branch
          -- returns `catchAllBody`.
          let shiftedReturnType := Term.shift 0 bodyDepth returnType
          let motive := boolMotive shiftedReturnType
          pure (Term.indRec "Bool" motive [catchBodyAtCtorDepth, methodBodyAtCtorDepth] guardTerm)
      -- Wrap body in the ctor-specific lambda chain the kernel
      -- iota rule expects to apply to.  Uses the UNSUBSTITUTED
      -- arg types — the kernel's indRec check re-substitutes
      -- `typeArgs` at method-type check time, so the method's
      -- lambda binders must carry `.var i` placeholders.
      let argTypeNamePairs := List.zip ctorSpec.args argNames
      let methodTerm :=
        wrapCtorMethod spec.name returnType finalMethodBodyAtCtorDepth 0 argTypeNamePairs
      let restMethods ← buildMethods (ctorIndex + 1) restCtors
      return methodTerm :: restMethods
  let methods ← buildMethods 0 spec.ctors
  -- Build non-dependent motive `\_ : ind spec.name typeArgs.
  -- shift 0 1 returnType` matching the shape B6 uses for if/else.
  -- For non-parameterized specs, `scrutineeTypeArgs` is `[]` and
  -- the motive's domain reduces to `ind spec.name []`.
  let motive := Term.lam Grade.default (Term.ind spec.name scrutineeTypeArgs)
                  (Term.shift 0 1 returnType)
  return Term.indRec spec.name motive methods scrutineeTerm

end  -- mutual (elabExpr, elabLamChain, foldElseChain, elabStmtChain, elabMatch)

/-! ## Type declaration elaboration (task B9) -/

/-- Elaborate one `VariantCtor` (name + arg list) into a kernel
    `IndCtor`.  `globalEnv` must already contain a placeholder spec
    for the enclosing type so self-references (`Succ(Nat)`) resolve
    at elab time.

    `paramScope` carries the enclosing type's type-parameter
    binders (B9 parameterized ADTs).  For non-parameterized ADTs
    it is `Scope.empty` — ctor args elaborate with no outer context
    (the pre-B9 behavior).  For `type box<a: type>`, the param
    scope has `a` pushed, so ctor arg references to `a` resolve
    to `Term.var 0`.

    Each arg's `typeExpr` elaborates under `paramScope` with
    expected type `Type<0>`. -/
partial def elabVariantCtor (globalEnv : GlobalEnv) (paramScope : Scope)
    (ctor : VariantCtor) : Except ElabError IndCtor := do
  match ctor with
  | .mk ctorName ctorArgs _span => do
    let elabArg (param : FnParam) : Except ElabError Term := do
      match param with
      | .mk _mode _name typeExpr _paramSpan => do
        elabExpr globalEnv paramScope (some (Term.type .zero)) typeExpr
    let argTypes ← ctorArgs.toList.mapM elabArg
    -- Preserve field names for record-field projection (B8).
    -- Synthetic `_arg_N` names for positional variant ctors still
    -- carry — they just never match `.field` lookups because users
    -- don't write `_arg_0` in surface syntax.
    let argNames := ctorArgs.toList.map fun param =>
      match param with
      | .mk _ name _ _ => name
    return { name := ctorName, args := argTypes, argNames := argNames }

/-- Build the full `IndSpec` for a type decl.  The spec is built in
    two phases: first, a placeholder (name + empty ctors) is
    registered on `globalEnv` so self-refs in ctor arg types resolve;
    then ctor args are elaborated against that env, and the resulting
    real spec is returned.  The caller is responsible for re-
    registering the real spec (shadowing the placeholder) on the
    running `GlobalEnv`.

    **Parameterized ADTs** (B9 landing).  For `type box<a: type>`:

      1. Each `typeParam : FnParam` elaborates its `typeExpr` into
         a kernel type (typically `Type<0>` for `a: type`).  These
         types become `spec.params`.
      2. The param names are pushed onto a fresh `paramScope` so
         ctor args written under the decl can reference them —
         `Full(a)`'s `a` resolves to `Term.var 0` in the ctor-arg
         scope, matching the `substParams` convention in
         `FX/Kernel/Substitution.lean`.
      3. The placeholder spec is registered with non-empty params so
         kernel `.ind name paramArgs` resolves correctly at ctor
         type-check time (via `Term.substParams`).

    Unchanged Phase-2 limitations:
      * No GADT shape (ctor return-type refinement) — deferred to
        A10 with dependent indices.
      * No empty-body decls with alias/record form — those emit
        P037 at parse time.
      * Kind annotations must be `type`; `nat`/`effect`/`region`
        kinds on type params are accepted but the kernel won't
        do anything special with them yet.
 -/
partial def elabTypeDeclSpec (globalEnv : GlobalEnv)
    (attrs : Array Ast.Expr) (name : String)
    (typeParams : Array FnParam) (ctors : Array VariantCtor)
    (span : Span) : Except ElabError IndSpec := do
  -- §7.8 / §17.4: scan `attrs` for the bare-var `@[copy]` marker.
  -- Any other attribute expression rides through as inert metadata
  -- (§17.4 "custom attributes, pure metadata, never change parsing
  -- or typechecking") — the elaborator doesn't need to enumerate
  -- them.  A non-var `copy(...)` shape (attribute with args) is
  -- deliberately NOT matched here; `@[copy]` is the nullary marker
  -- form per §7.8.
  let isCopyType : Bool := attrs.any fun attrExpr =>
    match attrExpr with
    | .var qualIdent => qualIdent.parts.isEmpty && qualIdent.final == "copy"
    | _              => false
  -- Phase 0: elaborate each type-parameter's kind into a kernel
  -- type.  `a: type` becomes `Term.type Level.zero` — the canonical
  -- kind for type parameters.  Other kinds (`nat`, `effect`,
  -- `region`) elaborate similarly through `elabExpr` under empty
  -- scope, giving the spec's param telescope.
  let elabParamKind (param : FnParam) : Except ElabError Term := do
    match param with
    | .mk _mode _name kindExpr _span =>
      elabExpr globalEnv Scope.empty none kindExpr
  let paramKinds ← typeParams.toList.mapM elabParamKind
  -- Build the param-scope for ctor-arg elaboration.  Push params
  -- left-to-right so the leftmost param has the largest de Bruijn
  -- index in the ctor-arg scope, matching §H.4 Ind-form and
  -- `substParams`'s convention (typeArgs passed in param-
  -- declaration order).
  let paramNames := typeParams.toList.map fun p =>
    match p with | .mk _ n _ _ => n
  let paramScope := Scope.empty.pushAll paramNames
  -- Phase 1: register placeholder spec so self-refs inside ctor args
  -- resolve via `Inductive.specByName? name globalEnv.userSpecs`.
  -- The placeholder carries the real `params` telescope so later
  -- typing sites that see `.ind name typeArgs` can substitute
  -- correctly.  Ctors are left empty on the placeholder — they get
  -- filled in Phase 2 and the caller re-registers the full spec.
  let placeholderSpec : IndSpec :=
    { name := name, params := paramKinds, ctors := [], isCopy := isCopyType }
  let envWithPlaceholder := globalEnv.addUserSpec placeholderSpec
  -- Phase 2: elaborate each ctor's arg types against env-with-
  -- placeholder under `paramScope`.  Self-refs inside arg types
  -- resolve to `Term.ind name paramAsArgs` (for recursive types
  -- like `List<a>`'s `Cons(a, List<a>)`).  Type-param references
  -- like `a` resolve to `Term.var i` per the scope's de Bruijn
  -- mapping.
  let elaboratedCtors ← ctors.toList.mapM
    (elabVariantCtor envWithPlaceholder paramScope)
  let fullSpec : IndSpec :=
    { name := name, params := paramKinds, ctors := elaboratedCtors
    , isCopy := isCopyType }
  -- Phase 3: strict-positivity check.  Mirrors what kernel does for
  -- prelude specs (Nat.Succ self-refs pass; negative occurrences
  -- reject).  Error T120 is the spec-registration failure code.
  if !StrictPositivity.isSatisfied fullSpec then
    throw (ElabError.make "T120"
      s!"type '{name}' violates strict positivity — self-reference appears in a negative (contravariant) position"
      span)
  -- Phase 4 (Q55): `@[copy]` soundness check per §7.8.
  -- A copy-marked type admits grade-ω at every binding site of
  -- instances of this type.  For that to be sound, every ctor
  -- argument must itself be duplicable — otherwise duplicating
  -- the outer value would silently duplicate a linear resource
  -- held by an arg (e.g. a FileDescriptor, a session channel).
  --
  -- The check:
  --   * Self-reference (`Term.ind name _`) is OK — the overall
  --     recursive type is uniformly grade-ω, so Succ-layer
  --     Nats inside a Nat are already copy (Nat itself is).
  --   * `Term.ind otherName _` is OK iff otherName's spec has
  --     `isCopy = true` (consults `envWithPlaceholder` so
  --     self-reference above resolves to the in-progress spec).
  --   * `Term.type _` is OK — type-valued fields are erased at
  --     runtime (§1.5), so duplication is trivially sound.
  --   * `Term.var _` (de Bruijn index into paramScope, i.e. a
  --     type parameter like `a` in `type Container<a>`) is
  --     deliberately REJECTED for Phase 2: without constraint
  --     syntax (`@[copy] type Box<a where copy(a)> { x: a }`),
  --     a generic @[copy] type cannot guarantee its type arg is
  --     copyable.  When constraints land (§16.4 where-clauses),
  --     this arm graduates to "OK iff the type param carries a
  --     copy constraint".
  --   * Other shapes (Pi, Sigma, etc.) are rejected — a @[copy]
  --     type holding a function or pair is generally unsound in
  --     Phase 2 (closures may capture linear data; Sigma-bound
  --     second components may be linear-dependent).
  if isCopyType then
    -- Re-register the full spec so the check sees its own isCopy
    -- flag for self-references (envWithPlaceholder had ctors = []).
    let envWithFullSpec := globalEnv.addUserSpec fullSpec
    let rec isCopyCompatibleType : Term → Bool
      | .ind argTypeName _ =>
        argTypeName == name
          || (match envWithFullSpec.specByName? argTypeName with
              | some resolvedSpec => resolvedSpec.isCopy
              | none              => false)
      | .app headTerm _ => isCopyCompatibleType headTerm
      | .type _         => true
      | _               => false
    for ctor in elaboratedCtors do
      for argType in ctor.args do
        if !isCopyCompatibleType argType then
          throw (ElabError.make "T121"
            s!"type '{name}' marked @[copy] but constructor '{ctor.name}' has a non-copy argument; every @[copy] type's ctor args must themselves be @[copy] (self-reference or copy-marked type)"
            span)
  return fullSpec

/-! ## Session declaration elaboration (S11)

Surface session declarations parse into `Decl.sessionDecl` carrying
an `Array SessionStep` and an optional `recBinder` label.  `S11`
turns that AST into a `FX.Derived.Session.SessionType` tree and
hands it to S9's `translate` to produce one or more `CoindSpec`s
that the global env registers via `addUserCoindSpecs`.

The conversion has two mutually recursive walks because
`SessionStep` and `SessionBranchArm` are mutual inductives in the
AST: a step list may end in a `branchStep`/`selectStep` whose
arms each carry their own step list.

Per `fx_design.md` §11.1, a step list's tail after a
branch/select/end/continue is unreachable — those four step kinds
terminate the surrounding sequence semantically.  This walk
honors that discipline by not threading `rest` through them.

Per `fx_design.md` §11.14 well-formedness: every `continue` must
be inside a `loop`, every `select`/`offer` must have distinct
labels.  We rely on `SessionType.wellFormed` (S4) to verify both;
on failure we emit S001.  We additionally check `continue`'s
label matches the enclosing `recBinder` (a label-mismatch is also
S001 — the surface declares the binder once and continue
references must agree).

Type parameters on session declarations are accepted by the parser
but ignored at this stage — payload types must be closed terms or
reference globals.  Wiring `<a: type, ...>` so payloads can be
generic in `a` is deferred (S22 covers session-contract bridging
where parametric payloads matter most). -/

mutual

/-- Convert a list of surface `SessionStep`s into a `SessionType`
    chain.  Send/recv steps thread the rest as their continuation;
    branch/select/end/continue terminate the chain (any tail is
    silently dropped per §11.1 semantics). -/
partial def stepsToSessionType (globalEnv : GlobalEnv) (declName : String)
    (recBinder : Option String) : List Ast.SessionStep
    → Except ElabError FX.Derived.Session.SessionType
  | [] => return .endS
  | step :: rest =>
    match step with
    | .sendStep _payloadName payloadTypeExpr _stepSpan => do
      let payloadTerm ← elabExpr globalEnv Scope.empty none payloadTypeExpr
      let continuation ← stepsToSessionType globalEnv declName recBinder rest
      return .send payloadTerm continuation
    | .recvStep _payloadName payloadTypeExpr _stepSpan => do
      let payloadTerm ← elabExpr globalEnv Scope.empty none payloadTypeExpr
      let continuation ← stepsToSessionType globalEnv declName recBinder rest
      return .recv payloadTerm continuation
    | .branchStep arms _stepSpan => do
      let branches ← armsToBranchList globalEnv declName recBinder arms.toList
      return .offerS branches
    | .selectStep arms _stepSpan => do
      let branches ← armsToBranchList globalEnv declName recBinder arms.toList
      return .selectS branches
    | .continueStep labelName stepSpan =>
      match recBinder with
      | none =>
        throw (ElabError.make "S001"
          s!"continue '{labelName}' outside any 'rec' binder in session '{declName}'"
          stepSpan)
      | some boundLabel =>
        if labelName != boundLabel then
          throw (ElabError.make "S001"
            s!"continue label '{labelName}' does not match enclosing 'rec {boundLabel}' in session '{declName}'"
            stepSpan)
        else
          return .continueS
    | .endStep _stepSpan => return .endS

/-- Convert each branch arm into a (label, body) pair.  The arm's
    body is its step list folded through `stepsToSessionType`. -/
partial def armsToBranchList (globalEnv : GlobalEnv) (declName : String)
    (recBinder : Option String) : List Ast.SessionBranchArm
    → Except ElabError (List (FX.Derived.Session.Label × FX.Derived.Session.SessionType))
  | [] => return []
  | .mk armLabel armSteps _ :: restArms => do
    let armBody ← stepsToSessionType globalEnv declName recBinder armSteps.toList
    let restBranches ← armsToBranchList globalEnv declName recBinder restArms
    return (armLabel, armBody) :: restBranches

end

/-- Elaborate a `sessionDecl` into the list of `CoindSpec`s that
    realize its protocol.  The first spec in the returned list is
    the channel's initial state; later specs are reachable
    sub-states (one per choice arm + one per send/recv
    continuation).

    Pass 1 of `checkFile` calls this and registers the result via
    `globalEnv.addUserCoindSpecs`.  The legacy single-decl path
    via `elabDeclE` returns a benign placeholder without spec
    registration (matching `elabTypeDeclSpec`'s pattern).

    Errors:
      * S001 — well-formedness failure (unguarded continue,
        mismatched continue label, duplicate branch label, or
        translation reported a structural error).
      * Any error from `elabExpr` on a payload type (typically
        T0xx for unknown type names).

    `_typeParams` is accepted but unused in v1 (see module
    docstring above for rationale). -/
partial def elabSessionDeclSpec (globalEnv : GlobalEnv) (declName : String)
    (_typeParams : Array FnParam) (recBinder : Option String)
    (steps : Array Ast.SessionStep) (span : Span)
    : Except ElabError (List CoindSpec) := do
  let bodySession ← stepsToSessionType globalEnv declName recBinder steps.toList
  let topSession : FX.Derived.Session.SessionType :=
    match recBinder with
    | none   => bodySession
    | some _ => .loopS bodySession
  -- S24: emit the specific S0xx code per §11.27 based on which
  -- well-formedness property failed.  S001 is unguarded
  -- `continueS`; S002 is duplicate `selectS`/`offerS` branch labels.
  match FX.Derived.Session.SessionType.wellFormedReason topSession with
  | some FX.Derived.Session.SessionType.WellFormedFailure.unguardedContinue =>
    throw (ElabError.make "S001"
      s!"session '{declName}': unguarded continue (continueS outside any enclosing loopS)"
      span)
  | some FX.Derived.Session.SessionType.WellFormedFailure.duplicateLabel =>
    throw (ElabError.make "S002"
      s!"session '{declName}': duplicate label in select/offer/branch"
      span)
  | none => pure ()
  -- S12: translate both the primary session and its dual in one
  -- pass.  The dual is required for `new_channel<S>()` (§11.2)
  -- which returns `(channel<S>, channel<dual(S)>)`; for both
  -- endpoints to type-check via the S6 Coind-form rule, both
  -- `CoindSpec`s must be registered.  The dual's prefix is
  -- `declName ++ "__dual"` (double underscore reserved for
  -- compiler-emitted specs so user-written `declName` can't
  -- collide).  S3's involutive-duality theorem ensures
  -- `dual (dual s) = s` at the session level, though names
  -- diverge (double-translation would produce `Chan__dual__dual`).
  let (primaryResult, dualResult) :=
    FX.Derived.Session.translateDualPair declName topSession
  let combinedErrors := primaryResult.errors ++ dualResult.errors
  if !combinedErrors.isEmpty then
    let errMsgs := combinedErrors.foldr (init := "") fun em acc =>
      if acc.isEmpty then em else s!"{em}; {acc}"
    throw (ElabError.make "S001"
      s!"session '{declName}' translation failed: {errMsgs}"
      span)
  return primaryResult.specs ++ dualResult.specs

/-! ## Declaration elaboration -/

-- `modeToGrade`, `piFromTerm`, and `lamFromTerm` live before
-- the expression mutual (above) so `elabStmtChain`'s local-fn
-- case (E-7) can call them.  They're pure Term operations
-- with no elaborator dependencies.

/-- Elaborate a fn declaration's parameters left-to-right under a
    growing scope, returning the final scope + mode-annotated
    param triples.  Factored out so both `elabFnType` (signature-
    only, used in `checkFile` pass 1 for forward/self-reference
    resolution) and `elabFnDecl` (full elab) share identical
    parameter handling. -/
partial def elabFnParamsInOrder (globalEnv : GlobalEnv)
    : List FnParam
    → Except ElabError (Scope × List (ParamMode × String × Term)) := fun allParams => do
  let rec loop (scope : Scope)
      (paramsSoFar : List (ParamMode × String × Term))
      : List FnParam → Except ElabError (Scope × List (ParamMode × String × Term))
    | [] => return (scope, paramsSoFar.reverse)
    | .mk paramMode paramName paramTypeExpr _ :: remainingParams => do
      let paramType ← elabExpr globalEnv scope none paramTypeExpr
      -- Q76: register the param type alongside its name so `match m`
      -- where `m` is a fn param can recover typeArgs for the motive.
      loop (scope.pushWithType paramName paramType)
           ((paramMode, paramName, paramType) :: paramsSoFar)
           remainingParams
  loop Scope.empty [] allParams

/-- Everything `elabFnDecl` and `elabFnType` need from a fn
    signature: the inner scope with every parameter bound, the
    mode-annotated param triples, the elaborated return type,
    and the assembled Pi-chain that IS the fn's declared type. -/
structure FnSignature where
  innerScope       : Scope
  elaboratedParams : List (ParamMode × String × Term)
  returnType       : Term
  declaredType     : Term

/-- Shared signature-elab prefix.  Given a globalEnv, the
    parameter list, and the return-type expression, produce the
    inner scope + mode-annotated param triples + elaborated
    return type + assembled Pi-chain.  Used by `elabFnType`
    (signature-only, pass-1 of `checkFile`) and `elabFnDecl`
    (full elab, pass-2) so both paths share identical parameter
    and return-type handling.

    **Zero-arg uniformity (§31.7 kernel translation).**  A fn
    declared with no parameters desugars to a ghost-graded
    Unit-parametered Pi — i.e. `fn io_op() : T with IO = body`
    elaborates as `λ (_ :_ghost Unit). body : Π (_ :_ghost
    Unit) → T @ IO`.  This keeps every fn's kernel shape a
    Pi: effects always fire at App sites via Pi-layer peeling,
    never at name references, consistent with the multi-arg
    translation pattern shown in §31.7.  The Unit binder is
    grade-0 (erased per §1.5), so there is zero runtime cost;
    call sites `f()` elaborate by synthesising the matching
    unit constructor argument at the elaborator's App case
    (see `elabExpr`).  This replaces an earlier "non-Pi
    declared type implies reference-fires-effect" special case
    in effect inference — now `Term.const` refs are uniformly
    `Tot`, App sites are uniformly where effects fire. -/
partial def elabFnSignature (globalEnv : GlobalEnv)
    (params : Array FnParam) (retType : Ast.Expr)
    (declaredEffect : Effect := Effect.tot)
    : Except ElabError FnSignature := do
  let (innerScope, elaboratedParams) ←
    if params.isEmpty then
      -- Synthetic ghost-Unit parameter per the §31.7 zero-arg
      -- uniform translation.  Name "_" signals unused; grade
      -- `Grade.ghost` marks it erased at compile time.
      pure (Scope.empty.push "_",
            [(ParamMode.ghost, "_", Term.ind "Unit" [])])
    else
      elabFnParamsInOrder globalEnv params.toList
  -- Return type elaborated once in the scope with every
  -- parameter bound.  Plays two roles downstream: innermost
  -- codomain of the Pi-chain, and B6 expected type for the body.
  let returnType   ← elabExpr globalEnv innerScope none retType
  let declaredType := piFromTerm globalEnv elaboratedParams returnType declaredEffect
  return { innerScope, elaboratedParams, returnType, declaredType }

/-- Translate a parsed surface `with EFFECT, …` list (each entry
    an `Expr`) into the kernel's `Effect` record.  Only recognizes
    bare `.var` shapes — `IO`, `Alloc`, `Read`, `Write`, `Async`,
    `Div`, `Ghost`, `Exn`, plus user-defined names which flow to
    the `unknown` residual (ignored at the kernel-Pi level; the
    elaborator's A12 pass catches them via the `constRefs`
    fallback).  Non-var shapes (`eff(T)`) silently drop for now
    (E-4 territory). -/
partial def effectsFromSurface (effectExprs : Array Ast.Expr) : Effect :=
  let names : List String := effectExprs.toList.filterMap fun expr =>
    match expr with
    | .var qualIdent => some qualIdent.final
    | _              => none
  (Effect.fromNames names).1

/-- Elaborate the declared type of a fn declaration (the Pi chain
    over parameters with the return type as innermost codomain).
    This is signature-only — the body isn't touched.  Used by
    `checkFile`'s pass-1 to pre-populate `globalEnv` with every
    decl's declared type so pass-2's body elab can resolve
    forward AND self references to `Term.const`. -/
partial def elabFnType (globalEnv : GlobalEnv)
    (params : Array FnParam) (retType : Ast.Expr)
    (declaredEffect : Effect := Effect.tot)
    : Except ElabError Term := do
  let sig ← elabFnSignature globalEnv params retType declaredEffect
  return sig.declaredType

/-- Rank a spec clause's kind in the canonical §5.1 ordering:
    `where` → `pre` → `post` → `decreases`.  Rising ranks mark
    a legal sequence; a later kind followed by an earlier one
    is an ordering violation (error R007).  Returned as a `Nat`
    so a strict `<` comparison detects regressions. -/
def specClauseRank : Ast.SpecClause → Nat
  | .whereCstr _ _    => 0
  | .preCond _ _      => 1
  | .postCond _ _ _   => 2
  | .decreases _ _    => 3

/-- Validate §5.1 clause ordering across a parsed spec list.
    Returns the first out-of-order clause's span (for the error
    diagnostic) or `none` when the ordering is legal.  Ignores
    repeated same-rank clauses (multiple `post` clauses are
    conjunctive per §5.1). -/
def checkSpecClauseOrder : Array Ast.SpecClause → Option Span := fun clauses =>
  let rec loop (prevRank : Nat) (idx : Nat) : Option Span :=
    if hLt : idx < clauses.size then
      let current := clauses[idx]
      let rank := specClauseRank current
      if rank < prevRank then
        -- Out-of-order: a spec kind with a lower rank follows a
        -- higher-ranked one.  Span of the offending clause names
        -- the source position of the violation.
        some (match current with
          | .whereCstr _ sp  => sp
          | .preCond _ sp    => sp
          | .postCond _ _ sp => sp
          | .decreases _ sp  => sp)
      else
        loop (max prevRank rank) (idx + 1)
    else
      none
  loop 0 0

/-- Elaborate a `fn` declaration to an ElabDecl.  The param
    types are elaborated in the *growing* scope (param k's type
    may refer to params 0..k-1 bound earlier).  The declared
    return type is elaborated once in the full inner scope and
    threaded as the B6 expected type when elaborating the body.
    B4 spec clauses (pre/post/decreases/where) are validated for
    §5.1 ordering, then each predicate is elaborated under the
    fn's param scope (plus the return-binder for `post`) and
    attached to the resulting ElabDecl for Stream E discharge. -/
partial def elabFnDecl (globalEnv : GlobalEnv) (name : String)
    (params : Array FnParam) (retType : Ast.Expr) (body : FnBody)
    (declaredEffect : Effect := Effect.tot)
    (transparent : Bool := false)
    (specs : Array Ast.SpecClause := #[])
    (_declSpan : Span := Span.zero)
    : Except ElabError ElabDecl := do
  let sig ← elabFnSignature globalEnv params retType declaredEffect
  -- B4: validate §5.1 clause ordering BEFORE elaborating each
  -- predicate so a mis-ordered file fails fast with a clear
  -- diagnostic (R007) rather than a downstream typing error.
  match checkSpecClauseOrder specs with
  | some badSpan =>
    throw (ElabError.make "R007"
      s!"fn {name}: specification clauses out of order — expected where → pre → post → decreases (§5.1)"
      badSpan)
  | none => pure ()
  -- B4: elaborate each surface spec clause under the fn's
  -- parameter scope so syntactic errors surface at elab time.
  -- `postCond` also binds the return-value name; the predicate
  -- lives in `innerScope.push returnBinder`.  Ghost-grade
  -- (erased at runtime per §1.5); the elaborated Terms are
  -- stored for SMT discharge in Stream E.
  let elabSpecs : Array ElabSpecClause ← specs.mapM fun specClause =>
    match specClause with
    | .whereCstr constraintExpr _ => do
      let constraintTerm ← elabExpr globalEnv sig.innerScope none constraintExpr
      pure (ElabSpecClause.whereCstr constraintTerm)
    | .preCond predicateExpr _ => do
      let predicateTerm ← elabExpr globalEnv sig.innerScope none predicateExpr
      pure (ElabSpecClause.preCond predicateTerm)
    | .postCond returnBinder predicateExpr _ => do
      -- Predicate sees all params plus the return-binder at
      -- de Bruijn 0.  Elaborate under the extended scope.
      let postScope := sig.innerScope.push returnBinder
      let predicateTerm ← elabExpr globalEnv postScope none predicateExpr
      pure (ElabSpecClause.postCond returnBinder predicateTerm)
    | .decreases measureExpr _ => do
      let measureTerm ← elabExpr globalEnv sig.innerScope none measureExpr
      pure (ElabSpecClause.decreases measureTerm)
  -- Build the declaration's body: lambda(p1:T1). lambda(p2:T2). … body
  match body with
  | .oneLiner bodyExpr =>
    let bodyTerm ← elabExpr globalEnv sig.innerScope (some sig.returnType) bodyExpr
    let lamTerm  := lamFromTerm globalEnv sig.elaboratedParams bodyTerm
    return { name := name, body := lamTerm, type := sig.declaredType
           , transparent, specs := elabSpecs }
  | .block stmts tailExpr =>
    let innerBody ← elabStmtChain globalEnv sig.innerScope stmts.toList
                                   tailExpr (some sig.returnType)
    let lamTerm := lamFromTerm globalEnv sig.elaboratedParams innerBody
    return { name := name, body := lamTerm, type := sig.declaredType
           , transparent, specs := elabSpecs }

/-- Elaborate a single declaration with an optional global globalEnv.
    The globalEnv provides the bodies of previously-elaborated decls
    for inline-by-name resolution at `elabExpr`'s `var` case.
    `@[transparent]` on a `fnDecl` flows into the `ElabDecl`'s
    `transparent` field, which `checkFile` / `elabFile` then
    forward to `GlobalEnv.addDecl`. -/
partial def elabDeclE (globalEnv : GlobalEnv) : Decl → Except ElabError ElabDecl
  | .fnDecl attrs _vis name params retType effects specs body span =>
    elabFnDecl globalEnv name params retType body
      (declaredEffect := effectsFromSurface effects)
      (transparent := hasTransparentAttr attrs)
      (specs := specs) span
  | .moduleDecl path _span =>
    -- `module Foo.Bar;` — module-system declarations are parsed
    -- and DROPPED in Phase-2.  Cross-file linkage (loading
    -- external modules, resolving qualified names across
    -- files) is Phase-6 per §25.  Until then, `module`
    -- clauses in a single-file program are no-ops; we emit
    -- a benign placeholder `ElabDecl` that the CLI treats as
    -- "ok but nothing to run".
    return { name := s!"<module {path.final}>"
           , body := Term.type .zero
           , type := Term.type (.succ .zero)
           , transparent := false }
  | .openDecl path _alias _span =>
    -- `open Std.List;` — same treatment as `module`.  Phase-2
    -- doesn't have cross-file scope merging; the decl is
    -- accepted and ignored.  Qualified names still work at
    -- use sites via the existing `.var (QualIdent)` parsing.
    return { name := s!"<open {path.final}>"
           , body := Term.type .zero
           , type := Term.type (.succ .zero)
           , transparent := false }
  | .includeDecl path _span =>
    return { name := s!"<include {path.final}>"
           , body := Term.type .zero
           , type := Term.type (.succ .zero)
           , transparent := false }
  | .constDecl name typeExpr valueExpr _span => do
    -- `const NAME : TYPE = EXPR;` — a zero-param alias.  Elaborates
    -- identically to a nullary fn: the declared type becomes the
    -- declaration's type, and the value expression (checked against
    -- that type for B6-style expected-type propagation) becomes the
    -- body.  No transparency attribute parsing yet; always opaque
    -- (§10.15 default).  Consts support forward references the same
    -- way fns do because `checkFile` pass 1 registers their
    -- signatures before pass 2 walks bodies (see below).
    let typeTerm ← elabExpr globalEnv Scope.empty none typeExpr
    let valueTerm ← elabExpr globalEnv Scope.empty (some typeTerm) valueExpr
    return { name := name, body := valueTerm, type := typeTerm, transparent := false }
  | .sorryDecl span =>
    throw (ElabError.make "E020" "sorry declarations not elaborated in Phase 2.1" span)
  | .valDecl name typeExpr _span => do
    -- `val NAME : TYPE ;` — forward declaration.  Elaborate the
    -- declared type against empty scope; the body is a placeholder
    -- `Term.const name` (self-ref) which at eval time resolves to
    -- the same placeholder — any actual use fails gracefully.
    -- Registers with `Trust.external` (§10.6) so release-build
    -- gates reject reachability from `Verified` callers absent an
    -- implementation elsewhere.
    let typeTerm ← elabExpr globalEnv Scope.empty none typeExpr
    return { name := name
           , body := Term.const name
           , type := typeTerm
           , transparent := false }
  | .typeDecl _attrs _name _typeParams _ctors _span =>
    -- Elaborated by `checkFile` pass 1 via `elabTypeDeclSpec` below —
    -- the spec is registered on `globalEnv.userSpecs` there, and no
    -- value-level `ElabDecl` entry is emitted (the name lives in
    -- userSpecs, not entries).  Reaching this path from a single-
    -- decl test via the legacy `elabDecl` (empty globalEnv) is the
    -- only case that fires; return a benign placeholder so the
    -- lone-decl test can observe success.
    return { name := s!"<type {_name}>"
           , body := Term.type .zero
           , type := Term.type (.succ .zero)
           , transparent := false }
  | .implDecl typeName _members _span =>
    -- B13 impl blocks are flattened into individual fn decls
    -- by `flattenImplDecls` BEFORE `elabDeclE` sees them.  Any
    -- `.implDecl` reaching here is an elab-path that bypassed
    -- flattening (single-decl test sweeps via `elabDecl`); emit
    -- a benign placeholder so the surface parses round-trip
    -- cleanly for diagnostics.
    return { name := s!"<impl {typeName}>"
           , body := Term.type .zero
           , type := Term.type (.succ .zero)
           , transparent := false }
  | .sessionDecl name typeParams recBinder steps span => do
    -- S11: validate by running `elabSessionDeclSpec` (catches
    -- ill-formed sessions, payload type errors, label mismatches),
    -- then return a benign placeholder.  The actual `CoindSpec`
    -- registration via `globalEnv.addUserCoindSpecs` happens in
    -- `checkFile` pass 1 — same pattern as `elabTypeDeclSpec`
    -- registering on `userSpecs`.  Single-decl tests that hit
    -- `elabDecl` directly will see the validation error here even
    -- though no spec gets persisted.
    let _specs ← elabSessionDeclSpec globalEnv name typeParams recBinder steps span
    return { name := s!"<session {name}>"
           , body := Term.type .zero
           , type := Term.type (.succ .zero)
           , transparent := false }
  | .effectDecl name _typeParams _ops _span =>
    -- E-4 parser half: accept the `effect Name ... end effect;`
    -- declaration and surface it as a benign placeholder.  The
    -- kernel effect row (FX/Kernel/Grade/Effect.lean) is a fixed
    -- 8-field struct today; registering a user-declared effect
    -- as a new row label requires making the row extensible
    -- (E-4 follow-on).  Until then, the decl parses, the AST
    -- exists, and tools can enumerate user effect names — but
    -- writing `with <UserEffect>` in a function's row falls
    -- through the built-in lookup and either errors at A12 or
    -- is silently dropped per the current row-from-surface
    -- decoder.  No registration of the operation signatures
    -- into GlobalEnv yet.
    return { name := s!"<effect {name}>"
           , body := Term.type .zero
           , type := Term.type (.succ .zero)
           , transparent := false }
  | .unimplemented note span =>
    throw (ElabError.make "E020" s!"unrecognized declaration: {note}" span)

/-- Legacy zero-globalEnv entry point: elaborate without reference to
    previously-elaborated decls.  Single-decl tests use this
    directly.  Multi-decl programs (via `fxi check`) should thread
    `GlobalEnv` through `elabDeclE`. -/
partial def elabDecl (decl : Decl) : Except ElabError ElabDecl :=
  elabDeclE GlobalEnv.empty decl

/-- Best-effort display name for a decl.  Used by tooling (`fxi check`)
    so that a failed elaboration can still be attributed to a source
    identifier.  Returns `"<anon>"` for forms that truly have no name
    (sorryDecl, moduleDecl doesn't define a value, …). -/
def Decl.nameHint : Decl → String
  | .fnDecl _ _ declName _ _ _ _ _ _ => declName
  | .constDecl declName _ _ _      => declName
  | .valDecl declName _ _          => declName
  | .typeDecl _ declName _ _ _     => declName
  | .implDecl typeName _ _         => s!"<impl {typeName}>"
  | .moduleDecl _ _              => "<module>"
  | .openDecl _ _ _              => "<open>"
  | .includeDecl _ _             => "<include>"
  | .sorryDecl _                 => "<sorry>"
  | .sessionDecl declName _ _ _ _ => declName
  | .effectDecl declName _ _ _   => declName
  | .unimplemented _ _           => "<unimpl>"

-- `prefixFnDeclName`, `flattenImplDecls`, `elabFile`,
-- `DeclResult`, `elabAndCheckE`, `elabAndCheck`, and
-- `checkFile` live in `FX/Elab/CheckFile.lean` (R5).  Imported
-- via the parent module so existing `import FX.Elab.Elaborate`
-- sites still resolve these names unchanged — the single-file
-- view is preserved through the shared `namespace FX.Elab`.

end FX.Elab
