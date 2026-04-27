import FX.Elab.Elaborate
import FX.Elab.EffectInference
import FX.Derived.PreludeFn

/-!
# File-level elaboration + kernel check driver

Extracted from `FX/Elab/Elaborate.lean` (R5).  Hosts every
whole-file orchestration routine:

  * `prefixFnDeclName` / `flattenImplDecls` — §16.1 impl-block
    expansion into qualified top-level fn decls.
  * `elabFile` — single-pass elaborate+register, no kernel
    checking.  Used by callers that want the elaborated
    forms without typing (tooling, CLI `fxi dump`).
  * `DeclResult` — the tri-state outcome tag for combined
    elab + kernel check.
  * `elabAndCheckE` / `elabAndCheck` — one-shot drivers for
    single-decl tests.
  * `checkFile` — the TWO-PASS driver that is the main
    production entry point (`fxi check`, `fxi run`).  Pass 1
    registers every signature; pass 2 elaborates bodies +
    runs the kernel checker + re-registers real bodies.

All of these live in `namespace FX.Elab` so existing imports of
this name (via the parent module) still work.
-/

namespace FX.Elab

open FX.Kernel
open FX.Syntax
open FX.Syntax.Ast

/-- Rename a `fnDecl` by prepending `TypeName.` to its name.
    Used by `flattenImplDecls` to flatten impl members into
    qualified top-level decls. -/
def prefixFnDeclName (typeName : String) : Decl → Decl
  | .fnDecl attrs vis methodName params retType effects specs body span =>
    .fnDecl attrs vis s!"{typeName}.{methodName}" params retType effects
            specs body span
  | other => other

/-- Expand every `.implDecl typeName members` into its member
    list with each fn renamed to `typeName.methodName`, leaving
    non-impl decls unchanged.  Every impl block thus flattens to
    zero-or-more top-level fn decls in source order.  Two
    traversal passes: an inline one here so both `elabFile` and
    `checkFile` start from the post-flatten decl list.  B13 §16.1. -/
def flattenImplDecls (decls : Array Decl) : Array Decl :=
  decls.foldl (init := (#[] : Array Decl)) fun acc decl =>
    match decl with
    | .implDecl typeName members _ =>
      acc ++ members.map (prefixFnDeclName typeName)
    | other => acc.push other

/-- Elaborate every decl in a file, threading a growing
    `GlobalEnv` across decls so later decls can reference earlier
    ones by name.  Returns one result per decl in source order. -/
def elabFile (file : File) : Array (Except ElabError ElabDecl) := Id.run do
  -- Q68: start with prelude fns pre-registered (nat_eq etc.) so
  -- binop elab can emit `Term.const "nat_eq"` calls that resolve
  -- at whnf-time.  `GlobalEnv.empty` stays available for callers
  -- that want a raw env (e.g. single-decl tests that don't use
  -- comparison operators).
  let mut globalEnv : GlobalEnv := FX.Derived.PreludeFn.emptyWithPrelude
  let mut perDeclResults : Array (Except ElabError ElabDecl) := #[]
  -- B13: flatten `impl TypeName { … }` blocks into renamed fn
  -- decls before the main elab loop so every member carries
  -- its qualified name `TypeName.methodName` end-to-end.
  for decl in flattenImplDecls file.decls do
    match elabDeclE globalEnv decl with
    | .ok elaboratedDecl =>
      globalEnv := globalEnv.addDecl elaboratedDecl.name elaboratedDecl.type
                          elaboratedDecl.body
                          (transparent := elaboratedDecl.transparent)
      perDeclResults := perDeclResults.push (.ok elaboratedDecl)
    | .error elabErr =>
      perDeclResults := perDeclResults.push (.error elabErr)
  return perDeclResults

/-! ## Check — run the kernel on an elaborated decl -/

/-- The combined result of elab + type-check of a decl. -/
inductive DeclResult where
  | okDecl   (elaboratedDecl : ElabDecl)                             : DeclResult
  | elabFail (elabError : ElabError)                                 : DeclResult
  | typeFail (elaboratedDecl : ElabDecl) (typeError : TypeError)     : DeclResult
  deriving Repr

/-- Elaborate a declaration, then run the kernel checker on it.
    `check context body type` against the empty context — declarations
    elaborate to closed kernel terms.  `globalEnv` provides prior decls
    for inline-by-name resolution at the `var` case. -/
def elabAndCheckE (globalEnv : GlobalEnv) (decl : Decl) : DeclResult :=
  match elabDeclE globalEnv decl with
  | .error elabErr => .elabFail elabErr
  | .ok elaboratedDecl =>
    -- First ensure the type itself is a well-formed type.
    match Term.inferType (TypingContext.empty) elaboratedDecl.type globalEnv with
    | .error typeErr => .typeFail elaboratedDecl typeErr
    | .ok _ =>
      match Term.check (TypingContext.empty) elaboratedDecl.body elaboratedDecl.type globalEnv with
      | .error typeErr => .typeFail elaboratedDecl typeErr
      | .ok _ => .okDecl elaboratedDecl

/-- Zero-globalEnv entry point for the single-decl case. -/
def elabAndCheck (decl : Decl) : DeclResult :=
  elabAndCheckE GlobalEnv.empty decl

/-- Two-pass driver for a whole file.

    **Pass 1** — signature elab.  For every `fn` decl, elaborate
    just the declared type (the Pi chain over its parameters).
    Register `(name, type, placeholder_body)` in `globalEnv`.
    Placeholder bodies are `Term.type .zero` — any well-typed term
    works because pass 2 overwrites them before the kernel
    evaluates.

    **Pass 2** — body elab + kernel check.  Every decl's body is
    elaborated with the full pass-1 `globalEnv` visible; forward
    and self references resolve to `Term.const`.  The kernel
    checker runs against the declared type using the same env.
    On success, the real body replaces the placeholder.

    ## Invariant

    After `checkFile file` returns:

      * For every decl that appears in `file.decls` and
        successfully elaborated its signature: the decl's
        **declared type** is in `globalEnv` (pass-1 write).
      * For every decl that ALSO successfully elaborated its body
        AND passed kernel check: the decl's **real body**
        replaces the pass-1 placeholder in `globalEnv`
        (pass-2 write).
      * For every decl whose signature failed: NO entry exists
        in `globalEnv`, and the return array records `.elabFail`
        at that index.  Subsequent decls' bodies referencing
        that name emit `Term.const` at elab time but fail kernel
        check with T120 (unknown global).

    This two-pass structure is what unlocks self-recursion without
    adding a kernel-level fixpoint: `Term.const`'s resolution at
    eval time (via `GlobalEnv.lookupBody?`) lets a decl refer to
    its own body after pass 2 has populated it.  Forward
    references (decl B mentions A, declared later) work the same
    way because pass 1 registers all signatures before any body
    elab starts.

    **F2 split.**  The body lives in `checkFileCore`, which
    takes an explicit `initialGlobals`.  Two thin wrappers at
    the bottom of this file delegate: `checkFile` starts from
    empty (the Phase-2 default for `fxi check`/`run`); the REPL
    calls `checkFileWithGlobals` to preserve cross-line state. -/
partial def checkFileCore (file : File) (initialGlobals : GlobalEnv)
    : Array DeclResult := Id.run do
  -- B13: flatten impl blocks BEFORE the two-pass walk so the
  -- pre-registration in pass 1 sees the renamed `TypeName.
  -- methodName` fns.  `flattenImplDecls` is idempotent on
  -- non-impl decls and preserves source order for everything
  -- else.
  let flattenedDecls := flattenImplDecls file.decls
  -- Q59 pre-pass: register EVERY typeDecl / sessionDecl before
  -- any fn/const/val signature elaborates.  Without this, a
  -- `fn foo(x: MyType)` that textually precedes `type MyType
  -- ... end type;` fails E001 because `MyType` isn't yet in
  -- `globalEnv.userSpecs` during the main pass-1 loop.  Fns
  -- can forward-reference each other through the shared
  -- `Term.const` knot + two-pass checkFile invariant, but type
  -- lookup requires the spec to be registered before the
  -- signature that uses it elaborates.  The pre-pass lifts that
  -- constraint: after it runs, every user-declared type and
  -- session spec is available to every subsequent signature
  -- regardless of textual order.
  --
  -- Errors from the pre-pass are stashed in `typeDeclErrors`
  -- indexed by original declaration position.  The main pass-1
  -- loop replays them into `pass1Errors` at the corresponding
  -- slot so downstream diagnostics stay stable against decl
  -- order.
  let mut globalEnv : GlobalEnv := initialGlobals
  let mut typeDeclErrors : Array (Option ElabError) :=
    Array.replicate flattenedDecls.size none
  for (decl, declIndex) in flattenedDecls.zipIdx do
    match decl with
    | .typeDecl attrs declName typeParams ctors span =>
      match elabTypeDeclSpec globalEnv attrs declName typeParams ctors span with
      | .ok fullSpec =>
        globalEnv := globalEnv.addUserSpec fullSpec
      | .error sigErr =>
        typeDeclErrors := typeDeclErrors.set! declIndex (some sigErr)
    | .sessionDecl declName typeParams recBinder steps span =>
      match elabSessionDeclSpec globalEnv declName typeParams recBinder steps span with
      | .ok specsList =>
        globalEnv := globalEnv.addUserCoindSpecs specsList
      | .error sigErr =>
        typeDeclErrors := typeDeclErrors.set! declIndex (some sigErr)
    | _ => pure ()
  -- Pass 1: elab signatures and pre-register them.  Non-fn decls
  -- are passed through unchanged; their type isn't used for
  -- forward references in the same way, and elabDeclE already
  -- rejects them cleanly in pass 2.  Pass-1 elab errors are
  -- recorded so pass 2 can report them without re-running sig
  -- elab.  Type/session decls re-enter the loop but consult the
  -- pre-pass result instead of re-registering — re-registration
  -- would either be redundant (on success) or surface the same
  -- T121 / T120 twice (on failure).
  let mut pass1Errors : Array (Option ElabError) := #[]
  for (decl, declIndex) in flattenedDecls.zipIdx do
    match decl with
    | .fnDecl _attrs _vis declName params retType effects _specs _body _span =>
      -- Pass 1 Pi is built with the declared effect row so that
      -- higher-order references (e.g., another fn passing this
      -- one as an arg) see the correct Pi-effect annotation
      -- during pass-2 body elab.  Without this, the kernel Pi
      -- would be `→{Tot}` and E-2's Pi-layer peeling would miss
      -- the effect contribution at App sites.
      let kernelEffect := effectsFromSurface effects
      match elabFnType globalEnv params retType kernelEffect with
      | .ok declType =>
        let paramNames := params.toList.map fun param =>
          match param with
          | .mk _mode paramName _typeExpr _span => paramName
        -- A12: extract effect-label strings from the parsed `with`
        -- row on the first-class `effects` field of fnDecl.  Each
        -- entry is a surface `Expr`; we accept `.var qi` shapes
        -- (bare identifiers like `IO`, `Alloc`, `eff`) and take
        -- `qi.final` as the label name.  Non-var shapes (future
        -- `eff(T)` parameterized effects per §9.5) silently drop
        -- here until the full effect-decl flow lands.
        let effectNames : List String := effects.toList.filterMap fun effectExpr =>
          match effectExpr with
          | .var qi => some qi.final
          | _       => none
        globalEnv := globalEnv.addDecl declName declType
                       (Term.type .zero) (transparent := false)
                       (paramNames := paramNames)
                       (effects := effectNames)
        pass1Errors := pass1Errors.push none
      | .error sigErr =>
        pass1Errors := pass1Errors.push (some sigErr)
    | .constDecl declName typeExpr _valueExpr _span =>
      -- Const sig: just the declared type.  Registering it in
      -- pass 1 enables forward references (decl A uses const B
      -- declared later).  The placeholder body is irrelevant —
      -- pass 2 overwrites both type and body with the fully-
      -- elaborated entry.  `paramNames` stays empty (const is
      -- nullary; no named-arg routing applies at call sites).
      match elabExpr globalEnv Scope.empty none typeExpr with
      | .ok typeTerm =>
        globalEnv := globalEnv.addDecl declName typeTerm
                       (Term.type .zero) (transparent := false)
        pass1Errors := pass1Errors.push none
      | .error sigErr =>
        pass1Errors := pass1Errors.push (some sigErr)
    | .valDecl declName typeExpr _span =>
      -- Val: forward declaration with type but no body.  Pre-
      -- register with placeholder `Term.const declName` body so
      -- callers that reference the name during pass 2 resolve
      -- against the declared type.  Trust level `Trust.external`
      -- propagates the "not-yet-implemented" status through the
      -- call graph.
      match elabExpr globalEnv Scope.empty none typeExpr with
      | .ok typeTerm =>
        globalEnv := globalEnv.addDecl declName typeTerm
                       (Term.const declName) (transparent := false)
                       (trust := Trust.external)
        pass1Errors := pass1Errors.push none
      | .error sigErr =>
        pass1Errors := pass1Errors.push (some sigErr)
    | .typeDecl _attrs _declName _typeParams _ctors _span =>
      -- Q59: type decl already registered in the pre-pass above.
      -- Replay the pre-pass result (success = none; failure =
      -- stashed T120/T121 ElabError) into pass1Errors to keep the
      -- per-decl diagnostic index aligned with declaration order.
      pass1Errors := pass1Errors.push typeDeclErrors[declIndex]!
    | .sessionDecl _declName _typeParams _recBinder _steps _span =>
      -- Q59: same as typeDecl — pre-pass handled registration.
      pass1Errors := pass1Errors.push typeDeclErrors[declIndex]!
    | _ =>
      -- Non-fn/const/type/session decls don't participate in
      -- sig-forwarding; let pass 2 produce its own error.
      pass1Errors := pass1Errors.push none
  -- Pass 2: full elab + kernel check with all signatures visible.
  -- On success, replace the placeholder body in `globalEnv` with
  -- the real body so subsequent decls that reference this one see
  -- the right unfolding at eval time.
  let mut perDeclResults : Array DeclResult := #[]
  for declIndex in [0:flattenedDecls.size] do
    let decl := flattenedDecls[declIndex]!
    match pass1Errors[declIndex]! with
    | some sigErr =>
      perDeclResults := perDeclResults.push (.elabFail sigErr)
    | none =>
      let declResult := elabAndCheckE globalEnv decl
      match declResult with
      | .okDecl elaboratedDecl =>
        -- Pass 2 re-adds with the real body.  Preserve `paramNames`
        -- and `effects` from pass 1's entry (they were registered
        -- when the signature elabed successfully).
        let declName := elaboratedDecl.name
        let paramNames := (globalEnv.lookupParamNames? declName).getD []
        let declaredEffects := (globalEnv.lookupEffects? declName).getD []
        -- A12 effect subsumption via E-2 tree-recursive inference
        -- per Appendix B.  `EffectInference.inferDeclBodyEffect`
        -- peels the lambda chain (one per surface param) to enter
        -- the body under a typing context, then walks each node
        -- composing effects via `Effect.add`:
        --
        --   * App chains fire each Pi-layer's return-effect from
        --     E-1's kernel Pi-effect field;
        --   * ctor / indRec / refl / idJ / quotMk / quotLift
        --     are pure eliminators (their effect is the union of
        --     children's effects only);
        --   * lambdas / types are pure constructions (Tot).
        --
        -- This replaces A12's `constRefs` walk — which treated any
        -- reference as a call and couldn't distinguish data from
        -- function heads.  The new inference uses the kernel Pi's
        -- return-effect field, so higher-order code gets the
        -- right answer.
        --
        -- Built-in effects check via `Effect.LessEq` (with `Read ≤
        -- Write` through `write_` saturation per §9.3).  Unknown
        -- labels (user-defined §9.5 effects — parsed but not yet
        -- given a kernel row) take the per-name subset path via
        -- the `declaredUnknown` list.
        -- Zero-arg fns carry one synthetic Unit binder injected at
        -- elab time (§31.7 kernel translation), so the elaborated
        -- body has one more outer lambda than the surface param
        -- count indicates.  Lift the peel depth by 1 when the
        -- surface list was empty so `inferDeclBodyEffect` reaches
        -- the real innermost expression.
        let paramCount :=
          if paramNames.isEmpty then 1 else paramNames.length
        let bodyBuiltin :=
          EffectInference.inferDeclBodyEffect globalEnv paramCount
            elaboratedDecl.body
        -- Unknown-effect fallback: per-name string subset.  Until
        -- E-4 wires user-effect decls, non-built-in labels
        -- (`State`, `Crypto`, …) flow through `Term.const`
        -- references without Pi knowledge, so `constRefs` still
        -- serves as the approximate source of "what user effects
        -- the body transitively touches."
        let bodyConstRefs := elaboratedDecl.body.constRefs
        let bodyUnknownFromRefs : List String := bodyConstRefs.foldl
          (init := ([] : List String)) fun acc refName =>
            match globalEnv.lookupEffects? refName with
            | some calleeEffects =>
              calleeEffects.foldl (init := acc) fun accInner effectName =>
                if accInner.contains effectName then accInner
                else effectName :: accInner
            | none         => acc
        let (_, bodyUnknown) := Effect.fromNames bodyUnknownFromRefs
        let (declaredBuiltin, declaredUnknown) := Effect.fromNames declaredEffects
        let builtinSubsumes : Bool := Effect.subsumes bodyBuiltin declaredBuiltin
        let unknownWidening : List String :=
          bodyUnknown.filter (fun effectName => !declaredUnknown.contains effectName)
        if builtinSubsumes && unknownWidening.isEmpty then
          globalEnv := globalEnv.addDecl declName
                         elaboratedDecl.type elaboratedDecl.body
                         (transparent := elaboratedDecl.transparent)
                         (paramNames := paramNames)
                         (effects := declaredEffects)
          perDeclResults := perDeclResults.push declResult
        else
          let declSpan : Span := match decl with
            | .fnDecl _ _ _ _ _ _ _ _ sp => sp
            | .constDecl _ _ _ sp      => sp
            | .valDecl _ _ sp          => sp
            | .typeDecl _ _ _ _ sp     => sp
            | _                        => Span.zero
          let builtinWidening : List String :=
            Effect.wideningNames bodyBuiltin declaredBuiltin
          let allWidening : List String := builtinWidening ++ unknownWidening
          let wideningJoin := allWidening.foldr (init := "") fun effectName acc =>
            if acc.isEmpty then effectName else s!"{effectName}, {acc}"
          let declaredJoin := declaredEffects.foldr (init := "") fun effectName acc =>
            if acc.isEmpty then effectName else s!"{effectName}, {acc}"
          let err := ElabError.make "E044"
            s!"{declName}: body performs effects not in declared row — callee-transitive effects include [{wideningJoin}], declared row is [{declaredJoin}]"
            declSpan
          -- Still register the body (for downstream refs to resolve)
          -- but report the elab failure via perDeclResults.
          globalEnv := globalEnv.addDecl declName
                         elaboratedDecl.type elaboratedDecl.body
                         (transparent := elaboratedDecl.transparent)
                         (paramNames := paramNames)
                         (effects := declaredEffects)
          perDeclResults := perDeclResults.push (.elabFail err)
      | _ =>
        perDeclResults := perDeclResults.push declResult
  return perDeclResults

/-- `checkFile` with an explicit initial environment.  Used by
    `fxi repl` (F2) to preserve cross-line state — each REPL
    line is a mini-`File` checked against the accumulated env.
    Non-REPL callers use the plain `checkFile` which starts
    from empty. -/
def checkFileWithGlobals (file : File) (initialGlobals : GlobalEnv)
    : Array DeclResult :=
  checkFileCore file initialGlobals

/-- Compatibility wrapper: the original `checkFile` entry that
    starts from a prelude-seeded env.  Used by `fxi check` /
    `fxi run` / `fxi dump` for single-file invocations.  Q68:
    seeds `nat_eq` and other kernel-level prelude fns via
    `FX.Derived.PreludeFn.emptyWithPrelude` so comparison
    operators (`==`, `!=`) reduce at whnf-time to concrete
    Bool values. -/
def checkFile (file : File) : Array DeclResult :=
  checkFileWithGlobals file FX.Derived.PreludeFn.emptyWithPrelude

end FX.Elab
