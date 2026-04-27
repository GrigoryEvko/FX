import FX.Eval.Env
import FX.Kernel.Inductive

/-!
# Big-step evaluator

Per `fx_design.md` §31 (kernel calculus reductions) and §22
(sketch mode VM design intent).  The evaluator takes a `Term` and
an `EvalEnv` and returns a `Value` — the normal form of the term
under the environment.

## Reduction strategy

Big-step, call-by-value evaluation matching the kernel's beta, iota,
and delta (global unfold) rules:

  * **beta** (`app (lam _ _ body) arg`) — evaluate `arg` to a value
    `v`, push it on the evalEnv, evaluate `body` under the extended
    evalEnv.  When the function position evaluates to a `Value.closure`,
    we enter the closure's captured evalEnv before extending.  When
    it evaluates to anything else (a `ctor`, a `neutral`, etc.),
    we produce a `Value.neutral` or extend the ctor's argument
    list respectively.
  * **iota** (`indRec name P methods (ctor name k _ args)`) — look up
    the spec, select `methods[k]`, apply to `args` plus recursive
    results for self-referential arg positions.  Uses `Inductive.
    specByName?` to decide which args are recursive.
  * **delta** (unfolding a transparent global) — not automatic at this
    layer; the elaborator already inlines global refs at
    elaboration time (task A11's approach).  The evaluator only
    sees closed Terms.

## Values that aren't canonical

When the evaluator encounters:

  * A free `var i` beyond the local stack: produces
    `Value.neutral i []` — stuck.  Subsequent `app` on this
    produces `Value.neutral i [args]` (extends the spine).
  * An indRec whose target evaluates to a neutral (not a ctor):
    produces `Value.neutralRec ...` — stuck until the scrutinee
    reduces further.

## Partial def / fuel

`eval` is `partial def` because the kernel's beta and iota reductions
are not guaranteed to terminate in general (Phase 2.2 ships no
termination check — §10.6 with Div).  Fuel-bounded variants for
safety at I/O boundaries land with the CLI (F1).
-/

namespace FX.Eval

open FX.Kernel

/- The evaluator.  Reduces `t` to a `Value` under `evalEnv`.

   * `var i`: lookup `evalEnv.locals[i]?`.  Hit → bound value.  Miss
     → `neutral i []` (stuck free var).
   * `const n`: lookup `evalEnv.globals.lookupBody? n`.  Hit → eval
     body with EMPTY locals (bodies are closed at their
     declaration scope).  Miss → `neutral 0 []` (defensive).
   * `type u`: `universe u`.
   * `pi` / `sigma`: Pi/Sigma-type value with captured evalEnv.
   * `lam`: closure with captured evalEnv.
   * `app f a`: eval both, then `applyValue` (threading globals).
   * `ind` / `ctor`: eval args, wrap in corresponding value.
   * `indRec`: eval everything, dispatch via `iotaValue` (threading globals).
   * `id` / `quot`: eval all, wrap as type-former value.
   * `coind _`: stuck (A2 deferred).

## globalEnv threading — design note

`applyValue` / `iotaValue` / `buildIotaSpine` / `applyAll` take
`globalEnv` as their FIRST positional argument.  This is not an
artifact of how closures are constructed — `Value.closure`
stores only `captured : List Value` (locals).  Globals are
supplied from the evaluation CONTEXT, not captured at closure
creation.

Rationale: globals are module-wide, not lexically captured.
When a closure is applied from a different evaluation site, it
sees the CALLER'S globals, not the globals at the time the
closure was created.  For single-file `fxi run` this distinction
is invisible (one module, one globalEnv).  But it matters for:

  * Recursive functions — `double`'s body refers to `const
    "double"`, which resolves against globalEnv at every
    recursive call.  If closures captured globals at creation,
    pass-1 placeholder bodies would leak into later evaluations.
  * Future module system — closures returned across module
    boundaries see the consuming module's environment.

Never hard-code globalEnv inside a Value.  If you need to
preserve a specific env, pass it explicitly through the mutual
block. -/

mutual

partial def eval (evalEnv : EvalEnv) : Term → Value
  | .var deBruijnIndex =>
    match evalEnv.lookupLocal? deBruijnIndex with
    | some boundValue => boundValue
    | none            => .neutral deBruijnIndex []
  | .const declName =>
    -- Global reference.  Look up in the globals env; if found,
    -- evaluate the body with EMPTY locals (bodies are closed at
    -- their declaration scope — they don't capture the caller's
    -- locals).  Missing global → stuck (shouldn't happen on
    -- elaborator-produced terms; reported as a neutral head).
    --
    -- Invariant enforced by the elaborator's two-pass checkFile:
    -- every body we see here has no free `var i` escaping its
    -- own binders.  If the invariant is violated (hand-built
    -- term, elaborator bug), the `.var` case further up returns
    -- `neutral i []` rather than silently capturing an
    -- empty-locals position.  Degradation is visible, not silent.
    match evalEnv.globals.lookupBody? declName with
    | some body => eval { evalEnv with locals := [] } body
    | none      => .neutral 0 []
  | .type universeLevel => .universe universeLevel
  | .forallLevel bodyTerm =>
    -- A10 U-poly: level binders are erased at runtime, so the
    -- value representation carries only the body term and the
    -- current local environment.  Analogous to `piType` /
    -- `sigmaType` at the type-constructor level.
    .forallLevelType bodyTerm evalEnv.locals
  | .pi    _grade domain codomain _returnEffect => .piType domain codomain evalEnv.locals
  | .sigma _grade domain codomain => .sigmaType domain codomain evalEnv.locals
  | .lam   _grade paramType body  => .closure   paramType body evalEnv.locals
  | .app funcTerm argTerm =>
    let funcValue := eval evalEnv funcTerm
    let argValue  := eval evalEnv argTerm
    applyValue evalEnv.globals funcValue argValue
  | .ind typeName typeArgs =>
    .indType typeName (evalList evalEnv typeArgs)
  | .ctor typeName ctorIndex typeArgs valueArgs =>
    .ctor typeName ctorIndex (evalList evalEnv typeArgs) (evalList evalEnv valueArgs)
  | .indRec typeName motive methods target =>
    -- Lazy method dispatch — eval target first, then evaluate
    -- only the method that matches the target's ctor index.
    -- This is critical for `if`/`match`-desugared indRecs where
    -- a non-selected branch contains a recursive self-reference
    -- (eagerly evaluating both branches would infinite-loop
    -- before the target's ctor tag is consulted).  See Q74's
    -- bug report — `gcd` with `if b == 0; a else gcd(...)` was
    -- hanging because the else-arm evaluated the recursive
    -- call before the if-guard fired.
    --
    -- For nullary / non-recursive ctors (all Bool ctors, leaf
    -- Nat Zero), we don't need the other methods at all.  For
    -- recursive-typed ctor args (Nat.Succ payload), we still
    -- eager-eval the full methods list so the sub-iota's
    -- `buildIotaSpine` can re-issue the eliminator — but those
    -- method bodies are lambdas (closures with no immediate
    -- recursion), so eager eval doesn't loop.
    let motiveValue := eval evalEnv motive
    let targetValue := eval evalEnv target
    match targetValue with
    | .ctor ctorTypeName ctorIndex _ ctorValueArgs =>
      if ctorTypeName != typeName then
        -- Type mismatch: defensive neutral (ill-typed input
        -- shouldn't happen on elaborator-emitted Terms).
        let methodsValue := evalList evalEnv methods
        .neutralRec typeName motiveValue methodsValue targetValue
      else
        match methods[ctorIndex]?,
              Inductive.specByName? typeName evalEnv.globals.userSpecs with
        | some methodTerm, some spec =>
          match spec.ctorAt? ctorIndex with
          | some ctorSpec =>
            let methodValue := eval evalEnv methodTerm
            -- Check whether this ctor carries a recursive-typed
            -- arg.  If yes, we need the full methods list for
            -- the self-recursion inside buildIotaSpine.  If no,
            -- we can skip eager-eval of the rest — this is the
            -- fix for the Bool-if-recursion trap.
            let hasRecursiveArg : Bool :=
              ctorSpec.args.any fun argType =>
                match argType with
                | .ind argSpecName _ => argSpecName == typeName
                | _                  => false
            let methodsValue : List Value :=
              if hasRecursiveArg then evalList evalEnv methods else []
            let flattenedSpine :=
              buildIotaSpine evalEnv.globals typeName motiveValue
                methodsValue ctorSpec.args ctorValueArgs
            applyAll evalEnv.globals methodValue flattenedSpine
          | none =>
            let methodsValue := evalList evalEnv methods
            .neutralRec typeName motiveValue methodsValue targetValue
        | _, _ =>
          let methodsValue := evalList evalEnv methods
          .neutralRec typeName motiveValue methodsValue targetValue
    | _ =>
      -- Stuck target (neutral / non-ctor): eval methods so the
      -- stuck form carries readable pretty output.
      let methodsValue := evalList evalEnv methods
      .neutralRec typeName motiveValue methodsValue targetValue
  | .id typeTerm leftTerm rightTerm =>
    .idType (eval evalEnv typeTerm) (eval evalEnv leftTerm) (eval evalEnv rightTerm)
  | .refl witnessTerm =>
    -- Id-intro: produce a refl value carrying the evaluated witness.
    .reflVal (eval evalEnv witnessTerm)
  | .idJ motiveTerm baseTerm eqProofTerm =>
    -- Id-elim: delegate to `idJValue`, which discharges to
    -- `applyValue base witness` when eq is a reflVal, else
    -- produces `neutralIdJ`.
    let motiveValue  := eval evalEnv motiveTerm
    let baseValue    := eval evalEnv baseTerm
    let eqProofValue := eval evalEnv eqProofTerm
    idJValue evalEnv.globals motiveValue baseValue eqProofValue
  | .quot typeTerm relationTerm =>
    .quotType (eval evalEnv typeTerm) (eval evalEnv relationTerm)
  | .quotMk relationTerm witnessTerm =>
    -- Quot-intro: wrap the evaluated (relation, witness) pair.
    .quotMkVal (eval evalEnv relationTerm) (eval evalEnv witnessTerm)
  | .quotLift liftedTerm respectsTerm targetTerm =>
    -- Quot-elim: delegate to `quotLiftValue`, which discharges
    -- to `applyValue lifted witness` when target is a
    -- `quotMkVal`, else produces `neutralQuotLift`.
    let liftedValue   := eval evalEnv liftedTerm
    let respectsValue := eval evalEnv respectsTerm
    let targetValue   := eval evalEnv targetTerm
    quotLiftValue evalEnv.globals liftedValue respectsValue targetValue
  | .coind _coindName _coindArgs => Value.placeholder
  | .coindUnfold _typeName _typeArgs _arms =>
    -- Value-level coinductive semantics live in S15/S16
    -- (Value.channel + queue + send/receive evaluation).
    -- Until then, evaluating an unfold produces a placeholder
    -- — runtime observation of codata via `.coindDestruct`
    -- below is similarly deferred.  The A5 kernel-level
    -- ν-reduction is still effective: on well-typed surface
    -- terms, destructor-of-unfold reduces before evaluation
    -- ever reaches an unfold-shaped value.  The placeholder
    -- is the defensive fallback for hand-built ill-typed
    -- input or future surface forms that skip β/ι/ν
    -- reduction.
    Value.placeholder
  | .coindDestruct _typeName _destructorIndex _target =>
    Value.placeholder

partial def evalList (evalEnv : EvalEnv) : List Term → List Value
  | []                    => []
  | headTerm :: restTerms => eval evalEnv headTerm :: evalList evalEnv restTerms

/-- Apply a function value to an argument value.  Three cases:

      * `closure pT body captured` — enter captured evalEnv, push arg,
        evaluate body.  Global refs inside the body resolve through
        the supplied `globalEnv` (closure values don't save globals
        themselves — they're module-wide, not captured).
      * `neutral head spine` — extend the spine.
      * anything else — produce a neutral from the caller's scope
        (shouldn't happen on well-typed input; defensive). -/
partial def applyValue (globalEnv : GlobalEnv) : Value → Value → Value
  | .closure _paramType body captured, argValue =>
    let innerEnv : EvalEnv := { locals := argValue :: captured, globals := globalEnv }
    eval innerEnv body
  | .neutral headIndex spine, argValue =>
    .neutral headIndex (spine ++ [argValue])
  | .neutralRec specName motiveValue methodsValue stuckTarget, argValue =>
    -- A stuck elim applied further: fold as an extended neutral
    -- on the eliminator's result-spine via a special shape.  For
    -- Phase 2.2 we collapse to a plain neutral; pretty-printer
    -- handles the display.
    .neutralRec specName motiveValue methodsValue
                (applyValue globalEnv stuckTarget argValue)
  | unexpectedHead, argValue =>
    -- Not typically reachable on well-typed closed input.  Treat
    -- as neutral head 0 so downstream code keeps working.
    .neutral 0 [unexpectedHead, argValue]

/-- iota-reduce an eliminator application.  When `target` is a `ctor
    name k _ args`, look up the spec's ctor by index, pick the
    matching method, and fold-apply it to `args` plus a recursive
    `indRec` call on each self-referential argument.  Otherwise
    produce `neutralRec`.  Mirrors `Reduction.iotaStep?` but at the
    Value layer.  `globalEnv` threads through so any `const` refs
    inside the method's body resolve correctly. -/
partial def iotaValue (globalEnv : GlobalEnv) (specName : String) (motive : Value)
    (methods : List Value) (target : Value) : Value :=
  match target with
  | .ctor ctorTypeName ctorIndex _ctorTypeArgs ctorValueArgs =>
    if ctorTypeName != specName then
      .neutralRec specName motive methods target
    else
      match Inductive.specByName? specName globalEnv.userSpecs with
      | none => .neutralRec specName motive methods target
      | some spec =>
        match spec.ctorAt? ctorIndex, methods[ctorIndex]? with
        | some ctorSpec, some method =>
          -- For each ctorValueArgs / ctorSpec.args pair, emit the arg and,
          -- if arg type is `ind specName _`, also emit the
          -- recursive iotaValue on that arg.
          let flattenedSpine :=
            buildIotaSpine globalEnv specName motive methods ctorSpec.args ctorValueArgs
          applyAll globalEnv method flattenedSpine
        | _, _ => .neutralRec specName motive methods target
  | _ => .neutralRec specName motive methods target

/-- Build the method's argument list per the iota rule: each
    non-recursive arg contributes itself; each recursive arg
    contributes itself AND the recursive eliminator call. -/
partial def buildIotaSpine (globalEnv : GlobalEnv) (specName : String) (motive : Value)
    (methods : List Value) : List Term → List Value → List Value
  | [], _ => []
  | _, [] => []
  | argType :: remainingTypes, argValue :: remainingValues =>
    let restOfSpine :=
      buildIotaSpine globalEnv specName motive methods remainingTypes remainingValues
    match argType with
    | .ind indName _ =>
      if indName == specName then
        argValue :: iotaValue globalEnv specName motive methods argValue :: restOfSpine
      else
        argValue :: restOfSpine
    | _ => argValue :: restOfSpine

/-- Reduce a head value against a spine of argument values,
    left-to-right, by repeated `applyValue`.  Each step performs
    beta reduction (into a closure body), extends a neutral spine,
    or defers an iota (on `neutralRec`).  NOT the same as
    `FX.Kernel.Reduction.appChain` — that one builds a syntactic
    `Term.app` chain without reducing anything; this one evaluates. -/
partial def applyAll (globalEnv : GlobalEnv) : Value → List Value → Value
  | headValue, []                        => headValue
  | headValue, nextArg :: remainingArgs  =>
    applyAll globalEnv (applyValue globalEnv headValue nextArg) remainingArgs

/-- iota-reduce a J eliminator at the Value layer (A3, H.6).
    When `eq` is a `reflVal witness`, `base` is applied to the
    witness via `applyValue`; otherwise a `neutralIdJ` preserves
    the shape for later.  Mirrors `Reduction.idJStep?` but
    operates on values instead of terms.  The motive is threaded
    only for the stuck form's pretty output — reduction never
    consults it. -/
partial def idJValue (globalEnv : GlobalEnv) (motive : Value)
    (base : Value) (eq : Value) : Value :=
  match eq with
  | .reflVal witness => applyValue globalEnv base witness
  | _                => .neutralIdJ motive base eq

/-- iota-reduce a Quot.lift at the Value layer (A4, H.7).
    When `target` is a `quotMkVal _ witness`, `lifted` is
    applied to the witness via `applyValue`; otherwise a
    `neutralQuotLift` preserves the shape.  Mirrors
    `Reduction.quotLiftStep?` on values.  The `respects` proof
    and the stored relation are threaded only for the stuck
    form's pretty output — reduction discards both. -/
partial def quotLiftValue (globalEnv : GlobalEnv) (lifted : Value)
    (respects : Value) (target : Value) : Value :=
  match target with
  | .quotMkVal _relation witness => applyValue globalEnv lifted witness
  | _                            => .neutralQuotLift lifted respects target

end

/-- Evaluate a top-level decl's body under the globals from `evalEnv`.
    Wrapper sharing the empty-locals entry point for M1 use. -/
def evalClosed (evalEnv : EvalEnv) (term : Term) : Value :=
  eval { evalEnv with locals := [] } term

/-- Evaluate the "invocation value" of a top-level decl: for a
    zero-arg fn (type `Π (_ :_ghost Unit) → T @ eff`, per the
    §31.7 uniform translation), apply `Unit.tt` to fire the
    effect and unwrap to the inner `T`; for anything else,
    evaluate the body as-is.  Detecting the zero-arg shape by
    the type's outer Pi with Unit domain + ghost grade — the
    exact shape `elabFnSignature` produces when the surface
    parameter list is empty.  This lets `fxi run` and test
    helpers that present a decl's "value" behave consistently
    whether the decl is a zero-arg fn or a genuine value. -/
def evalDecl (evalEnv : EvalEnv) (bodyTerm : Term)
    (declaredType : Term) : Value :=
  match declaredType with
  | .pi _grade (.ind "Unit" _) _returnType _effect =>
    -- Zero-arg fn: body is `λ (_ :_ghost Unit). inner`.
    -- Apply `Unit.tt` via an extra app layer; the β-reduction
    -- in `eval` strips the lambda and returns the inner value.
    evalClosed evalEnv (Term.app bodyTerm (.ctor "Unit" 0 [] []))
  | _ => evalClosed evalEnv bodyTerm

end FX.Eval
