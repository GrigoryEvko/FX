import FX.Kernel.Substitution
import FX.Kernel.Inductive
import FX.Kernel.Env

/-!
# Reduction

Per `fx_design.md` §31 (kernel normalization) and Appendix H
beta/eta/iota/nu reduction rules.

All five reduction kinds surface in `whnf` / `normalize`:
beta (H.2), iota-Ind (H.4), iota-Id (H.6), iota-Quot (H.7),
nu-Coind (H.5), and delta on `Term.const` (§10.15 opacity
discipline).  eta lives in `Conversion.lean` as a convertibility
rule, not as a reduction step.  Sigma-intro / Sigma-elim are
not surfaced at Phase-2 (no Sigma pair value constructor yet).

## Phase 2.2 scope (after task A1/A5)

  * **beta-reduction** — `app (lam _ _ body) a ⟶ openWith a body`.
  * **iota-reduction on inductives (H.4)** — `indRec name P methods
    (ctor name k _typeArgs args) ⟶ methods[k]` applied (with
    recursive results inserted for self-referential arg
    positions).  The self-reference check consults
    `Inductive.specByName?` to read the ctor's arg type telescope.
  * **eta-reduction** — still a conversion equivalence, not a
    reduction step.  Handled in `Conversion.lean`.
  * **J-of-refl iota (A3, H.6)** — `idJ motive base (refl witness)`
    reduces to `app base witness`.  The motive is discarded at
    reduction time — it was consumed by typing, not needed for
    evaluation.
  * **Quot-lift iota (A4, H.7)** — `quotLift lifted respects
    (quotMk relation witness)` reduces to `app lifted witness`.
    The respects-proof and stored relation are both discarded at
    reduction time — they are purely typing obligations.
  * **nu-reduction on coinductives (H.5)** — `coindDestruct name i
    (coindUnfold name _typeArgs arms) ⟶ arms[i]`.  Dual of
    `iotaStep?` for inductives: a single-destructor observation
    on an `unfold` value fires the matching arm.  No motive (a
    single observation has no branching structure to discriminate
    through); the `typeArgs` are discarded on the reduct (they
    were consumed by typing, not reduction).  `nuStep?` is the
    helper; `whnf` / `normalize` dispatch through it.
  * **delta-reduction on `Term.const`** — `whnf`/`normalize` take
    an optional `globalEnv`; a `const name` whose entry is
    registered `transparent := true` unfolds to its body via
    `GlobalEnv.unfold?`.  Opaque entries (the default per §10.15)
    stay as `const`.  Callers without a `globalEnv` get the old
    opaque-everywhere behavior by omitting the parameter — it
    defaults to the empty env, where `unfold?` is `none` for
    every name.  Eval-time unfolding is separate: `FX/Eval/
    Interp.lean` unconditionally looks up every const body
    regardless of transparency, matching FX's execution
    semantics (opacity is an SMT/conversion discipline, not a
    runtime policy).

## Totality

Reduction is not guaranteed to terminate (`Div` effect opts out).
`whnf`/`normalize` are fuel-bounded: they take a `fuel : Nat`
budget and return the best reduct within that budget.  Exceeded
fuel returns the current term; the typing layer reports `R_fuel`
at inspection boundaries.

Default fuel: 4096 steps.
-/

namespace FX.Kernel

namespace Term

/-! ## Iota reduction helper -/

/-- Given the constructor's arg-type telescope (from `IndCtor.args`)
    and the actual runtime arg values, produce the flat list to
    feed the matching method: each non-recursive arg contributes
    itself; each recursive arg (type `ind specName _`) contributes
    both itself AND the recursive `indRec` call on it. -/
def iotaArgs (specName : String) (motive : Term) (methods : List Term)
    (argTypes : List Term) (argValues : List Term) : List Term :=
  let rec loop : List Term → List Term → List Term
    | [], _ => []
    | _, [] => []
    | argType :: remainingTypes, argValue :: remainingValues =>
      let rest := loop remainingTypes remainingValues
      match argType with
      | .ind referencedName _ =>
        if referencedName == specName then
          -- Self-reference: emit value + recursive result.
          argValue :: indRec specName motive methods argValue :: rest
        else
          argValue :: rest
      | _ => argValue :: rest
  loop argTypes argValues

/-- Build a left-associated application chain from a head term and
    a list of argument terms: `appChain h [a, b, c] = app (app
    (app h a) b) c`.  Pure syntactic construction — no reduction
    happens, the result is the spelled-out `Term.app` tree.

    The Value-layer analog is `FX.Eval.Interp.applyAll`, which
    reduces a head value against a value spine by repeatedly
    calling `applyValue` (beta + closure invocation + spine
    extension on stuck terms).  The two operations live at
    different conceptual levels — syntactic builder vs reductive
    applicator — and are NOT interchangeable. -/
def appChain : Term → List Term → Term
  | head, []              => head
  | head, argument :: rest => appChain (app head argument) rest

/-- One step of iota reduction: `indRec name motive methods
    (ctor name k typeArgs args)` → `methods[k]` applied to the
    iota-expanded arg list.  Returns `none` when the target is
    not a matching constructor application, when the spec isn't
    registered, or when the ctor index / method count mismatch. -/
def iotaStep? (specName : String) (motive : Term)
    (methods : List Term) (target : Term)
    (userSpecs : List IndSpec := []) : Option Term :=
  match target with
  | Term.ctor ctorTypeName ctorIndex _typeArgs ctorArgs =>
    if ctorTypeName != specName then none
    else
      match Inductive.specByName? specName userSpecs with
      | none => none
      | some spec =>
        match spec.ctorAt? ctorIndex, methods[ctorIndex]? with
        | some ctorSpec, some method =>
          let argList :=
            iotaArgs specName motive methods ctorSpec.args ctorArgs
          some (appChain method argList)
        | _, _ => none
  | _ => none

/-! ## J-of-refl iota (A3, H.6)

When `idJ motive base eqProof` meets an `eqProof` that is literally
`refl witness`, the eliminator discharges to `app base witness`.
Motive is consumed by typing (§31 H.6 Id-J rule) and discarded at
reduction time — reduction doesn't need it to build the result.

The helper signature drops `motive` for the same reason: it is
never referenced on the result path.  Callers that need the
motive for pretty-printing a stuck form (e.g., the `Value`-level
`neutralIdJ` in `FX/Eval/Interp.lean`) carry it through their own
structure. -/

/-- One step of J-reduction.  Returns `some (app base witness)`
    when `eqProof = refl witness`, otherwise `none`. -/
def idJStep? (base : Term) (eqProof : Term) : Option Term :=
  match eqProof with
  | .refl witnessTerm => some (.app base witnessTerm)
  | _                 => none

/-! ## Quot-lift-of-quotMk iota (A4, H.7)

When `quotLift lifted respects target` meets a `target` that is
`quotMk relation witness`, the eliminator discharges to
`app lifted witness`.  The respects-proof and stored relation are
discarded on the result path; they were consumed by typing
(§31 H.7 Quot-lift) and evaluation doesn't need them.

Mirrors `idJStep?` in shape: drop the arguments that don't appear
on the reduct, take only what reduction consumes. -/

/-- One step of Quot-lift reduction.  Returns
    `some (app lifted witness)` when
    `target = quotMk _ witness`, otherwise `none`. -/
def quotLiftStep? (lifted : Term) (target : Term) : Option Term :=
  match target with
  | .quotMk _relation witnessTerm => some (.app lifted witnessTerm)
  | _                             => none

/-! ## ν reduction on coinductives (A5, H.5)

Dual of `iotaStep?` for inductive recursion.  When a destructor
observation `coindDestruct specName i target` meets a `target`
that is literally `coindUnfold specName typeArgs arms`, the
eliminator discharges to `arms[i]`.  The `typeArgs` and the
unfold-side `specName` are verified by typing and discarded at
reduction — reduction doesn't need them to build the result.

Parallel in shape to `iotaStep?`:

  * The name check `unfoldName ≠ destructName` returns `none`
    (stuck — typing should have rejected upstream; if it didn't,
    we leave the term as-is for a later conversion failure to
    pick up).
  * The index bound check `arms[destructorIndex]?` returns
    `none` when the unfold's arm list is shorter than the
    destructor index — again, typing should have caught it,
    but be defensive.

Mirrors the defensive pattern in `iotaStep?` where a matched
constructor that doesn't align with the declared spec (wrong
ctor index, missing spec registration) returns `none` rather
than crashing or looping. -/

/-- One step of ν reduction.  Returns `some (arms[destructorIndex])`
    when `target = coindUnfold specName _ arms` and the index is
    in range; `none` when `target` is not an unfold, the spec
    names disagree, or the index is out of bounds. -/
def nuStep? (specName : String) (destructorIndex : Nat) (target : Term)
    : Option Term :=
  match target with
  | .coindUnfold unfoldName _typeArgs arms =>
    if unfoldName != specName then none
    else arms[destructorIndex]?
  | _ => none

/-! ## One step of reduction at the head -/

/-- Attempt a single reduction step at the head of `t`.

    Matches: beta (`app (lam _ _ body) arg`), iota-Ind
    (`indRec name P methods (ctor name k _ args)`), iota-Id
    (`idJ motive base (refl witness)`), iota-Quot
    (`quotLift lifted respects (quotMk _ witness)`), and
    nu-Coind (`coindDestruct name i (coindUnfold name _ arms)`).
    Every other shape returns `none`.

    Grade and domain annotations on matched binders are
    discarded; the typing layer has already verified them before
    reduction is ever invoked. -/
def betaStep? : Term → Option Term
  | .app (.lam _grade _domain body) argument => some (openWith argument body)
  | .indRec name motive methods target =>
    iotaStep? name motive methods target
  | .idJ _motive base eqProof =>
    idJStep? base eqProof
  | .quotLift lifted _respects target =>
    quotLiftStep? lifted target
  | .coindDestruct name destructorIndex target =>
    nuStep? name destructorIndex target
  | _ => none

/-! ## Weak-head normal form -/

/-- Reduce a term to weak-head normal form within `fuel` steps.

    A term is in whnf when its head is not a beta-, iota-, or
    delta-redex.  `whnf` repeatedly applies head reduction,
    recursing into the application's function position and the
    eliminator's target so further redexes can surface.

    `globalEnv` is consulted for delta-reduction on `.const`
    heads: an entry with `transparent := true` unfolds to its
    body.  Opaque entries (default per §10.15) stay as
    `const`.  Omit the parameter — it defaults to the empty
    env — to opt out of delta entirely.

    Returns the last term reached.  If `fuel = 0`, returns `t`
    unchanged.  If a reduction chain exceeds `fuel`, returns the
    current head — the caller decides whether to report an
    `R_fuel` diagnostic. -/
partial def whnf (fuel : Nat) (term : Term) (globalEnv : GlobalEnv := {}) : Term :=
  if fuel = 0 then term
  else
    match term with
    | .const name =>
      match globalEnv.unfold? name with
      | some body => whnf (fuel - 1) body globalEnv
      | none      => term
    | .app funPart argument =>
      let reducedFun := whnf (fuel - 1) funPart globalEnv
      match reducedFun with
      | .lam _grade _domain body => whnf (fuel - 1) (openWith argument body) globalEnv
      | _ => .app reducedFun argument
    | .indRec name motive methods target =>
      let reducedTarget := whnf (fuel - 1) target globalEnv
      match iotaStep? name motive methods reducedTarget globalEnv.userSpecs with
      | some step => whnf (fuel - 1) step globalEnv
      | none      => .indRec name motive methods reducedTarget
    | .idJ motive base eqProof =>
      let reducedEqProof := whnf (fuel - 1) eqProof globalEnv
      match idJStep? base reducedEqProof with
      | some step => whnf (fuel - 1) step globalEnv
      | none      => .idJ motive base reducedEqProof
    | .quotLift lifted respects target =>
      let reducedTarget := whnf (fuel - 1) target globalEnv
      match quotLiftStep? lifted reducedTarget with
      | some step => whnf (fuel - 1) step globalEnv
      | none      => .quotLift lifted respects reducedTarget
    | .coindDestruct specName destructorIndex target =>
      let reducedTarget := whnf (fuel - 1) target globalEnv
      match nuStep? specName destructorIndex reducedTarget with
      | some step => whnf (fuel - 1) step globalEnv
      | none      => .coindDestruct specName destructorIndex reducedTarget
    | _ => term

/-! ## Full normal form -/

/-- Reduce a term to normal form: whnf at the head, then recurse
    into every sub-term.  Exceeded fuel returns the current term.

    `globalEnv` threads to `whnf` and to every recursive
    `normalize` call so delta-reduction applies throughout the
    term.  A `.const` head with a transparent body unfolds at
    whnf; a `.const` nested inside another position (e.g., the
    argument to an application where the function doesn't
    reduce) also unfolds because normalize descends recursively
    into that position. -/
partial def normalize (fuel : Nat) (term : Term) (globalEnv : GlobalEnv := {}) : Term :=
  if fuel = 0 then term
  else
    let headReduced := whnf fuel term globalEnv
    match headReduced with
    | .var index => .var index
    | .const name =>
      -- A `const` that reached whnf unchanged is either opaque
      -- or unregistered — either way, don't try to unfold it
      -- again at normalize.  whnf already made the delta call.
      .const name
    | .app funPart argument =>
      .app (normalize (fuel - 1) funPart globalEnv) (normalize (fuel - 1) argument globalEnv)
    | .lam grade domain body =>
      .lam grade (normalize (fuel - 1) domain globalEnv) (normalize (fuel - 1) body globalEnv)
    | .pi grade domain body returnEffect =>
      .pi grade (normalize (fuel - 1) domain globalEnv)
          (normalize (fuel - 1) body globalEnv) returnEffect
    | .sigma grade domain body =>
      .sigma grade (normalize (fuel - 1) domain globalEnv) (normalize (fuel - 1) body globalEnv)
    | .type universeLevel => .type universeLevel
    | .forallLevel bodyTerm =>
      .forallLevel (normalize (fuel - 1) bodyTerm globalEnv)
    | .ind name args =>
      .ind name (args.map (normalize (fuel - 1) · globalEnv))
    | .ctor name ctorIndex typeArgs valueArgs =>
      .ctor name ctorIndex
        (typeArgs.map (normalize (fuel - 1) · globalEnv))
        (valueArgs.map (normalize (fuel - 1) · globalEnv))
    | .indRec name motive methods target =>
      .indRec name (normalize (fuel - 1) motive globalEnv)
        (methods.map (normalize (fuel - 1) · globalEnv))
        (normalize (fuel - 1) target globalEnv)
    | .coind typeName typeArgs =>
      .coind typeName (typeArgs.map (normalize (fuel - 1) · globalEnv))
    | .coindUnfold typeName typeArgs arms =>
      -- An unfold that reached `whnf` unchanged is in weak-head
      -- normal form (no destructor wrapping it).  Recurse into
      -- every sub-term to surface further redexes inside the
      -- typeArgs or arm bodies.
      .coindUnfold typeName
        (typeArgs.map (normalize (fuel - 1) · globalEnv))
        (arms.map (normalize (fuel - 1) · globalEnv))
    | .coindDestruct typeName destructorIndex targetTerm =>
      -- Same rationale as `.indRec` / `.idJ` / `.quotLift` arms:
      -- `headReduced` already went through `whnf`, so a
      -- `coindUnfold`-tipped target would have been discharged
      -- upstream via `nuStep?`.  A `coindDestruct` surviving
      -- `whnf` is therefore stuck on a non-unfold target;
      -- recurse into the target to surface further redexes.
      .coindDestruct typeName destructorIndex
        (normalize (fuel - 1) targetTerm globalEnv)
    | .id eqType lhs rhs =>
      .id (normalize (fuel - 1) eqType globalEnv) (normalize (fuel - 1) lhs globalEnv)
        (normalize (fuel - 1) rhs globalEnv)
    | .refl witnessTerm =>
      .refl (normalize (fuel - 1) witnessTerm globalEnv)
    | .idJ motive base eqProof =>
      -- `headReduced` already went through `whnf`, so a `refl`-tipped
      -- `eqProof` would have been discharged upstream and we'd never
      -- reach this arm.  An `idJ` surviving `whnf` is therefore stuck
      -- on a non-refl eq; we recurse into every sub-term to surface
      -- further redexes inside the motive, base, or stuck proof.
      .idJ (normalize (fuel - 1) motive globalEnv)
           (normalize (fuel - 1) base globalEnv)
           (normalize (fuel - 1) eqProof globalEnv)
    | .quot carrier relation =>
      .quot (normalize (fuel - 1) carrier globalEnv) (normalize (fuel - 1) relation globalEnv)
    | .quotMk relationTerm witnessTerm =>
      .quotMk (normalize (fuel - 1) relationTerm globalEnv)
              (normalize (fuel - 1) witnessTerm globalEnv)
    | .quotLift liftedTerm respectsTerm targetTerm =>
      -- Same rationale as the `.idJ` arm above: `headReduced`
      -- already went through `whnf`, so a `quotMk`-tipped
      -- `target` would have been discharged upstream and we
      -- wouldn't reach this arm.  Surviving `quotLift` here is
      -- stuck on a non-`quotMk` target; recurse into every
      -- sub-term to surface further redexes.
      .quotLift (normalize (fuel - 1) liftedTerm globalEnv)
                (normalize (fuel - 1) respectsTerm globalEnv)
                (normalize (fuel - 1) targetTerm globalEnv)

/-- Default reduction fuel for kernel queries.

    `4096` steps is the budget passed to `whnf` / `normalize` /
    `convEq` / `subOrConv` from every typing call site.  Rationale:

      * Empirically, every elaborator-produced term in the M1/M2
        test suite reduces in ≤ 200 steps.  The 20× headroom
        absorbs future features without re-tuning.
      * A single step is one reduction rule application (β, ι, ν,
        or η).  4096 steps is cheap to run — eval latency on the
        largest current test is sub-millisecond.
      * Large enough that a runaway reduction on a malformed
        term (Phase-2 elaborator bug, ill-typed construction via
        test helpers) surfaces as `R_fuel` rather than hanging the
        compiler.

    Per-obligation tuning belongs in the §10.12 proof-stability
    tracker once that lands; this constant is the kernel
    one-size-fits-all default.  Do NOT reference `4096` directly
    in kernel code — always go through this symbol so future tuning
    is a single-line change. -/
def defaultFuel : Nat := 4096

end Term

end FX.Kernel
