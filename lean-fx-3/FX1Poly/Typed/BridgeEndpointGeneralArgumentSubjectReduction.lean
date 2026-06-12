import FX1Poly.Typed.BridgeEndpointStep
import FX1Poly.Typed.HasTypeDescPiSubstitution
import FX1Poly.Typed.BridgeEndpointNativeSubjectReduction

/-! # FX1Poly/Typed/BridgeEndpointGeneralArgumentSubjectReduction — NATIVE-09: endpoint-β SR for general
    arguments via the grown substitution lemma.

`BridgeEndpointNativeSubjectReduction` closed the endpoint-β subject reduction on the two SHIPPED
fragments — the dimension-constant body (reduct GROWN-typed via `subst0_weaken`) and the identity-path
body at a bare endpoint (reduct DATA-INTRO-typed) — and recorded the remaining residual: a GENERAL body's
endpoint-β reduct `body[ε]` needs the grown single-substitution lemma to be typed.

This is that residual.  `HasTypeDescPi.substituteUnderBinding` (the grown β-engine) transports a derivation
under a binder along a grown-typed argument.  Supplying the body GROWN-typed under the interval binder at
the redex's own (weakened) classifier together with a GROWN-typed interval argument lets the grown
substitution lemma fire, and `subst0_weaken` collapses the substituted classifier back to the original —
so the reduct is GROWN-typed at the original classifier, for an ARBITRARY body (not just the constant or
identity-path special cases).  All engine-free (only the grown engine `HasTypeDescPi`); the retired
`HasTypeDescBridge` typing engine (NATIVE-45) is not referenced.

This completes the wall-falls picture by classifying the endpoint-β reduct by ARGUMENT:

  * argument GROWN-typed at the interval (e.g. a context-bound interval variable) → reduct GROWN-typed
    (this file, via the grown substitution lemma);
  * argument a bare endpoint `interval0`/`interval1` → reduct DATA-INTRO-typed (the wall case, native
    `dataIntroNullary` row).

Both land in `EndpointBetaReductNativelyTyped` — the combined native target — so endpoint-β preserves
combined-native typing for EVERY grown-typed body, whichever native layer the argument inhabits.

## What ships

  * **`endpointBetaGeneralArgumentGrownReduct` (★)** — the general theorem: a body grown-typed under the
    interval binder at `weaken classifier` + a grown-typed interval argument ⟹ the endpoint-β step fires
    AND the reduct `body[argument]` is GROWN-typed at `classifier`.  Pure substitution transport — no
    restriction on the body's shape.
  * **`endpointBetaGeneralArgumentNativelyTyped`** — the corollary into the combined predicate
    `EndpointBetaReductNativelyTyped`: the same reduct is combined-native-typed via the `ofGrown`
    disjunct.  So the constant fragment, the identity-path-at-endpoint fragment, AND every grown-argument
    fragment all speak the ONE preservation predicate.
  * **`endpointBetaConstantBodySubsumed`** — the headline SUBSUMES the constant fragment: a constant body
    `weaken constantBody` is one instance of the general body, recovering the reflexivity-bridge reduct
    typing through the SAME grown substitution lemma.

## Zero-axiom

The general theorem is `substituteUnderBinding` (the shipped grown β-engine) composed with the
`subst0_weaken` classifier collapse + `StepBridgeEndpoint.pathBeta`; the corollary and the subsumption are
constructor applications.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ The general endpoint-β subject reduction via the grown substitution lemma.**  For an ARBITRARY
body grown-typed under the interval binder at the redex's weakened classifier, and ANY grown-typed interval
argument, the endpoint-β step fires and the reduct `body[argument]` is GROWN-typed at the original
classifier.  The grown β-engine `substituteUnderBinding` transports the body along the argument; the
substituted classifier `subst0 (weaken classifier) argument` collapses to `classifier` by `subst0_weaken`.
The substitution-transport residual the wall-case fragments deferred — now discharged for every body
shape. -/
theorem endpointBetaGeneralArgumentGrownReduct {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {body : RawTerm (scope + 1)}
    {classifier argument : RawTerm scope}
    (bodyTyped : HasTypeDescPi profile (context.cons intervalTypeCell) body
      (RawTerm.weaken classifier))
    (argumentGrownTyped : HasTypeDescPi profile context argument intervalTypeCell) :
    StepBridgeEndpoint (pathAppCell (pathLamCell body) argument)
      (RawTerm.subst0 body argument) ∧
    HasTypeDescPi profile context (RawTerm.subst0 body argument) classifier := by
  refine ⟨StepBridgeEndpoint.pathBeta body argument, ?_⟩
  have substituted :=
    HasTypeDescPi.substituteUnderBinding argument bodyTyped argumentGrownTyped
  rw [RawTerm.subst0_weaken classifier argument] at substituted
  exact substituted

/-- **The general grown-argument reduct lands in the combined native predicate.**  The corollary into
`EndpointBetaReductNativelyTyped` (the `ofGrown` disjunct): the constant fragment, the
identity-path-at-endpoint fragment, and every grown-argument fragment now all speak the ONE endpoint-β
preservation predicate. -/
theorem endpointBetaGeneralArgumentNativelyTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {body : RawTerm (scope + 1)}
    {classifier argument : RawTerm scope}
    (bodyTyped : HasTypeDescPi profile (context.cons intervalTypeCell) body
      (RawTerm.weaken classifier))
    (argumentGrownTyped : HasTypeDescPi profile context argument intervalTypeCell) :
    StepBridgeEndpoint (pathAppCell (pathLamCell body) argument)
      (RawTerm.subst0 body argument) ∧
    EndpointBetaReductNativelyTyped profile context (RawTerm.subst0 body argument) classifier := by
  obtain ⟨fires, grownReduct⟩ :=
    endpointBetaGeneralArgumentGrownReduct bodyTyped argumentGrownTyped
  exact ⟨fires, EndpointBetaReductNativelyTyped.ofGrown grownReduct⟩

/-- **The general theorem subsumes the constant fragment.**  A dimension-constant body
`weaken constantBody` is one instance of an arbitrary grown-typed body: the reduct `subst0 (weaken
constantBody) argument` collapses to `constantBody` and is grown-typed at `classifier` through the SAME
grown substitution lemma — recovering the reflexivity-bridge reduct typing as a special case, now uniform
with the binder-using bodies. -/
theorem endpointBetaConstantBodySubsumed {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {constantBody classifier argument : RawTerm scope}
    (constantBodyTyped : HasTypeDescPi profile (context.cons intervalTypeCell)
      (RawTerm.weaken constantBody) (RawTerm.weaken classifier))
    (argumentGrownTyped : HasTypeDescPi profile context argument intervalTypeCell) :
    HasTypeDescPi profile context constantBody classifier := by
  have grownReduct :=
    (endpointBetaGeneralArgumentGrownReduct constantBodyTyped argumentGrownTyped).2
  rw [RawTerm.subst0_weaken constantBody argument] at grownReduct
  exact grownReduct

/-- **★ Non-vacuous contrast smoke: a grown-typed interval-variable argument gives a GROWN reduct.**  In a
context binding the dimension variable, the identity-path body applied to that variable fires endpoint-β to
the variable itself, and the reduct is GROWN-typed (the variable's own typing) — where the SAME identity
path applied to a bare ENDPOINT reaches only the data-intro engine.  The endpoint-β reduct's
classification BY ARGUMENT made concrete: grown argument → grown reduct; bare endpoint → data reduct.  The
reduct `subst0 (var 0) (var 0)` computes to `var 0` definitionally (innermost-var-0 substitution), and the
two grown-typed interval variables (the body's path binder, the context's dimension binder) are the
`HasTypeDesc.var` lookups — `weaken intervalTypeCell` collapses to `intervalTypeCell` for the closed cell. -/
theorem intervalVariableEndpointBetaGrownReduct {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    StepBridgeEndpoint
      (pathAppCell (pathLamCell (variableCell ⟨0, Nat.succ_pos (scope + 1)⟩))
        (variableCell ⟨0, Nat.succ_pos scope⟩))
      (variableCell ⟨0, Nat.succ_pos scope⟩) ∧
    HasTypeDescPi profile (context.cons intervalTypeCell)
      (variableCell ⟨0, Nat.succ_pos scope⟩) intervalTypeCell :=
  endpointBetaGeneralArgumentGrownReduct (classifier := intervalTypeCell)
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var ((context.cons intervalTypeCell).cons intervalTypeCell)
        ⟨0, Nat.succ_pos (scope + 1)⟩))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (context.cons intervalTypeCell) ⟨0, Nat.succ_pos scope⟩))

end FX1Poly.Typed
