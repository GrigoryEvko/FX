import LeanFX2.Term

/-! # Foundation/TermTranspPathVacuity — vacuity foundations for the
`Term.transp` leaf dispatcher (#2015, unblock-A.leaf.transp).

The raw inversion lemma `RawStep.par.transp_inv`
(`Reduction/RawParInversion/CubicalAndIdentity.lean:315`) enumerates
SEVEN cases under a `RawTerm.transp pathRaw sourceRaw` head: cong,
transpReflBeta (shallow), transpReflBetaDeep (deep refl-β), uaBeta
(D3.6-S1 shallow), uaBetaDeep (deep ua-β), transpCompose (D3.6-S3
shallow), transpComposeDeep (deep compose-β).

At the typed level, `Term.transp ... pathSource sourceValue` has
`pathSource : Term context (Ty.path (Ty.universe _) sourceTyRaw
targetTyRaw) pathRaw`.  The dispatcher leaf must lift any raw step
to a typed parallel step.

* Cong + transpReflBeta (shallow) are routed through the existing
  `Step.par.transp` / `Step.par.transpReflBeta` typed ctors.
* `transpReflBetaDeep` requires a NEW typed mirror ctor (the only
  genuine kernel extension in the transp cascade — landing as the
  single Path B β arm of #2063).
* `uaBeta`, `uaBetaDeep`, `transpCompose`, `transpComposeDeep` are
  **vacuous at the typed level**.  The two lemmas in this file
  refute these four cases by showing that no typed `Term context
  (Ty.path ...) ...` can have raw projection `RawTerm.uaToEquiv _`
  or `RawTerm.pathCompose _ _`.

The vacuity holds because the typed kernel:

1. Has exactly ONE ctor producing raw `RawTerm.uaToEquiv _`:
   `Term.uaToEquiv` (`Term.lean:1074`) — whose result type is
   `Ty.equiv leftTy rightTy`, NOT `Ty.path ...`.  By Ty
   constructor injectivity, no inhabitant of `Term context (Ty.path
   ...) (RawTerm.uaToEquiv _)` exists.

2. Has ZERO ctors producing raw `RawTerm.pathCompose _ _`.  The
   typed `Term.pathCompose` is deferred to v1.1 (#1574
   D3.10-PATH-COMPOSE-HOTT); until then, no typed Term has this
   raw shape regardless of type index.

## Cascade role

* Consumed by future `RawStep.par.lift_full_transp` (#2065) to
  discharge 4 of the 7 raw inversion arms via vacuity, mirroring
  the discharge pattern of `Term.pathLam_excludes_closedTy`
  (#2066 hcomp closed-carrier) and `Term.uaToEquiv_excludes_oeqRefl_witness`
  (#2059 equivApply close).
* Reduces #2063 scope from "ship 5 typed deep+ua+compose β arms"
  to "ship 1 typed Step.par.transpReflBetaDeep ctor" — the only
  raw deep arm that admits a typed source.

## Audit

Both theorems verified zero-axiom via `#print axioms`.

## Pitfalls + mitigations

* P-1 (`Term.var`'s `varType context position` opaque to dep-elim):
  Direct `cases` on a Term at a fixed dependent type sometimes
  fails on `Term.var` because Lean cannot statically refute
  `Ty.path ... = varType context position`.  Mitigation: the
  `suffices`-then-`intro` indirection frees the type index so the
  matcher on the generic Term sees a free `someType` rather than
  a fixed dependent type.  Same pattern as
  `Term.pathLam_excludes_closedTy` (Foundation/TermPathLamExcludes.lean:62).
* P-2 (raw shape determines exactly one ctor): For
  `RawTerm.uaToEquiv _`, the `cases genericTerm` step iterates only
  the `Term.uaToEquiv` ctor (raw projection ALL OTHER ctors are
  distinct).  For `RawTerm.pathCompose _ _`, the `cases genericTerm`
  step iterates ZERO ctors (no Term ctor matches).
* P-13: N/A — `False` is the conclusion; no Decidable witness
  needed. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}
variable {context : Ctx mode level scope}

/-- **A typed `Term` at `Ty.path ...` cannot have raw projection
`RawTerm.uaToEquiv _`.**

The only Term ctor whose raw projection is `RawTerm.uaToEquiv _`
is `Term.uaToEquiv` (`Term.lean:1074`).  Its result type is
`Ty.equiv leftTy rightTy`, while the hypothesis lives at
`Ty.path pathCarrier leftEndpoint rightEndpoint`.  `Ty.equiv` and
`Ty.path` are distinct Ty constructors; no-confusion via `cases`
on the type equation discharges False.

Consumed by `RawStep.par.lift_full_transp` (#2065) to refute the
`uaBeta` shallow arm (raw `pathTerm = RawTerm.uaToEquiv proofRaw`)
and, after subject reduction on the deep path-target, the
`uaBetaDeep` arm of `RawStep.par.transp_inv`. -/
theorem Term.uaToEquiv_excludes_pathTy
    {pathCarrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {proofRaw : RawTerm scope}
    (pathTypedTerm :
      Term context
        (Ty.path pathCarrier leftEndpoint rightEndpoint)
        (RawTerm.uaToEquiv proofRaw)) :
    False := by
  suffices key :
      ∀ {someType : Ty level scope}
        (genericTerm :
          Term context someType (RawTerm.uaToEquiv proofRaw))
        {pathCarrierInner : Ty level scope}
        {leftEndpointInner rightEndpointInner : RawTerm scope}
        (pathEq :
          someType = Ty.path pathCarrierInner leftEndpointInner
                                              rightEndpointInner),
        False by
    exact key pathTypedTerm rfl
  intro someType genericTerm _pathCarrierInner _leftEndpointInner
        _rightEndpointInner pathEq
  cases genericTerm
  cases pathEq

/-- **No typed `Term` has raw projection `RawTerm.pathCompose _ _`.**

The typed kernel ships ZERO constructors producing
`RawTerm.pathCompose _ _` — `Term.pathCompose` is deferred to
v1.1 (#1574 D3.10-PATH-COMPOSE-HOTT).  The `RawTerm.pathCompose`
ctor itself exists only for raw-layer confluence-closure
(D3.6-S3 univalence-β cascade), supporting
`RawStep.par.transpCompose` / `transpComposeDeep` raw-only β
rules.

The `cases genericTerm` step iterates zero matching ctors, so
the goal is vacuously discharged.

Consumed by `RawStep.par.lift_full_transp` (#2065) to refute the
`transpCompose` shallow arm (raw `pathTerm = RawTerm.pathCompose
left right`) and, after subject reduction on the deep
path-target, the `transpComposeDeep` arm of
`RawStep.par.transp_inv`. -/
theorem Term.pathCompose_uninhabited
    {someType : Ty level scope}
    {leftRaw rightRaw : RawTerm scope}
    (genericTerm :
      Term context someType (RawTerm.pathCompose leftRaw rightRaw)) :
    False := by
  cases genericTerm

end LeanFX2
