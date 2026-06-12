import FX1Poly.Typed.HasTypeDescGradedIntro
import FX1Poly.Typed.UntypableHeadDecision
import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Core.RawTermSubstIdentity
import FX1Poly.Core.RawTermRenameSubstCommute
import FX1Poly.Core.RawTermSubstPointwise
import FX1Poly.Core.RawTermOccurrenceRename

/-! # FX1Poly/Typed/BridgeEndpointStep — the endpoint-β computation as a GATED SIBLING (OP1-INT brick 5)

The bridge family's computation rule `pathApp (pathLam body) ε ↝ body[i := ε]` — the BCM
endpoint-β — shipped under the **`Step.eta` sibling-inductive discipline**: a standalone
relation gated BY CONSTRUCTION (the single constructor fires only on the exact redex shape),
NOT an arm of the core `Step` inductive.  This is the kernel's established zero-cascade route
for new reduction rules (η-M8b precedent): no refresh of the ~80 full-enumeration Step
consumers (SR arms, `fireRootRedex`, ParStep, complete development, critical pairs, encode
bridges); promotion of the rule into core `Step` is a recorded FUTURE event with its own
SR/ι-refresh budget — that promotion is what flips `Generator.hasRedexHead` for `gen_pathApp`
and migrates its ONORM-M2 sconing role `inertEliminator → eliminator` (breaking the
`LiveGenerator` enum BY DESIGN).

## The retired bridge typing engine (NATIVE-45)

The bespoke `HasTypeDescBridge` typing engine has been RETIRED: the native union
`HasTypeNativeUnion` (and its keystone substrate `HasTypeDescGradedIntro` for path INTRO,
`HasTypeDescGeneralElim` for path ELIM) types everything the bridge engine did, so this file
no longer imports it.  This file sits UPSTREAM of `HasTypeNativeUnion` and `HasTypeDescGeneralElim`
in the import order, so its typed companions speak only the engine available here — the native
graded-intro engine `HasTypeDescGradedIntro` (the substrate the union's `gradedBinderIntro` arm
embeds) for path INTRO.  The elimination-side typed companions (the applied path, the typed
round-trips, the cross-engine SR instances) now live DOWNSTREAM where the elim engine is in scope:
`HasTypeDescGeneralElim.gradedIntroEndpointIotaComputesTyped` (the typed endpoint-ι) and
`HasTypeNativeUnion.endpointRedexNativelyTypedWhole` (the whole redex in one union derivation);
the engine-specific inversion stack is subsumed by the union inversion suite
(`HasTypeNativeUnionInversion` / `HasTypeNativeUnionPathProjInversion`).

## What ships here

  * **`StepBridgeEndpoint`** — the sibling relation, one `pathBeta` constructor.
  * **`sourceShape`** — by-construction gating pin: every step source is exactly a
    `pathApp(pathLam …, …)` redex (so the relation cannot over-fire); `deterministic`.
  * **`RawTerm.subst0_weaken`** — the substitution collapse `subst0 (weaken t) a = t`
    (rename-then-subst composition down to the identity substitution), the constant-bridge
    computation engine.
  * **Computation smokes** — the constant bridge applied to an endpoint computes to its body;
    the identity path applied to an endpoint computes to that endpoint; SYMBOLIC constant
    bodies compute via the collapse (`constantPathBetaComputesToBody`).
  * **`identityPathGradedTyped`** — the identity path `pathLam(var 0)` typed at the bridge code
    NATIVELY by `HasTypeDescGradedIntro` (the graded-intro engine, the union's `gradedBinderIntro`
    substrate), the affine premise discharged by `occurrenceCountAt_var_self`.  The operational
    smokes' INTRO-side typed companion.
  * **`constantBridgeGradedOfTyped`** — ★ every grown-typed term embeds as the reflexivity bridge
    `pathLam(weaken t)`, typed NATIVELY by `HasTypeDescGradedIntro`: the affine premise is the
    grade-0 occurrence lemma (`occurrenceCountAt_weaken_zeroPosition`, discharged not hypothesized)
    and the endpoints collapse by `subst0_weaken`.  The derivable `refl` of internal parametricity,
    its INTRO half stated against the live native engine.
  * **`intervalZeroGrownUntypable`** — ★ the machine-checked CROSS-ENGINE WALL: the
    identity-path reduct (`interval0`) heads no grown-typed cell, so general endpoint-β SR
    cannot target `HasTypeDescPi` alone.  A general-`ε` reduct mixes grown structure with
    interval leaves; the honest general SR statement lives in the native union (interval rows
    are native `dataIntroNullary` rows) — the wall falls into the union, witnessed downstream by
    `BridgeEndpointNativeSubjectReduction`.

## Zero-axiom

The sibling inductive is positive and non-indexed-trap (free source/reduct indices); smokes
are constructor applications closed by `whnf`-defeq substitution computation (nullary cells
and innermost-var-0 bodies compute by `rfl`); the native typed companions route through
`gradedIntroEngine_typesPathLam` with the affine premise discharged by the occurrence lemmas;
the collapse is `rename_subst_commute` + a `PointwiseEq`-to-identity `rfl` + `subst_identity_apply`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Core

/-- **The substitution collapse**: substituting anything into a WEAKENED term is the identity —
`subst0 (weaken t) a = t`.  Rename-then-subst composes to the pointwise-identity substitution
(`singleton a ∘ Fin.succ` sends position `k` to `var k`), which `subst_identity_apply`
collapses.  The dimension-CONSTANT bridge computation engine. -/
theorem RawTerm.subst0_weaken {scope : Nat}
    (constantTerm : RawTerm scope) (rawArg : RawTerm scope) :
    RawTerm.subst0 (RawTerm.weaken constantTerm) rawArg = constantTerm := by
  show RawTerm.subst (RawTermSubst.singleton rawArg)
      (RawTerm.weaken constantTerm) = constantTerm
  rw [RawTerm.weaken_eq_rename, RawTerm.rename_subst_commute]
  have collapseToIdentity :
      RawTermSubst.PointwiseEq
        (RawRenaming.thenSubst FX1Poly.Foundation.RawRenaming.weaken
          (RawTermSubst.singleton rawArg))
        RawTermSubst.identity := by
    intro position
    cases position with
    | mk positionValue positionBound => rfl
  rw [RawTerm.subst_pointwise collapseToIdentity]
  exact RawTerm.subst_identity_apply constantTerm

end FX1Poly.Core

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The endpoint-β reduction, gated sibling.**  `pathApp (pathLam body) ε ↝ body[i := ε]` —
the single rule of the bridge family's operational semantics, a SIBLING of core `Step`
(η-discipline): by-construction it fires ONLY on the exact redex shape, and it does not touch
any core-Step consumer.  Promotion into core `Step` (the event that makes `gen_pathApp`
operationally live for the candidates/scones) is the recorded future task. -/
inductive StepBridgeEndpoint : {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
  | pathBeta {scope : Nat} (body : RawTerm (scope + 1)) (argument : RawTerm scope) :
      StepBridgeEndpoint (pathAppCell (pathLamCell body) argument)
        (RawTerm.subst0 body argument)

/-- By-construction GATING pin: every `StepBridgeEndpoint` source is exactly an endpoint-β
redex and every reduct is the corresponding substitution — the relation cannot over-fire. -/
theorem StepBridgeEndpoint.sourceShape {scope : Nat} {source reduct : RawTerm scope}
    (step : StepBridgeEndpoint source reduct) :
    ∃ body : RawTerm (scope + 1), ∃ argument : RawTerm scope,
      source = pathAppCell (pathLamCell body) argument ∧
        reduct = RawTerm.subst0 body argument := by
  cases step with
  | pathBeta body argument => exact ⟨body, argument, rfl, rfl⟩

/-- The endpoint-β step is deterministic: one source, one reduct. -/
theorem StepBridgeEndpoint.deterministic {scope : Nat}
    {source firstReduct secondReduct : RawTerm scope}
    (firstStep : StepBridgeEndpoint source firstReduct)
    (secondStep : StepBridgeEndpoint source secondReduct) :
    firstReduct = secondReduct := by
  obtain ⟨firstBody, firstArgument, firstSourceEq, firstReductEq⟩ := firstStep.sourceShape
  obtain ⟨secondBody, secondArgument, secondSourceEq, secondReductEq⟩ := secondStep.sourceShape
  have cellsEqual : pathAppCell (pathLamCell firstBody) firstArgument
      = pathAppCell (pathLamCell secondBody) secondArgument :=
    firstSourceEq.symm.trans secondSourceEq
  injection cellsEqual with _scopeEq _generatorEq _payloadEq childrenEq
  injection childrenEq with _pathScopeEq _pathShiftEq _pathRestShiftsEq pathCellsEqual restEq
  injection restEq with _argScopeEq _argShiftEq _argRestShiftsEq argumentsEqual _nilEq
  injection pathCellsEqual with _innerScopeEq _innerGeneratorEq _innerPayloadEq innerChildrenEq
  injection innerChildrenEq with _bodyScopeEq _bodyShiftEq _bodyRestShiftsEq bodiesEqual _bodyNilEq
  rw [firstReductEq, secondReductEq, bodiesEqual, argumentsEqual]

/-! ## Computation smokes — the rule FIRES on the typed witnesses -/

/-- The constant bridge applied to the left endpoint computes to its body:
`pathApp(pathLam(Type@0), 0) ↝ Type@0` (the closed nullary body is fixed by substitution,
definitionally). -/
theorem StepBridgeEndpoint.constantBridgeAppliedComputes {scope : Nat} (flag : UniverseFlag) :
    StepBridgeEndpoint
      (pathAppCell (pathLamCell (universeCodeCell LevelExpr.lzero flag))
        (intervalZeroCell (scope := scope)))
      (universeCodeCell LevelExpr.lzero flag) :=
  StepBridgeEndpoint.pathBeta (universeCodeCell LevelExpr.lzero flag) intervalZeroCell

/-- The identity path applied to the left endpoint computes to that endpoint:
`pathApp(pathLam(i), 0) ↝ 0` (innermost-var-0 substitution computes definitionally). -/
theorem StepBridgeEndpoint.identityPathAppliedComputes {scope : Nat} :
    StepBridgeEndpoint
      (pathAppCell (pathLamCell (variableCell ⟨0, Nat.succ_pos scope⟩))
        (intervalZeroCell (scope := scope)))
      intervalZeroCell :=
  StepBridgeEndpoint.pathBeta (variableCell ⟨0, Nat.succ_pos scope⟩) intervalZeroCell

/-- **SYMBOLIC constant-body computation**: for ANY body of the form `weaken constantBody`
(the dimension-constant bridges) and ANY argument, the redex computes to exactly
`constantBody` — via the `subst0_weaken` collapse. -/
theorem StepBridgeEndpoint.constantPathBetaComputesToBody {scope : Nat}
    (constantBody argument : RawTerm scope) :
    StepBridgeEndpoint
      (pathAppCell (pathLamCell (RawTerm.weaken constantBody)) argument) constantBody := by
  have fired := StepBridgeEndpoint.pathBeta (RawTerm.weaken constantBody) argument
  rw [RawTerm.subst0_weaken constantBody argument] at fired
  exact fired

/-! ## The native path-intro typed companions (`HasTypeDescGradedIntro`, the union substrate)

The bespoke `HasTypeDescBridge` typing engine is RETIRED.  The path-INTRO typed companions of
the operational smokes are restated against the LIVE native graded-intro engine
`HasTypeDescGradedIntro` (the substrate the union's `gradedBinderIntro` arm embeds, NATIVE-23):
`pathLam` types via `gradedIntroEngine_typesPathLam` at the body-dependent bridge code, with the
affine usage premise discharged exactly as the bespoke `pathIntro` discharged it.  The
elimination-side companions (the applied path, the typed round-trips, the cross-engine SR) live
DOWNSTREAM where the elim engine is in scope — see the module docstring. -/

/-- **The identity path on the interval, typed natively**: `pathLam(i) :
Bridge(Interval, 0, 1)` — the dimension variable itself as a bridge body, the FIRST inhabitant
that genuinely USES its dimension binder (affine count exactly 1, discharged by
`occurrenceCountAt_var_self`), typed by the native graded-intro engine.  The body's classifier
is the weakened interval code; its endpoint substitutions compute definitionally to the bare
endpoints, so the bridge code reads `Bridge(Interval, 0, 1)`. -/
theorem identityPathGradedTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeDescGradedIntro profile context
      (pathLamCell (variableCell ⟨0, Nat.succ_pos scope⟩))
      (bridgeTypeCell intervalTypeCell intervalZeroCell intervalOneCell) :=
  gradedIntroEngine_typesPathLam (carrierCode := intervalTypeCell)
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (context.cons intervalTypeCell) ⟨0, Nat.succ_pos scope⟩))
    (Nat.le_of_eq (RawTerm.occurrenceCountAt_var_self ⟨0, Nat.succ_pos scope⟩))

/-- **★ Every typed term embeds as the reflexivity bridge, typed natively.**  `t : T  ⟹
pathLam(weaken t) : Bridge(T, t, t)` — the reflexivity bridge (the derivable `refl` of internal
parametricity), with the affine usage premise PROVED at grade `0`
(`occurrenceCountAt_weaken_zeroPosition`) and both endpoints collapsing to `t` itself by
`subst0_weaken`.  Stated against the live native graded-intro engine; its endpoint application
(the elimination half) computes back to `t` with the same grown typing downstream
(`HasTypeDescGeneralElim.gradedIntroEndpointIotaComputesTyped`,
`HasTypeNativeUnion.endpointRedexNativelyTypedWhole`). -/
theorem constantBridgeGradedOfTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {constantBody typeCode : RawTerm scope}
    (bodyTyped : HasTypeDescPi profile context constantBody typeCode) :
    HasTypeDescGradedIntro profile context (pathLamCell (RawTerm.weaken constantBody))
      (bridgeTypeCell typeCode constantBody constantBody) := by
  have intro := gradedIntroEngine_typesPathLam (carrierCode := typeCode)
    (body := RawTerm.weaken constantBody)
    (bodyTyped.weakenUnderBinding intervalTypeCell)
    (by rw [RawTerm.occurrenceCountAt_weaken_zeroPosition]
        exact Nat.zero_le 1)
  rw [RawTerm.subst0_weaken, RawTerm.subst0_weaken] at intro
  exact intro

/-- **★ The CROSS-ENGINE WALL, machine-checked.**  The identity-path reduct `interval0` heads
NO grown-typed cell (`isUntypableHead gen_interval0` holds for the grown-only classifier).  So
the general endpoint-β SR cannot be stated against `HasTypeDescPi` alone: a general-`ε` reduct
mixes grown structure with interval leaves.  The honest general SR target is the native union
`HasTypeNativeUnion` (interval endpoints are native `dataIntroNullary` rows) — the wall FALLS
into the union, witnessed downstream by `BridgeEndpointNativeSubjectReduction`.  Consumed by the
union adequacy (`HasTypeNativeUnion`) to refute a grown image for the bare interval. -/
theorem intervalZeroGrownUntypable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (intervalZeroCell (scope := scope)) classifier) :
    False :=
  isUntypableHead_sound rfl typed

end FX1Poly.Typed
