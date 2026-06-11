import FX1Poly.Typed.HasTypeDescBridge
import FX1Poly.Typed.UntypableHeadDecision
import FX1Poly.Core.RawTermSubstIdentity
import FX1Poly.Core.RawTermRenameSubstCommute
import FX1Poly.Core.RawTermSubstPointwise

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
  * **`pathAppSubjectInversion` / `pathLamAtBridgeInversion` / `pathBetaRedexInversion`** —
    the deterministic inversion stack (the bridge engine has NO conv arm): typing a redex
    yields the body's typing under the interval binder, the FORCED affinity bound, and the
    argument's interval typing — the skeleton every future SR proof consumes.
  * **`pathBetaRoundTrip`** — intro-then-elim is typed AND the redex fires (the general typed
    round-trip at a symbolic body/argument, affine premise supplied by the caller).
  * **Two non-vacuous SR instances**: `constantBridgeEndpointSubjectReduction` (the reduct is
    GROWN-typed at the same classifier — the bridge eliminator computes INTO the grown world
    on the dimension-constant fragment) and `identityPathEndpointSubjectReduction` (the reduct
    is BRIDGE-typed at the same classifier — elimination of the identity path on the interval).
  * **`intervalZeroGrownUntypable`** — ★ the machine-checked CROSS-ENGINE WALL: the
    identity-path reduct (`interval0`) heads no grown-typed cell, so general endpoint-β SR
    cannot target `HasTypeDescPi` alone.  A general-`ε` reduct mixes grown structure with
    bridge leaves; the honest general SR statement lives in an INTEGRATED engine (bridge rows
    folded into the rule tables) — the recorded residual, exactly the listElim
    engine-separation finding's shape.

## Zero-axiom

The sibling inductive is positive and non-indexed-trap (free source/reduct indices); smokes
are constructor applications closed by `whnf`-defeq substitution computation (nullary cells
and innermost-var-0 bodies compute by `rfl`); inversions follow the free-subject + threaded
equality recipe with `injections` drilling; the collapse is
`rename_subst_commute` + a `PointwiseEq`-to-identity `rfl` + `subst_identity_apply`.
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

/-! ## The identity path — the second typed bridge inhabitant -/

/-- **The identity path on the interval**: `pathLam(i) : Bridge(dim, 0, 1)` — the dimension
variable itself as a bridge body, the FIRST inhabitant that genuinely USES its dimension
binder (affine count exactly 1, discharged by `occurrenceCountAt_var_self`).  The endpoint
substitutions compute definitionally to the endpoints. -/
theorem HasTypeDescBridge.identityPathTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeDescBridge profile context
      (pathLamCell (variableCell ⟨0, Nat.succ_pos scope⟩))
      (bridgeTypeCell intervalTypeCell intervalZeroCell intervalOneCell) :=
  HasTypeDescBridge.pathIntro context (variableCell ⟨0, Nat.succ_pos scope⟩)
    intervalTypeCell
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (context.cons intervalTypeCell) ⟨0, Nat.succ_pos scope⟩))
    (Nat.le_of_eq (RawTerm.occurrenceCountAt_var_self ⟨0, Nat.succ_pos scope⟩))

/-- The identity path eliminated at the left endpoint is typed at the interval. -/
theorem HasTypeDescBridge.identityPathAppliedTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeDescBridge profile context
      (pathAppCell (pathLamCell (variableCell ⟨0, Nat.succ_pos scope⟩)) intervalZeroCell)
      intervalTypeCell :=
  HasTypeDescBridge.pathElim context
    (pathLamCell (variableCell ⟨0, Nat.succ_pos scope⟩)) intervalZeroCell
    intervalTypeCell intervalZeroCell intervalOneCell
    (HasTypeDescBridge.identityPathTyped context)
    (HasTypeDescBridge.intervalZero context)

/-! ## The deterministic inversion stack (no conv arm in the bridge engine) -/

/-- Inversion at a `pathApp`-headed subject: the only typing arm is `pathElim`, so the
argument is interval-typed and the path is typed at a bridge over THIS classifier. -/
theorem HasTypeDescBridge.pathAppSubjectInversion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescBridge profile context subject classifier) :
    ∀ {path argument : RawTerm scope}, subject = pathAppCell path argument →
      HasTypeDescBridge profile context argument intervalTypeCell ∧
      ∃ leftEndpoint rightEndpoint : RawTerm scope,
        HasTypeDescBridge profile context path
          (bridgeTypeCell classifier leftEndpoint rightEndpoint) := by
  cases derivation with
  | intervalFormation _flag =>
      intro path argument subjectEq
      exact absurd (congrArg RawTerm.rootGenerator subjectEq) (by intro headEq; cases headEq)
  | intervalZero =>
      intro path argument subjectEq
      exact absurd (congrArg RawTerm.rootGenerator subjectEq) (by intro headEq; cases headEq)
  | intervalOne =>
      intro path argument subjectEq
      exact absurd (congrArg RawTerm.rootGenerator subjectEq) (by intro headEq; cases headEq)
  | bridgeFormation _typeCode _leftEndpoint _rightEndpoint _level _flag
      _typeCodeTyped _leftTyped _rightTyped =>
      intro path argument subjectEq
      exact absurd (congrArg RawTerm.rootGenerator subjectEq) (by intro headEq; cases headEq)
  | pathIntro _armBody _armTypeCode _bodyTyped _dimensionAffine =>
      intro path argument subjectEq
      exact absurd (congrArg RawTerm.rootGenerator subjectEq) (by intro headEq; cases headEq)
  | pathElim armPath armArgument _armTypeCode armLeftEndpoint armRightEndpoint
      pathTyped argumentTyped =>
      intro path argument subjectEq
      injection subjectEq with _scopeEq _generatorEq _payloadEq childrenEq
      injection childrenEq with _pathScopeEq _pathShiftEq _pathRestShiftsEq pathsEqual restEq
      injection restEq with _argScopeEq _argShiftEq _argRestShiftsEq argumentsEqual _nilEq
      exact ⟨argumentsEqual ▸ argumentTyped,
        armLeftEndpoint, armRightEndpoint, pathsEqual ▸ pathTyped⟩

/-- Inversion at a `pathLam`-headed subject AGAINST a bridge classifier: the only typing arm
is `pathIntro`, so the body is grown-typed under the interval binder, the affinity bound is
FORCED, and the classifier's endpoints are exactly the body's endpoint substitutions. -/
theorem HasTypeDescBridge.pathLamAtBridgeInversion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescBridge profile context subject classifier) :
    ∀ {body : RawTerm (scope + 1)} {typeCode leftEndpoint rightEndpoint : RawTerm scope},
      subject = pathLamCell body →
      classifier = bridgeTypeCell typeCode leftEndpoint rightEndpoint →
      HasTypeDescPi profile (context.cons intervalTypeCell) body (RawTerm.weaken typeCode) ∧
      RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ ≤ 1 ∧
      leftEndpoint = RawTerm.subst0 body intervalZeroCell ∧
      rightEndpoint = RawTerm.subst0 body intervalOneCell := by
  cases derivation with
  | intervalFormation _flag =>
      intro body typeCode leftEndpoint rightEndpoint subjectEq _classifierEq
      exact absurd (congrArg RawTerm.rootGenerator subjectEq) (by intro headEq; cases headEq)
  | intervalZero =>
      intro body typeCode leftEndpoint rightEndpoint subjectEq _classifierEq
      exact absurd (congrArg RawTerm.rootGenerator subjectEq) (by intro headEq; cases headEq)
  | intervalOne =>
      intro body typeCode leftEndpoint rightEndpoint subjectEq _classifierEq
      exact absurd (congrArg RawTerm.rootGenerator subjectEq) (by intro headEq; cases headEq)
  | bridgeFormation _typeCode _leftEndpoint _rightEndpoint _level _flag
      _typeCodeTyped _leftTyped _rightTyped =>
      intro body typeCode leftEndpoint rightEndpoint subjectEq _classifierEq
      exact absurd (congrArg RawTerm.rootGenerator subjectEq) (by intro headEq; cases headEq)
  | pathIntro armBody armTypeCode bodyTyped dimensionAffine =>
      intro body typeCode leftEndpoint rightEndpoint subjectEq classifierEq
      injection subjectEq with _scopeEq _generatorEq _payloadEq bodyChildrenEq
      injection bodyChildrenEq with _bodyScopeEq _bodyShiftEq _bodyRestShiftsEq
        bodiesEqual _bodyNilEq
      injection classifierEq with _cScopeEq _cGeneratorEq _cPayloadEq classifierChildrenEq
      injection classifierChildrenEq with _tScopeEq _tShiftEq _tRestShiftsEq
        typeCodesEqual classifierRestEq
      injection classifierRestEq with _lScopeEq _lShiftEq _lRestShiftsEq
        leftEqualRaw classifierRest2Eq
      injection classifierRest2Eq with _rScopeEq _rShiftEq _rRestShiftsEq
        rightEqualRaw _cNilEq
      subst bodiesEqual
      subst typeCodesEqual
      subst leftEqualRaw
      subst rightEqualRaw
      exact ⟨bodyTyped, dimensionAffine, rfl, rfl⟩
  | pathElim _path _argument _typeCode _leftEndpoint _rightEndpoint
      _pathTyped _argumentTyped =>
      intro body typeCode leftEndpoint rightEndpoint subjectEq _classifierEq
      exact absurd (congrArg RawTerm.rootGenerator subjectEq) (by intro headEq; cases headEq)

/-- **The redex inversion — the SR skeleton.**  Typing an endpoint-β redex yields exactly the
data subject reduction needs: the body grown-typed under the interval binder AT THE REDEX'S
OWN CLASSIFIER (weakened), the forced affinity bound, and the argument's interval typing.
What remains for general SR is ONLY the cross-engine substitution transport — see
`intervalZeroGrownUntypable` for why that transport cannot target the grown engine alone. -/
theorem HasTypeDescBridge.pathBetaRedexInversion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {body : RawTerm (scope + 1)}
    {argument classifier : RawTerm scope}
    (typed : HasTypeDescBridge profile context
      (pathAppCell (pathLamCell body) argument) classifier) :
    HasTypeDescPi profile (context.cons intervalTypeCell) body (RawTerm.weaken classifier) ∧
    RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ ≤ 1 ∧
    HasTypeDescBridge profile context argument intervalTypeCell := by
  obtain ⟨argumentTyped, leftEndpoint, rightEndpoint, pathTyped⟩ :=
    typed.pathAppSubjectInversion rfl
  obtain ⟨bodyTyped, dimensionAffine, _, _⟩ :=
    pathTyped.pathLamAtBridgeInversion rfl rfl
  exact ⟨bodyTyped, dimensionAffine, argumentTyped⟩

/-! ## The general typed round-trip + the two non-vacuous SR instances -/

/-- **The general endpoint-β round-trip**: intro-then-elim is bridge-typed at the body's own
type code AND the redex fires to the substituted body — for a SYMBOLIC body and argument
(the affine premise supplied by the caller; dischargeable by `rfl`-computation for closed
bodies and by `occurrenceCountAt_var_self` for the identity body). -/
theorem HasTypeDescBridge.pathBetaRoundTrip {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {body : RawTerm (scope + 1)}
    {typeCode : RawTerm scope}
    (bodyTyped : HasTypeDescPi profile (context.cons intervalTypeCell) body
      (RawTerm.weaken typeCode))
    (dimensionAffine : RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ ≤ 1)
    {argument : RawTerm scope}
    (argumentTyped : HasTypeDescBridge profile context argument intervalTypeCell) :
    HasTypeDescBridge profile context (pathAppCell (pathLamCell body) argument) typeCode ∧
    StepBridgeEndpoint (pathAppCell (pathLamCell body) argument)
      (RawTerm.subst0 body argument) :=
  ⟨HasTypeDescBridge.pathElim context (pathLamCell body) argument typeCode
      (RawTerm.subst0 body intervalZeroCell) (RawTerm.subst0 body intervalOneCell)
      (HasTypeDescBridge.pathIntro context body typeCode bodyTyped dimensionAffine)
      argumentTyped,
   StepBridgeEndpoint.pathBeta body argument⟩

/-- **★ SR instance 1 — the CROSS-ENGINE fragment (dimension-constant bridges).**  The typed
constant-bridge redex fires, and its reduct is GROWN-typed at the SAME classifier: the bridge
eliminator computes INTO the grown world on the constant fragment.  Redex typed (bridge) +
step fires (sibling) + reduct typed (grown), all at `Type@1`. -/
theorem constantBridgeEndpointSubjectReduction {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescBridge profile (TypingContext.empty : TypingContext profile 0)
      (pathAppCell (pathLamCell (universeCodeCell LevelExpr.lzero flag)) intervalZeroCell)
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) ∧
    StepBridgeEndpoint
      (pathAppCell (pathLamCell (universeCodeCell LevelExpr.lzero flag))
        (intervalZeroCell (scope := 0)))
      (universeCodeCell LevelExpr.lzero flag) ∧
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (universeCodeCell LevelExpr.lzero flag)
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) :=
  ⟨HasTypeDescBridge.constantBridgeAppliedTyped flag,
   StepBridgeEndpoint.constantBridgeAppliedComputes flag,
   HasTypeDescPi.ofFormation
     (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag)⟩

/-- **★ SR instance 2 — WITHIN the bridge engine (the identity path).**  The typed
identity-path redex fires to the endpoint, and the endpoint is bridge-typed at the SAME
classifier (the interval): elimination of the genuinely-dimension-using inhabitant is
type-preserving inside the engine. -/
theorem identityPathEndpointSubjectReduction {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeDescBridge profile context
      (pathAppCell (pathLamCell (variableCell ⟨0, Nat.succ_pos scope⟩)) intervalZeroCell)
      intervalTypeCell ∧
    StepBridgeEndpoint
      (pathAppCell (pathLamCell (variableCell ⟨0, Nat.succ_pos scope⟩)) intervalZeroCell)
      (intervalZeroCell (scope := scope)) ∧
    HasTypeDescBridge profile context intervalZeroCell intervalTypeCell :=
  ⟨HasTypeDescBridge.identityPathAppliedTyped context,
   StepBridgeEndpoint.identityPathAppliedComputes,
   HasTypeDescBridge.intervalZero context⟩

/-- **★ The CROSS-ENGINE WALL, machine-checked.**  The identity-path reduct `interval0` heads
NO grown-typed cell (`isUntypableHead gen_interval0` holds for the grown-only classifier —
the bridge rows live in the standalone engine).  So the general endpoint-β SR cannot be
stated against `HasTypeDescPi` alone: a general-`ε` reduct mixes grown structure with bridge
leaves, and the honest general SR target is an INTEGRATED engine (bridge rows folded into the
rule tables) — the recorded OP1-INT residual. -/
theorem intervalZeroGrownUntypable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (intervalZeroCell (scope := scope)) classifier) :
    False :=
  isUntypableHead_sound rfl typed

end FX1Poly.Typed
