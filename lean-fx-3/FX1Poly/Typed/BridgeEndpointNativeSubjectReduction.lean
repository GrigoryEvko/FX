import FX1Poly.Typed.BridgeEndpointStep
import FX1Poly.Typed.NativeUnionRuleTables

/-! # FX1Poly/Typed/BridgeEndpointNativeSubjectReduction — NATIVE-08 ★: the cross-engine wall falls

`BridgeEndpointStep` ships the endpoint-β reduction `pathApp(pathLam body) ε ↝ body[i := ε]` and two
non-vacuous subject-reduction fragments, but it ALSO ships the obstruction
`intervalZeroGrownUntypable`: the identity-path reduct `interval0` heads no GROWN-typed cell
(`isUntypableHead gen_interval0 = true`, like `boolTrue`), so a general endpoint-β subject reduction
CANNOT target `HasTypeDescPi` alone — a general-`ε` reduct mixes grown structure with bare interval
leaves.  That was the recorded **cross-engine wall**.

NATIVE-07 makes the wall FALL.  The interval endpoints are now NATIVELY typed by the union's
`dataIntroNullary` arm (`interval0`/`interval1 : intervalCode`).  So the endpoint-β reduct that escapes
the grown engine — `interval0` — is caught by a DIFFERENT native arm.  Endpoint-β is subject-reducing against the COMBINED native engine even though
it is not against the grown engine alone: the bridge eliminator computes INTO the data-value layer.

## What ships

  * **`EndpointBetaReductNativelyTyped`** — the combined-native typing of an endpoint-β reduct: typed by
    the grown engine OR the bridge engine OR the union's `dataIntroNullary` arm.  The honest SR target the
    `intervalZeroGrownUntypable` wall forces (no single engine suffices; their union does).
  * **`intervalZeroReductNativelyTyped` / `intervalOneReductNativelyTyped`** — the bare interval
    endpoints are combined-native-typed (the `ofDataIntro` disjunct), the reducts the grown engine
    cannot reach.
  * **`intervalOneGrownUntypable`** — the right-endpoint twin of `intervalZeroGrownUntypable` (the
    grown engine cannot type `interval1` either).
  * **`endpointBetaWallFalls` (★)** — the wall-falls witness: `interval0` is combined-native-typed AND
    grown-untypable SIMULTANEOUSLY.  The combined engine succeeds exactly where the grown engine alone
    provably fails — the precise statement of the wall falling.
  * **`identityPathEndpointSubjectReductionNative` (★)** — the full identity-path endpoint-β SR against
    the combined engine: the redex is bridge-typed, the step fires, and the reduct `interval0` is
    combined-native-typed (via dataIntro) where `intervalZeroGrownUntypable` proves the grown engine
    cannot type it.  The genuine cross-engine SR instance — the eliminator computes into the data layer.
  * **`reflexivityBridgeEndpointSubjectReductionNative`** — the constant fragment under the SAME combined
    target: the reduct lands in the `ofGrown` disjunct.  Both fragments now speak ONE preservation
    predicate.
  * **`endpointBetaNativeSubjectReductionVerdict` (★★)** — the honest capstone: endpoint-β preserves
    combined-native typing on BOTH fragments (constant → grown, identity-path → dataIntro), and the
    grown-only target is provably insufficient on the identity-path fragment.  The wall has fallen — the
    union of the native engines is the correct SR target, as NATIVE-40's unified engine will internalize.

## Zero-axiom

The combined predicate is a 3-constructor positive `Prop` inductive; every theorem is a constructor
application over the shipped `BridgeEndpointStep` SR fragments + the NATIVE-07 `intervalZeroTyped` /
`intervalOneTyped` smokes; the grown-untypability twin is `isUntypableHead_sound rfl` (the `rfl` proves
`isUntypableHead gen_interval1 = true`, grown-only, unaffected by the union's dataIntroNullary rows).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Combined-native typing of an endpoint-β reduct.**  A reduct is native-typed when SOME of the
kernel's native typing engines types it: the GROWN engine (`HasTypeDescPi`, the constant-fragment
reduct), the BRIDGE engine (`HasTypeDescBridge`, the within-engine endpoint), or the union's
`dataIntroNullary` row (the bare interval endpoint — the reduct the grown engine cannot reach).

`ofDataIntro` carries the row witness DIRECTLY (`dataIntroNullaryRuleDescOf generator = some rule`, the
reduct is the row's childless cell, the classifier is the row's output type-code) rather than the
`HasTypeNativeUnion` derivation: this file sits UPSTREAM of `HasTypeNativeUnion` in the import order, so
it cannot mention the union inductive without a cycle.  The witness is DEFINITIONALLY the union's
`dataIntroNullary` arm at this row — same content, no forward dependency.

The honest endpoint-β SR target: the `intervalZeroGrownUntypable` wall proves no single engine suffices,
and this union is exactly what NATIVE-40's unified engine internalizes. -/
inductive EndpointBetaReductNativelyTyped (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (reduct classifier : RawTerm scope) : Prop where
  | ofGrown (typed : HasTypeDescPi profile context reduct classifier)
  | ofBridge (typed : HasTypeDescBridge profile context reduct classifier)
  | ofDataIntro (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope)
      (rule : DataIntroNullaryRuleDesc)
      (isDataIntro : dataIntroNullaryRuleDescOf generator = some rule)
      (reductIsCell : reduct = .mkGen generator payload children)
      (classifierIsRowOutput : classifier = rule.outputTypeCode scope)

/-- **The left interval endpoint is combined-native-typed.**  `interval0 : intervalCode` via the union's
`dataIntroNullary` arm (NATIVE-07) — the endpoint-β reduct the grown engine cannot type. -/
theorem intervalZeroReductNativelyTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    EndpointBetaReductNativelyTyped profile context intervalZeroCell intervalTypeCell :=
  EndpointBetaReductNativelyTyped.ofDataIntro .gen_interval0 () .childNil
    { outputTypeCode := fun _ => intervalTypeCell } rfl rfl rfl

/-- **The right interval endpoint is combined-native-typed.**  `interval1 : intervalCode` via the union's
`dataIntroNullary` row (NATIVE-07). -/
theorem intervalOneReductNativelyTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    EndpointBetaReductNativelyTyped profile context intervalOneCell intervalTypeCell :=
  EndpointBetaReductNativelyTyped.ofDataIntro .gen_interval1 () .childNil
    { outputTypeCode := fun _ => intervalTypeCell } rfl rfl rfl

/-- **The right-endpoint grown-untypability twin.**  Like `intervalZeroGrownUntypable`: the grown engine
cannot type `interval1` (`isUntypableHead gen_interval1 = true`, grown-only — unaffected by the standalone
data-intro row).  Completes the wall on both endpoints. -/
theorem intervalOneGrownUntypable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (intervalOneCell (scope := scope)) classifier) :
    False :=
  isUntypableHead_sound rfl typed

/-- **★ The cross-engine wall falls.**  The endpoint-β reduct `interval0` is combined-native-typed (via
the union's dataIntroNullary arm, NATIVE-07) AND grown-untypable SIMULTANEOUSLY (`intervalZeroGrownUntypable`): the
combined native engine succeeds exactly where the grown engine alone provably fails.  This is the precise
statement that the recorded cross-engine wall has fallen — the endpoint-β reduct that escaped
`HasTypeDescPi` is caught by the union of the native engines. -/
theorem endpointBetaWallFalls {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    EndpointBetaReductNativelyTyped profile context intervalZeroCell intervalTypeCell ∧
    (HasTypeDescPi profile context intervalZeroCell intervalTypeCell → False) :=
  ⟨intervalZeroReductNativelyTyped context,
   fun grownTyped => intervalZeroGrownUntypable grownTyped⟩

/-- **★ The identity-path endpoint-β subject reduction against the combined engine.**  The
identity-path redex `pathApp(pathLam(i), 0)` is bridge-typed at `intervalCode`, the endpoint-β step
FIRES to `interval0`, and the reduct is combined-native-typed — by the union's dataIntroNullary arm, where
`intervalZeroGrownUntypable` proves the grown engine cannot type it.  The genuine cross-engine SR
instance: the bridge eliminator computes INTO the data-value layer, type-preservingly under the combined
engine.  This supersedes `identityPathEndpointSubjectReduction` (which closed inside the bridge engine
only) by routing the reduct through the native data-value typing — the wall-crossing SR. -/
theorem identityPathEndpointSubjectReductionNative {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeDescBridge profile context
      (pathAppCell (pathLamCell (variableCell ⟨0, Nat.succ_pos scope⟩)) intervalZeroCell)
      intervalTypeCell ∧
    StepBridgeEndpoint
      (pathAppCell (pathLamCell (variableCell ⟨0, Nat.succ_pos scope⟩)) intervalZeroCell)
      (intervalZeroCell (scope := scope)) ∧
    EndpointBetaReductNativelyTyped profile context intervalZeroCell intervalTypeCell :=
  ⟨HasTypeDescBridge.identityPathAppliedTyped context,
   StepBridgeEndpoint.identityPathAppliedComputes,
   intervalZeroReductNativelyTyped context⟩

/-- **The constant fragment under the SAME combined target.**  From `t : T` (grown) and an interval-typed
argument, the reflexivity-bridge endpoint-β fires to `t` and the reduct lands in the `ofGrown` disjunct of
the combined predicate: both endpoint-β fragments now speak ONE preservation predicate (constant → grown,
identity-path → data-intro).  Harvests `reflexivityBridgeRoundTrip` into the unified target. -/
theorem reflexivityBridgeEndpointSubjectReductionNative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {constantBody typeCode : RawTerm scope}
    (bodyTyped : HasTypeDescPi profile context constantBody typeCode)
    {argument : RawTerm scope}
    (argumentTyped : HasTypeDescBridge profile context argument intervalTypeCell) :
    HasTypeDescBridge profile context
      (pathAppCell (pathLamCell (RawTerm.weaken constantBody)) argument) typeCode ∧
    StepBridgeEndpoint
      (pathAppCell (pathLamCell (RawTerm.weaken constantBody)) argument) constantBody ∧
    EndpointBetaReductNativelyTyped profile context constantBody typeCode := by
  obtain ⟨_reflexivityTyped, elimTyped, fires, grownReduct⟩ :=
    reflexivityBridgeRoundTrip bodyTyped argumentTyped
  exact ⟨elimTyped, fires, EndpointBetaReductNativelyTyped.ofGrown grownReduct⟩

/-- **★★ The endpoint-β native subject-reduction verdict — the honest capstone.**  Endpoint-β preserves
combined-native typing on BOTH shipped fragments (the constant fragment lands GROWN, the identity-path
endpoint lands DATA-INTRO), AND the grown-only target is provably INSUFFICIENT on the identity-path
fragment (`intervalZeroGrownUntypable`).  The cross-engine wall has fallen: the union of the native
engines is the correct endpoint-β SR target — the bridge eliminator computes into whichever native layer
its reduct inhabits, exactly as NATIVE-40's single unified engine will internalize.  Bundles the wall-
falls witness with both fragment instances at a single concrete context. -/
theorem endpointBetaNativeSubjectReductionVerdict {profile : PolyProfile}
    (flag : UniverseFlag) :
    -- the identity-path fragment: reduct combined-native-typed where grown alone fails
    (EndpointBetaReductNativelyTyped profile (TypingContext.empty : TypingContext profile 0)
        intervalZeroCell intervalTypeCell ∧
      (HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
        intervalZeroCell intervalTypeCell → False)) ∧
    -- the constant fragment: reduct combined-native-typed via the grown disjunct
    EndpointBetaReductNativelyTyped profile (TypingContext.empty : TypingContext profile 0)
      (universeCodeCell LevelExpr.lzero flag)
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) :=
  ⟨endpointBetaWallFalls TypingContext.empty,
   EndpointBetaReductNativelyTyped.ofGrown
     (HasTypeDescPi.ofFormation
       (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))⟩

end FX1Poly.Typed
