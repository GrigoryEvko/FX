import FX1Poly.Typed.HasTypeDescTermIndexedFormerWeakening
import FX1Poly.Typed.HasTypeDescBridge

/-! # FX1Poly/Typed/BridgeFormationTermIndexedAdequacy — NATIVE-18: bridge formation adequacy (standalone ↔ generic)

NATIVE-12 shipped `termIndexedFormerGenFormation_reconstructsBridge`: the generic term-indexed `genFormation` arm
at the `gen_bridgeCode` row produces EXACTLY `bridgeFormation`'s conclusion FROM `bridgeFormation`'s premises (one
direction, at the premise level).  This file lands the FULL TWO-WAY adequacy at the DERIVATION level: the bespoke
standalone arm `HasTypeDescBridge.bridgeFormation` and the generic `HasTypeDescTermIndexedFormer` row are
INTER-DERIVABLE on bridge-type subjects — the bridge engine's formation arm IS the table row.

  * `HasTypeDescBridge.bridgeFormationToTermIndexed` — standalone ⟹ generic.  A `HasTypeDescBridge` derivation of
    a `bridgeTypeCell A a b` subject is the `bridgeFormation` arm (the other five arms produce interval / pathLam /
    pathApp cells — different head generators, so `cases` auto-drops them by no-confusion on the subject index);
    its three premises feed `reconstructsBridge`.
  * `HasTypeDescTermIndexedFormer.bridgeRowToStandalone` — generic ⟹ standalone.  A term-indexed derivation of a
    `bridgeTypeCell A a b` subject is the `genFormation` arm at `gen_bridgeCode`; the telescope premise destructures
    to the carrier + the two endpoint typings, which rebuild the bespoke `bridgeFormation`.
  * `bridgeFormationTermIndexedAdequacy` — the biconditional capstone (both maps), the formal "the two engines
    agree on bridge formation" statement.
  * `…adequacyAtUniverseSmoke` — the closed instance at `Bridge(Type@1, Type@0, Type@0) : Type@2`.

## Zero-axiom

`cases` on the subject-indexed derivations (impossible arms auto-dropped by head-generator no-confusion);
`termIndexedFormerRuleIsCarrierOutput` pins the generic output to `universeCodeCell`; the telescope/endpoint
destructuring is single-constructor `cases` over the concrete `childCons` spine (so the shifts are concrete — no
stuck dependent elimination).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ Bridge formation: standalone ⟹ generic.**  A `HasTypeDescBridge` derivation whose subject is a
`bridgeTypeCell` is necessarily the bespoke `bridgeFormation` arm (the five other arms head different generators —
`cases` drops them by no-confusion on the subject index); its three premises reconstruct the generic term-indexed
arm via `termIndexedFormerGenFormation_reconstructsBridge`. -/
theorem HasTypeDescBridge.bridgeFormationToTermIndexed {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode left right classifier : RawTerm scope}
    (derivation : HasTypeDescBridge profile context (bridgeTypeCell typeCode left right) classifier) :
    HasTypeDescTermIndexedFormer profile context (bridgeTypeCell typeCode left right) classifier := by
  cases derivation with
  | bridgeFormation _typeCode _left _right level flag typeCodeTyped leftTyped rightTyped =>
      exact termIndexedFormerGenFormation_reconstructsBridge typeCode left right level flag
        typeCodeTyped leftTyped rightTyped

/-- **★ Bridge formation: generic ⟹ standalone.**  A `HasTypeDescTermIndexedFormer` derivation whose subject is a
`bridgeTypeCell` is the `genFormation` arm at the `gen_bridgeCode` row (forced by the subject index); the rule
pins the output to `universeCodeCell` (`termIndexedFormerRuleIsCarrierOutput`), and the telescope premise
destructures to the carrier typing + the two endpoint typings, which rebuild the bespoke
`HasTypeDescBridge.bridgeFormation`. -/
theorem HasTypeDescTermIndexedFormer.bridgeRowToStandalone {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode left right classifier : RawTerm scope}
    (derivation : HasTypeDescTermIndexedFormer profile context (bridgeTypeCell typeCode left right) classifier) :
    HasTypeDescBridge profile context (bridgeTypeCell typeCode left right) classifier := by
  cases derivation with
  | genFormation _generator _payload _children carrier level flag rule isTermIndexed premises =>
      obtain rfl : rule = { outputType := termIndexedCarrierOutput } :=
        termIndexedFormerRuleIsCarrierOutput isTermIndexed
      show HasTypeDescBridge profile context (bridgeTypeCell typeCode left right)
        (universeCodeCell level flag)
      cases premises with
      | mk _carrier _restEndpoints _level _flag carrierTyped endpointsTyped =>
          cases endpointsTyped with
          | cons _leftEndpoint _restRight leftTyped rightEndpointsTyped =>
              cases rightEndpointsTyped with
              | cons _rightEndpoint _nilRest rightTyped _restNilTyped =>
                  exact HasTypeDescBridge.bridgeFormation context typeCode left right level flag
                    carrierTyped leftTyped rightTyped

/-- **★ The bridge formation adequacy capstone.**  The bespoke `HasTypeDescBridge.bridgeFormation` arm and the
generic `HasTypeDescTermIndexedFormer` row are INTER-DERIVABLE on bridge-type subjects — the formal statement that
the standalone bridge engine's formation arm IS the term-indexed table row. -/
theorem bridgeFormationTermIndexedAdequacy {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode left right classifier : RawTerm scope} :
    HasTypeDescBridge profile context (bridgeTypeCell typeCode left right) classifier ↔
      HasTypeDescTermIndexedFormer profile context (bridgeTypeCell typeCode left right) classifier :=
  ⟨HasTypeDescBridge.bridgeFormationToTermIndexed,
    HasTypeDescTermIndexedFormer.bridgeRowToStandalone⟩

/-- **★ Closed adequacy witness.**  The two engines agree on `Bridge(Type@1, Type@0, Type@0) : Type@2`: the
bespoke `bridgeOfUniverseCodesTyped` and the generic `…bridgeUniverseSmoke` are the two sides of the
biconditional at the universe smoke. -/
theorem bridgeFormationAdequacyAtUniverseSmoke {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescTermIndexedFormer profile (TypingContext.empty : TypingContext profile 0)
      (bridgeTypeCell (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
        (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag))
      (universeCodeCell (LevelExpr.lsucc (LevelExpr.lsucc LevelExpr.lzero)) flag) :=
  bridgeFormationTermIndexedAdequacy.mp (HasTypeDescBridge.bridgeOfUniverseCodesTyped flag)

end FX1Poly.Typed
