import FX1Poly.Core.CertifyRawCellExactCoverage
import FX1Poly.Core.StepTable
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.GeneratorTagRoundTrip
import FX1Poly.Typed.GeneratorSemanticTier

/-! # FX1Poly/Typed/UniverseModeGenerators — the four 2LTT universe-mode codes (M24-Z2)

The §11.8.2 / §3.16.3 universe-mode family lands at the Generator-table level:

* `gen_universeU` — inner univalent universe (cubical Kan reduction discipline);
* `gen_universeS` — outer strict universe (strict reduction calculus + strict
  large-elim; univalence STILL applies per the §11.8.13 univalence-everywhere
  register — "strictness" is an elim/reduction discipline, NOT a K-axiom);
* `gen_universeD` — directed universe (Riehl-Shulman synthetic (∞,1));
* `gen_universeOmega` — (∞,ω)-directed universe (Loubaton).

Each carries the SAME `LevelExpr × UniverseFlag` payload as `gen_universeCode`,
arity 0, empty child specs, output sort `.type`.  This module is the smoke +
honesty companion to the table rows:

* **Certifier acceptance** — each mode cell at payload `(lzero, standard)`
  certifies through the general ingress at sort `.type` (`rfl`, mirroring
  `CertifyRawCellExactCoverage`).
* **Leaf operational status** — each mode cell is a no-step normal leaf,
  hence strongly normalizing (mirroring `noStep_universeCode`).
* **Reserved tier** — none of the four has a typing or reduction rule yet, so
  `semanticTier` classifies all four `.reserved` (`rfl` pins).  The typing
  rows (mode-aware formation) and the per-mode reduction disciplines are the
  LATER Z-arc / §11.8.4 work, NOT this table migration.
* **Serialization stability** — the four tags `198–201` round-trip (`rfl`
  pins), extending the §11.6.4 table validation.

## Honest payload-admission scope

The M24-Z2 acceptance asked the certifier to "reject an ill-scoped level
payload".  Under the shipped fxProfile that rejection is VACUOUS BY DESIGN:
`GenPayloadEvidence` is uniformly `Unit` and `genPayloadEvidence?_isSome`
pins the unbounded-universes commitment (every `LevelExpr × UniverseFlag`
payload is admitted, exactly as for `gen_universeCode`).  No level-variable
scoping predicate exists in the payload layer.  `universeU_payloadAlwaysAdmitted`
states this positively; the restricting refinement is the HON-11 /
restricted-profile track, not this migration.

## Zero-axiom verification

Acceptance smokes, tier pins, and tag pins close by `rfl`; the leaf lemmas
mirror the shipped `noStep_universeCode` route (`cases step` + `noStepChildren_childNil`).
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Core.StepStar
open FX1Poly.Universe

/-! ## The four mode cells at the canonical smoke payload -/

/-- Inner univalent universe cell at `(lzero, standard)`. -/
def universeURaw : RawCell 0 :=
  .termBase (.mkGen .gen_universeU (LevelExpr.lzero, UniverseFlag.standard) .childNil)

/-- Outer strict universe cell at `(lzero, standard)`. -/
def universeSRaw : RawCell 0 :=
  .termBase (.mkGen .gen_universeS (LevelExpr.lzero, UniverseFlag.standard) .childNil)

/-- Directed universe cell at `(lzero, standard)`. -/
def universeDRaw : RawCell 0 :=
  .termBase (.mkGen .gen_universeD (LevelExpr.lzero, UniverseFlag.standard) .childNil)

/-- (∞,ω)-directed universe cell at `(lzero, standard)`. -/
def universeOmegaRaw : RawCell 0 :=
  .termBase (.mkGen .gen_universeOmega (LevelExpr.lzero, UniverseFlag.standard) .childNil)

/-! ## Certifier acceptance — each mode cell certifies at sort `.type` -/

theorem coverage_universeURaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0 universeURaw) =
      some .type := rfl

theorem coverage_universeSRaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0 universeSRaw) =
      some .type := rfl

theorem coverage_universeDRaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0 universeDRaw) =
      some .type := rfl

theorem coverage_universeOmegaRaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0 universeOmegaRaw) =
      some .type := rfl

/-! ## Leaf operational status — no-step normal leaves, hence SN -/

/-- An inner-univalent-universe atom is a normal leaf. -/
theorem noStep_universeU {scope : Nat}
    (modePayload : LevelExpr × UniverseFlag) {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_universeU modePayload .childNil : RawTerm scope)
        targetTerm →
      False := by
  intro step
  cases Step.weakHeadOrChildCong step with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨childrenAfter, _targetEq, childStep⟩ := congShape
      exact noStepChildren_childNil childStep

/-- An outer-strict-universe atom is a normal leaf. -/
theorem noStep_universeS {scope : Nat}
    (modePayload : LevelExpr × UniverseFlag) {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_universeS modePayload .childNil : RawTerm scope)
        targetTerm →
      False := by
  intro step
  cases Step.weakHeadOrChildCong step with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨childrenAfter, _targetEq, childStep⟩ := congShape
      exact noStepChildren_childNil childStep

/-- A directed-universe atom is a normal leaf. -/
theorem noStep_universeD {scope : Nat}
    (modePayload : LevelExpr × UniverseFlag) {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_universeD modePayload .childNil : RawTerm scope)
        targetTerm →
      False := by
  intro step
  cases Step.weakHeadOrChildCong step with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨childrenAfter, _targetEq, childStep⟩ := congShape
      exact noStepChildren_childNil childStep

/-- An (∞,ω)-directed-universe atom is a normal leaf. -/
theorem noStep_universeOmega {scope : Nat}
    (modePayload : LevelExpr × UniverseFlag) {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_universeOmega modePayload .childNil : RawTerm scope)
        targetTerm →
      False := by
  intro step
  cases Step.weakHeadOrChildCong step with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨childrenAfter, _targetEq, childStep⟩ := congShape
      exact noStepChildren_childNil childStep

/-- Inner-univalent-universe atoms are strongly normalizing. -/
theorem universeU_isStronglyNormalizing {scope : Nat}
    (modePayload : LevelExpr × UniverseFlag) :
    IsStronglyNormalizing
      (.mkGen .gen_universeU modePayload .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step =>
      noStep_universeU modePayload (targetTerm := targetTerm) step)

/-- Outer-strict-universe atoms are strongly normalizing. -/
theorem universeS_isStronglyNormalizing {scope : Nat}
    (modePayload : LevelExpr × UniverseFlag) :
    IsStronglyNormalizing
      (.mkGen .gen_universeS modePayload .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step =>
      noStep_universeS modePayload (targetTerm := targetTerm) step)

/-- Directed-universe atoms are strongly normalizing. -/
theorem universeD_isStronglyNormalizing {scope : Nat}
    (modePayload : LevelExpr × UniverseFlag) :
    IsStronglyNormalizing
      (.mkGen .gen_universeD modePayload .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step =>
      noStep_universeD modePayload (targetTerm := targetTerm) step)

/-- (∞,ω)-directed-universe atoms are strongly normalizing. -/
theorem universeOmega_isStronglyNormalizing {scope : Nat}
    (modePayload : LevelExpr × UniverseFlag) :
    IsStronglyNormalizing
      (.mkGen .gen_universeOmega modePayload .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step =>
      noStep_universeOmega modePayload (targetTerm := targetTerm) step)

/-! ## Reserved tier — no typing/reduction rules yet, classified honestly -/

theorem semanticTier_universeU : semanticTier .gen_universeU = .reserved := rfl
theorem semanticTier_universeS : semanticTier .gen_universeS = .reserved := rfl
theorem semanticTier_universeD : semanticTier .gen_universeD = .reserved := rfl
theorem semanticTier_universeOmega : semanticTier .gen_universeOmega = .reserved := rfl

/-! ## Serialization stability — tags 198–201 round-trip -/

theorem fromTag_universeU : Generator.fromTag 198 = some .gen_universeU := rfl
theorem fromTag_universeS : Generator.fromTag 199 = some .gen_universeS := rfl
theorem fromTag_universeD : Generator.fromTag 200 = some .gen_universeD := rfl
theorem fromTag_universeOmega : Generator.fromTag 201 = some .gen_universeOmega := rfl

/-! ## The honest payload-admission scope (the unbounded-universes commitment) -/

/-- Under fxProfile EVERY `gen_universeU` payload is admitted — the same
unbounded-universes commitment `genPayloadEvidence?_isSome` pins for
`gen_universeCode`.  The "reject an ill-scoped level" refinement is a
restricted-profile obligation (HON-11 track), NOT a property of the default
profile; stating the admission positively keeps the ledger honest. -/
theorem universeU_payloadAlwaysAdmitted {scope : Nat}
    (modePayload : Generator.payload .gen_universeU scope) :
    (genPayloadEvidence? (generator := .gen_universeU)
      (scope := scope) modePayload).isSome = true := rfl

/-! ## SProp — the definitional-proof-irrelevance universe (M26-Z1)

`gen_sprop` is nullary with `Unit` payload, output sort `.type` — the
proof-irrelevant universe per §3.16.3.  The DISCIPLINE (SProp elimination
into Type restricted to subsingleton targets + `False`, and the
trivial-univalence collapse "any two inhabitants are equal" per the
§11.8.13 register) is a TYPING-row + judgmental-equality obligation, NOT a
table-shape property; the table lands the alphabet, the discipline lands
with the SProp formation/elim rows (SN-076 #579 and beyond). -/

/-- The SProp universe cell. -/
def spropRaw : RawCell 0 :=
  .termBase (.mkGen .gen_sprop () .childNil)

theorem coverage_spropRaw_sort {profile : PolyProfile} :
    certifiedResultSort?
      (inferRawCellGeneral? (profile := profile) 0 spropRaw) =
      some .type := rfl

/-- An SProp-universe atom is a normal leaf. -/
theorem noStep_sprop {scope : Nat} {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_sprop () .childNil : RawTerm scope) targetTerm →
      False := by
  intro step
  cases Step.weakHeadOrChildCong step with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨childrenAfter, _targetEq, childStep⟩ := congShape
      exact noStepChildren_childNil childStep

/-- SProp-universe atoms are strongly normalizing. -/
theorem sprop_isStronglyNormalizing {scope : Nat} :
    IsStronglyNormalizing
      (.mkGen .gen_sprop () .childNil : RawTerm scope) :=
  isStronglyNormalizing_of_noStep
    (fun targetTerm step => noStep_sprop (targetTerm := targetTerm) step)

theorem semanticTier_sprop : semanticTier .gen_sprop = .reserved := rfl

theorem fromTag_sprop : Generator.fromTag 202 = some .gen_sprop := rfl

/-! ## The mode bridges — the shipped name-encoded design supersedes LiftDirection

The M26 plan called for ONE `gen_univLift` generator carrying a
`LiftDirection` payload enum (InnerToOuter / OuterToInner / DirectedLift).
The kernel SHIPPED the equivalent encoding with the direction in the
GENERATOR NAME instead: `gen_liftInnerToOuter` (arity 1 — innerTerm) and
`gen_lowerOuterToInner` (arity 2 — outerTerm, cofibrancy), with SN-077
reducibility already proven over them.  The name-encoded design is
STRICTLY better for the zero-axiom discipline: no payload enum (no
DecidableEq derivation to audit), head-directed dispatch and direction
no-confusion come free from `Generator.noConfusion`, and the §11.8.13
"lifts are univalence-preserving" obligation attaches per-generator.
The pins below LOCK the shipped table shapes so a silent redesign breaks
loudly.  HONEST GAP: the third planned direction (the directed lift,
universeU↔universeD) has no shipped generator — that bridge lands with
the directed-mode typing work, not this migration. -/

theorem liftInnerToOuter_arity : Generator.arity .gen_liftInnerToOuter = 1 := rfl
theorem liftInnerToOuter_shifts :
    Generator.binderShifts .gen_liftInnerToOuter = [0] := rfl
theorem lowerOuterToInner_arity : Generator.arity .gen_lowerOuterToInner = 2 := rfl
theorem lowerOuterToInner_shifts :
    Generator.binderShifts .gen_lowerOuterToInner = [0, 0] := rfl

/-- The two shipped bridge generators are distinct — the direction
no-confusion the LiftDirection enum would have needed a DecidableEq for,
free at the generator level. -/
theorem liftBridges_directionsDistinct :
    Generator.gen_liftInnerToOuter ≠ Generator.gen_lowerOuterToInner := by
  intro headsEqual
  exact Generator.noConfusion headsEqual

end FX1Poly.Typed
