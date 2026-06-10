import FX1Poly.Core.CertifyRawCellExactCoverage
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
  cases step with
  | cong _ _ childStep =>
      exact noStepChildren_childNil childStep

/-- An outer-strict-universe atom is a normal leaf. -/
theorem noStep_universeS {scope : Nat}
    (modePayload : LevelExpr × UniverseFlag) {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_universeS modePayload .childNil : RawTerm scope)
        targetTerm →
      False := by
  intro step
  cases step with
  | cong _ _ childStep =>
      exact noStepChildren_childNil childStep

/-- A directed-universe atom is a normal leaf. -/
theorem noStep_universeD {scope : Nat}
    (modePayload : LevelExpr × UniverseFlag) {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_universeD modePayload .childNil : RawTerm scope)
        targetTerm →
      False := by
  intro step
  cases step with
  | cong _ _ childStep =>
      exact noStepChildren_childNil childStep

/-- An (∞,ω)-directed-universe atom is a normal leaf. -/
theorem noStep_universeOmega {scope : Nat}
    (modePayload : LevelExpr × UniverseFlag) {targetTerm : RawTerm scope} :
    Step (.mkGen .gen_universeOmega modePayload .childNil : RawTerm scope)
        targetTerm →
      False := by
  intro step
  cases step with
  | cong _ _ childStep =>
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

end FX1Poly.Typed
