import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.StepOver.StepOverBundle
import FX1Poly.Typed.Metatheory.SubjectReduction.TableRootEtaSubjectReductionNative
import FX1PolyAudit.OneEngineSignoff

/-! # FX1PolyAudit/OneSystemSignoff — FX's kernel is ONE signature + ONE reduction bundle + ONE typing union

The grand sign-off.  The kernel's collapse to a single coherent system has three pillars, each shipped:

  1. **ONE typing engine** — the union judgment `HasTypeUnion`, table-driven, fully covered
     (the Stage-2 `OneEngineSignoff` bundles its classifier, nativity, subject reduction, canonicity,
     and honesty inversions, plus the Stage-1 unified-corpus capstone).

  2. **ONE reduction relation** — `Step` IS the iota-only `StepOver fxBundle` (RW-5), and the full
     kernel bundle `StepOver fxBundle` is the genuine βιη relation in which β/ι fire via the
     `iotaRedex` arm over the canonical `iotaRuleTable` and η fires via the `etaRedex` arm over the
     canonical `etaRuleTable` — ONE relation, no bespoke `Step.eta` sibling (retired in TABLE-CANON-ETA).

  3. **Table-native eta** — the canonical `etaRuleTable` rows fire through `StepEtaRootTable`, and grown
     subject reduction is preserved across a root-eta-table step with NO bespoke `Step.eta` construction
     (`HasTypeDescPi.preservedByTableEtaRootNative` / `subjectReductionTableBetaEtaRootNative`).

This module is the ONE-SYSTEM grand sign-off: a single named certificate tying together those three
pillars BY CITATION (it re-proves nothing).

## What this certificate ties together

  * **The one typing engine** — `FX1PolyAudit.oneEngineSignoffHolds : OneEngineSignoff profile`
    (`FX1PolyAudit/OneEngineSignoff.lean`).

  * **The one reduction relation, β/ι/η fused** —
      - `FX1Poly.Core.step_iff_stepOver_fxIotaBundle` (`FX1Poly/Core/StepOverBundle.lean`): core `Step`
        IS `StepOver fxIotaBundle` — the canonical β+ι relation is exactly the iota-only bundle (RW-5);
      - `FX1Poly.Core.StepOver.fxBundlePathBetaFires`: endpoint-β fires in `StepOver fxBundle` via the
        `iotaRedex` arm;
      - `FX1Poly.Core.StepOver.fxBundleEtaLamFires` / `…fxBundleEtaPairFires`: function-η and pair-η
        fire in the SAME `StepOver fxBundle` relation via the `etaRedex` arm.
    Together: β, ι, and η all live in the ONE `StepOver fxBundle` relation.

  * **Table-native eta subject reduction** —
    `FX1Poly.Typed.HasTypeDescPi.preservedByTableEtaRootNative` and
    `FX1Poly.Typed.HasTypeDescPi.subjectReductionTableBetaEtaRootNative`
    (`FX1Poly/Typed/TableRootEtaSubjectReductionNative.lean`): grown typing is preserved across a
    `StepEtaRootTable` root-eta step / a `StepTableBetaEtaRoot` union step, with no `Step.eta` value
    ever constructed.

## The bundle inhabitant's reading

`oneSystemSignoff` certifies: **FX's kernel is one signature + one reduction bundle + one typing union,
every semantic fact a table row** — the one typing engine (Stage 2), the one reduction relation
(`Step = StepOver fxBundle`, RW-5, β/ι/η fused), and the table-native eta layer, joined into one checked
object.  The inhabitant `oneSystemSignoffHolds` constructs each field from a shipped named declaration,
so the grand sign-off cannot silently decay.

## Layering note

Lives in the AUDIT layer because it cites the Stage-2 `oneEngineSignoffHolds`, itself an audit-layer
bundle (transitively the audit-side FX0 cross-check).

## Zero-axiom verification

`OneSystemSignoff` is a `Prop` structure whose every field is the type of a shipped zero-axiom theorem;
the eta-SR pillars are carried as `@`-anchored proof-term aliases (the `MetatheoryParityLedger`
cross-reference idiom) re-gated below.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated below in this same file. -/

namespace FX1PolyAudit

open FX1Poly.Core
  (PolyProfile RawTerm RawTermChildren Generator RuleTableBundle StepOver Step fxBundle fxIotaBundle
   step_iff_stepOver_fxIotaBundle)
open FX1PolyAudit (OneEngineSignoff oneEngineSignoffHolds)

/-- The reduction-relation pillar's eta-SR anchor (function-and-pair root-eta table step): a thin
proof-term alias of the shipped native eta subject reduction, so the grand sign-off file breaks if that
theorem is renamed, and its gate re-certifies it zero-axiom. -/
def oneSystemAnchor_etaTableSubjectReduction :=
  @FX1Poly.Typed.HasTypeDescPi.preservedByTableEtaRootNative

/-- The reduction-relation pillar's β-η-union-SR anchor (`StepTableBetaEtaRoot` step): a thin proof-term
alias of the shipped native β-η-root union subject reduction. -/
def oneSystemAnchor_betaEtaRootUnionSubjectReduction :=
  @FX1Poly.Typed.HasTypeDescPi.subjectReductionTableBetaEtaRootNative

/-- **The ONE-SYSTEM grand sign-off certificate.**  One `Prop` whose fields bundle, by citation, the
three pillars of the kernel's collapse to a single coherent system: the one typing engine (Stage 2),
the one reduction relation (`Step = StepOver fxBundle`, β/ι/η fused, RW-5), and the table-native eta
layer.  An inhabitant certifies FX's kernel is one signature + one reduction bundle + one typing union,
every semantic fact a table row. -/
structure OneSystemSignoff (profile : PolyProfile) : Prop where
  /-- Pillar 1 — the ONE typing engine: the Stage-2 sign-off (table classifier + nativity + subject
  reduction + canonicity + honesty inversions + the unified-corpus capstone). -/
  oneTypingEngine : OneEngineSignoff profile
  /-- Pillar 2a — the ONE reduction relation: core `Step` IS the iota-only `StepOver fxIotaBundle`
  (RW-5). -/
  stepIsTheIotaBundle : ∀ {scope : Nat} {source target : RawTerm scope},
    Step source target ↔ StepOver fxIotaBundle source target
  /-- Pillar 2b — endpoint-β fires in the full βιη bundle `StepOver fxBundle` via the `iotaRedex` arm. -/
  betaFiresInTheBundle : ∀ {scope : Nat} (body : RawTerm (scope + 1)) (arg : RawTerm scope),
    StepOver fxBundle
      (RawTerm.mkGen Generator.gen_pathApp ()
        (RawTermChildren.childCons
          (RawTerm.mkGen Generator.gen_pathLam ()
            (RawTermChildren.childCons body RawTermChildren.childNil))
          (RawTermChildren.childCons arg RawTermChildren.childNil)))
      (RawTerm.subst0 body arg)
  /-- Pillar 2c — function-η fires in the SAME `StepOver fxBundle` relation via the `etaRedex` arm. -/
  functionEtaFiresInTheBundle : ∀ {scope : Nat} (domainAnn innerFunction : RawTerm scope),
    StepOver fxBundle (RawTerm.etaLamSource domainAnn innerFunction) innerFunction
  /-- Pillar 2d — pair-η also fires in the SAME `StepOver fxBundle` relation (the non-left-linear row). -/
  pairEtaFiresInTheBundle : ∀ {scope : Nat} (pairTerm : RawTerm scope),
    StepOver fxBundle (RawTerm.etaPairSource pairTerm) pairTerm
  /-- Pillar 3a — table-native eta subject reduction: grown typing is preserved across a
  `StepEtaRootTable` root-eta step, with NO bespoke `Step.eta` construction. -/
  tableNativeEtaSubjectReduction : ∀ {scope : Nat}
    {context : FX1Poly.Typed.TypingContext profile scope}
    {source target classifier : RawTerm scope},
    FX1Poly.Typed.WfContextDescPi context →
    FX1Poly.Typed.HasTypeDescPi profile context source classifier →
    FX1Poly.Core.StepEtaRootTable source target →
    FX1Poly.Typed.HasTypeDescPi profile context target classifier
  /-- Pillar 3b — the full β-η-root union step preserves grown typing
  (`subjectReductionTableBetaEtaRootNative`). -/
  tableNativeBetaEtaUnionSubjectReduction : ∀ {scope : Nat}
    {context : FX1Poly.Typed.TypingContext profile scope}
    {subject reduct classifier : RawTerm scope},
    FX1Poly.Typed.WfContextDescPi context →
    FX1Poly.Typed.HasTypeDescPi profile context subject classifier →
    FX1Poly.Typed.StepTableBetaEtaRoot subject reduct →
    FX1Poly.Typed.HasTypeDescPi profile context reduct classifier

/-- **★ The ONE-SYSTEM grand sign-off HOLDS.**  Every field is the shipped named carrier:
`oneEngineSignoffHolds`, `step_iff_stepOver_fxIotaBundle`, `StepOver.fxBundlePathBetaFires`,
`StepOver.fxBundleEtaLamFires`, `StepOver.fxBundleEtaPairFires`,
`HasTypeDescPi.preservedByTableEtaRootNative`, `HasTypeDescPi.subjectReductionTableBetaEtaRootNative`.
FX's kernel is one signature + one reduction bundle + one typing union, every semantic fact a table
row — one checked object. -/
theorem oneSystemSignoffHolds {profile : PolyProfile} : OneSystemSignoff profile where
  oneTypingEngine := oneEngineSignoffHolds
  stepIsTheIotaBundle := step_iff_stepOver_fxIotaBundle
  betaFiresInTheBundle := StepOver.fxBundlePathBetaFires
  functionEtaFiresInTheBundle := StepOver.fxBundleEtaLamFires
  pairEtaFiresInTheBundle := StepOver.fxBundleEtaPairFires
  tableNativeEtaSubjectReduction := fun wellFormed typed rootStep =>
    FX1Poly.Typed.HasTypeDescPi.preservedByTableEtaRootNative wellFormed typed rootStep
  tableNativeBetaEtaUnionSubjectReduction := fun wellFormed typed unionStep =>
    FX1Poly.Typed.HasTypeDescPi.subjectReductionTableBetaEtaRootNative wellFormed typed unionStep

end FX1PolyAudit

-- ===== Per-declaration zero-axiom audit gates =====
-- ★ the one-system grand sign-off bundle + its inhabitant
#assert_no_axioms FX1PolyAudit.OneSystemSignoff
#assert_no_axioms FX1PolyAudit.oneSystemSignoffHolds
-- the eta-SR anchors (proof-term aliases, re-gated)
#assert_no_axioms FX1PolyAudit.oneSystemAnchor_etaTableSubjectReduction
#assert_no_axioms FX1PolyAudit.oneSystemAnchor_betaEtaRootUnionSubjectReduction
-- the cited carriers, re-verified zero-axiom at the bundle site
#assert_no_axioms FX1PolyAudit.oneEngineSignoffHolds
#assert_no_axioms FX1Poly.Core.step_iff_stepOver_fxIotaBundle
#assert_no_axioms FX1Poly.Core.StepOver.fxBundlePathBetaFires
#assert_no_axioms FX1Poly.Core.StepOver.fxBundleEtaLamFires
#assert_no_axioms FX1Poly.Core.StepOver.fxBundleEtaPairFires
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.preservedByTableEtaRootNative
#assert_no_axioms FX1Poly.Typed.HasTypeDescPi.subjectReductionTableBetaEtaRootNative
