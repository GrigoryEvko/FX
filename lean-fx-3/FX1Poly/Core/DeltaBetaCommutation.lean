import FX1Poly.Core.DeltaRuleTable
import FX1Poly.Core.StepInversion
import FX1Poly.Core.GeneratorRedexHeadSoundness

/-! # DeltaBetaCommutation — RW-4: δ commutes with the canonical β/ι system

The δ-rule table (`DeltaRuleTable.lean`) is a STANDALONE sibling relation:
its redex is a nullary RESERVED-constant leaf (`gen_hyperreal` / `gen_qubit`),
structurally disjoint from every β/ι redex shape of the canonical `Step`.
This module proves the load-bearing consequence — **δ and the canonical
β/ι reduction never compete at the root** — and hence the δ-postponement /
commutation property the §6.8-style orthogonality argument needs.

## The structural fact

A canonical β/ι ROOT redex fires only on a LIVE redex head (`gen_app`
for β, the eliminators for ι — exactly `Generator.hasRedexHead = true`).
A δ-rule keys on a RESERVED constant head, for which
`hasRedexHead = false`.  So:

* a δ-redex cell is NOT a canonical root redex (`hasRootStepSource =
  false`), and — its constant heads being NULLARY — it is in fact a full
  canonical normal form (`¬ Step …`, the `no_step_from_unit` shape); and
* dually, a canonical β/ι root redex is never a δ-redex.

Therefore a term that δ-root-reduces does NOT β/ι-reduce at that cell:
the two single-step root relations have DISJOINT sources.  δ commutes
trivially over canonical reduction at the root — the postponement core.

## Why a SEPARATE module (not in `DeltaRuleTable.lean`)

Relating the δ relation to the canonical `Step` inherently imports the
canonical reduction substrate.  Keeping that dependency OUT of the
dependency-light δ-core file (`DeltaRuleTable.lean` imports only
`RawTermWeaken` + `Newman`) preserves the honesty discipline: the δ
relation's DEFINITION never mentions `Step`, so the constant heads stay
RESERVED in the canonical kernel (`GeneratorHonestyLedger` unchanged).
Commutation is a THEOREM about the two relations, not a wiring of δ into
`Step`.

## Zero-axiom

The canonical normal-form facts reuse the established `no_step_from_unit`
pattern (`Step.weakHeadOrChildCong` + `StepChildren.no_step_at_empty_spine`,
both `propext`-clean); the head-disjointness facts are `rfl` over the
`decide`-based `Generator.hasRedexHead` plus the zero-axiom
`hasRedexHead_false_imp_no_root_redex`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## The δ-redex cells are canonical β/ι normal forms

`gen_hyperreal` and `gen_qubit` are nullary RESERVED constants: their
cells head no β/ι redex AND carry no child to congruence-step, so the
canonical `Step` is empty out of them.  Same one-line shape as
`Step.no_step_from_unit`. -/

/-- **The `gen_hyperreal` δ-constant cell admits no canonical `Step`.** -/
theorem Step.no_step_from_hyperreal
    {scope : Nat} {target : RawTerm scope} :
    ¬ Step (.mkGen .gen_hyperreal () .childNil) target := by
  intro reduction
  cases Step.weakHeadOrChildCong reduction with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨_childrenAfter, _targetEq, childStep⟩ := congShape
      exact StepChildren.no_step_at_empty_spine childStep

/-- **The `gen_qubit` δ-constant cell admits no canonical `Step`.** -/
theorem Step.no_step_from_qubit
    {scope : Nat} {target : RawTerm scope} :
    ¬ Step (.mkGen .gen_qubit () .childNil) target := by
  intro reduction
  cases Step.weakHeadOrChildCong reduction with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨_childrenAfter, _targetEq, childStep⟩ := congShape
      exact StepChildren.no_step_at_empty_spine childStep

/-! ## The structural reason — δ heads are not redex heads

The head-level fact underlying the normal-form theorems: every δ-table
constant head has `Generator.hasRedexHead = false`, so a cell built on it
is not a canonical ROOT redex.  This is what makes δ disjoint from the
WHOLE β/ι table at once (each row, including any future row, keys on a
LIVE eliminator head). -/

/-- Each canonical-table δ-constant head is NOT a β/ι redex head. -/
theorem deltaConstantHead_notRedexHead {rule : DeltaRuleDesc}
    (isRow : rule ∈ deltaRuleTable) : rule.constantHead.hasRedexHead = false := by
  cases isRow with
  | head => rfl
  | tail _ isRow =>
      cases isRow with
      | head => rfl
      | tail _ isRow => cases isRow

/-- **A δ-redex cell heads no canonical β/ι ROOT redex.**  Any cell whose
head is a δ-table constant has `hasRootStepSource = false` — it cannot be
the source of a canonical root reduction (β nor any ι row), no matter what
payload/children it carries.  The general (any-scope, any-spine) form of
the two concrete normal-form pins above. -/
theorem deltaConstantCell_noRootStepSource {rule : DeltaRuleDesc}
    (isRow : rule ∈ deltaRuleTable) {scope : Nat}
    (payload : rule.constantHead.payload scope)
    (children : RawTermChildren rule.constantHead.binderShifts scope) :
    RawTerm.hasRootStepSource
      (.mkGen rule.constantHead payload children) = false :=
  hasRedexHead_false_imp_no_root_redex
    (deltaConstantHead_notRedexHead isRow) payload children

/-! ## The commutation core — δ-root and canonical-root are disjoint

The two single-step ROOT relations never both fire at one cell: a
δ-root-redex cell is a canonical normal form, so no canonical `Step`
competes.  Hence δ trivially POSTPONES over canonical β/ι reduction at the
root (and vice versa) — the orthogonality the §6.8 argument relies on. -/

/-- **`gen_hyperreal ↝ unit` faces no competing canonical step.**  The cell
that the `hyperrealDeltaRow` δ-unfolds is a canonical β/ι normal form:
δ and β/ι have disjoint root sources here. -/
theorem hyperrealDeltaRedex_canonicalNormal {scope : Nat} :
    ¬ ∃ canonicalTarget : RawTerm scope,
        Step (.mkGen .gen_hyperreal () .childNil) canonicalTarget := by
  intro ⟨_canonicalTarget, canonicalStep⟩
  exact Step.no_step_from_hyperreal canonicalStep

/-- **`gen_qubit ↝ gen_hyperreal` faces no competing canonical step.** -/
theorem qubitDeltaRedex_canonicalNormal {scope : Nat} :
    ¬ ∃ canonicalTarget : RawTerm scope,
        Step (.mkGen .gen_qubit () .childNil) canonicalTarget := by
  intro ⟨_canonicalTarget, canonicalStep⟩
  exact Step.no_step_from_qubit canonicalStep

/-- **★ Root commutation: δ-unfolding and canonical reduction never compete.**
A cell of δ-ROOT-redex shape (one of the two δ-constant cells of the
canonical table) admits NO canonical `Step` — so a δ root unfolding needs
no postponement past a β/ι root step: there is none.  The disjoint-sources
property that makes δ orthogonal to the β/ι system.  (Restricted to δ-ROOT
redexes by design: a δ-CONG step, firing inside a child, leaves the whole
cell free to canonically step elsewhere — only a δ-root redex is a
canonical normal form.) -/
theorem deltaRootRedex_noCanonicalStep {scope : Nat}
    {deltaSource : RawTerm scope}
    (isRootUnfolding :
      deltaSource = .mkGen .gen_hyperreal () .childNil
      ∨ deltaSource = .mkGen .gen_qubit () .childNil)
    {canonicalTarget : RawTerm scope}
    (canonicalStep : Step deltaSource canonicalTarget) : False := by
  cases isRootUnfolding with
  | inl hyperrealCell =>
      exact Step.no_step_from_hyperreal (hyperrealCell ▸ canonicalStep)
  | inr qubitCell =>
      exact Step.no_step_from_qubit (qubitCell ▸ canonicalStep)

/-- **Non-vacuity: δ fires exactly where the canonical system is stuck.**
The `gen_hyperreal` cell BOTH δ-unfolds (to `unit`) AND admits no canonical
`Step` — a concrete witness that δ reduction does genuine work at a β/ι
normal form, so the commutation/postponement above is not vacuous. -/
theorem hyperrealDeltaFiresAtCanonicalNormal {scope : Nat} :
    StepDeltaTable (scope := 0)
        (.mkGen .gen_hyperreal () .childNil)
        (.mkGen .gen_unit () .childNil)
      ∧ ¬ ∃ canonicalTarget : RawTerm scope,
          Step (.mkGen .gen_hyperreal () .childNil) canonicalTarget :=
  ⟨hyperrealDeltaRow_fires, hyperrealDeltaRedex_canonicalNormal⟩

end FX1Poly.Core
