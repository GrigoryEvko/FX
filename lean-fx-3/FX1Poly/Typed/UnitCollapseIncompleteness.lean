import FX1Poly.Typed.UnitVariableCollapse
import FX1Poly.Core.StepTable
import FX1Poly.Core.TableOneStepReducts
import FX1Poly.Core.IotaTableOrthogonality

/-! # FX1Poly/Typed/UnitCollapseIncompleteness
   — ★ the one-pass collapse-then-compare procedure is INCOMPLETE (ULC-3B verdict)

The β-surfacing phenomenon, machine-checked: a β-step can move unit-variable occurrences from
UNDER a binder (where the zero-shift collapse cannot see them) into collapse-reachable positions.
Witness, in the wf unit-variable context `(x : Unit)`:

  * `betaSurfacingRedex` := `app(lam(Unit, var₁), x)` — the body's `var₁` IS `x`, hidden under
    the lambda binder.  Grown-typed at `unitTypeCell` (the application's codomain instance), so
    it is congruently unit-η-equal to `x` by ONE `unitEta` leaf.
  * Its collapse only reaches the ARGUMENT: `collapse = app(lam(Unit, var₁), unitCell)`, whose
    sole βη-reduct is `var₀ = x` — while `collapse(x) = unitCell`.  The two collapses NEVER join
    (`x` and `unitCell` are distinct βη-normal forms reachable from the two sides).

So `DefEqUnitEtaCong t u` holds while `¬ ConvTableBetaEtaRoot (collapse t) (collapse u)` — the
table-native union conversion comparison after ONE collapse pass answers NO on a related pair.
(A fortiori the syntactic mode is incomplete here too.)  The ULC-2 soundness theorems are
untouched: positive answers remain certificates; the procedure is a sound SEMI-decision.

## The corrected route (the campaign's next target)

Collapse and β-reduction do not commute one-pass: β SURFACES new collapse sites.  The corrected
canonicalizer must βη-NORMALIZE FIRST (typed SN supplies the normal form on the wf fragment),
THEN collapse: on the witness, `betaSurfacingRedex` βη-normalizes to `x`, and both sides then
collapse to `unitCell`.  Completeness of normalize-then-collapse is the remaining open brick
(it needs: collapse preserves βη-normality, and the canonicalizer argument over the spec's
`trans` rule).

## Zero-axiom verification

The typing is a concrete `piIntro`/`piElim` derivation over the #1205 unit-formation row; the
collapse computations are `rfl`; the table-native non-convertibility characterizes the collapsed
redex's single union step via the computable reduct enumeration
(`oneStepReductsOverTable_complete` at `iotaRuleTable_isWf`, root eta blocked by
`fireRootEtaTableRedex?_blocksStep`), folds it into the reachability set by induction on the snoc
union chain, and collapses the union-normal `unitCell` leg by `unionStarEqOfNormal` (rigidity) —
the head/structure clash by `decide`.  (The retained bespoke `Step`-level characterization
`collapsedBetaSurfacingRedex_step_eq` / `noEtaFromAppHead` is the βη-relation twin, no longer on
the conversion critical path.)  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The β-surfacing redex `app(lam(Unit, var₁), x)` — the unit variable occurs BOTH as the
argument (collapse-reachable) and as the body's `var₁` (hidden under the binder). -/
def betaSurfacingRedex : RawTerm 1 :=
  appCell (lamCell unitTypeCell (variableCell ⟨1, Nat.le.refl⟩))
    (variableCell ⟨0, Nat.zero_lt_one⟩)

/-- The collapse of the β-surfacing redex: only the ARGUMENT is rewritten — the body's `var₁`
stays hidden under the binder. -/
def collapsedBetaSurfacingRedex : RawTerm 1 :=
  appCell (lamCell unitTypeCell (variableCell ⟨1, Nat.le.refl⟩)) unitCell

/-- The collapse computes exactly the argument rewrite (by `rfl`). -/
theorem collapse_betaSurfacingRedex (profile : PolyProfile) :
    collapseUnitVariables (unitVariableContext profile) betaSurfacingRedex
      = collapsedBetaSurfacingRedex := rfl

/-- **The redex is grown-typed at `unitTypeCell`**: `lam(Unit, var₁) : Π(_:Unit).Unit` by
`piIntro` over the #1205 unit-formation row, applied to the unit variable by `piElim` (the
codomain instance computes to `unitTypeCell`). -/
theorem betaSurfacingRedexTyped (profile : PolyProfile) :
    HasTypeDescPi profile (unitVariableContext profile) betaSurfacingRedex unitTypeCell :=
  HasTypeDescPi.piElim
    (HasTypeDescPi.piIntro LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard
      (HasTypeDescPi.ofFormation (unitTypeCellFormationTyped (unitVariableContext profile)))
      (HasTypeDescPi.ofFormation (unitTypeCellFormationTyped
        ((unitVariableContext profile).cons unitTypeCell)))
      (HasTypeDescPi.ofFormation
        (HasTypeDesc.var ((unitVariableContext profile).cons unitTypeCell) ⟨1, Nat.le.refl⟩)))
    (unitVariableTyped profile)

/-- **The pair IS congruently unit-η-equal**: both sides typed at `unitTypeCell`, one `unitEta`
leaf. -/
theorem betaSurfacingPair_congruentlyEqual (profile : PolyProfile) :
    DefEqUnitEtaCong profile (unitVariableContext profile)
      betaSurfacingRedex (variableCell ⟨0, Nat.zero_lt_one⟩) :=
  .ofDefEq (.unitEta (Or.inr (betaSurfacingRedexTyped profile))
    (Or.inr (unitVariableTyped profile)))

/-- Root η never fires at an `app`-headed cell — every η source is `lam`/`pair`/`pathLam`/
`modIntro`/`glueIntro`-headed. -/
theorem noEtaFromAppHead {scope : Nat} {sourceTerm reduct : RawTerm scope}
    (etaStep : Step.eta sourceTerm reduct)
    (sourceIsApp : RawTerm.headGenerator sourceTerm = Generator.gen_app) : False := by
  cases etaStep <;> exact Generator.noConfusion sourceIsApp

/-- **Single-step characterization of the collapsed redex**: its ONLY βη-reduct is `var₀` — the
root β fires (children are step-normal leaves, refuted by `reduceOnce_complete` +
`isStepNormalForm_blocks_step`; root η is refuted by the head clash). -/
theorem collapsedBetaSurfacingRedex_step_eq {reduct : RawTerm 1}
    (step : Step.betaEta collapsedBetaSurfacingRedex reduct) :
    reduct = variableCell ⟨0, Nat.zero_lt_one⟩ := by
  cases step with
  | inl betaIotaStep =>
      cases Step.weakHeadOrChildCong betaIotaStep with
      | inl weakHeadStep =>
        cases weakHeadStep with
        | beta => rfl
        | appCongruence functionStep =>
            cases functionStep with
            | rootIota iotaHead => cases iotaHead
        | rootIota iotaHead => cases iotaHead
      | inr congShape =>
          obtain ⟨childrenAfter, _targetEq, childrenStep⟩ := congShape
          cases childrenStep with
          | here rest childStep =>
              exact absurd childStep
                (RawTerm.isStepNormalForm_blocks_step
                  (RawTerm.reduceOnce_complete (rfl :
                    (lamCell unitTypeCell (variableCell ⟨1, Nat.le.refl⟩) :
                      RawTerm 1).reduceOnce = none)) _)
          | there headChild tailStep =>
              cases tailStep with
              | here rest childStep =>
                  exact absurd childStep
                    (RawTerm.isStepNormalForm_blocks_step
                      (RawTerm.reduceOnce_complete (rfl :
                        (unitCell : RawTerm 1).reduceOnce = none)) _)
              | there headChild2 tailStep2 => cases tailStep2
  | inr etaStep => exact (noEtaFromAppHead etaStep rfl).elim

/-- **Single union step characterization of the collapsed redex**: its ONLY
`StepTableBetaEtaRootUnion` reduct is `var₀` — the table-iota path-beta row is the sole firing
(witnessed by the computable reduct enumeration `oneStepReductsOverTable` listing exactly `[var₀]`,
the children being union-normal leaves), and a root table eta step is impossible (the firer halts
at `rfl` on the app head). -/
theorem collapsedBetaSurfacingRedex_unionStep_eq {reduct : RawTerm 1}
    (step : StepTableBetaEtaRootUnion collapsedBetaSurfacingRedex reduct) :
    reduct = variableCell ⟨0, Nat.zero_lt_one⟩ := by
  cases step with
  | inl iotaStep =>
      have listed := oneStepReductsOverTable_complete iotaRuleTable_isWf iotaStep
      have enumEq :
          oneStepReductsOverTable iotaRuleTable collapsedBetaSurfacingRedex
            = [variableCell ⟨0, Nat.zero_lt_one⟩] := rfl
      rw [enumEq] at listed
      cases listed with
      | head => rfl
      | tail _ memRest => nomatch memRest
  | inr etaStep =>
      exact absurd etaStep
        (RawTerm.fireRootEtaTableRedex?_blocksStep
          (rfl : collapsedBetaSurfacingRedex.fireRootEtaTableRedex? = none) reduct)

/-- **The reachability set of the collapsed redex**: every union reduct is the redex itself or
`var₀` — induction on the snoc union chain, the last step characterized by
`collapsedBetaSurfacingRedex_unionStep_eq` (from the redex) or blocked (from the union-normal
`var₀`). -/
theorem collapsedBetaSurfacingRedex_reachSet {reduct : RawTerm 1}
    (chain : UnionStar (StepTable (scope := 1)) StepEtaRootTable
      collapsedBetaSurfacingRedex reduct) :
    reduct = collapsedBetaSurfacingRedex ∨ reduct = variableCell ⟨0, Nat.zero_lt_one⟩ := by
  induction chain with
  | refl => exact Or.inl rfl
  | tailLeft _prefixChain leftStep prefixCase =>
      cases prefixCase with
      | inl atRedex =>
          subst atRedex
          exact Or.inr (collapsedBetaSurfacingRedex_unionStep_eq (Or.inl leftStep))
      | inr atVar =>
          subst atVar
          exact absurd (Or.inl leftStep)
            (fun unionStep =>
              RawTerm.reduceOnceTableBetaEtaRoot?_blocksStep
                (rfl : (variableCell ⟨0, Nat.zero_lt_one⟩ : RawTerm 1).reduceOnceTableBetaEtaRoot?
                  = none) unionStep)
  | tailRight _prefixChain rightStep prefixCase =>
      cases prefixCase with
      | inl atRedex =>
          subst atRedex
          exact Or.inr (collapsedBetaSurfacingRedex_unionStep_eq (Or.inr rightStep))
      | inr atVar =>
          subst atVar
          exact absurd (Or.inr rightStep)
            (fun unionStep =>
              RawTerm.reduceOnceTableBetaEtaRoot?_blocksStep
                (rfl : (variableCell ⟨0, Nat.zero_lt_one⟩ : RawTerm 1).reduceOnceTableBetaEtaRoot?
                  = none) unionStep)

/-- **The collapses never union-join**: the unit side is union-normal (so any common reduct IS
`unitCell` by rigidity), while every union reduct of the collapsed redex is the redex itself or
`var₀` — both head-distinct from `unitCell`.  Table-native (`ConvTableBetaEtaRoot`); the
characterization rests on `collapsedBetaSurfacingRedex_reachSet` + `unionStarEqOfNormal`. -/
theorem collapsedBetaSurfacingRedex_notConvTable_unitCell :
    ¬ ConvTableBetaEtaRoot collapsedBetaSurfacingRedex (unitCell : RawTerm 1) := by
  intro convertible
  obtain ⟨commonTerm, redexToCommon, unitToCommon⟩ := convertible
  have unitIsCommon : (unitCell : RawTerm 1) = commonTerm :=
    unionStarEqOfNormal
      (fun next unionStep =>
        RawTerm.reduceOnceTableBetaEtaRoot?_blocksStep
          (rfl : (unitCell : RawTerm 1).reduceOnceTableBetaEtaRoot? = none) unionStep)
      unitToCommon
  rw [← unitIsCommon] at redexToCommon
  cases collapsedBetaSurfacingRedex_reachSet redexToCommon with
  | inl reachesRedex => exact absurd reachesRedex (by decide)
  | inr reachesVar => exact absurd reachesVar (by decide)

/-- **★ INCOMPLETENESS of the one-pass collapse-then-compare procedure**: a congruently
unit-η-equal pair whose collapses are NOT βη-convertible (a fortiori not equal).  β SURFACES
binder-hidden unit-variable occurrences after the collapse has passed.  The ULC-2 soundness is
untouched (positive answers certify); the procedure is a sound SEMI-decision, and completeness
requires the normalize-FIRST canonicalizer (the corrected route in the module docstring). -/
theorem unitEtaCongProcedure_isIncomplete (profile : PolyProfile) :
    ∃ (leftTerm rightTerm : RawTerm 1),
      DefEqUnitEtaCong profile (unitVariableContext profile) leftTerm rightTerm ∧
        ¬ ConvTableBetaEtaRoot
            (collapseUnitVariables (unitVariableContext profile) leftTerm)
            (collapseUnitVariables (unitVariableContext profile) rightTerm) :=
  ⟨betaSurfacingRedex, variableCell ⟨0, Nat.zero_lt_one⟩,
    betaSurfacingPair_congruentlyEqual profile,
    fun convertible => collapsedBetaSurfacingRedex_notConvTable_unitCell convertible⟩

end FX1Poly.Typed
