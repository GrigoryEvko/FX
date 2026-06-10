import FX1Poly.Typed.UnitVariableCollapse

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

So `DefEqUnitEtaCong t u` holds while `¬ BetaEtaConv (collapse t) (collapse u)` — the βη
comparison after ONE collapse pass answers NO on a related pair.  (A fortiori the syntactic mode
is incomplete here too.)  The ULC-2 soundness theorems are untouched: positive answers remain
certificates; the procedure is a sound SEMI-decision.

## The corrected route (the campaign's next target)

Collapse and β-reduction do not commute one-pass: β SURFACES new collapse sites.  The corrected
canonicalizer must βη-NORMALIZE FIRST (typed SN supplies the normal form on the wf fragment),
THEN collapse: on the witness, `betaSurfacingRedex` βη-normalizes to `x`, and both sides then
collapse to `unitCell`.  Completeness of normalize-then-collapse is the remaining open brick
(it needs: collapse preserves βη-normality, and the canonicalizer argument over the spec's
`trans` rule).

## Zero-axiom verification

The typing is a concrete `piIntro`/`piElim` derivation over the #1205 unit-formation row; the
collapse computations are `rfl`; the non-joinability is the shipped leaf discipline
(`reduceOnceBetaEta_complete` at `rfl` + βη star-rigidity) plus a single-step characterization of
the collapsed redex (`cases` on the step; child positions refuted by the same leaf discipline,
root η refuted by head-generator clash).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
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
root β fires (children are βη-normal leaves, refuted by the reducer-completeness discipline; root
η is refuted by the head clash). -/
theorem collapsedBetaSurfacingRedex_step_eq {reduct : RawTerm 1}
    (step : Step.betaEta collapsedBetaSurfacingRedex reduct) :
    reduct = variableCell ⟨0, Nat.zero_lt_one⟩ := by
  cases step with
  | inl betaIotaStep =>
      cases betaIotaStep with
      | beta => rfl
      | cong gen payload childrenStep =>
          cases childrenStep with
          | here rest childStep =>
              exact absurd (Or.inl childStep)
                (RawTerm.reduceOnceBetaEta_complete (rfl :
                  (lamCell unitTypeCell (variableCell ⟨1, Nat.le.refl⟩) :
                    RawTerm 1).reduceOnceBetaEta = none) _)
          | there headChild tailStep =>
              cases tailStep with
              | here rest childStep =>
                  exact absurd (Or.inl childStep)
                    (RawTerm.reduceOnceBetaEta_complete (rfl :
                      (unitCell : RawTerm 1).reduceOnceBetaEta = none) _)
              | there headChild2 tailStep2 => cases tailStep2
  | inr etaStep => exact (noEtaFromAppHead etaStep rfl).elim

/-- **The collapses never βη-join**: the unit side is βη-normal (so any join lands at
`unitCell`), while every chain from the collapsed redex passes through `var₀` — and `var₀` is
βη-normal and distinct from `unitCell`. -/
theorem collapsedBetaSurfacingRedex_notBetaEtaConv_unitCell :
    ¬ BetaEtaConv collapsedBetaSurfacingRedex (unitCell : RawTerm 1) := by
  intro convertible
  obtain ⟨commonTerm, redexChain, unitChain⟩ := convertible
  have unitIsCommon : (unitCell : RawTerm 1) = commonTerm :=
    Step.betaEtaStar.eq_of_noBetaEtaStep
      (RawTerm.reduceOnceBetaEta_complete (rfl :
        (unitCell : RawTerm 1).reduceOnceBetaEta = none))
      unitChain
  cases redexChain with
  | refl _ =>
      exact Generator.noConfusion (congrArg RawTerm.headGenerator unitIsCommon.symm)
  | trans headStep tailChain =>
      have secondIsVar := collapsedBetaSurfacingRedex_step_eq headStep
      subst secondIsVar
      have varIsCommon : (variableCell ⟨0, Nat.zero_lt_one⟩ : RawTerm 1) = commonTerm :=
        Step.betaEtaStar.eq_of_noBetaEtaStep
          (RawTerm.reduceOnceBetaEta_complete (rfl :
            (variableCell ⟨0, Nat.zero_lt_one⟩ : RawTerm 1).reduceOnceBetaEta = none))
          tailChain
      exact Generator.noConfusion
        (congrArg RawTerm.headGenerator (varIsCommon.trans unitIsCommon.symm))

/-- **★ INCOMPLETENESS of the one-pass collapse-then-compare procedure**: a congruently
unit-η-equal pair whose collapses are NOT βη-convertible (a fortiori not equal).  β SURFACES
binder-hidden unit-variable occurrences after the collapse has passed.  The ULC-2 soundness is
untouched (positive answers certify); the procedure is a sound SEMI-decision, and completeness
requires the normalize-FIRST canonicalizer (the corrected route in the module docstring). -/
theorem unitEtaCongProcedure_isIncomplete (profile : PolyProfile) :
    ∃ (leftTerm rightTerm : RawTerm 1),
      DefEqUnitEtaCong profile (unitVariableContext profile) leftTerm rightTerm ∧
        ¬ BetaEtaConv
            (collapseUnitVariables (unitVariableContext profile) leftTerm)
            (collapseUnitVariables (unitVariableContext profile) rightTerm) :=
  ⟨betaSurfacingRedex, variableCell ⟨0, Nat.zero_lt_one⟩,
    betaSurfacingPair_congruentlyEqual profile,
    fun convertible => collapsedBetaSurfacingRedex_notBetaEtaConv_unitCell convertible⟩

end FX1Poly.Typed
