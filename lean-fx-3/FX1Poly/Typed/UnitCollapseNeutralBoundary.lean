import FX1Poly.Typed.UnitVariableCollapseDeepSound

/-! # FX1Poly/Typed/UnitCollapseNeutralBoundary
   — ★ the deep collapse is incomplete at COMPOUND unit-typed neutrals (ULC-4 brick D verdict)

The mandated re-analysis before building brick D, machine-checked.  Good news first: the deep
collapse ERASES both prior refutation witnesses — the β-surfacing redex and the binder-fence pair
both join after the deep collapse (the fence module proves the latter by `rfl`).  But
completeness still fails, at a boundary SIMPLER than either: the `unitEta` leaf relates a unit
VARIABLE to a COMPOUND unit-typed neutral, and the variable-only detection never touches the
latter.  Witness, in the context `(f : Π(_:Unit).Unit, x : Unit)`:

  * `x` and `app(f, x)` are both typed at `unitTypeCell` (the `var` rule; `piElim` of the
    variable `f` — the codomain instance computes to `unitTypeCell`), hence congruently
    unit-η-equal by ONE `unitEta` leaf.
  * Their deep collapses are `unitCell` and `app(f, unitCell)` — distinct, both βη-NORMAL, never
    joining.  Both comparison modes answer NO on a Cong-related pair.

## The brick-D verdict

Completeness of the congruent unit-η decider is EXACTLY the completeness of unit-typedness
DETECTION at replacement sites: variables are one decidable lookup (shipped); compound neutrals
require deciding `typed-at-unitTypeCell` for application spines — the whnf-directed checker in
check-mode against `unitTypeCell`, whose SOUNDNESS lives only on the route-H wf fragment (the
STR-5 refutation bars the raw relation: an unsound positive would break the collapse's soundness,
not just its completeness).  This is the checker entanglement deferred since ULC-1, now proved
unavoidable.  Equivalently: the full #481 type-directed readback (which carries the classifier
at every position by construction) is the natural home of the complete procedure — the unit
campaign's elimination chain ends by pointing exactly there.

## Honest scope notes

(1) The witness context is well-formable (the unit row + the Π-formation row both live in
`typingRuleDescOf`); the witness itself needs no wf — both typings are wf-free (`var` + `piElim`).
(2) All shipped soundness packages (fenced, deep, both comparison modes) remain intact — every
procedure stays a sound semi-decision; the deep one still strictly dominates the fenced one.

## Zero-axiom verification

The typings are `var`/`piElim` applications with `rfl`-computing lookups; the collapses compute
by `rfl`; non-joinability is the blocked-leaf discipline; inequalities by `decide` on closed
cells.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- The context `(f : Π(_:Unit).Unit, x : Unit)` — home of the compound unit-typed neutral
`app(f, x)`. -/
def unitFunctionContext (profile : PolyProfile) : TypingContext profile 2 :=
  ((TypingContext.empty : TypingContext profile 0).cons
    (piTyCodeCell unitTypeCell unitTypeCell)).cons unitTypeCell

/-- The compound unit-typed neutral `app(f, x)` — unit-typed but NOT a variable, so the
variable-only detection never collapses it. -/
def compoundUnitNeutral : RawTerm 2 :=
  appCell (variableCell ⟨1, Nat.le.refl⟩) (variableCell ⟨0, Nat.le.step Nat.le.refl⟩)

/-- The compound neutral is grown-typed at `unitTypeCell`: `piElim` of the variable `f` (typed at
its looked-up `Π(_:Unit).Unit`) applied to the variable `x` — the codomain instance computes to
`unitTypeCell`.  No well-formedness needed. -/
theorem compoundUnitNeutralTyped (profile : PolyProfile) :
    HasTypeDescPi profile (unitFunctionContext profile) compoundUnitNeutral unitTypeCell :=
  HasTypeDescPi.piElim
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (unitFunctionContext profile) ⟨1, Nat.le.refl⟩))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (unitFunctionContext profile) ⟨0, Nat.le.step Nat.le.refl⟩))

/-- **The unit variable and the compound unit-typed neutral are congruently unit-η-equal** — one
`unitEta` leaf, both sides typed at `unitTypeCell`. -/
theorem unitVariable_congruentlyEqual_compoundNeutral (profile : PolyProfile) :
    DefEqUnitEtaCong profile (unitFunctionContext profile)
      (variableCell ⟨0, Nat.le.step Nat.le.refl⟩) compoundUnitNeutral :=
  .ofDefEq (.unitEta
    (Or.inr (HasTypeDescPi.ofFormation
      (HasTypeDesc.var (unitFunctionContext profile) ⟨0, Nat.le.step Nat.le.refl⟩)))
    (Or.inr (compoundUnitNeutralTyped profile)))

/-- The deep collapses: the variable becomes `unitCell`; the compound neutral keeps its
application node (only its variable ARGUMENT collapses — `f`'s lookup is the Π code, not
`unitTypeCell`). -/
theorem deepCollapse_compoundUnitNeutral (profile : PolyProfile) :
    collapseUnitVariablesDeep (unitFunctionContext profile) compoundUnitNeutral
      = appCell (variableCell ⟨1, Nat.le.refl⟩) unitCell := rfl

/-- **The collapsed pair never βη-joins**: both sides are βη-normal (`app` of a variable to a
value has no rule; `unitCell` is a leaf) and distinct. -/
theorem collapsedCompoundNeutral_notBetaEtaConv_unitCell :
    ¬ BetaEtaConv (appCell (variableCell ⟨1, Nat.le.refl⟩) unitCell) (unitCell : RawTerm 2) := by
  intro convertible
  obtain ⟨commonTerm, neutralChain, unitChain⟩ := convertible
  have neutralEq :=
    Step.betaEtaStar.eq_of_noBetaEtaStep
      (RawTerm.reduceOnceBetaEta_complete (rfl :
        (appCell (variableCell ⟨1, Nat.le.refl⟩) unitCell : RawTerm 2).reduceOnceBetaEta
          = none))
      neutralChain
  have unitEq :=
    Step.betaEtaStar.eq_of_noBetaEtaStep
      (RawTerm.reduceOnceBetaEta_complete (rfl :
        (unitCell : RawTerm 2).reduceOnceBetaEta = none))
      unitChain
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator (neutralEq.trans unitEq.symm))

/-- **★ The deep procedure is INCOMPLETE at compound unit-typed neutrals**: a Cong-related pair
(one `unitEta` leaf — no β, no binder, the simplest possible gap) whose deep collapses are
distinct, βη-normal, and never join.  Both comparison modes answer NO.  Completeness of the
congruent unit-η decider IS the completeness of unit-typedness detection at replacement sites —
the checker entanglement, or equivalently the full type-directed readback. -/
theorem deepCollapseProcedure_isIncompleteAtCompoundNeutrals (profile : PolyProfile) :
    ∃ (leftTerm rightTerm : RawTerm 2),
      DefEqUnitEtaCong profile (unitFunctionContext profile) leftTerm rightTerm ∧
        collapseUnitVariablesDeep (unitFunctionContext profile) leftTerm
          ≠ collapseUnitVariablesDeep (unitFunctionContext profile) rightTerm ∧
        ¬ BetaEtaConv
            (collapseUnitVariablesDeep (unitFunctionContext profile) leftTerm)
            (collapseUnitVariablesDeep (unitFunctionContext profile) rightTerm) :=
  ⟨variableCell ⟨0, Nat.le.step Nat.le.refl⟩, compoundUnitNeutral,
    unitVariable_congruentlyEqual_compoundNeutral profile,
    fun collapsesEqual =>
      absurd
        (show (unitCell : RawTerm 2)
            = appCell (variableCell ⟨1, Nat.le.refl⟩) unitCell from collapsesEqual)
        (by decide),
    fun convertible =>
      collapsedCompoundNeutral_notBetaEtaConv_unitCell (BetaEtaConv.sym convertible)⟩

end FX1Poly.Typed
