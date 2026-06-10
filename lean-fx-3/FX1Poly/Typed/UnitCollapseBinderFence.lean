import FX1Poly.Typed.UnitCollapseIncompleteness

/-! # FX1Poly/Typed/UnitCollapseBinderFence
   — ★ the normalize-FIRST canonicalizer is ALSO incomplete: the binder fence (ULC-4 sub-spike)

`UnitCollapseIncompleteness` killed the one-pass procedure (β surfaces unit variables AFTER the
collapse).  The planned correction — βη-normalize FIRST, then collapse — dies on the SAME
phenomenon one level deeper: β can move the unit-difference UNDER A BINDER, where the zero-shift
collapse never looks, and where it persists IN the βη normal forms themselves.  Witness, in the
unit-variable context `(x : Unit)` with the constant double-lambda `konst := λ(a:Unit).λ(b:Unit).a`:

  * `app(konst, x)` and `app(konst, unitCell)` are congruently unit-η-equal — one `congGen`
    descent, the arguments related by `unitEta` at the ZERO-SHIFT argument position.
  * Their βη NORMAL FORMS are `λ(b:Unit). x↑` and `λ(b:Unit). unitCell` — the β-substitution
    carried the argument under the remaining binder.  Both are βη-normal, NOT βη-convertible,
    and BOTH are fixed by the zero-shift collapse (the difference sits in a binder child).

So `c := collapse ∘ betaEtaNormalForm` does NOT identify this Cong-related pair — under EITHER
comparison mode.  No binder-fenced canonicalizer can be complete for the congruent relation:
congruence injects the unit-difference at a zero-shift position, and β relocates it under a
binder before any traversal that stops at binders can erase it.

## The route consequence (the ULC-4 re-scope)

The complete canonicalizer MUST collapse under binders, which requires the extended context at
each binder child — per-generator binder-domain metadata (which child types each binder
position: `gen_lam`'s T2 domain child, `gen_piTyCode`'s domain for its codomain binder,
eliminator motives' scrutinee types, ...).  That table + the binder-crossing collapse IS the
type-directed traversal skeleton of the η-long readback (#481) — the unit story has reproduced
the general lesson exactly: type-directed normalization cannot be assembled from binder-fenced
raw machinery.

## Honest scope notes

(1) The refutation is against the relation AS SPECIFIED (endpoints need not be grown-typed —
the `unitEta` leaf accepts the data-intro typing of `unitCell`).  A completeness statement
restricted to BOTH-grown-typed endpoints dodges THIS witness only through an engine-separation
artifact (`app(konst, unitCell)` is grown-untypable today because data values are not grown
typed); it dies the moment data intros join the grown engine.  (2) The ULC-2/ULC-3A soundness
theorems remain untouched — both procedures stay sound semi-decisions.

## Zero-axiom verification

The Cong witness is one `congGen` + the shipped `unitEta` leaves; the β chains are single
`Step.beta` steps whose `subst0` reducts compute definitionally; normality and the
non-joinability reuse the `reduceOnceBetaEta_complete`-at-`rfl` + star-rigidity leaf discipline;
the inequalities are `decide` on concrete cells.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- The constant double-lambda `λ(a:Unit).λ(b:Unit).a` at scope 1 — the β that applies it
relocates its argument UNDER the remaining binder. -/
def konstUnitFunction : RawTerm 1 :=
  lamCell unitTypeCell
    (lamCell unitTypeCell (variableCell ⟨1, Nat.le.step Nat.le.refl⟩))

/-- The βη normal form of `app(konst, x)`: the unit VARIABLE, weakened under the surviving
binder — exactly where the zero-shift collapse cannot reach. -/
def konstAppliedToVariableNormalForm : RawTerm 1 :=
  lamCell unitTypeCell (variableCell ⟨1, Nat.le.refl⟩)

/-- The βη normal form of `app(konst, unitCell)`: the unit VALUE under the surviving binder. -/
def konstAppliedToUnitNormalForm : RawTerm 1 :=
  lamCell unitTypeCell unitCell

/-- **The applications are congruently unit-η-equal**: one `congGen` descent; the arguments are
the gap components (`unitEta`) at the ZERO-SHIFT argument position. -/
theorem konstApplications_congruentlyEqual (profile : PolyProfile) :
    DefEqUnitEtaCong profile (unitVariableContext profile)
      (appCell konstUnitFunction (variableCell ⟨0, Nat.zero_lt_one⟩))
      (appCell konstUnitFunction unitCell) :=
  DefEqUnitEtaCong.congGen (generator := Generator.gen_app) ()
    (.consEqualZero
      (.consZero
        (.ofDefEq (.unitEta (Or.inr (unitVariableTyped profile))
          (Or.inl (HasTypeDescDataIntro.unitValueTyped (unitVariableContext profile)))))
        .nil))

/-- The variable side β-reduces in ONE step to its normal form (the `subst0` reduct computes
definitionally to the binder-buried weakened variable). -/
theorem konstAppliedToVariable_normalizes :
    Step.betaEtaStar (appCell konstUnitFunction (variableCell ⟨0, Nat.zero_lt_one⟩))
      konstAppliedToVariableNormalForm :=
  Step.betaEtaStar.trans (Or.inl Step.beta) (Step.betaEtaStar.refl _)

/-- The unit side β-reduces in ONE step to its normal form. -/
theorem konstAppliedToUnit_normalizes :
    Step.betaEtaStar (appCell konstUnitFunction unitCell) konstAppliedToUnitNormalForm :=
  Step.betaEtaStar.trans (Or.inl Step.beta) (Step.betaEtaStar.refl _)

/-- **The two normal forms never βη-join** — both are βη-normal (the unit-difference sits under
the binder, out of every rule's reach) and they are distinct. -/
theorem konstNormalForms_notBetaEtaConv :
    ¬ BetaEtaConv konstAppliedToVariableNormalForm konstAppliedToUnitNormalForm := by
  intro convertible
  obtain ⟨commonTerm, variableSideChain, unitSideChain⟩ := convertible
  have variableSideEq :=
    Step.betaEtaStar.eq_of_noBetaEtaStep
      (RawTerm.reduceOnceBetaEta_complete (rfl :
        konstAppliedToVariableNormalForm.reduceOnceBetaEta = none))
      variableSideChain
  have unitSideEq :=
    Step.betaEtaStar.eq_of_noBetaEtaStep
      (RawTerm.reduceOnceBetaEta_complete (rfl :
        konstAppliedToUnitNormalForm.reduceOnceBetaEta = none))
      unitSideChain
  exact absurd (variableSideEq.trans unitSideEq.symm) (by decide)

/-- **The zero-shift collapse fixes BOTH normal forms** — the unit-difference is a binder child,
behind the fence — so the collapsed normal forms remain distinct. -/
theorem collapsedKonstNormalForms_distinct (profile : PolyProfile) :
    collapseUnitVariables (unitVariableContext profile) konstAppliedToVariableNormalForm
      ≠ collapseUnitVariables (unitVariableContext profile) konstAppliedToUnitNormalForm :=
  fun collapsesEqual =>
    absurd
      (show konstAppliedToVariableNormalForm = konstAppliedToUnitNormalForm from collapsesEqual)
      (by decide)

/-- **★ The normalize-FIRST canonicalizer is INCOMPLETE — the binder fence**: a congruently
unit-η-equal pair whose βη normal forms are reached by explicit chains, are βη-normal, are FIXED
by the zero-shift collapse, and are neither equal after collapse nor βη-convertible.  Any
canonicalizer that βη-normalizes (in any order, any number of passes) and collapses only at
zero-shift positions answers NO on this Cong-related pair.  Completeness requires collapsing
UNDER binders — the per-generator binder-domain table, the true #481 type-directed readback
skeleton. -/
theorem normalizeFirstCanonicalizer_isIncomplete (profile : PolyProfile) :
    ∃ (leftTerm rightTerm leftNormalForm rightNormalForm : RawTerm 1),
      DefEqUnitEtaCong profile (unitVariableContext profile) leftTerm rightTerm ∧
      Step.betaEtaStar leftTerm leftNormalForm ∧
      (∀ reduct : RawTerm 1, ¬ Step.betaEta leftNormalForm reduct) ∧
      Step.betaEtaStar rightTerm rightNormalForm ∧
      (∀ reduct : RawTerm 1, ¬ Step.betaEta rightNormalForm reduct) ∧
      collapseUnitVariables (unitVariableContext profile) leftNormalForm
        ≠ collapseUnitVariables (unitVariableContext profile) rightNormalForm ∧
      ¬ BetaEtaConv leftNormalForm rightNormalForm :=
  ⟨appCell konstUnitFunction (variableCell ⟨0, Nat.zero_lt_one⟩),
    appCell konstUnitFunction unitCell,
    konstAppliedToVariableNormalForm, konstAppliedToUnitNormalForm,
    konstApplications_congruentlyEqual profile,
    konstAppliedToVariable_normalizes,
    RawTerm.reduceOnceBetaEta_complete (rfl :
      konstAppliedToVariableNormalForm.reduceOnceBetaEta = none),
    konstAppliedToUnit_normalizes,
    RawTerm.reduceOnceBetaEta_complete (rfl :
      konstAppliedToUnitNormalForm.reduceOnceBetaEta = none),
    collapsedKonstNormalForms_distinct profile,
    konstNormalForms_notBetaEtaConv⟩

end FX1Poly.Typed
