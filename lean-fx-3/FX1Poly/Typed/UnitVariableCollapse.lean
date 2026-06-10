import FX1Poly.Typed.UnitEtaCongruentEquality

/-! # FX1Poly/Typed/UnitVariableCollapse
   — the computable unit-collapse (variable fragment) + UNCONDITIONAL congruence soundness (ULC-2)

The first computable canonicalizer for the congruent unit-η equality: a term-structural traversal
replacing every unit-typed VARIABLE (a `gen_var` leaf whose context lookup is `unitTypeCell`) with
the unit value `unitCell`, descending through shift-0 child positions and leaving binder children
untouched — exactly the `DefEqUnitEtaCong` zero-shift fence.

## Why VARIABLES, and why no checker

ULC-2's planned classifier supply was check-mode via the whnf-directed grown checker (route-H wf
fragment).  The variable fragment makes that machinery unnecessary: whether a variable is
unit-typed is ONE decidable context-lookup comparison, and the replacement is sound
UNCONDITIONALLY — the `var` rule types the variable at its looked-up type in ANY context, no
well-formedness needed.  And by `dataIntroUnitPairsCollapseToRefl`, the strict content of unit-η
lives at open unit-typed NEUTRALS — variables are the canonical case.  Compound unit-typed
neutrals (`f x : Unit` for `f : A -> Unit`) DO need the checker; that extension is the named
follow-on, and it inherits this module's soundness skeleton (only the detection predicate at the
replacement site changes).

## What this module ships

  * `collapseUnitVariables` / `collapseUnitVariablesChildren` — the mutual computable traversal.
  * ★ `collapseUnitVariables_congruent` — soundness, UNCONDITIONAL: every term is congruently
    unit-η-equal to its collapse, in any context, with no well-formedness hypothesis (each
    replacement site discharges `unitEta` with the `var` typing + `unitValueTyped`; everything
    else is congruence / reflexivity).
  * ★ `collapseUnitVariables_computesGapPair` — the canonicalizer COMPUTES the gap:
    `collapse pair(x,x) = pair(unit,unit)` by `rfl` at the unit-variable context.
  * `collapse_rederivesGapPair` — the computed collapse + soundness REDERIVE the hand-built
    `gapPairCongruentlyEqual` witness: the canonicalizer route and the spec route agree.

## Honest boundaries

(1) Variables only: a compound unit-typed neutral is NOT collapsed (needs the checker-directed
detection — the named follow-on); the traversal is still SOUND, just not maximal.  (2) Zero-shift
positions only (binder children untouched), matching the spec's `consEqual` fence.  (3) This is
the canonicalizer HALF of the congruent decider; the compare half (collapse-then-βη-compare) and
the completeness/transitivity payoff are the follow-on bricks.

## Zero-axiom verification

Mutual structural recursion (term ↔ children spine), decidable-equality branching, the `var`
typing rule + `unitValueTyped` at replacement sites.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

mutual

/-- **The unit-variable collapse**: replace every unit-typed variable (context lookup =
`unitTypeCell`) with `unitCell`; descend through shift-0 children; leave binder children
untouched. -/
def collapseUnitVariables {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) : RawTerm scope → RawTerm scope
  | .mkGen generator payload children =>
      if isVariable : generator = Generator.gen_var then
        if (context.lookup
            (Eq.rec (motive := fun targetGenerator _ => targetGenerator.payload scope)
              payload isVariable)) = unitTypeCell then
          unitCell
        else
          .mkGen generator payload children
      else
        .mkGen generator payload (collapseUnitVariablesChildren context children)

/-- Children traversal: collapse shift-0 heads, keep binder heads, recurse on the spine. -/
def collapseUnitVariablesChildren {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    {shifts : List Nat} → RawTermChildren shifts scope → RawTermChildren shifts scope
  | _, .childNil => .childNil
  | _, @RawTermChildren.childCons _ 0 _ headChild restChildren =>
      .childCons (collapseUnitVariables context headChild)
        (collapseUnitVariablesChildren context restChildren)
  | _, @RawTermChildren.childCons _ (_ + 1) _ headChild restChildren =>
      .childCons headChild (collapseUnitVariablesChildren context restChildren)

end

mutual

/-- **★ Collapse soundness — UNCONDITIONAL**: every term is congruently unit-η-equal to its
unit-variable collapse, in ANY context, with NO well-formedness hypothesis.  Replacement sites
discharge `unitEta` with the `var` rule (which needs no wf) + `unitValueTyped`; everything else
is congruence or reflexivity. -/
theorem collapseUnitVariables_congruent {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    (term : RawTerm scope) →
      DefEqUnitEtaCong profile context term (collapseUnitVariables context term)
  | .mkGen generator payload children => by
      dsimp only [collapseUnitVariables]
      by_cases isVariable : generator = Generator.gen_var
      · rw [dif_pos isVariable]
        subst isVariable
        by_cases isUnitBinding : context.lookup payload = unitTypeCell
        · rw [if_pos isUnitBinding]
          rw [RawTermChildren.eq_childNil children]
          exact .ofDefEq (.unitEta
            (Or.inr (HasTypeDescPi.ofFormation
              (isUnitBinding ▸ HasTypeDesc.var context payload)))
            (Or.inl (HasTypeDescDataIntro.unitValueTyped context)))
        · rw [if_neg isUnitBinding]
          exact DefEqUnitEtaCong.refl _
      · rw [dif_neg isVariable]
        exact .congGen payload (collapseUnitVariablesChildren_congruent context children)

/-- Children soundness: shift-0 heads by the term soundness, binder heads by `consEqualHigher`
(the fenced collapse leaves them untouched). -/
theorem collapseUnitVariablesChildren_congruent {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    {shifts : List Nat} → (children : RawTermChildren shifts scope) →
      ChildrenUnitEtaCong profile context none shifts children
        (collapseUnitVariablesChildren context children)
  | _, .childNil => .nil
  | _, @RawTermChildren.childCons _ 0 _ headChild restChildren =>
      .consZero (collapseUnitVariables_congruent context headChild)
        (collapseUnitVariablesChildren_congruent context restChildren)
  | _, @RawTermChildren.childCons _ (_ + 1) _ _headChild restChildren =>
      .consEqualHigher (collapseUnitVariablesChildren_congruent context restChildren)

end

/-- **★ The canonicalizer COMPUTES the gap pair**: at the unit-variable context, the collapse of
`pair(x,x)` IS `pair(unit,unit)` — by `rfl` (the lookup, the decidable comparison, and the
traversal all reduce). -/
theorem collapseUnitVariables_computesGapPair (profile : PolyProfile) :
    collapseUnitVariables (unitVariableContext profile) pairOfUnitVariables
      = pairOfUnitValues := rfl

/-- The computed collapse + soundness REDERIVE the hand-built spec witness: the canonicalizer
route and the `gapPairCongruentlyEqual` constructor route agree on the gap pair. -/
theorem collapse_rederivesGapPair (profile : PolyProfile) :
    DefEqUnitEtaCong profile (unitVariableContext profile)
      pairOfUnitVariables pairOfUnitValues :=
  collapseUnitVariables_computesGapPair profile ▸
    collapseUnitVariables_congruent (unitVariableContext profile) pairOfUnitVariables

/-! ## The decision procedure's SOUNDNESS — collapse, then compare

Two comparison modes, both composing through the collapsed middle via the spec's `trans` rule:

  * SYNTACTIC equality of the collapses — UNCONDITIONAL (decidable by the structural
    `DecidableEq RawTerm`, no typing, no wf).  This mode already decides the gap pair: both
    collapses compute to `pair(unit, unit)`.
  * βη-conversion of the collapses — on the wf fragment with the COLLAPSED terms grown-typed at a
    shared classifier (the #1202 `BetaEtaConv.decidableOfWfTyped` decides it).  The collapsed
    typings are HYPOTHESES, not derived: the collapse does NOT preserve typing at the same
    classifier (replacing `x` by `unitCell` inside a dependent classifier `B[x]` moves the type
    by the congruent equality itself, not by `Conv`) — typing preservation under congruent
    equality is the conversion-rule question, deliberately out of scope here.

COMPLETENESS (a negative comparison refutes the relation) is the genuinely hard half — it needs
the collapse/βη commutation — and remains the named open brick of the campaign. -/

/-- **Sound semi-decision, syntactic mode — UNCONDITIONAL**: if the collapses are EQUAL, the
terms are congruently unit-η-equal.  Decidable with no hypotheses at all. -/
theorem DefEqUnitEtaCong.ofCollapsesEqual {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {leftTerm rightTerm : RawTerm scope}
    (collapsesEqual :
      collapseUnitVariables context leftTerm = collapseUnitVariables context rightTerm) :
    DefEqUnitEtaCong profile context leftTerm rightTerm :=
  .trans (collapseUnitVariables_congruent context leftTerm)
    (collapsesEqual ▸ (collapseUnitVariables_congruent context rightTerm).sym)

/-- **Sound semi-decision, βη mode**: if the collapses are βη-convertible — with the context
well-formed and both COLLAPSED terms grown-typed at a shared classifier — the original terms are
congruently unit-η-equal.  The comparison itself is decided by the #1202 βη decider under the
same hypotheses. -/
theorem DefEqUnitEtaCong.ofCollapsedBetaEtaConv {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {leftTerm rightTerm : RawTerm scope}
    {sharedClassifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (leftCollapsedTyped : HasTypeDescPi profile context
      (collapseUnitVariables context leftTerm) sharedClassifier)
    (rightCollapsedTyped : HasTypeDescPi profile context
      (collapseUnitVariables context rightTerm) sharedClassifier)
    (collapsesConvertible : BetaEtaConv
      (collapseUnitVariables context leftTerm) (collapseUnitVariables context rightTerm)) :
    DefEqUnitEtaCong profile context leftTerm rightTerm :=
  .trans (collapseUnitVariables_congruent context leftTerm)
    (.trans
      (.ofDefEq (.ofBetaEtaConv contextWellFormed leftCollapsedTyped rightCollapsedTyped
        collapsesConvertible))
      ((collapseUnitVariables_congruent context rightTerm).sym))

/-- The collapsed βη comparison is DECIDABLE under the βη-mode hypotheses (the #1202 decider on
the collapsed pair) — together with `ofCollapsedBetaEtaConv`, the positive branch certifies the
congruent equality. -/
def DefEqUnitEtaCong.collapsedComparisonDecidable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {leftTerm rightTerm : RawTerm scope}
    {sharedClassifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (leftCollapsedTyped : HasTypeDescPi profile context
      (collapseUnitVariables context leftTerm) sharedClassifier)
    (rightCollapsedTyped : HasTypeDescPi profile context
      (collapseUnitVariables context rightTerm) sharedClassifier) :
    Decidable (BetaEtaConv
      (collapseUnitVariables context leftTerm) (collapseUnitVariables context rightTerm)) :=
  BetaEtaConv.decidableOfWfTyped contextWellFormed leftCollapsedTyped rightCollapsedTyped

/-- **★ The procedure decides the gap pair in syntactic mode, hypothesis-free**: both collapses
compute to `pair(unit, unit)` (`pair(unit, unit)` itself is collapse-invariant — its components
are values, not variables), so `ofCollapsesEqual rfl` rederives the gap witness through the
DECISION PROCEDURE — the third independent derivation of the flagship congruent pair. -/
theorem unitEtaCongProcedure_decidesGapPair (profile : PolyProfile) :
    DefEqUnitEtaCong profile (unitVariableContext profile)
      pairOfUnitVariables pairOfUnitValues :=
  DefEqUnitEtaCong.ofCollapsesEqual rfl

end FX1Poly.Typed
