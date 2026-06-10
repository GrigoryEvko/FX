import FX1Poly.Typed.UnitVariableCollapseDeep

/-! # FX1Poly/Typed/UnitVariableCollapseDeepSound
   — UNCONDITIONAL soundness of the binder-crossing collapse (ULC-4 brick C)

The spec gained its binder-crossing congruence arm (`ChildrenUnitEtaCong.consBinder`, threading
the SHARED preceding sibling — the shared-only threading that keeps `sym` provable), and this
module proves the deep collapse sound against it: every term is congruently unit-η-equal to its
binder-crossing collapse, in ANY context, with NO well-formedness hypothesis.

## The two-leg composition

A cell's children change in TWO ways (binder bodies collapse under the extension; shift-0 heads
collapse in the ambient context), but the spec's `consBinder` arm requires the domain SHARED —
so the proof routes through the bodies-only intermediate spine
(`collapseBinderBodiesOnlyChildren`: heads kept, binder bodies collapsed) and composes per cell
with the spec's `trans` rule:

    mkGen g p ch  ~[congGen leg1]~  mkGen g p (bodiesOnly ch)  ~[congGen leg2]~  deepCollapse cell

`leg1` relates each binder body to its collapse via `consBinder` (the head children are SHARED,
flowing through `consEqualZero`); `leg2` relates each shift-0 head to its collapse via `consZero`
(the binder bodies are now SHARED, kept by `consEqualHigher`).  At replacement sites the
`unitEta` leaf is justified by the `var` rule in the EXTENDED context — still no wf needed.

## What this module ships

  * `collapseBinderBodiesOnlyChildren` — the intermediate spine.
  * ★ `collapseUnitVariablesDeep_congruent` — deep soundness, UNCONDITIONAL.
  * `DefEqUnitEtaCong.ofDeepCollapsesEqual` — the deep syntactic-mode sound semi-decision
    (hypothesis-free, decidable by structural `DecidableEq`).
  * ★ `konstNormalForms_congruentlyEqual` — the βη normal forms that refuted normalize-first are
    now PROVED congruently equal through the deep canonicalizer (its computation + soundness) —
    the binder-fence pair is decided POSITIVELY by the deep procedure.

## Honest boundaries

Completeness of the deep canonicalizer remains the open brick — the congGen/normalization
commutation question stands; this module makes the deep procedure a SOUND semi-decision strictly
stronger than the fenced one (it additionally decides the binder-fence family).

## Zero-axiom verification

Three-way mutual structural recursion (term / leg1 / leg2 over the children spine), the shipped
leaf discipline at replacement sites, `trans`/`congGen` composition.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- The bodies-only intermediate spine: heads kept (still threaded as domain candidates), binder
bodies collapsed under the extension — the `trans` middle of the two-leg soundness. -/
def collapseBinderBodiesOnlyChildren {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    Option (RawTerm scope) → {shifts : List Nat} →
      RawTermChildren shifts scope → RawTermChildren shifts scope
  | _, _, .childNil => .childNil
  | _, _, @RawTermChildren.childCons _ 0 _ headChild restChildren =>
      .childCons headChild
        (collapseBinderBodiesOnlyChildren context (some headChild) restChildren)
  | some domainSibling, _, @RawTermChildren.childCons _ 1 _ bodyChild restChildren =>
      .childCons (collapseUnitVariablesDeep (context.cons domainSibling) bodyChild)
        (collapseBinderBodiesOnlyChildren context none restChildren)
  | none, _, @RawTermChildren.childCons _ 1 _ headChild restChildren =>
      .childCons headChild (collapseBinderBodiesOnlyChildren context none restChildren)
  | _, _, @RawTermChildren.childCons _ (_ + 2) _ headChild restChildren =>
      .childCons headChild (collapseBinderBodiesOnlyChildren context none restChildren)

mutual

/-- **★ Deep-collapse soundness — UNCONDITIONAL**: every term is congruently unit-η-equal to its
binder-crossing collapse, in ANY context, no well-formedness.  Replacement sites (including those
UNDER binders) discharge `unitEta` via the `var` rule in the local context; cells compose the
two legs through the bodies-only middle with the spec's `trans` rule. -/
theorem collapseUnitVariablesDeep_congruent {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    (term : RawTerm scope) →
      DefEqUnitEtaCong profile context term (collapseUnitVariablesDeep context term)
  | .mkGen generator payload children => by
      dsimp only [collapseUnitVariablesDeep]
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
        exact .trans
          (.congGen payload (collapseBinderBodiesLeg context none children))
          (.congGen payload (collapseHeadsLeg context none children))

/-- Leg 1: the original spine relates to the bodies-only spine — heads SHARED (flowing as domain
candidates via `consEqualZero`), binder bodies by `consBinder` + the term soundness in the
extended context. -/
theorem collapseBinderBodiesLeg {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    (previousShared : Option (RawTerm scope)) → {shifts : List Nat} →
      (children : RawTermChildren shifts scope) →
      ChildrenUnitEtaCong profile context previousShared shifts children
        (collapseBinderBodiesOnlyChildren context previousShared children)
  | _, _, .childNil => .nil
  | _, _, @RawTermChildren.childCons _ 0 _ headChild restChildren =>
      .consEqualZero (collapseBinderBodiesLeg context (some headChild) restChildren)
  | some domainSibling, _, @RawTermChildren.childCons _ 1 _ bodyChild restChildren =>
      .consBinder
        (collapseUnitVariablesDeep_congruent (context.cons domainSibling) bodyChild)
        (collapseBinderBodiesLeg context none restChildren)
  | none, _, @RawTermChildren.childCons _ 1 _ _headChild restChildren =>
      .consEqualHigher (collapseBinderBodiesLeg context none restChildren)
  | _, _, @RawTermChildren.childCons _ (_ + 2) _ _headChild restChildren =>
      .consEqualHigher (collapseBinderBodiesLeg context none restChildren)

/-- Leg 2: the bodies-only spine relates to the fully collapsed spine — shift-0 heads by
`consZero` + the term soundness, binder bodies now SHARED (`consEqualHigher`). -/
theorem collapseHeadsLeg {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    (functionPrevious : Option (RawTerm scope)) → {shifts : List Nat} →
      (children : RawTermChildren shifts scope) →
      ChildrenUnitEtaCong profile context none shifts
        (collapseBinderBodiesOnlyChildren context functionPrevious children)
        (collapseUnitVariablesDeepChildren context functionPrevious children)
  | _, _, .childNil => .nil
  | _, _, @RawTermChildren.childCons _ 0 _ headChild restChildren =>
      .consZero (collapseUnitVariablesDeep_congruent context headChild)
        (collapseHeadsLeg context (some headChild) restChildren)
  | some _domainSibling, _, @RawTermChildren.childCons _ 1 _ _bodyChild restChildren =>
      .consEqualHigher (collapseHeadsLeg context none restChildren)
  | none, _, @RawTermChildren.childCons _ 1 _ _headChild restChildren =>
      .consEqualHigher (collapseHeadsLeg context none restChildren)
  | _, _, @RawTermChildren.childCons _ (_ + 2) _ _headChild restChildren =>
      .consEqualHigher (collapseHeadsLeg context none restChildren)

end

/-- **Sound semi-decision, deep syntactic mode — UNCONDITIONAL**: equal deep collapses certify
the congruent equality (decidable by the structural `DecidableEq`, no hypotheses). -/
theorem DefEqUnitEtaCong.ofDeepCollapsesEqual {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {leftTerm rightTerm : RawTerm scope}
    (collapsesEqual : collapseUnitVariablesDeep context leftTerm
      = collapseUnitVariablesDeep context rightTerm) :
    DefEqUnitEtaCong profile context leftTerm rightTerm :=
  .trans (collapseUnitVariablesDeep_congruent context leftTerm)
    (collapsesEqual ▸ (collapseUnitVariablesDeep_congruent context rightTerm).sym)

/-- **★ The binder-fence pair is decided POSITIVELY by the deep procedure**: the βη normal forms
that refuted normalize-first are congruently equal — proved through the deep canonicalizer's
computation + soundness.  The deep semi-decision is strictly stronger than the fenced one. -/
theorem konstNormalForms_congruentlyEqual (profile : PolyProfile) :
    DefEqUnitEtaCong profile (unitVariableContext profile)
      konstAppliedToVariableNormalForm konstAppliedToUnitNormalForm :=
  DefEqUnitEtaCong.ofDeepCollapsesEqual (deepCollapse_identifiesKonstNormalForms profile)

end FX1Poly.Typed
