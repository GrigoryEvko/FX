import FX1Poly.Typed.ClosedStronglyNormalizing
import FX1Poly.Typed.UntypedOmegaNotStronglyNormalizing

/-! # Foundation/PolyCell/Typed/TypedFragmentAcyclicity
    — typing rules out non-termination: Ω is untypable, and typed reduction is acyclic

`UntypedOmegaNotStronglyNormalizing.lean` proves that the raw (untyped) Ω
combinator β-steps to itself and is therefore not strongly normalizing — and
remarks, in prose, that Ω is untypable.  This file discharges that remark as a
THEOREM and draws the corollary for the whole typed fragment.

The lever is SN-043 (`HasTypeDescPi.closedStronglyNormalizing`): every closed
well-typed term is strongly normalizing.  Contrapositively:

  * `omegaCombinator_notClosedWellTyped` — Ω has NO closed type.  Were it typed,
    SN-043 would make it strongly normalizing, but it is not.  So the typing
    rules genuinely REJECT the non-terminating Ω; its untypability is proven, not
    observed.
  * `closedWellTypedTerm_notStepSelfLoop` — more generally, no closed well-typed
    term β-steps to itself.  A self-loop makes a term non-accessible under the
    one-step-successor relation (`accessibleElementNotSelfRelated`), contradicting
    its strong normalization.  Typed reduction is acyclic.

`typingRulesOutSelfLooping` packages the contrast: a self-looping closed term (Ω)
exists and is untypable, while every closed well-typed term has no self-loop —
typing is exactly what separates the two.  This is the concrete face of "typing
guarantees termination": the prototypical divergence is the prototypical
ill-typed term.

Zero-axiom: SN-043 + the firing-`UntypedOmega` facts (`omegaCombinator`'s
self-step and non-SN, the `accessibleElementNotSelfRelated` "an accessible
element cannot self-relate" lemma).
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open StepStar

/-- No closed well-typed term β-steps to itself: typed reduction is acyclic.
A self-loop would make the term non-accessible under the one-step-successor
relation, contradicting SN-043 (`closedStronglyNormalizing`). -/
theorem closedWellTypedTerm_notStepSelfLoop
    {profile : PolyProfile} {subject classifier : RawTerm 0}
    (typing : HasTypeDescPi profile TypingContext.empty subject classifier) :
    ¬ Step subject subject :=
  fun stepSelf =>
    accessibleElementNotSelfRelated
      (HasTypeDescPi.closedStronglyNormalizing typing) stepSelf

/-- ★ Ω is NOT closed-well-typed: no type classifies it.  Were it typed, SN-043
would make it strongly normalizing, but Ω is not (it β-steps to itself forever).
So the typing rules genuinely REJECT the non-terminating Ω — its untypability is
a theorem, not an observation. -/
theorem omegaCombinator_notClosedWellTyped {profile : PolyProfile} :
    ¬ ∃ classifier : RawTerm 0,
      HasTypeDescPi profile TypingContext.empty omegaCombinator classifier :=
  fun ⟨_classifier, typing⟩ =>
    omegaCombinator_notStronglyNormalizing
      (HasTypeDescPi.closedStronglyNormalizing typing)

/-- The contrast, packaged: there is a closed term (Ω) that β-self-loops and is
untypable, while every closed well-typed term has no self-loop.  Typing is what
separates the two — the prototypical divergence is the prototypical ill-typed
term. -/
theorem typingRulesOutSelfLooping {profile : PolyProfile} :
    (∃ selfLooper : RawTerm 0,
      Step selfLooper selfLooper ∧
      ¬ ∃ classifier, HasTypeDescPi profile TypingContext.empty selfLooper classifier) ∧
    (∀ (subject classifier : RawTerm 0),
      HasTypeDescPi profile TypingContext.empty subject classifier →
        ¬ Step subject subject) :=
  ⟨⟨omegaCombinator, omegaCombinator_betaSelfStep, omegaCombinator_notClosedWellTyped⟩,
    fun _ _ typing => closedWellTypedTerm_notStepSelfLoop typing⟩

end FX1Poly.Typed
