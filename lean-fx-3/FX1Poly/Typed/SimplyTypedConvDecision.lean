import FX1Poly.Core.Normalize
import FX1Poly.Typed.SimplyTypedTermFundamentalLevelFree

/-! # FX1Poly/Typed/SimplyTypedConvDecision
    — decidable conversion for the simply-typed fragment, with the strong-normalization hypothesis
      DISCHARGED by the fundamental theorem.

`Core/Normalize.lean` shipped `Conv.decidableOfStronglyNormalizing`: two `IsStronglyNormalizing` terms have
a decidable conversion (normalize each, compare normal forms).  But it still *takes* the SN proofs as
hypotheses — and raw `Step` is not globally strongly normalizing, so SN cannot be supplied for an arbitrary
raw term.

The simply-typed level-free fundamental theorem (`SimplyTypedTermLF.stronglyNormalizing*`) supplies exactly
those proofs for the typed fragment: every simply-typed term is strongly normalizing (Tait reducibility).
Composing the two — the normalizer's decider fed by the FT's SN — gives decidable conversion on the
simply-typed fragment with NO SN hypothesis: typing alone decides convertibility.  This is the first point
in the development where `Decidable (Conv …)` holds with strong normalization *proven* rather than assumed,
joining the two completed lines (the fundamental theorem and the weak-normalization normalizer).

The conclusion is about the *closing substitution* `RawTerm.subst substitution …` rather than the bare
terms: the FT's reducibility candidate is stated under a substitution into a non-empty scope (the
fresh-variable demand of the arrow case's CR1), so SN — and hence the decision — lands on the substituted
forms.

* `Conv.decidableOfSimplyTypedUnderSubst` — general: two terms typed in the same context, a closing
  substitution, and a reducible environment for it.
* `Conv.decidableOfSimplyTypedClosed` — the headline: two closed simply-typed terms and any closing
  substitution; the environment is vacuously reducible, so typing alone decides Conv.

## Zero-axiom verification

Pure composition: `Conv.decidableOfStronglyNormalizing` applied to `SimplyTypedTermLF.stronglyNormalizing*`.
The FT's `IsStronglyNormalizing` is `StepStar.IsStronglyNormalizing` (the `Acc StepSuccessor` the decider
consumes), so the witnesses match with no glue.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **Decidable conversion for simply-typed terms under a closing substitution.**  Two terms typed in the
same context convert decidably once closed by a reducible substitution — the fundamental theorem discharges
both strong-normalization obligations the decider needs. -/
def Conv.decidableOfSimplyTypedUnderSubst {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {firstTerm firstType secondTerm secondType : RawTerm scope}
    (firstTyped : SimplyTypedTermLF context firstTerm firstType)
    (secondTyped : SimplyTypedTermLF context secondTerm secondType)
    {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    (envReducible : ReducibleEnv context substitution) :
    Decidable (Conv (RawTerm.subst substitution firstTerm) (RawTerm.subst substitution secondTerm)) :=
  Conv.decidableOfStronglyNormalizing
    (firstTyped.stronglyNormalizingUnderSubst substitution envReducible)
    (secondTyped.stronglyNormalizingUnderSubst substitution envReducible)

/-- **Decidable conversion for closed simply-typed terms.**  Typing alone decides convertibility of two
closed simply-typed terms (under any closing substitution): the empty environment is vacuously reducible,
so the fundamental theorem supplies both SN proofs with no further hypotheses. -/
def Conv.decidableOfSimplyTypedClosed {profile : PolyProfile} {targetScope : Nat}
    {firstTerm firstType secondTerm secondType : RawTerm 0}
    (firstTyped : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) firstTerm firstType)
    (secondTyped : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) secondTerm secondType)
    (substitution : RawTermSubst 0 (targetScope + 1)) :
    Decidable (Conv (RawTerm.subst substitution firstTerm) (RawTerm.subst substitution secondTerm)) :=
  Conv.decidableOfStronglyNormalizing
    (firstTyped.stronglyNormalizingClosed substitution)
    (secondTyped.stronglyNormalizingClosed substitution)

end FX1Poly.Typed
