import FX1Poly.Core.Normalize
import FX1Poly.Core.StronglyNormalizingSubst
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

The first two deciders conclude about the *closing substitution* `RawTerm.subst substitution …` rather than
the bare terms: the FT's reducibility candidate is stated under a substitution into a non-empty scope (the
fresh-variable demand of the arrow case's CR1), so SN — and hence the decision — lands on the substituted
forms.  The third decider removes that wart for closed terms.

* `Conv.decidableOfSimplyTypedUnderSubst` — general: two terms typed in the same context, a closing
  substitution, and a reducible environment for it.
* `Conv.decidableOfSimplyTypedClosed` — two closed simply-typed terms and any closing substitution; the
  environment is vacuously reducible, so typing alone decides Conv (of the substituted forms).
* `Conv.decidableOfSimplyTypedBareClosed` — the headline: decidable conversion of the *bare* closed terms
  themselves, no substitution wart.  `StepStar.stronglyNormalizing_of_subst` pulls the FT's SN-of-substituted
  back to SN-of-bare, so the decider runs on the original `RawTerm 0` terms.  This is the cleanest statement
  of "the simply-typed fragment has decidable conversion": two closed simply-typed terms, typing alone
  decides whether they convert, with strong normalization PROVEN (no hypothesis, no substitution).

## Zero-axiom verification

Pure composition: `Conv.decidableOfStronglyNormalizing` applied to `SimplyTypedTermLF.stronglyNormalizing*`
(and, for the bare variant, threaded through `StepStar.stronglyNormalizing_of_subst`).  The FT's
`IsStronglyNormalizing` is `StepStar.IsStronglyNormalizing` (the `Acc StepSuccessor` the decider consumes),
so the witnesses match with no glue.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
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

/-- The canonical closing substitution from the empty scope into scope 1: there are no source variables, so
the empty function `Fin.elim0` is the unique substitution `RawTermSubst 0 1`.  It supplies the non-empty
target scope the fundamental theorem demands while substituting nothing into a closed term. -/
def emptyClosingSubst : RawTermSubst 0 1 := Fin.elim0

/-- **Decidable conversion for bare closed simply-typed terms.**  Two closed simply-typed terms have
decidable conversion with NO substitution wart and NO strong-normalization hypothesis: the fundamental
theorem gives strong normalization of each term closed by `emptyClosingSubst`, and
`StepStar.stronglyNormalizing_of_subst` reflects that back to strong normalization of the bare terms, which
the normalizer's decider then consumes directly.  Typing alone decides convertibility of the originals. -/
def Conv.decidableOfSimplyTypedBareClosed {profile : PolyProfile}
    {firstTerm firstType secondTerm secondType : RawTerm 0}
    (firstTyped : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) firstTerm firstType)
    (secondTyped : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) secondTerm secondType) :
    Decidable (Conv firstTerm secondTerm) :=
  Conv.decidableOfStronglyNormalizing
    (StepStar.stronglyNormalizing_of_subst emptyClosingSubst firstTerm
      (firstTyped.stronglyNormalizingClosed emptyClosingSubst))
    (StepStar.stronglyNormalizing_of_subst emptyClosingSubst secondTerm
      (secondTyped.stronglyNormalizingClosed emptyClosingSubst))

end FX1Poly.Typed
