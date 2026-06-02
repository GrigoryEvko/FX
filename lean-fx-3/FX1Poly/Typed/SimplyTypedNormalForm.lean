import FX1Poly.Core.Normalize
import FX1Poly.Core.NormalizeMeta
import FX1Poly.Core.StronglyNormalizingSubst
import FX1Poly.Typed.SimplyTypedConvDecision

/-! # FX1Poly/Typed/SimplyTypedNormalForm
    — the computable canonical normal form of a closed simply-typed term.

`SimplyTypedConvDecision.lean` shipped `Conv.decidableOfSimplyTypedBareClosed`: typing alone DECIDES whether
two closed simply-typed terms convert.  This file ships the NORMALIZE companion to that DECIDE — it extracts
the canonical normal form itself and proves its characterizing properties.

The bridge is `stronglyNormalizing_of_subst`: the fundamental theorem supplies strong normalization of the
term closed by `emptyClosingSubst` (its reducibility candidate lives under a substitution into a non-empty
scope), and the reflection lemma pulls that back to strong normalization of the BARE term.  With bare SN in
hand, the WN-grind normalizer (`RawTerm.normalize`) runs on the original `RawTerm 0`.

* `SimplyTypedTermLF.stronglyNormalizingBare` — every closed simply-typed term is strongly normalizing, the
  bare statement (the SN companion to the bare-closed decider; the single use site of
  `stronglyNormalizing_of_subst`).
* `SimplyTypedTermLF.normalForm` — the canonical normal form, a computable `RawTerm 0`.
* `SimplyTypedTermLF.conv_normalForm` — a term converts to its normal form.
* `SimplyTypedTermLF.normalForm_isStepNormalForm` — the normal form is structurally normal.
* `SimplyTypedTermLF.normalForm_eq_self_of_isStepNormalForm` — an already-normal term is its own normal form
  (no spurious rewriting).
* `SimplyTypedTermLF.conv_iff_normalForm_eq` — two terms convert IFF their normal forms coincide: the
  canonical normal form is a complete conversion invariant, the explicit characterization behind
  `Conv.decidableOfSimplyTypedBareClosed`.

These hold for an INHABITED fragment (`SimplyTypedTermLF` has closed witnesses — `identityIsSimplyTyped`,
`arrowIdentityIsSimplyTyped` in `SimplyTypedTermInhabitationLevelFree.lean`), so none of the statements is
vacuously quantified.

## Zero-axiom verification

Pure composition: `stronglyNormalizing_of_subst` ∘ the FT's `stronglyNormalizingClosed` feeds the WN-grind
normalizer's `normalize` / `conv_normalize` / `normalize_isStepNormalForm` /
`normalize_eq_self_of_isStepNormalForm` / `normalize_eq_iff_conv`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **Every closed simply-typed term is strongly normalizing** — the BARE statement, no closing
substitution.  The fundamental theorem gives strong normalization of `subst emptyClosingSubst term`;
`StepStar.stronglyNormalizing_of_subst` reflects it back to strong normalization of `term` itself.  The SN
companion to `Conv.decidableOfSimplyTypedBareClosed`. -/
theorem SimplyTypedTermLF.stronglyNormalizingBare {profile : PolyProfile}
    {term type : RawTerm 0}
    (typed : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type) :
    StepStar.IsStronglyNormalizing term :=
  StepStar.stronglyNormalizing_of_subst emptyClosingSubst term
    (typed.stronglyNormalizingClosed emptyClosingSubst)

/-- **The canonical normal form of a closed simply-typed term** — a computable `RawTerm 0` obtained by
running the WN-grind normalizer along the bare strong-normalization witness. -/
def SimplyTypedTermLF.normalForm {profile : PolyProfile}
    {term type : RawTerm 0}
    (typed : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type) : RawTerm 0 :=
  RawTerm.normalize term typed.stronglyNormalizingBare

/-- A closed simply-typed term converts to its canonical normal form (the normalizer's reduction chain lifts
to `Conv`). -/
theorem SimplyTypedTermLF.conv_normalForm {profile : PolyProfile}
    {term type : RawTerm 0}
    (typed : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type) :
    Conv term typed.normalForm :=
  RawTerm.conv_normalize term typed.stronglyNormalizingBare

/-- The canonical normal form of a closed simply-typed term is structurally normal — no redex remains. -/
theorem SimplyTypedTermLF.normalForm_isStepNormalForm {profile : PolyProfile}
    {term type : RawTerm 0}
    (typed : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type) :
    RawTerm.isStepNormalForm typed.normalForm :=
  RawTerm.normalize_isStepNormalForm term typed.stronglyNormalizingBare

/-- An already-normal closed simply-typed term is its own canonical normal form — the normalizer performs no
spurious rewriting on a normal input. -/
theorem SimplyTypedTermLF.normalForm_eq_self_of_isStepNormalForm {profile : PolyProfile}
    {term type : RawTerm 0}
    (typed : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type)
    (normal : RawTerm.isStepNormalForm term) :
    typed.normalForm = term :=
  RawTerm.normalize_eq_self_of_isStepNormalForm term typed.stronglyNormalizingBare normal

/-- **Two closed simply-typed terms convert iff their canonical normal forms coincide.**  The canonical
normal form is a COMPLETE invariant for conversion on the closed simply-typed fragment — the explicit
biconditional behind `Conv.decidableOfSimplyTypedBareClosed`. -/
theorem SimplyTypedTermLF.conv_iff_normalForm_eq {profile : PolyProfile}
    {firstTerm firstType secondTerm secondType : RawTerm 0}
    (firstTyped : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) firstTerm firstType)
    (secondTyped : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) secondTerm secondType) :
    Conv firstTerm secondTerm ↔ firstTyped.normalForm = secondTyped.normalForm :=
  RawTerm.normalize_eq_iff_conv firstTerm secondTerm
    firstTyped.stronglyNormalizingBare secondTyped.stronglyNormalizingBare

end FX1Poly.Typed
