import FX1Poly.Core.NormalizeBetaEta
import FX1Poly.Typed.BetaEtaConvGapStatement

/-! # FX1Poly/Typed/BetaEtaConvDecidable
   — ★ decidable βη-conversion on the wf-typed fragment (closes the ETA-2 arc, the #364(A) half)

The ETA-1 census (`BetaEtaConvGapStatement`) committed that decidable `BetaEtaConv` on the
wf-typed fragment was ONE computable artifact away: a sound+complete βη one-step reducer.  That
artifact shipped (`reduceOnceBetaEta`, `Core/FireRootEtaRedex`), the βη normalizer over it shipped
(`normalizeBetaEta`, `Core/NormalizeBetaEta`), and this file performs the promised assembly:

  * `BetaEtaConv.iff_normalizeBetaEta_eq_of_wfTyped` — the characterization: two well-typed terms
    (same well-formed context, any classifiers) are βη-convertible IFF the βη normalizer maps them
    to the SAME term.  Forward: typed βη Church-Rosser (BECR-1) re-routes the join's common reduct
    to the left normal form, star-rigidity pins it, and the typed unique-βη-NF theorem identifies
    the two normal forms.  Backward: the two normalizer chains meet at the shared output.
  * `BetaEtaConv.decidableOfWfTyped` — the decider: normalize both sides (termination by typed
    βη-SN, OSN-1), compare with `RawTerm` structural equality.
  * `betaEtaConvDecidableOnWfFragment` — the gate-able headline: over EVERY well-formed context,
    βη-conversion of well-typed terms is decidable.

Typing is load-bearing in BOTH legs: termination of the normalizer is typed βη-SN (raw βη is not
SN), and well-definedness of the comparison is typed βη-CR (raw βη-CR is Nederpelt-FALSE).  What
remains of ★#364 after this file is exactly its (B) half: TYPE-DIRECTED η beyond the 5 syntactic
rules (unit-η / SProp / modal kin via η-long readback, η-M15d/e) — judgmental-equality extension
territory, not decision-procedure territory.

## Zero-axiom verification

The characterization composes `normalizeBetaEta_reducesTo` / `_isBetaEtaNormalForm` with the
shipped typed βη-CR, unique-NF, and star-rigidity theorems; the decider is a `dite` over
`RawTerm` `DecidableEq`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **βη-conversion IS βη-normalizer-output equality on the wf-typed fragment.**  The two terms may
sit at different classifiers; what matters is that both are typed in the SAME well-formed context,
so typed βη-CR and the typed unique-βη-NF theorem apply to each.  The accessibility witnesses are
explicit hypotheses (any witnesses work — `Acc` is proof-irrelevant); on the wf fragment they are
supplied by typed βη-SN. -/
theorem BetaEtaConv.iff_normalizeBetaEta_eq_of_wfTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {leftTerm leftClassifier rightTerm rightClassifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (leftTyped : HasTypeDescPi profile context leftTerm leftClassifier)
    (rightTyped : HasTypeDescPi profile context rightTerm rightClassifier)
    (leftTerminates : Step.betaEtaStar.IsStronglyNormalizing leftTerm)
    (rightTerminates : Step.betaEtaStar.IsStronglyNormalizing rightTerm) :
    BetaEtaConv leftTerm rightTerm ↔
      RawTerm.normalizeBetaEta leftTerm leftTerminates =
        RawTerm.normalizeBetaEta rightTerm rightTerminates := by
  constructor
  · intro convertible
    obtain ⟨commonTerm, leftChain, rightChain⟩ := convertible
    obtain ⟨apex, normalFormToApex, commonToApex⟩ :=
      HasTypeDescPi.subjectBetaEtaConfluenceTypedUnconditional contextWellFormed leftTyped
        (RawTerm.normalizeBetaEta_reducesTo leftTerm leftTerminates) leftChain
    have hNormalFormIsApex :=
      Step.betaEtaStar.eq_of_noBetaEtaStep
        (RawTerm.normalizeBetaEta_isBetaEtaNormalForm leftTerm leftTerminates) normalFormToApex
    have commonToLeftNormalForm :
        Step.betaEtaStar commonTerm (RawTerm.normalizeBetaEta leftTerm leftTerminates) := by
      rw [hNormalFormIsApex]
      exact commonToApex
    exact HasTypeDescPi.uniqueBetaEtaNormalFormTypedUnconditional contextWellFormed rightTyped
      (Step.betaEtaStar.trans_compose rightChain commonToLeftNormalForm)
      (RawTerm.normalizeBetaEta_isBetaEtaNormalForm leftTerm leftTerminates)
      (RawTerm.normalizeBetaEta_reducesTo rightTerm rightTerminates)
      (RawTerm.normalizeBetaEta_isBetaEtaNormalForm rightTerm rightTerminates)
  · intro hOutputsEqual
    refine ⟨RawTerm.normalizeBetaEta leftTerm leftTerminates,
      RawTerm.normalizeBetaEta_reducesTo leftTerm leftTerminates, ?_⟩
    rw [hOutputsEqual]
    exact RawTerm.normalizeBetaEta_reducesTo rightTerm rightTerminates

/-- **★ The decider**: βη-conversion of two well-typed terms over a well-formed context is decided
by normalizing both with the βη normalizer (termination: typed βη-SN) and comparing the outputs
structurally (well-definedness: the characterization above, hence typed βη-CR). -/
def BetaEtaConv.decidableOfWfTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {leftTerm leftClassifier rightTerm rightClassifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (leftTyped : HasTypeDescPi profile context leftTerm leftClassifier)
    (rightTyped : HasTypeDescPi profile context rightTerm rightClassifier) :
    Decidable (BetaEtaConv leftTerm rightTerm) :=
  have leftTerminates : Step.betaEtaStar.IsStronglyNormalizing leftTerm :=
    HasTypeDescPi.betaEtaStronglyNormalizingOfWfContextDesc contextWellFormed leftTyped
  have rightTerminates : Step.betaEtaStar.IsStronglyNormalizing rightTerm :=
    HasTypeDescPi.betaEtaStronglyNormalizingOfWfContextDesc contextWellFormed rightTyped
  if hOutputsEqual : RawTerm.normalizeBetaEta leftTerm leftTerminates =
      RawTerm.normalizeBetaEta rightTerm rightTerminates then
    .isTrue ((BetaEtaConv.iff_normalizeBetaEta_eq_of_wfTyped contextWellFormed leftTyped
      rightTyped leftTerminates rightTerminates).mpr hOutputsEqual)
  else
    .isFalse (fun convertible =>
      hOutputsEqual ((BetaEtaConv.iff_normalizeBetaEta_eq_of_wfTyped contextWellFormed leftTyped
        rightTyped leftTerminates rightTerminates).mp convertible))

/-- **★ The headline (#364(A))**: over EVERY well-formed context, βη-conversion of well-typed
terms is decidable — the βη analogue of the A0 decidability floor, now with the 5 syntactic η
rules inside the decided relation. -/
theorem betaEtaConvDecidableOnWfFragment {profile : PolyProfile} :
    ∀ {scope : Nat} {context : TypingContext profile scope}
      {leftTerm leftClassifier rightTerm rightClassifier : RawTerm scope},
      WfContextDesc context →
      HasTypeDescPi profile context leftTerm leftClassifier →
      HasTypeDescPi profile context rightTerm rightClassifier →
      Nonempty (Decidable (BetaEtaConv leftTerm rightTerm)) :=
  fun contextWellFormed leftTyped rightTyped =>
    ⟨BetaEtaConv.decidableOfWfTyped contextWellFormed leftTyped rightTyped⟩

end FX1Poly.Typed
