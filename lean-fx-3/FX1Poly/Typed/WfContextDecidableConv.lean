import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Typed.HasTypeDescPiConditionalConfluence

/-! # FX1Poly/Typed/WfContextDecidableConv
    — harvesting open SN-043: UNCONDITIONAL decidable typed Conv + global confluence on the WfContext fragment
      (SN-051 / SN-046-unconditional)

The conditional package (`HasTypeDescPiConditionalConfluence.lean`) keyed its results — decidable typed Conv,
global confluence — on the UNQUALIFIED typed-SN interface `HasTypeDescPiStronglyNormalizes` (SN for well-typed
terms in EVERY context).  Open SN-043 (`HasTypeDescPi.stronglyNormalizingOfWfContext`, OB-5) supplies SN directly
for terms in a WELL-FORMED context — so these results become UNCONDITIONAL once the qualifier moves from "assume
typed-SN" to "assume the context is well-formed" (a decidable presupposition, and the honest precondition: the
unqualified interface is unprovable because the var rule types in any context, well-formed or not).

  * `Conv.decidableOfWellTypedInWfContext` (SN-051) — two well-typed subjects in a well-formed context have
    DECIDABLE convertibility, with NO typed-SN hypothesis: feed each subject's OB-5 SN witness to the parameter-
    free SN-fragment decider `Conv.decidableOfStronglyNormalizing` (normalize both, compare propext-free).
  * `HasTypeDescPi.subjectConfluenceOfWfContext` (SN-046, unconditional) — any two reducts of a well-typed
    subject in a well-formed context join, via per-term Newman (`confluence_of_localJoin_and_accessible`) on the
    OB-5 SN witness.  Raw global confluence (false by Ω) is never used.

## Zero-axiom verification

Each is a one-line composition of OB-5 (`stronglyNormalizingOfWfContext`) with a shipped SN-fragment result.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **SN-051: decidable typed Conv on the WfContext fragment, UNCONDITIONALLY.**  Two well-typed subjects in a
well-formed context have decidable convertibility — the SN-fragment qualifier is discharged by open SN-043
(OB-5): each subject is strongly normalizing (`stronglyNormalizingOfWfContext`), so the parameter-free decider
`Conv.decidableOfStronglyNormalizing` (normalize both, compare normal forms) applies.  The unconditional form of
`Conv.decidableOfHasTypeDescPiStronglyNormalizes`. -/
def Conv.decidableOfWellTypedInWfContext {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {leftSubject leftClassifier rightSubject rightClassifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (leftTyped : HasTypeDescPi profile context leftSubject leftClassifier)
    (rightTyped : HasTypeDescPi profile context rightSubject rightClassifier) :
    Decidable (Conv leftSubject rightSubject) :=
  Conv.decidableOfStronglyNormalizing
    (HasTypeDescPi.stronglyNormalizingOfWfContext contextWellFormed leftTyped)
    (HasTypeDescPi.stronglyNormalizingOfWfContext contextWellFormed rightTyped)

/-- **SN-046 (unconditional): global confluence on the WfContext fragment.**  Any two reducts of a well-typed
subject in a well-formed context join — per-term Newman (`StepStar.confluence_of_localJoin_and_accessible`, raw
local confluence baked in) fed the subject's OB-5 SN witness.  The unconditional form of
`HasTypeDescPi.subjectConfluenceOfStronglyNormalizes`; raw global confluence (false by Ω) is never used. -/
theorem HasTypeDescPi.subjectConfluenceOfWfContext {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (typed : HasTypeDescPi profile context subject classifier)
    {leftReduct rightReduct : RawTerm scope}
    (subjectToLeft : StepStar subject leftReduct)
    (subjectToRight : StepStar subject rightReduct) :
    StepStar.Join leftReduct rightReduct :=
  StepStar.confluence_of_localJoin_and_accessible
    (HasTypeDescPi.stronglyNormalizingOfWfContext contextWellFormed typed)
    subjectToLeft subjectToRight

end FX1Poly.Typed
