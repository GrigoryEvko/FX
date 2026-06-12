import FX1Poly.Typed.HasTypeDescNativeDecidable
import FX1Poly.Typed.HasTypeDescStronglyNormalizing
import FX1Poly.Typed.WfContextDesc
import FX1Poly.Core.Normalize

/-! # FX1Poly/Typed/HasTypeDescDecidable — the description engine is DECIDABLE
    (the P11 "0-FN" payoff, via the cascade-free decider)

The description-driven generic engine `HasTypeDesc` (§11.8.5 / §5.2: the
Natural-Model display map as a data-driven cascade-free `gen` arm) has a DECISION
procedure: `Decidable (HasTypeDesc Γ t T)` — its P11 "0 false negatives" property
(every typing question is decidable).

The decision routes through the native cascade-free
`HasTypeDesc.decidableOfWellFormedNative` (built entirely from `HasTypeDesc` pieces over
`WfContextDesc`), and the signature threads `WfContextDesc` natively.

## Zero-axiom verification

`decidableOfWellFormed` is a thin wrapper over the native `decidableOfWellFormedNative`
(itself zero-axiom — head `match` + SN-gated `Conv` decision); `Conv.decidableOfHasTypeDesc`
normalizes each native-SN classifier and compares.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The description engine is decidable: `Decidable (HasTypeDesc Γ subject classifier)`.
Routes through the native cascade-free `HasTypeDesc.decidableOfWellFormedNative` over the
threaded `WfContextDesc`.  The P11 "0-FN" deliverable for the cascade-free engine. -/
def HasTypeDesc.decidableOfWellFormed {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContextDesc context)
    (subject classifier : RawTerm scope) :
    Decidable (HasTypeDesc profile context subject classifier) :=
  HasTypeDesc.decidableOfWellFormedNative wellFormed subject classifier

/-- **Decidable typed classifier conversion for the description engine.**  If two subjects are typed by
`HasTypeDesc`, their classifiers' convertibility is decidable.  Each classifier is strongly normalizing by the
native `HasTypeDesc.classifierStronglyNormalizing` (its intrinsic native validity turns the classifier
into an `IsTypeDesc`, whose subject — the classifier — is then SN), and the parameter-free SN-fragment decider
`Conv.decidableOfStronglyNormalizing` decides by normalizing each side and comparing normal forms.  The
description-engine typed-Conv leg paired with `HasTypeDesc.decidableOfWellFormed`. -/
def Conv.decidableOfHasTypeDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {firstSubject firstClassifier secondSubject secondClassifier : RawTerm scope}
    (wellFormed : WfContextDesc context)
    (firstTyped : HasTypeDesc profile context firstSubject firstClassifier)
    (secondTyped : HasTypeDesc profile context secondSubject secondClassifier) :
    Decidable (Conv firstClassifier secondClassifier) :=
  Conv.decidableOfStronglyNormalizing
    (firstTyped.classifierStronglyNormalizing wellFormed)
    (secondTyped.classifierStronglyNormalizing wellFormed)

end FX1Poly.Typed
