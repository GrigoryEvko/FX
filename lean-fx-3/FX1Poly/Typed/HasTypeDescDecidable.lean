import FX1Poly.Typed.HasTypeDescNativeDecidable
import FX1Poly.Typed.HasTypeDescStronglyNormalizing
import FX1Poly.Typed.WfContextDesc
import FX1Poly.Typed.WfContextDescFromWfContext
import FX1Poly.Core.Normalize

/-! # FX1Poly/Typed/HasTypeDescDecidable — the description engine is DECIDABLE
    (the P11 "0-FN" payoff, now via the NATIVE cascade-free decider)

The moonshot description-driven generic engine `HasTypeDesc` (§11.8.5 / §5.2: the
Natural-Model display map as a data-driven cascade-free `gen` arm) has a DECISION
procedure: `Decidable (HasTypeDesc Γ t T)` — its P11 "0 false negatives" property
(every typing question is decidable).

This file once LIFTED the bespoke `HasType.decidableOfWellFormed` (#461/#302) across
the `HasTypeDesc ⟺ HasType` equivalence (completeness `HasType.toHasTypeDesc` forward,
soundness `HasTypeDesc.toHasType` backward).  As part of retiring the old `HasType`
engine (HT-B), the decision now routes DIRECTLY through the native cascade-free
`HasTypeDesc.decidableOfWellFormedNative` (built entirely from `HasTypeDesc` pieces over
`WfContextDesc`, no `HasType` oracle); the public `WfContext` signature is preserved (a
consumer's `WfContext` is bridged to `WfContextDesc` by the shipped
`WfContextDesc.ofWfContext`), so call sites are unaffected.

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
`WfContextDesc` obtained from the threaded `WfContext` via the shipped migration bridge
`WfContextDesc.ofWfContext` — NO transport across `HasType` (no `HasType.decidableOfWellFormed`,
no `HasType.toHasTypeDesc`, no `HasTypeDesc.toHasType`).  The P11 "0-FN" deliverable for the
cascade-free engine, now off the old `HasType` decider (HT-B). -/
def HasTypeDesc.decidableOfWellFormed {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContext context)
    (subject classifier : RawTerm scope) :
    Decidable (HasTypeDesc profile context subject classifier) :=
  HasTypeDesc.decidableOfWellFormedNative (WfContextDesc.ofWfContext wellFormed) subject classifier

/-- **Decidable typed classifier conversion for the description engine.**  If two subjects are typed by
`HasTypeDesc`, their classifiers' convertibility is decidable.  HasType-FREE (HT-A4): each classifier is
strongly normalizing by the native `HasTypeDesc.classifierStronglyNormalizing` (its intrinsic validity turns
the classifier into an `IsTypeDesc`, whose subject — the classifier — is then SN), and the parameter-free
SN-fragment decider `Conv.decidableOfStronglyNormalizing` decides by normalizing each side and comparing normal
forms.  No `HasTypeDesc.toHasType`, no bespoke `Conv.decidableOfTyped`.  The description-engine typed-Conv leg
paired with `HasTypeDesc.decidableOfWellFormed`. -/
def Conv.decidableOfHasTypeDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {firstSubject firstClassifier secondSubject secondClassifier : RawTerm scope}
    (wellFormed : WfContext context)
    (firstTyped : HasTypeDesc profile context firstSubject firstClassifier)
    (secondTyped : HasTypeDesc profile context secondSubject secondClassifier) :
    Decidable (Conv firstClassifier secondClassifier) :=
  Conv.decidableOfStronglyNormalizing
    (firstTyped.classifierStronglyNormalizing wellFormed)
    (secondTyped.classifierStronglyNormalizing wellFormed)

end FX1Poly.Typed
