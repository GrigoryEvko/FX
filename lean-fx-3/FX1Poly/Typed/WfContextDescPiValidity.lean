import FX1Poly.Typed.WfContextDescPiLookup
import FX1Poly.Typed.HasTypeDescValidity

/-! # FX1Poly/Typed/WfContextDescPiValidity — classifier-validity over the GROWN well-formedness

The grown engine's validity / inversion metatheory currently threads the `HasType`-based `WfContext` (e.g.
`HasTypeDesc.classifierIsTypeDesc`, `HasTypeDescPi.classifierIsTypeDesc`, `inversionPiCodeComponents`,
`piCodeInstantiationIsType`, `betaSubjectReduction`).  That hypothesis is STRONGER than these lemmas need —
they only use `wellFormed` to conclude a looked-up variable's type is a GROWN type, and they conclude grown
types throughout — yet it is the obstruction to the master subject-reduction dispatcher (SN-055 / TG-3), which
must EXTEND well-formedness at a grown `piIntro` binder where `WfContext` cannot reach (no `HasTypeDescPi →
IsType` bridge).  The fix is to re-thread these lemmas over the grown `WfContextDescPi` (WFG-1, which DOES
extend at grown binders), each a mechanical `WfContext → WfContextDescPi` / `WfContext.lookupIsType →
WfContextDescPi.lookupIsType` swap (`WfContext → WfContextDescPi` holds via `ofWfContext`, so the grown
versions subsume the existing ones).

This file accrues those grown-validity twins.  First brick:

  * `HasTypeDesc.classifierIsTypeDescPi` — a FORMATION-typed cell's classifier is a grown type (`IsTypeDescPi`)
    under `WfContextDescPi`.  The `var` arm reads off `WfContextDescPi.lookupIsType` (WFG-2) directly (the
    looked-up binding is a grown type — under a grown context a formation variable's type is grown, not a
    formation `IsTypeDesc`); `conv` / `universeFormation` / `genFormation` lift the formation universe-typing
    through `ofFormation`.  The mirror of `HasTypeDesc.classifierIsTypeDesc`, and the formation-engine leaf of
    the grown classifier-validity the master SR needs (the grown `HasTypeDescPi.classifierIsTypeDescPi` + the
    `inversionPiCodeComponents` / `piCodeInstantiationIsType` / `betaSubjectReduction` twins follow, each a
    `WfContextDescPi` swap).

## Zero-axiom verification

Full-enumeration term-mode `match` on the formation derivation + `WfContextDescPi.lookupIsType` +
`HasTypeDescPi.ofFormation` + `HasTypeDesc.universeFormation` + the `typingRuleDescOf_outputIsUniverseFormer`
table fact.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- A FORMATION-typed cell's classifier is a GROWN type (`IsTypeDescPi`) under the grown well-formedness
`WfContextDescPi`.  The `var` arm concludes `IsTypeDescPi` directly via `WfContextDescPi.lookupIsType`; the
remaining arms lift the formation universe-typing through `ofFormation`.  The grown mirror of
`HasTypeDesc.classifierIsTypeDesc`, and the formation-engine leaf of grown classifier-validity. -/
theorem HasTypeDesc.classifierIsTypeDescPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (derivation : HasTypeDesc profile context subject classifier) :
    IsTypeDescPi profile context classifier :=
  match derivation with
  | .var context index => WfContextDescPi.lookupIsType context wellFormed index
  | .conv levelExpr flag _typed _converts reclassifierTyped =>
      ⟨levelExpr, flag, HasTypeDescPi.ofFormation reclassifierTyped⟩
  | .universeFormation context levelExpr flag =>
      ⟨_, _, HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation context levelExpr.lsucc flag)⟩
  | .genFormation context generator _payload _children levels flag rule isFormation _premises => by
      rw [typingRuleDescOf_outputIsUniverseFormer isFormation]
      exact ⟨(lmaxAll levels).lsucc, flag,
        HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation context (lmaxAll levels) flag)⟩

end FX1Poly.Typed
