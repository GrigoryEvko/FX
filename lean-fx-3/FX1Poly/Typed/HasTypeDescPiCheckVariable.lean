import FX1Poly.Typed.HasTypeDescPiCheckOfInferred
import FX1Poly.Typed.HasTypeDescPiVariableInversion
import FX1Poly.Typed.IsTypeDescDecidableGeneric
import FX1Poly.Typed.WfContextDescLookup
import FX1Poly.Typed.WfContextDescFromWfContext

/-! # FX1Poly/Typed/HasTypeDescPiCheckVariable
    — the VARIABLE case of the bidirectional grown-engine checker (SN-052), in CHECK mode

The first COMPLETE case of the SN-052 decidable checker, and the first to compose the shipped bricks
end-to-end.  Deciding `variableCell index : targetType` (given the target's typehood threaded as input — the
CHECK-mode discipline that avoids deciding grown-typehood in the recursion, and SR-free since there is no λ)
reduces to deciding `Conv (context.lookup index) targetType`:

  * INFERENCE: the variable's principal type is `context.lookup index`, derived directly by
    `.ofFormation (HasTypeDesc.var …)`;
  * the principal type's own typehood (`lookup index : Type`) — the COMPARE step needs it as DATA, so it is
    extracted via the NATIVE `IsTypeDesc.decideTypeGeneric` (which returns a `PSum` carrying the typing
    witness as a `HasTypeDesc` derivation — no `HasType.toHasTypeDesc` bridge); the impossible `.inr` branch is
    refuted by `WfContextDesc.lookupIsTypeDesc` (a well-formed context's entries ARE types);
  * UNIQUENESS: `HasTypeDescPi.inversionVariable` — every type a variable receives is `Conv` to its lookup;
  * the COMPARE step `HasTypeDescPi.decidableCheckOfInferredUniqueAtType` assembles these into the decision.

This is the template the other infer-mode positions (application) will follow once their inference +
per-subject uniqueness land; the introduction position (λ) is the separate CHECK-mode half (gated on exposing
the target's Π-components, i.e. on subject reduction).

## Native (HT-B): off the old `HasType` engine

The lookup-typehood is now decided by the native `IsTypeDesc.decideTypeGeneric` (HT-A4 B1) over a
`WfContextDesc` obtained from the threaded `WfContext` via the shipped migration bridge
`WfContextDesc.ofWfContext`; its `.inl` carries a `HasTypeDesc` witness directly, so the inferred-type typing
is `.ofFormation` of that native witness with NO `HasType.toHasTypeDesc`, and the `.inr` refutation is
`WfContextDesc.lookupIsTypeDesc` (not the old `WfContext.lookupIsType`).  The `WfContext` hypothesis remains
only to feed the two grown-engine consumers (`decidableCheckOfInferredUniqueAtType`, `inversionVariable`),
which carry their own `WfContext` until their migration — this file's PROOF no longer references the old
engine.

## Zero-axiom verification

A `match` on `IsTypeDesc.decideTypeGeneric` feeding the shipped COMPARE step + variable inversion; the `.inr`
branch is `absurd … WfContextDesc.lookupIsTypeDesc`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Decidable checking of a variable against a known-type target.**  `variableCell index : targetType` is
decided by `Conv (context.lookup index) targetType` (the COMPARE step), the variable's inferred type being its
context lookup and its per-subject uniqueness being `inversionVariable`.  The target's typehood
`targetTyped` is threaded as input (CHECK mode); the lookup's typehood is recovered as data via the NATIVE
`IsTypeDesc.decideTypeGeneric`, its impossible non-type branch refuted by `WfContextDesc.lookupIsTypeDesc`. -/
def HasTypeDescPi.decidableCheckVariableAtType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (wellFormed : WfContext context)
    (index : Fin scope)
    {targetType : RawTerm scope} {targetLevel : LevelExpr} {targetFlag : UniverseFlag}
    (targetTyped :
      HasTypeDescPi profile context targetType (universeCodeCell targetLevel targetFlag)) :
    Decidable (HasTypeDescPi profile context (variableCell index) targetType) :=
  match IsTypeDesc.decideTypeGeneric (WfContextDesc.ofWfContext wellFormed) (context.lookup index) with
  | .inl ⟨_lookupLevel, _lookupFlag, lookupTypedNative⟩ =>
      HasTypeDescPi.decidableCheckOfInferredUniqueAtType wellFormed
        (inferred := .ofFormation (HasTypeDesc.var context index))
        (inferredTypeTyped := .ofFormation lookupTypedNative)
        (targetTyped := targetTyped)
        (uniqueAtSubject := fun derivation =>
          (HasTypeDescPi.inversionVariable derivation wellFormed).sym)
  | .inr notType =>
      absurd
        (WfContextDesc.lookupIsTypeDesc context (WfContextDesc.ofWfContext wellFormed) index)
        notType

end FX1Poly.Typed
