import FX1Poly.Typed.HasTypeDescPiCheckOfInferred
import FX1Poly.Typed.HasTypeDescPiVariableInversion
import FX1Poly.Typed.IsTypeDescDecidableGeneric
import FX1Poly.Typed.WfContextDescLookup

/-! # FX1Poly/Typed/HasTypeDescPiCheckVariable
    — the VARIABLE case of the bidirectional grown-engine checker, in CHECK mode

The VARIABLE case of the decidable checker, composing the bricks
end-to-end.  Deciding `variableCell index : targetType` (given the target's typehood threaded as input — the
CHECK-mode discipline that avoids deciding grown-typehood in the recursion, and SR-free since there is no λ)
reduces to deciding `Conv (context.lookup index) targetType`:

  * INFERENCE: the variable's principal type is `context.lookup index`, derived directly by
    `.ofFormation (HasTypeDesc.var …)`;
  * the principal type's own typehood (`lookup index : Type`) — the COMPARE step needs it as DATA, so it is
    extracted via the NATIVE `IsTypeDesc.decideTypeGeneric` (which returns a `PSum` carrying the typing
    witness as a `HasTypeDesc` derivation); the impossible `.inr` branch is refuted by
    `WfContextDesc.lookupIsTypeDesc` (a well-formed context's entries ARE types);
  * UNIQUENESS: `HasTypeDescPi.inversionVariable` — every type a variable receives is `Conv` to its lookup;
  * the COMPARE step `HasTypeDescPi.decidableCheckOfInferredUniqueAtType` assembles these into the decision.

This is the template the other infer-mode positions (application) will follow once their inference +
per-subject uniqueness land; the introduction position (λ) is the separate CHECK-mode half (gated on exposing
the target's Π-components, i.e. on subject reduction).

## Native: threading `WfContextDesc`

The lookup-typehood is decided by the native `IsTypeDesc.decideTypeGeneric` over the threaded
`WfContextDesc` directly; its `.inl` carries a `HasTypeDesc` witness directly, so the inferred-type typing is
`.ofFormation` of that native witness, and the `.inr` refutation is `WfContextDesc.lookupIsTypeDesc`.  The same
`WfContextDesc` hypothesis flows straight into the COMPARE consumer `decidableCheckOfInferredUniqueAtType`
(whose native typed-Conv decider `Conv.decidableOfWellTypedInWfContextDesc` consumes the formation
`WfContextDesc` — grown→formation has no lift, so the COMPARE step keeps the formation predicate), so the
variable checker is uniformly `WfContextDesc`.

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
    (wellFormed : WfContextDesc context)
    (index : Fin scope)
    {targetType : RawTerm scope} {targetLevel : LevelExpr} {targetFlag : UniverseFlag}
    (targetTyped :
      HasTypeDescPi profile context targetType (universeCodeCell targetLevel targetFlag)) :
    Decidable (HasTypeDescPi profile context (variableCell index) targetType) :=
  match IsTypeDesc.decideTypeGeneric wellFormed (context.lookup index) with
  | .inl ⟨_lookupLevel, _lookupFlag, lookupTypedNative⟩ =>
      HasTypeDescPi.decidableCheckOfInferredUniqueAtType wellFormed
        (inferred := .ofFormation (HasTypeDesc.var context index))
        (inferredTypeTyped := .ofFormation lookupTypedNative)
        (targetTyped := targetTyped)
        (uniqueAtSubject := fun derivation =>
          (HasTypeDescPi.inversionVariable derivation).sym)
  | .inr notType =>
      absurd
        (WfContextDesc.lookupIsTypeDesc context wellFormed index)
        notType

end FX1Poly.Typed
