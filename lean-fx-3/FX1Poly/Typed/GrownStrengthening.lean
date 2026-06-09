import FX1Poly.Typed.HasTypeDescPiVarInversion
import FX1Poly.Core.ConvRenameReflection

/-! # FX1Poly/Typed/GrownStrengthening — the variable arm of grown strengthening (inverse of `weakenUnderBinding`)

Grown strengthening is the inverse of `weakenUnderBinding`: from a grown typing of a WEAKENED subject at a
WEAKENED classifier under one extra binding, recover the typing in the smaller context.  It is the residual
of grown η-contraction subject reduction (#477 λ-case / PAR-2): η-contraction sends `lam (app (weaken f)
(var 0))` to `f`, and re-typing `f` in the smaller context is exactly strengthening on the function part.

The full theorem is a generalized strengthening-at-position induction over the mutual `HasTypeDescPi` ⋈
`DescTelescopePi` derivation; its binder (piIntro) arm is the crux and remains a multi-firing push.  This
file lands the ONE non-recursive (leaf) arm — the VARIABLE case — completely and zero-axiom, the base case
of that induction and the first concrete consumer of `Conv.reflectWeaken` (#1167):

  * **`lookupConsSuccEqWeaken`** — `(context.cons B).lookup innerIndex.succ = weaken (context.lookup
    innerIndex)`.  Holds by `rfl` (the cons-lookup successor clause IS a `weaken` of the rest-lookup).
  * **`HasTypeDescPi.strengthenVariableClassifier`** — the genuine content: a weakened variable grown-typed
    at a weakened classifier forces the un-weakened classifier `Conv` the variable's looked-up type.  Proof:
    `invertVar` (#1118) extracts `Conv (weaken classifier) ((cons B).lookup succ)`, the bridge exposes a
    `weaken` on the right, and `Conv.reflectWeaken` strips both.  No validity premise needed.
  * **`HasTypeDescPi.strengthenVariableUnderBinding`** — the full var-arm conclusion shape: given the
    un-weakened classifier is a valid universe code in the smaller context, the variable re-types at it.
    Var rule (at the natural lookup type) + grown `conv` with the classifier-`Conv` above + the validity.
    The validity premise is exactly what the full mutual bundle threads through its presupposition; here it
    is taken as a hypothesis so the leaf arm is self-contained.

## Zero-axiom

`lookupConsSuccEqWeaken` is `rfl`; the two strengthening lemmas compose `invertVar`, `Conv.reflectWeaken`,
the grown `conv`/`ofFormation`/`HasTypeDesc.var` rules, and `Conv.sym`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation FX1Poly.Universe

/-- Looking up the successor index in a `cons` is the weakening of the rest-lookup (the cons-lookup
successor clause, definitionally). -/
theorem lookupConsSuccEqWeaken {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (bindingType : RawTerm scope)
    (innerIndex : Fin scope) :
    (context.cons bindingType).lookup innerIndex.succ
      = RawTerm.weaken (context.lookup innerIndex) := rfl

/-- **Var arm of grown strengthening (classifier).**  A weakened variable grown-typed at a weakened
classifier under an extra binding forces the un-weakened classifier to be convertible to the variable's
looked-up type.  `invertVar` extracts the `Conv` against the cons-lookup, the cons-lookup-succ bridge
exposes a `weaken`, and `Conv.reflectWeaken` (#1167) strips it. -/
theorem HasTypeDescPi.strengthenVariableClassifier {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {bindingType : RawTerm scope}
    {innerIndex : Fin scope} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile (context.cons bindingType)
      (variableCell innerIndex.succ) (RawTerm.weaken classifier)) :
    Conv classifier (context.lookup innerIndex) := by
  have convFact := HasTypeDescPi.invertVar typed
  rw [lookupConsSuccEqWeaken] at convFact
  exact Conv.reflectWeaken convFact

/-- **Var arm of grown strengthening (full typing).**  Given additionally that the un-weakened classifier
is a valid universe code in the smaller context, the variable re-types at that classifier there — the var
case of `strengthenUnderBinding` at its full conclusion shape.  Var rule at the natural lookup type + grown
`conv` (via the classifier-`Conv` above) + the supplied validity. -/
theorem HasTypeDescPi.strengthenVariableUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {bindingType : RawTerm scope}
    {innerIndex : Fin scope} {classifier : RawTerm scope}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (typed : HasTypeDescPi profile (context.cons bindingType)
      (variableCell innerIndex.succ) (RawTerm.weaken classifier))
    (classifierValid : HasTypeDescPi profile context classifier
      (universeCodeCell levelExpr flag)) :
    HasTypeDescPi profile context (variableCell innerIndex) classifier :=
  HasTypeDescPi.conv levelExpr flag
    (HasTypeDescPi.ofFormation (HasTypeDesc.var context innerIndex))
    (HasTypeDescPi.strengthenVariableClassifier typed).sym
    classifierValid

end FX1Poly.Typed
