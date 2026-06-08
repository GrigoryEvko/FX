import FX1Poly.Typed.HasTypeDescPiVarInversion
import FX1Poly.Typed.HasTypeDescPiContextConversionPiElimReduction

/-! # FX1Poly/Typed/VarHeadedAppContextConversion — the var-headed Abel-reflection piElim arm

The grown context-conversion piElim arm (GrownCtxConv-5, #842) is the lone open arm of grown context
conversion.  The firing-22/#1112 architectural finding is that it cannot transport the application's typing as
a BLACK BOX; it must RECONSTRUCT the typing from the application's var-headed spine — re-typing each spine leaf
under the converted target via the var rule + the context-conversion `Conv`, then `piElim`-reassembling (Abel
reflection).  This file lands that reconstruction for the VAR-HEADED case.

## The two pieces

  * `varConvertedUnderContextConv` — ★ the Abel-reflection LEAF.  A `variableCell index` typed at `classifier`
    under the source is typed at a `Conv`-equal classifier under any pointwise-`Conv` target context, WITHOUT
    recursion: `invertVar` (#1118) gives `Conv classifier (sourceContext.lookup index)`, composed with the
    context-conversion `Conv` at `index` and re-applying the var rule under the target.  This is exactly the
    `functionConverted`/`argumentConverted` shape `reassembleApplicationUnderContextConversion` (#1092)
    consumes — the var leaf LOOKS UP, it does not recurse (the whole point of reflection: the mutual
    context-conversion recursion is replaced by a lookup at the variable spine leaves).

  * `varHeadedAppReassemblyUnderContextConv` — the assembled reconstruction.  A var-headed application
    `(var f)(var a)` (function typed at `Π D C`, argument at `D`) reassembles under the converted target,
    REDUCED to the single `Π`-validity-in-target obligation `IsTypeDescPi tgt (Π D C)`.  Both reassembly inputs
    are discharged non-recursively via `varConvertedUnderContextConv`; the residual `piValidityTarget` is
    exactly `ConvContextPreservesPiValidity` — which the typed-LR semantic route (#1110/#1114-1117) supplies.

So the var-headed piElim arm is now PRECISELY the `Π`-validity residual: the application-reassembly and both
spine re-typings are free.

## Zero-axiom verification

`varConvertedUnderContextConv`: one `⟨_, Conv.trans invertVar (contextConv index), ofFormation (HasTypeDesc.var
…)⟩`.  `varHeadedAppReassemblyUnderContextConv`: `reassembleApplicationUnderContextConversion` applied to the
two leaf conversions + the `piValidityTarget`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **★ The Abel-reflection LEAF: a variable's typing converts under context conversion.**  A `variableCell
index` typed at `classifier` under `sourceContext` is, under any pointwise-`Conv` target context, typed at a
`Conv`-equal classifier — WITHOUT recursion: invert the var typing (`Conv classifier (sourceContext.lookup
index)`, #1118), compose with the context-conversion `Conv` at `index`, and re-apply the var rule under the
target.  Produces both the `functionConverted` and `argumentConverted` inputs the application reassembly
(#1092) consumes; the variable spine leaves LOOK UP rather than recurse. -/
theorem HasTypeDescPi.varConvertedUnderContextConv {profile : PolyProfile} {scope : Nat}
    {sourceContext targetContext : TypingContext profile scope}
    {index : Fin scope} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile sourceContext (variableCell index) classifier)
    (contextConv : ∀ i : Fin scope,
      Conv (sourceContext.lookup i) (targetContext.lookup i)) :
    ∃ classifier', Conv classifier classifier' ∧
      HasTypeDescPi profile targetContext (variableCell index) classifier' :=
  ⟨targetContext.lookup index,
    Conv.trans typed.invertVar (contextConv index),
    HasTypeDescPi.ofFormation (HasTypeDesc.var targetContext index)⟩

/-- **★ The var-headed neutral-application reconstruction (the Abel-reflection piElim arm for a var-headed
spine).**  A var-headed application `(var f)(var a)` — function typed at `Π domainCode codomainCode`, argument
at `domainCode` under the source — reassembles under any pointwise-`Conv` target context, REDUCED to the single
`Π`-validity-in-target obligation `IsTypeDescPi targetContext (Π domainCode codomainCode)`.  The
`functionConverted`/`argumentConverted` reassembly inputs are discharged non-recursively via
`varConvertedUnderContextConv` (a var leaf looks up, it does not recurse — the genuine reflection move); the
remaining `piValidityTarget` is exactly the named residual `ConvContextPreservesPiValidity`, supplied by the
typed-LR semantic route.  The application reassembly and both spine re-typings are now FREE for var heads. -/
theorem HasTypeDescPi.varHeadedAppReassemblyUnderContextConv {profile : PolyProfile} {scope : Nat}
    {sourceContext targetContext : TypingContext profile scope}
    {functionIndex argumentIndex : Fin scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (functionTyped :
      HasTypeDescPi profile sourceContext (variableCell functionIndex)
        (piTyCodeCell domainCode codomainCode))
    (argumentTyped :
      HasTypeDescPi profile sourceContext (variableCell argumentIndex) domainCode)
    (contextConv : ∀ i : Fin scope,
      Conv (sourceContext.lookup i) (targetContext.lookup i))
    (piValidityTarget :
      IsTypeDescPi profile targetContext (piTyCodeCell domainCode codomainCode)) :
    ∃ classifier', Conv (RawTerm.subst0 codomainCode (variableCell argumentIndex)) classifier' ∧
      HasTypeDescPi profile targetContext
        (appCell (variableCell functionIndex) (variableCell argumentIndex)) classifier' :=
  HasTypeDescPi.reassembleApplicationUnderContextConversion
    (functionTyped.varConvertedUnderContextConv contextConv)
    (argumentTyped.varConvertedUnderContextConv contextConv)
    piValidityTarget

end FX1Poly.Typed
