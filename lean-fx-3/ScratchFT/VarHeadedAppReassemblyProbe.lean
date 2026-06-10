import FX1Poly.Typed.HasTypeDescPiVarInversion
import FX1Poly.Typed.HasTypeDescPiContextConversionPiElimReduction

/-! Probe: the var-headed neutral-application reconstruction (the Abel-reflection piElim arm for var heads).
    Leaf: a variable's typing converts under context conversion (invertVar + Conv.trans + var rule, NO
    recursion). Then assemble via reassembleApplicationUnderContextConversion (#1092). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- ★ The Abel-reflection LEAF: a variable's typing converts under context conversion.  A `variableCell index`
typed at `classifier` under `sourceContext` is, under any pointwise-`Conv` target context, typed at a
`Conv`-equal classifier — WITHOUT recursion: invert the var typing (`Conv classifier (src.lookup index)`),
compose with the context-conversion `Conv` at `index`, and re-apply the var rule under the target.  Produces
both the `functionConverted` and `argumentConverted` inputs the application reassembly consumes. -/
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

/-- ★ The var-headed neutral-application reconstruction (the Abel-reflection piElim arm for a var-headed
spine).  A var-headed application `(var f)(var a)` — with the function typed at `Π D C` and the argument at
`D` under the source — reassembles under any pointwise-`Conv` target context, REDUCED to the single
`Π`-validity-in-target obligation (`IsTypeDescPi tgt (Π D C)`).  The `functionConverted`/`argumentConverted`
inputs are DISCHARGED non-recursively via `varConvertedUnderContextConv` (the genuine Abel-reflection move: a
var leaf looks up, it does not recurse); the remaining `piValidityTarget` is exactly the named residual
`ConvContextPreservesPiValidity`, which the typed-LR semantic route supplies. -/
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

#print axioms FX1Poly.Typed.HasTypeDescPi.varConvertedUnderContextConv
#print axioms FX1Poly.Typed.HasTypeDescPi.varHeadedAppReassemblyUnderContextConv
