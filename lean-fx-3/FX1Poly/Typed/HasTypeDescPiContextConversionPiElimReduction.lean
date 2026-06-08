import FX1Poly.Typed.HasTypeDescPiFunctionComponentValidity
import FX1Poly.Typed.HasTypeDescPiContextConversion

/-! # FX1Poly/Typed/HasTypeDescPiContextConversionPiElimReduction
    — the GCC-5 piElim arm reduced to ONE pure type-formation residual (GCC-5-REASSEMBLY, toward #842)

Grown-engine context-conversion (`HasTypeDescPi.convContextOfPiElimArm`, GCC-1..4/#838-841) is conditional on
its lone hard arm `piElimArm` (GCC-5, `#842` — "the entangled crux").  This file does NOT discharge that arm
(it genuinely needs the mutual fundamental-metatheory bundle, GTL-20/`#834` — see the finding below), but it
ISOLATES the residual: it proves that the piElim arm's REASSEMBLY (rebuild `appCell function argument` under the
target context, at a `Conv`-equal classifier) reduces to a SINGLE pure type-formation fact —

  > **a `Π`-type-code's validity is stable under context conversion**
  > (`IsTypeDescPi src (Π D C)` + pointwise-`Conv` `src ≅ tgt` ⟹ `IsTypeDescPi tgt (Π D C)`).

No term-elimination, no β, no `WfContextDescPi tgt`.  This converts "the entangled crux" into a strictly
simpler, clearly-bounded sub-problem.

## The reassembly (the load-bearing observation)

`reassembleApplicationUnderContextConversion`: given the function-IH output (`function` already
context-converted to the target at a classifier `Conv`-equal to `Π D C`), the argument-IH output (`argument`
converted), and the SINGLE residual `piValidityTarget : IsTypeDescPi tgt (Π D C)`, the application reassembles
at `subst0 C argument` under the target.  The key economy: that ONE `Π`-validity supplies BOTH

  * the `conv`-rule reclassifier that re-types `function` from its converted classifier back to the exact
    `Π D C` (`Conv`-symmetry of the function-IH conversion + `piValidityTarget`'s universe witness), AND
  * the `argument`'s domain typing — read off `piValidityTarget` via the well-formedness-free
    `inversionPiCodeComponentsUnconditional`, so NO separate `WfContextDescPi tgt` /
    `reclassifyArgumentToFunctionDomain` is needed.

Then `piElim` fires directly.  The classifier is `subst0 C argument` itself (`Conv.refl`).

## The discharge shape (what closes GCC-5)

`HasTypeDescPi.piElimArmFromPiValidityTransfer`: under the residual `ConvContextPreservesPiValidity` and source
well-formedness `WfContextDescPi src` (which the master SR dispatcher already threads), the full piElim arm
follows from the two convContext IH outputs.  Proof: `classifierIsTypeDescPi` (WFG-3, `#857`) gives
`IsTypeDescPi src (Π D C)`; the residual transfers it to the target; `reassembleApplicationUnderContextConversion`
finishes.  So the EXACT GCC-5 obligation, once `WfContextDescPi` is threaded, is `ConvContextPreservesPiValidity`.

## Why the residual is not itself discharged here (the well-founded-vs-semantic finding)

`ConvContextPreservesPiValidity` context-converts a `Π`-VALIDITY derivation
(`HasTypeDescPi src (Π D C) (universe)`).  That derivation is produced by `classifierIsTypeDescPi`, NOT a
structural sub-derivation of the piElim node — and `classifierIsTypeDescPi` can return a TALLER derivation, so
neither structural recursion nor naive derivation-height induction breaks the knot.  Master SR
(`lnOfPiElimArm`) is gated on the SAME `piElimArm`, so "reduce the function's classifier via SR" is circular
too.  The honest closure is therefore the mutual fundamental-metatheory bundle (validity + context-conversion +
SR proved together, GTL-20) OR the semantic/reducibility route (semantic types are `Conv`-closed by
construction; cf. `SN-034` Conv-invariance of reducibility, `#537`).  This file pins the residual so that
bundle has a single, precisely-named type-formation obligation to hit.

## Zero-axiom verification

`reassembleApplicationUnderContextConversion`: two `obtain`s + two `HasTypeDescPi.conv` (function reclassify,
argument reclassify) + `inversionPiCodeComponentsUnconditional` + `piElim` + `Conv.refl`/`.sym`.
`piElimArmFromPiValidityTransfer`: `classifierIsTypeDescPi` + the residual + the reassembly.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The GCC-5 residual, named.**  A `Π`-type-code's validity is stable under context conversion: if
`piTyCodeCell domainCode codomainCode` is a grown type under `sourceContext`, then it is a grown type under any
pointwise-`Conv`-related `targetContext`.  This is a PURE type-formation fact (no term elimination), and — per
`piElimArmFromPiValidityTransfer` below — it is the exact obligation whose discharge turns the conditional grown
context-conversion (GCC-1..4) unconditional (GCC-5, `#842`). -/
def ConvContextPreservesPiValidity (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {sourceContext targetContext : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)},
    IsTypeDescPi profile sourceContext (piTyCodeCell domainCode codomainCode) →
    (∀ index : Fin scope, Conv (sourceContext.lookup index) (targetContext.lookup index)) →
    IsTypeDescPi profile targetContext (piTyCodeCell domainCode codomainCode)

/-- **The piElim-arm reassembly, reduced to the single `Π`-validity residual.**  Given the function-IH output
(`functionTerm` context-converted to `targetContext` at a classifier `Conv`-equal to `Π domainCode codomainCode`),
the argument-IH output (`argument` converted), and `piValidityTarget : IsTypeDescPi targetContext (Π …)`, the
application `appCell functionTerm argument` reassembles under `targetContext` at `subst0 codomainCode argument`.

The single `Π`-validity supplies everything: its universe witness reclassifies `functionTerm` back to the exact
`Π domainCode codomainCode` (`conv` + the function-IH conversion's symmetry), and its
`inversionPiCodeComponentsUnconditional` domain conjunct reclassifies `argument` to `domainCode` — so NO
`WfContextDescPi targetContext` is required.  Then `piElim` fires; the classifier is `subst0 codomainCode
argument` (`Conv.refl`). -/
theorem HasTypeDescPi.reassembleApplicationUnderContextConversion {profile : PolyProfile} {scope : Nat}
    {targetContext : TypingContext profile scope}
    {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (functionConverted : ∃ functionClassifier,
      Conv (piTyCodeCell domainCode codomainCode) functionClassifier ∧
        HasTypeDescPi profile targetContext functionTerm functionClassifier)
    (argumentConverted : ∃ argumentClassifier,
      Conv domainCode argumentClassifier ∧
        HasTypeDescPi profile targetContext argument argumentClassifier)
    (piValidityTarget : IsTypeDescPi profile targetContext (piTyCodeCell domainCode codomainCode)) :
    ∃ classifier', Conv (RawTerm.subst0 codomainCode argument) classifier' ∧
      HasTypeDescPi profile targetContext (appCell functionTerm argument) classifier' := by
  obtain ⟨functionClassifier, convPiToFunctionClassifier, functionAtClassifier⟩ := functionConverted
  obtain ⟨argumentClassifier, convDomainToArgClassifier, argumentAtClassifier⟩ := argumentConverted
  obtain ⟨piLevel, piFlag, piTyped⟩ := piValidityTarget
  have functionAtPi : HasTypeDescPi profile targetContext functionTerm
      (piTyCodeCell domainCode codomainCode) :=
    HasTypeDescPi.conv piLevel piFlag functionAtClassifier convPiToFunctionClassifier.sym piTyped
  obtain ⟨domainLevel, _codomainLevel, flag, domainTyped, _codomainTyped⟩ :=
    HasTypeDescPi.inversionPiCodeComponentsUnconditional piTyped
  have argumentAtDomain : HasTypeDescPi profile targetContext argument domainCode :=
    HasTypeDescPi.conv domainLevel flag argumentAtClassifier convDomainToArgClassifier.sym domainTyped
  exact ⟨RawTerm.subst0 codomainCode argument, Conv.refl _,
    HasTypeDescPi.piElim functionAtPi argumentAtDomain⟩

/-- **The piElim arm follows from the `Π`-validity residual + source well-formedness + the convContext IH.**
Under `piValidityTransfers : ConvContextPreservesPiValidity` and `WfContextDescPi sourceContext` (the leg the
master SR dispatcher already threads), the grown context-conversion piElim arm holds: `classifierIsTypeDescPi`
(WFG-3) exposes the function's `Π`-classifier as a source type, the residual transfers that validity to the
target, and `reassembleApplicationUnderContextConversion` rebuilds the application.  The two `…Converted`
hypotheses are exactly the convContext IH outputs on the function and argument sub-derivations — so this is the
GCC-5 piElim arm modulo the single residual `piValidityTransfers`. -/
theorem HasTypeDescPi.piElimArmFromPiValidityTransfer {profile : PolyProfile}
    (piValidityTransfers : ConvContextPreservesPiValidity profile)
    {scope : Nat} {sourceContext targetContext : TypingContext profile scope}
    {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (sourceWellFormed : WfContextDescPi sourceContext)
    (functionTyped :
      HasTypeDescPi profile sourceContext functionTerm (piTyCodeCell domainCode codomainCode))
    (contextConv : ∀ index : Fin scope,
      Conv (sourceContext.lookup index) (targetContext.lookup index))
    (functionConverted : ∃ functionClassifier,
      Conv (piTyCodeCell domainCode codomainCode) functionClassifier ∧
        HasTypeDescPi profile targetContext functionTerm functionClassifier)
    (argumentConverted : ∃ argumentClassifier,
      Conv domainCode argumentClassifier ∧
        HasTypeDescPi profile targetContext argument argumentClassifier) :
    ∃ classifier', Conv (RawTerm.subst0 codomainCode argument) classifier' ∧
      HasTypeDescPi profile targetContext (appCell functionTerm argument) classifier' :=
  HasTypeDescPi.reassembleApplicationUnderContextConversion functionConverted argumentConverted
    (piValidityTransfers (functionTyped.classifierIsTypeDescPi sourceWellFormed) contextConv)

end FX1Poly.Typed
