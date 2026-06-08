import FX1Poly.Typed.HasTypeDescPiContextConversionValidityReduction
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional

/-! # FX1Poly/Typed/HasTypeDescPiContextConversionPiElimUnderWf
    — the flexible grown context-conversion piElim arm, UNCONDITIONAL under target well-formedness

`HasTypeDescPiContextConversionValidityReduction.lean` (`#1094`) reduced the grown context-conversion `piElim`
arm to the residual `TypeCodeValidityRespectsReduction` (type validity survives reduction) via
`piElimArmFromValidityRespectsReduction`.  That residual was, at the time, believed to "route through the
logical relation."  It does NOT: once master subject reduction is unconditional, its `StepStar` corollary
discharges validity-survives-reduction for the FULL grown engine under a well-formed context
(`HasTypeDescPi.typeValiditySurvivesReductionUnderWf`).

This file lands the consequence: the flexible `piElim` context-conversion arm, with NO residual hypothesis —
only the benign target well-formedness `WfContextDescPi targetContext`.  It is `piElimArmFromValidityRespectsReduction`
with the global residual application replaced by `typeValiditySurvivesReductionUnderWf` at the (well-formed) target
context.  This is the FIRST unconditional discharge of the obstruction that every prior context-conversion firing
left "reduced to the Π-validity residual."

## Shape: the IH-consuming `piElim` CASE (toward the flexible mutual)

`piElimArmUnderWfTarget` consumes the ALREADY-context-converted function/argument typings
(`functionConverted` / `argumentConverted`) plus the function's classifier-validity in the target
(`functionFlexible`), exactly as `piElimArmFromValidityRespectsReduction` does — i.e. it is the `piElim` arm of a
flexible context-conversion mutual (where those are the recursive IHs), not the `WfContextDescPi`-free standalone
`piElimArm` hypothesis of `convContextOfPiElimArm`.  Note `functionFlexible` is NOT a separate recursion: under
the target well-formedness it derives from `functionConverted` via `HasTypeDescPi.classifierIsTypeDescPi` (the
classifier of a typed term is a valid type), so a flexible mutual built on this arm needs only the single
term-conversion recursion.

## Zero-axiom verification

`Conv.reducesToPiTyCode` (`#1060`) + `HasTypeDescPi.typeValiditySurvivesReductionUnderWf` (the SR-U4 follow-on) +
`HasTypeDescPi.reassembleApplicationFromConvEqualPiValidity` (`#1094`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The flexible `piElim` context-conversion arm, UNCONDITIONAL under target well-formedness.**  Given the
function's classifier-validity in the (well-formed) target (`functionFlexible`), the context-converted function
typing (`functionConverted`) and argument typing (`argumentConverted`), the application re-types in the target at
a `Conv`-equal classifier.  `Conv.reducesToPiTyCode` exposes the flexible classifier's reduction to a `Π`-code,
`typeValiditySurvivesReductionUnderWf` carries the validity across that reduction at the well-formed target, and
`reassembleApplicationFromConvEqualPiValidity` rebuilds the application.  The well-formed-context twin of
`piElimArmFromValidityRespectsReduction` (`#1094`) — the residual the latter took as a hypothesis is now
discharged. -/
theorem HasTypeDescPi.piElimArmUnderWfTarget {profile : PolyProfile} {scope : Nat}
    {targetContext : TypingContext profile scope}
    {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (targetWellFormed : WfContextDescPi targetContext)
    (functionFlexible : ∃ functionClassifier,
      Conv (piTyCodeCell domainCode codomainCode) functionClassifier ∧
        IsTypeDescPi profile targetContext functionClassifier)
    (functionConverted : ∃ functionClassifier,
      Conv (piTyCodeCell domainCode codomainCode) functionClassifier ∧
        HasTypeDescPi profile targetContext functionTerm functionClassifier)
    (argumentConverted : ∃ argumentClassifier,
      Conv domainCode argumentClassifier ∧
        HasTypeDescPi profile targetContext argument argumentClassifier) :
    ∃ classifier', Conv (RawTerm.subst0 codomainCode argument) classifier' ∧
      HasTypeDescPi profile targetContext (appCell functionTerm argument) classifier' := by
  obtain ⟨flexClassifier, convPiToFlex, flexValid⟩ := functionFlexible
  obtain ⟨reductDomain, reductCodomain, flexReducesToPi, convDomainReduct, convCodomainReduct⟩ :=
    Conv.reducesToPiTyCode convPiToFlex.sym
  have piReductValid : IsTypeDescPi profile targetContext
      (piTyCodeCell reductDomain reductCodomain) :=
    HasTypeDescPi.typeValiditySurvivesReductionUnderWf targetWellFormed flexValid flexReducesToPi
  exact HasTypeDescPi.reassembleApplicationFromConvEqualPiValidity functionConverted argumentConverted
    convDomainReduct convCodomainReduct piReductValid

end FX1Poly.Typed
