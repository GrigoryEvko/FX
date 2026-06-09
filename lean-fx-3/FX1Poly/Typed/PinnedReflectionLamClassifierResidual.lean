import FX1Poly.Typed.PinnedReflectionPiElimDispatcher
import FX1Poly.Typed.PlateauPinnedReflection
import FX1Poly.Typed.NeutralReductResidualDischarge

/-! # FX1Poly/Typed/PinnedReflectionLamClassifierResidual — the campaign's open core, named
     (route-H reflection, λ-reduct reduction)

With the neutral-reduct head residual discharged (`NeutralReductResidualDischarge`), the pinned
reflection's remaining open content is the λ-reduct head: the function whnf-reduces to a normal λ,
whose classifier — unlike a neutral's — has no spine to extract a pin from (`piIntro` classifiers
live under arbitrary `conv`).  This file names that open content as ONE residual and collapses the
whole campaign onto it:

  * `PinnedReflectionLamClassifierResidual` — a NORMAL, IN-IMAGE, grown-typed λ has a pinned
    classifier.  The λ-complement of the shipped `normalNonLambdaClassifierPinned`.
  * `pinnedReflectionPiElimLamReductResidualOfLamClassifierResidual` — given the pin, the λ-reduct
    head discharges as the exact mirror of the neutral one: the reduct is in-image
    (`StepStar.reflectRename`), keeps the Π classifier (`subjectReductionStar`), the residual pins
    it, and `pinnedReflectionPiElimCore` finishes with the original premise reflections.
  * `pinnedReflectionPiElimResidualOfLamClassifierResidual` — the FULL piElim residual conditional
    on the λ-classifier pin alone (dispatcher composition with the discharged neutral head).
  * `HasTypeDescPi.pinnedReflectionOfLamClassifierResidual` — the pinned-reflection MASTER
    conditional on the λ-classifier pin alone.

The strengthening campaign's open core is now exactly one statement.

## Zero-axiom verification

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The λ-classifier pin residual** — the campaign's remaining open core: a NORMAL, IN-IMAGE,
grown-typed λ has a pinned classifier.  The λ-complement of the shipped
`normalNonLambdaClassifierPinned` (whose spine extraction is structurally impossible for λ heads:
`piIntro` classifiers live under arbitrary `conv`, with no spine to walk). -/
def PinnedReflectionLamClassifierResidual (profile : PolyProfile) : Prop :=
  ∀ {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {lamBody : RawTerm (targetScope + 1)} {classifier : RawTerm targetScope},
    HasTypeDescPi profile targetContext (lamCell lamBody) classifier →
    RawTerm.isStepNormalForm (lamCell lamBody) →
    WfContextDescPi targetContext →
    ∀ {sourceScope : Nat} (rho : RawRenaming sourceScope targetScope)
      (sourceContext : TypingContext profile sourceScope),
      Function.Injective rho →
      ContextReflectsRename profile rho sourceContext targetContext →
      WfContextDescPi sourceContext →
      ∀ {sourceLam : RawTerm sourceScope},
        lamCell lamBody = RawTerm.rename rho sourceLam →
        ∃ base : RawTerm sourceScope,
          Conv classifier (RawTerm.rename rho base) ∧
          IsTypeDescPi profile sourceContext base

/-- **The λ-reduct head residual reduces to the λ-classifier pin**: when the function whnf-reduces
to a normal λ, the λ-classifier pin hands back the reduct's classifier — which IS the Π classifier
(subject reduction keeps it across the chain) — and the pinned-function core finishes with the
original premise reflections.  Exact mirror of the shipped neutral-reduct discharge with the
plateau pin-extraction swapped for the residual. -/
theorem pinnedReflectionPiElimLamReductResidualOfLamClassifierResidual (profile : PolyProfile)
    (lamClassifierResidual : PinnedReflectionLamClassifierResidual profile) :
    PinnedReflectionPiElimLamReductResidual profile := by
  intro targetScope targetContext functionTerm argument domainCode codomainCode lamBody
    functionTyped argumentTyped functionReduces reductNormal functionIH argumentIH
  intro targetWellFormed sourceScope rho sourceContext rhoInjective condition wellFormed
    sourceSubject pinBase subjectInImage _pinned _pinBaseTyped
  obtain ⟨sourceFunction, sourceArgument, hSubject, hFunction, hArgument⟩ :=
    renameEqAppCellInversion rho subjectInImage.symm
  subst hSubject
  rw [hFunction] at functionReduces functionTyped
  obtain ⟨sourceReduct, _sourceChain, imageEq⟩ :=
    StepStar.reflectRename rho functionReduces
  have reductTyped : HasTypeDescPi profile targetContext (lamCell lamBody)
      (piTyCodeCell domainCode codomainCode) :=
    HasTypeDescPi.subjectReductionStar targetWellFormed functionTyped functionReduces
  obtain ⟨reflectedPiBase, piPinned, piBaseTyped⟩ :=
    lamClassifierResidual reductTyped reductNormal targetWellFormed rho sourceContext
      rhoInjective condition wellFormed imageEq.symm
  exact pinnedReflectionPiElimCore profile functionIH argumentIH rho sourceContext
    targetWellFormed rhoInjective condition wellFormed hFunction hArgument
    piPinned piBaseTyped

/-- **The full piElim residual conditional on the λ-classifier pin alone**: the neutral head is
discharged outright, the λ head reduces to the classifier pin, the dispatcher composes. -/
theorem pinnedReflectionPiElimResidualOfLamClassifierResidual (profile : PolyProfile)
    (lamClassifierResidual : PinnedReflectionLamClassifierResidual profile) :
    PinnedReflectionPiElimResidual profile :=
  pinnedReflectionPiElimResidualOfHeadResiduals profile
    (pinnedReflectionPiElimLamReductResidualOfLamClassifierResidual profile
      lamClassifierResidual)
    (pinnedReflectionPiElimNeutralReductResidualHolds profile)

/-- **The pinned-reflection master conditional on the λ-classifier pin alone** — the whole
strengthening campaign's open core is now ONE statement: pin the classifier of a normal in-image
λ. -/
theorem HasTypeDescPi.pinnedReflectionOfLamClassifierResidual {profile : PolyProfile}
    (lamClassifierResidual : PinnedReflectionLamClassifierResidual profile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (derivation : HasTypeDescPi profile targetContext subject classifier) :
    PinnedReflectionConclusion profile targetContext subject classifier :=
  HasTypeDescPi.pinnedReflectionConditional
    (pinnedReflectionPiElimResidualOfLamClassifierResidual profile lamClassifierResidual)
    derivation

end FX1Poly.Typed
