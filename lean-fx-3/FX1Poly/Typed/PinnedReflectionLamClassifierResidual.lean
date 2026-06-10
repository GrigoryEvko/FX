import FX1Poly.Typed.PinnedReflectionPiElimDispatcher
import FX1Poly.Typed.PlateauPinnedReflection
import FX1Poly.Typed.NeutralReductResidualDischarge
import FX1Poly.Typed.ConvExistentialStrengtheningRefutation

/-! # FX1Poly/Typed/PinnedReflectionLamClassifierResidual — the bare λ-classifier pin: named,
     reduced onto, and REFUTED (route-H reflection, λ-reduct factorization fence)

With the neutral-reduct head residual discharged (`NeutralReductResidualDischarge`), the pinned
reflection's remaining open content is the λ-reduct head: the function whnf-reduces to a normal λ,
whose classifier — unlike a neutral's — has no spine to extract a pin from (`piIntro` classifiers
live under arbitrary `conv`).  This file names the OBVIOUS factorization of that head — pin every
normal in-image λ's classifier — proves the reduction theorems, and then REFUTES the factorization:

  * `PinnedReflectionLamClassifierResidual` — a NORMAL, IN-IMAGE, grown-typed λ has a pinned
    classifier.  The λ-complement of the shipped `normalNonLambdaClassifierPinned`.
  * `pinnedReflectionPiElimLamReductResidualOfLamClassifierResidual` /
    `pinnedReflectionPiElimResidualOfLamClassifierResidual` /
    `HasTypeDescPi.pinnedReflectionOfLamClassifierResidual` — the λ-reduct head, the full piElim
    residual, and the MASTER, each conditional on the λ-classifier pin (mirrors of the neutral
    discharge through the dispatcher and the conditional master).
## T2 retirement of the refutation (user-approved deletion, 2026-06-10)

PRE-T2 this file ALSO refuted the residual (`pinnedReflectionLamClassifierResidual_isFalse`): the
Curry-style weakened identity λ was grown-typed at `Π (var 0). (var 1)` while that classifier has
no pin.  UNDER T2 the witness is dead — `piIntro` pins the λ's domain annotation to the Π domain,
so the only inhabitant of a `var 0`-domain Π is the `var 0`-annotated identity, which is NOT a
weaken-image — and the residual is consequently EXPECTED TO BE TRUE: the reduction theorems below
are no longer fenced-off vacuities but the live assembly route, firing once the residual's
positive proof (the λ-classifier pin via domain reflection) lands.

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
    {lamDomain : RawTerm targetScope} {lamBody : RawTerm (targetScope + 1)}
    {classifier : RawTerm targetScope},
    HasTypeDescPi profile targetContext (lamCell lamDomain lamBody) classifier →
    RawTerm.isStepNormalForm (lamCell lamDomain lamBody) →
    WfContextDescPi targetContext →
    ∀ {sourceScope : Nat} (rho : RawRenaming sourceScope targetScope)
      (sourceContext : TypingContext profile sourceScope),
      Function.Injective rho →
      ContextReflectsRename profile rho sourceContext targetContext →
      WfContextDescPi sourceContext →
      ∀ {sourceLam : RawTerm sourceScope},
        lamCell lamDomain lamBody = RawTerm.rename rho sourceLam →
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
  intro targetScope targetContext functionTerm argument domainCode lamDomain codomainCode lamBody
    functionTyped argumentTyped functionReduces reductNormal functionIH argumentIH
  intro targetWellFormed sourceScope rho sourceContext rhoInjective condition wellFormed
    sourceSubject pinBase subjectInImage _pinned _pinBaseTyped
  obtain ⟨sourceFunction, sourceArgument, hSubject, hFunction, hArgument⟩ :=
    renameEqAppCellInversion rho subjectInImage.symm
  subst hSubject
  rw [hFunction] at functionReduces functionTyped
  obtain ⟨sourceReduct, _sourceChain, imageEq⟩ :=
    StepStar.reflectRename rho functionReduces
  have reductTyped : HasTypeDescPi profile targetContext (lamCell lamDomain lamBody)
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
    (flagUnique : SourceUniverseFlagUnique profile)
    (lamClassifierResidual : PinnedReflectionLamClassifierResidual profile) :
    PinnedReflectionPiElimResidual profile :=
  pinnedReflectionPiElimResidualOfHeadResiduals profile
    (pinnedReflectionPiElimLamReductResidualOfLamClassifierResidual profile
      lamClassifierResidual)
    (pinnedReflectionPiElimNeutralReductResidualHolds profile flagUnique)

/-- **The pinned-reflection master conditional on the λ-classifier pin.**  Pre-T2 this route was
fenced off (the hypothesis was refuted); under T2 the annotation pin makes the hypothesis
plausibly TRUE, so this is the live assembly route — it fires once the residual's positive proof
lands. -/
theorem HasTypeDescPi.pinnedReflectionOfLamClassifierResidual {profile : PolyProfile}
    (lamClassifierResidual : PinnedReflectionLamClassifierResidual profile)
    (flagUnique : SourceUniverseFlagUnique profile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (derivation : HasTypeDescPi profile targetContext subject classifier) :
    PinnedReflectionConclusion profile targetContext subject classifier :=
  HasTypeDescPi.pinnedReflectionConditional
    (pinnedReflectionPiElimResidualOfLamClassifierResidual profile flagUnique lamClassifierResidual)
    flagUnique
    derivation

/- RETIRED: `pinnedReflectionLamClassifierResidual_isFalse` lived here pre-T2 (witness: the
Curry-style weakened identity λ typed at `Π (var 0). (var 1)` with an unpinnable classifier).
Under T2 the witness typing is impossible — the annotation pin kills the λ-classifier float —
and the residual is expected TRUE.  Deleted with user approval 2026-06-10; the positive proof of
`PinnedReflectionLamClassifierResidual` is the campaign's next target. -/

end FX1Poly.Typed
