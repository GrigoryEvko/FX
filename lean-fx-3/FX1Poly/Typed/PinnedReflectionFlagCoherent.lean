import FX1Poly.Typed.PinnedReflectionPiElimDispatcher
import FX1Poly.Typed.PinSelectsCallerPair

/-! # The flag-coherent pinned-reflection motive (E2-0)

The pinned-reflection motive with the reflection condition upgraded to
`ContextReflectsRenameFlagCoherent` — the enriched ecosystem's anchor.  The enriched condition
PROJECTS onto the plain one, so the whole shipped conditional master transfers freely
(`pinnedReflectionFlagCoherentOfPlainResidual`); the point of the enrichment is the RESIDUAL:
its eventual discharge (the route-(A) typed-LR argument) receives the flag-coherent condition —
the per-variable shared-universe triples that steer the λ-reduct's fresh (domain, codomain)
choice, per the E4-0/E4-1 spike findings (whole-pin reflection and syntactic linkage are both
refuted; see the campaign fences).

Consumers: STR-9's strengthening instance enters through `ofWeakenCons` (which produces the
enriched condition directly under source wf), so the enriched master serves the campaign
endpoint exactly as the plain one would. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The flag-coherent pinned-reflection motive**: `PinnedReflectionConclusion` with the
reflection condition upgraded to `ContextReflectsRenameFlagCoherent` (Conv + the shared-universe
TRIPLE per variable).  Weaker as a statement (stronger premise), so the shipped plain master
transfers freely; the point is the RESIDUAL — its discharge receives the richer condition. -/
def PinnedReflectionConclusionFlagCoherent (profile : PolyProfile) {targetScope : Nat}
    (targetContext : TypingContext profile targetScope)
    (subject classifier : RawTerm targetScope) : Prop :=
  WfContextDescPi targetContext →
  ∀ {sourceScope : Nat} (rho : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope),
    Function.Injective rho →
    ContextReflectsRenameFlagCoherent profile rho sourceContext targetContext →
    WfContextDescPi sourceContext →
    ∀ {sourceSubject pinBase : RawTerm sourceScope},
      subject = RawTerm.rename rho sourceSubject →
      Conv classifier (RawTerm.rename rho pinBase) →
      IsTypeDescPi profile sourceContext pinBase →
      ∃ reflectedClassifier : RawTerm sourceScope,
        Conv classifier (RawTerm.rename rho reflectedClassifier) ∧
        HasTypeDescPi profile sourceContext sourceSubject reflectedClassifier

/-- The plain conclusion weakens to the flag-coherent one (the enriched condition projects). -/
theorem PinnedReflectionConclusion.toFlagCoherent {profile : PolyProfile}
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (plain : PinnedReflectionConclusion profile targetContext subject classifier) :
    PinnedReflectionConclusionFlagCoherent profile targetContext subject classifier :=
  fun targetWellFormed {_sourceScope} rho sourceContext rhoInjective coherent
      sourceWellFormed {_sourceSubject} {_pinBase} subjectEq pinned pinBaseTyped =>
    plain targetWellFormed rho sourceContext rhoInjective
      coherent.toContextReflectsRename sourceWellFormed subjectEq pinned pinBaseTyped

/-- **The flag-coherent piElim residual** — the route-(A) target's umbrella form: as the shipped
`PinnedReflectionPiElimResidual` but with the flag-coherent motive throughout (the IH premises
weaken, the conclusion's condition enriches). -/
def PinnedReflectionPiElimResidualFlagCoherent (profile : PolyProfile) : Prop :=
  ∀ {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {functionTerm argument domainCode : RawTerm targetScope}
    {codomainCode : RawTerm (targetScope + 1)},
    HasTypeDescPi profile targetContext functionTerm
      (piTyCodeCell domainCode codomainCode) →
    HasTypeDescPi profile targetContext argument domainCode →
    PinnedReflectionConclusionFlagCoherent profile targetContext functionTerm
      (piTyCodeCell domainCode codomainCode) →
    PinnedReflectionConclusionFlagCoherent profile targetContext argument domainCode →
    PinnedReflectionConclusionFlagCoherent profile targetContext
      (appCell functionTerm argument) (RawTerm.subst0 codomainCode argument)

/-- **The flag-coherent λ-reduct residual** — THE precise route-(A) discharge target: the
λ-headed-after-whnf case with the flag-coherent condition available in the conclusion's
premises (the binder-steering data the E4-0/E4-1 spikes showed the discharge needs). -/
def PinnedReflectionPiElimLamReductResidualFlagCoherent (profile : PolyProfile) : Prop :=
  ∀ {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {functionTerm argument domainCode : RawTerm targetScope}
    {codomainCode lamBody : RawTerm (targetScope + 1)},
    HasTypeDescPi profile targetContext functionTerm
      (piTyCodeCell domainCode codomainCode) →
    HasTypeDescPi profile targetContext argument domainCode →
    StepStar functionTerm (lamCell lamBody) →
    RawTerm.isStepNormalForm (lamCell lamBody) →
    PinnedReflectionConclusionFlagCoherent profile targetContext functionTerm
      (piTyCodeCell domainCode codomainCode) →
    PinnedReflectionConclusionFlagCoherent profile targetContext argument domainCode →
    PinnedReflectionConclusionFlagCoherent profile targetContext
      (appCell functionTerm argument) (RawTerm.subst0 codomainCode argument)

/-- **The free transfer**: given the PLAIN piElim residual, EVERY grown derivation satisfies the
flag-coherent conclusion — the whole shipped conditional master weakens through the projection.
The enriched ecosystem's anchor: route (A) replaces the plain-residual hypothesis with a direct
discharge of the flag-coherent residual; until then the two masters agree wherever the plain
residual fires. -/
theorem HasTypeDescPi.pinnedReflectionFlagCoherentOfPlainResidual {profile : PolyProfile}
    (residual : PinnedReflectionPiElimResidual profile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (derivation : HasTypeDescPi profile targetContext subject classifier) :
    PinnedReflectionConclusionFlagCoherent profile targetContext subject classifier :=
  (HasTypeDescPi.pinnedReflectionConditional residual derivation).toFlagCoherent

end FX1Poly.Typed

