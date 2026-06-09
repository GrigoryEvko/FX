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
  * `pinnedReflectionLamClassifierResidual_isFalse` — ★ the residual is FALSE.  The STR-1 witness
    (the weakened identity λ, grown-typed at `Π (var 0). (var 1)` in `[Type@0]`) satisfies EVERY
    premise — normal, in-image, both contexts wf, vacuous condition, vacuously-injective empty
    renaming — yet `variableDomainPi_notConvWeakenImage` shows its classifier has no pin.

## Consequence (the route fence)

The reduction theorems above are sound implications but can NEVER fire — this factorization is a
dead end, mechanically fenced like the three STR refutations before it.  An UNAPPLIED λ's
classifier genuinely floats outside the image.  The surviving route is discharging
`PinnedReflectionPiElimLamReductResidual` DIRECTLY: there the λ is the whnf of an APPLIED
function, and the conclusion's OUTPUT-PIN premise (`Conv (subst0 codomainCode argument) (rename
rho pinBase)`) excludes exactly this witness — its instantiated codomain is the fresh variable
itself, unpinnable, so the premises are unsatisfiable on the refuting shape.  The output pin and
the argument premises are load-bearing, not conveniences.

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

/-- **The pinned-reflection master conditional on the λ-classifier pin** — a sound implication,
permanently VACUOUS by the refutation below: the hypothesis is false, so this route never fires.
Kept as the mechanical fence record of the factorization attempt. -/
theorem HasTypeDescPi.pinnedReflectionOfLamClassifierResidual {profile : PolyProfile}
    (lamClassifierResidual : PinnedReflectionLamClassifierResidual profile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (derivation : HasTypeDescPi profile targetContext subject classifier) :
    PinnedReflectionConclusion profile targetContext subject classifier :=
  HasTypeDescPi.pinnedReflectionConditional
    (pinnedReflectionPiElimResidualOfLamClassifierResidual profile lamClassifierResidual)
    derivation

/-- ★ **The bare λ-classifier pin residual is FALSE.**  The STR-1 witness instantiates every
premise: the weakened identity λ is normal, in the (empty-source) weaken image, grown-typed at
`Π (var 0). (var 1)` in the well-formed `[Type@0]`, with the vacuous reflection condition and the
vacuously-injective scope-0 renaming — and `variableDomainPi_notConvWeakenImage` denies the
concluded pin.  An UNAPPLIED λ's classifier genuinely floats; only the λ-REDUCT residual (whose
output-pin premise excludes this witness) remains dischargeable. -/
theorem pinnedReflectionLamClassifierResidual_isFalse (profile : PolyProfile) :
    ¬ PinnedReflectionLamClassifierResidual profile := by
  intro residual
  have subjectEq : RawTerm.weaken identityLambda
      = lamCell (variableCell (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2)) := rfl
  have lamTyped : HasTypeDescPi profile
      ((TypingContext.empty (profile := profile)).cons (typeZeroCode 0))
      (lamCell (variableCell (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2))) variableDomainPi := by
    have weakenedTyping := weakenedIdentityTypedAtVariableDomainPi profile
    rwa [subjectEq] at weakenedTyping
  have lamNormal : RawTerm.isStepNormalForm
      (lamCell (variableCell (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2))) := by decide
  have targetWellFormed : WfContextDescPi
      ((TypingContext.empty (profile := profile)).cons (typeZeroCode 0)) :=
    ⟨trivial, LevelExpr.lzero.lsucc, UniverseFlag.standard,
      HasTypeDescPi.ofFormation
        (HasTypeDesc.universeFormation .empty LevelExpr.lzero UniverseFlag.standard)⟩
  have weakenInjectiveAtZero :
      Function.Injective (RawRenaming.weaken : RawRenaming 0 1) :=
    fun {leftIndex} _rightIndex _imagesAgree => leftIndex.elim0
  obtain ⟨base, classifierPinned, _baseValid⟩ :=
    residual lamTyped lamNormal targetWellFormed RawRenaming.weaken TypingContext.empty
      weakenInjectiveAtZero
      (ContextReflectsRename.ofWeakenCons profile TypingContext.empty (typeZeroCode 0))
      WfContextDescPi.emptyIsWellFormed
      (sourceLam := identityLambda) subjectEq.symm
  exact variableDomainPi_notConvWeakenImage base classifierPinned

end FX1Poly.Typed
