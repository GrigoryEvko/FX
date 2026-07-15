import FX1Poly.Typed.Metatheory.Strengthening.PinnedReflectionFlagCoherentMaster
import FX1Poly.Typed.Engine.HasTypeDescPi.Inversion.HasTypeDescPiLamInversion
import FX1Poly.Typed.Engine.HasTypeDescPi.Inversion.HasTypeDescPiAppInversion
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiClassifierValidity
import FX1Poly.Typed.Engine.Classifier.UntypableHeadDecision
import FX1Poly.Typed.Engine.HasTypeDescPi.Eta.HasTypeDescPiEtaExpansionGrown
import FX1Poly.Axis.Term.Subst.RawTermSubstLiftWeaken

/-! # FX1Poly/Typed/GrownEtaShapePreservation — shape-stated grown η subject
reduction (bespoke-import-free), extracted from `GrownEtaSubjectReduction`

These are the η subject-reduction arms stated over the η-redex SOURCE
SHAPES (`RawTerm.etaLamSource` et al., now housed in the bespoke-free
`EtaSources`) — they never mention the bespoke `Step.eta` inductive.
Housing them here, in a file whose transitive closure excludes
`StepEta`, lets the KEEP-SET consumers — the table-native subject
reduction `preservedByTableEtaRootNative`, which calls `preservedByEtaLam`
directly — depend on them without depending on the bespoke `Step.eta`
relation.  The relation-dispatching arms (`preservedByEta`,
`subjectReductionBetaEta`, …), which case on `Step.eta` / `Step.betaEta`,
stay in `GrownEtaSubjectReduction` (the bespoke-relation home, slated for
the TABLE-CANON-ETA retirement); that file now imports THIS one for the
substantive λ-arm.

The substantive content is `preservedByEtaLam` (STR-10): η-contraction of
`lam domainAnn (app (weaken f) newestVar)` to `f` is exactly strengthening
on the function part, discharged by the shipped pinned-reflection master.
The four structural arms (pair/path/modal/Glue) are currently vacuous —
their source heads are `isUntypableHead = true` BY `rfl`, so the grown
engine types no instance; each arm holds with a FALSE premise via
`isUntypableHead_sound`, and the `rfl` is the cascade alarm that fires
loudly if those heads ever become grown-typable.

## Zero-axiom verification

Every ingredient is a shipped zero-axiom brick; the composition adds none.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax

/-- **η-SR, λ-arm (STR-10)**: a grown typing of the function-η source
`lam domainAnn (app (weaken f) newestVar)` in a well-formed context descends to `f` at the SAME
classifier — grown typing is preserved by the canonical function-η (`etaLamRow`) contraction (the
shape-stated arm the table-native SR consumes; the legacy `Step.eta.etaLam` fires the same
shape). -/
theorem HasTypeDescPi.preservedByEtaLam {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainAnn innerFunction : RawTerm scope} {classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context
      (RawTerm.etaLamSource domainAnn innerFunction) classifier) :
    HasTypeDescPi profile context innerFunction classifier := by
  have lamTyped : HasTypeDescPi profile context
      (lamCell domainAnn
        (appCell (RawTerm.weaken innerFunction) RawTerm.newestVar)) classifier := typed
  obtain ⟨bodyClassifier, domainLevel, codomainLevel, flag, convToPi, domainTyped,
      _bodyClassifierTyped, bodyTyped⟩ := HasTypeDescPi.invertLam lamTyped
  obtain ⟨innerDomain, innerCodomain, weakenedFunctionTyped, argumentTyped,
      bodyClassifierConv⟩ := HasTypeDescPi.invertApp bodyTyped
  have wellFormedUnderBinder : WfContextDescPi (context.cons domainAnn) :=
    ⟨wellFormed, domainLevel, flag, domainTyped⟩
  -- (1) pin the weakened function's Π classifier: normalize, keep the Π by subject reduction,
  --     reflect the chain, extract the pin from the NORMAL reduct (λ-inclusive).
  have functionStronglyNormalizing :
      StepStar.IsStronglyNormalizing (RawTerm.weaken innerFunction) :=
    HasTypeDescPi.stronglyNormalizingOfWfContextDescPi wellFormedUnderBinder
      weakenedFunctionTyped
  obtain ⟨reduct, functionReduces, reductNormal⟩ :
      ∃ reduct : RawTerm (scope + 1),
        StepStar (RawTerm.weaken innerFunction) reduct ∧ RawTerm.isStepNormalForm reduct :=
    ⟨RawTerm.normalize _ functionStronglyNormalizing,
      RawTerm.normalize_reducesTo _ functionStronglyNormalizing,
      RawTerm.normalize_isStepNormalForm _ functionStronglyNormalizing⟩
  have reductTyped : HasTypeDescPi profile (context.cons domainAnn) reduct
      (piTyCodeCell innerDomain innerCodomain) :=
    HasTypeDescPi.subjectReductionStar wellFormedUnderBinder weakenedFunctionTyped
      functionReduces
  obtain ⟨sourceReduct, _sourceChain, imageEq⟩ :=
    StepStar.reflectRename RawRenaming.weaken
      (show StepStar (RawTerm.rename RawRenaming.weaken innerFunction) reduct
        from functionReduces)
  obtain ⟨piBase, piPinned, piBaseTyped⟩ :=
    normalClassifierPinnedFlagCoherent (budget := reduct.size)
      (fun {smallBound} _withinBudget =>
        piElimResidualGuardedAtEveryBound profile (sourceUniverseFlagUniqueHolds profile)
          smallBound)
      (sourceUniverseFlagUniqueHolds profile) reductTyped reductNormal (Nat.le_refl _)
      wellFormedUnderBinder RawRenaming.weaken context RawRenaming.weaken_finInjective
      (ContextReflectsRenameFlagCoherent.ofWeakenCons profile domainAnn wellFormed)
      wellFormed imageEq.symm
  -- (2) reflect the weakened function's typing to the smaller scope (premise-free master).
  obtain ⟨reflectedPi, reflectedPiConv, functionReflected⟩ :=
    HasTypeDescPi.pinnedReflectionFlagCoherentUnconditional weakenedFunctionTyped
      wellFormedUnderBinder RawRenaming.weaken context RawRenaming.weaken_finInjective
      (ContextReflectsRenameFlagCoherent.ofWeakenCons profile domainAnn wellFormed)
      wellFormed
      (show RawTerm.weaken innerFunction
          = RawTerm.rename RawRenaming.weaken innerFunction from rfl)
      piPinned piBaseTyped
  -- (3) the reflected Π's exact-image components.
  obtain ⟨reflectedDomain, reflectedCodomain, reflectedChain, innerDomainConv,
      innerCodomainConv⟩ :=
    Conv.pinnedPiComponentsWithSourceChain RawRenaming.weaken reflectedPiConv
  -- (4) η-coherence, codomain leg: the body classifier collapses to the reflected codomain —
  --     the lifted-weakening substitution at the newest variable is the identity.
  have substConv : Conv (RawTerm.subst0 innerCodomain RawTerm.newestVar)
      (RawTerm.subst0
        (RawTerm.rename (RawRenaming.lift RawRenaming.weaken) reflectedCodomain)
        RawTerm.newestVar) :=
    Conv.subst _ innerCodomainConv
  rw [RawTerm.subst0_lift_weaken_newestVar] at substConv
  have bodyClassifierToReflected : Conv bodyClassifier reflectedCodomain :=
    bodyClassifierConv.trans substConv
  -- (5) η-coherence, domain leg: the inner domain pins to the weakened annotation through the
  --     newest variable's lookup, and `Conv.reflectWeaken` strips the shared weakening.
  have innerDomainToWeakenedAnn :
      Conv innerDomain (RawTerm.rename RawRenaming.weaken domainAnn) :=
    HasTypeDescPi.invertVar argumentTyped
  have annToReflectedDomain : Conv domainAnn reflectedDomain :=
    Conv.reflectWeaken (innerDomainToWeakenedAnn.sym.trans innerDomainConv)
  -- (6) assemble: the original λ classifier is Conv to the reflected classifier.
  have reflectedPiToComponents :
      Conv reflectedPi (piTyCodeCell reflectedDomain reflectedCodomain) :=
    ⟨piTyCodeCell reflectedDomain reflectedCodomain, reflectedChain, StepStar.refl _⟩
  have piComponentsCong :
      Conv (piTyCodeCell domainAnn bodyClassifier)
        (piTyCodeCell reflectedDomain reflectedCodomain) :=
    Conv.piTyCode_cong annToReflectedDomain bodyClassifierToReflected
  have classifierToReflectedPi : Conv classifier reflectedPi :=
    (convToPi.trans piComponentsCong).trans reflectedPiToComponents.sym
  -- (7) land at the ORIGINAL classifier via the grown conv rule (classifier validity from wf).
  obtain ⟨classifierLevel, classifierFlag, classifierTyped⟩ :=
    typed.classifierIsTypeDescPi wellFormed
  exact HasTypeDescPi.conv classifierLevel classifierFlag functionReflected
    classifierToReflectedPi.sym classifierTyped

/-! ## The structural η arms (STR-11) — VACUOUS on the current grown engine, honestly so

The pair / cubical-path / modal / Glue η sources are headed by `gen_pair` / `gen_pathLam` /
`gen_modIntro` / `gen_glueIntro` — all `isUntypableHead = true` BY `rfl` (no formation, intro,
or elim row; not a bespoke head), so the grown engine types NO instance of these sources and
each arm holds with a FALSE premise via `isUntypableHead_sound`.

This is the honest current status, not a permanent fact: when pair/modal/cubical/Glue typing
rules land in the grown tables, `isUntypableHead` flips to `false` for those heads BY `rfl`
FAILURE — these proofs then break loudly at the `rfl` argument and force substantive
re-proofs.  The decision procedure is the cascade alarm. -/

/-- η-SR, pair arm — vacuous: `gen_pair` is grown-untypable today. -/
theorem HasTypeDescPi.preservedByEtaPair {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {pairTerm : RawTerm scope} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context
      (RawTerm.etaPairSource pairTerm) classifier) :
    HasTypeDescPi profile context pairTerm classifier :=
  (isUntypableHead_sound rfl typed).elim

/-- η-SR, cubical-path arm — vacuous: `gen_pathLam` is grown-untypable today. -/
theorem HasTypeDescPi.preservedByEtaPathLam {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {innerPath : RawTerm scope} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context
      (RawTerm.etaPathLamSource innerPath) classifier) :
    HasTypeDescPi profile context innerPath classifier :=
  (isUntypableHead_sound rfl typed).elim

/-- η-SR, modal arm — vacuous: `gen_modIntro` is grown-untypable today. -/
theorem HasTypeDescPi.preservedByEtaModIntro {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {modalTerm : RawTerm scope} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context
      (RawTerm.etaModIntroSource modalTerm) classifier) :
    HasTypeDescPi profile context modalTerm classifier :=
  (isUntypableHead_sound rfl typed).elim

/-- η-SR, Glue arm — vacuous: `gen_glueIntro` is grown-untypable today. -/
theorem HasTypeDescPi.preservedByEtaGlueIntro {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {gluedTerm : RawTerm scope} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context
      (RawTerm.etaGlueIntroSource gluedTerm) classifier) :
    HasTypeDescPi profile context gluedTerm classifier :=
  (isUntypableHead_sound rfl typed).elim

/-- **η-SR round-trip regression (non-vacuity of the λ-arm)**: for ANY grown-typed function,
the forward η-expansion (`etaExpansionPreservesTypingGrown`, TY-ETA-GROWN) produces a REAL
typed η-source, and the λ-arm contracts it back to the function at the SAME classifier — the
λ-arm fires on every grown function typing, not just on an empty premise. -/
theorem HasTypeDescPi.etaExpandContractRoundTrip {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (wellFormed : WfContextDescPi context)
    (functionTyped :
      HasTypeDescPi profile context functionTerm (piTyCodeCell domainCode codomainCode)) :
    HasTypeDescPi profile context functionTerm (piTyCodeCell domainCode codomainCode) :=
  HasTypeDescPi.preservedByEtaLam wellFormed
    (HasTypeDescPi.etaExpansionPreservesTypingGrown wellFormed functionTyped)

end FX1Poly.Typed
