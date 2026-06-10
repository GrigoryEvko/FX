import FX1Poly.Typed.PinnedReflectionContext
import FX1Poly.Typed.HasTypeDescPiFormerInversion
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional

/-! # FX1Poly/Typed/PinnedReflectionPiIntro — THE MOTIVE + the piIntro arm of the pinned reflection
     (route-H reflection brick 6 — the historical wall)

The strengthening campaign's binder arm — the freely-chosen-domain wall that produced the STR-1 and
STR-5b refutations — closes under the pinned motive.  This file ships:

  * `PinnedReflectionConclusion` — THE route-H induction motive.  For a target judgment
    `Δ ⊢ subject : classifier`: for every Fin-injective `ρ` and well-formed source context `Γ`
    satisfying the Kripke image condition, if the subject is an EXACT `ρ`-image and the classifier
    is `Conv`-PINNED to a `ρ`-image of a source-TYPED base, then the source subject is typed at a
    source classifier whose image is `Conv` to the original classifier.
  * `pinnedReflectionPiIntroArm` — the piIntro arm, end-to-end.  The proof composes the whole
    brick-1..5 kit:
      1. `renameEqLamCellInversion` destructures the in-image λ subject;
      2. `Conv.pinnedPiComponentsWithSourceChain` converts the pin into EXACT image components plus
         the SOURCE chain `classifierBase ↝* piTyCodeCell domainBase codomainBase`;
      3. source `subjectReductionStar` + `invertPiTyCode` type `domainBase` / `codomainBase` at
         universes on the SOURCE side (discharging the rebuilt rule's side premises — the step the
         pre-pin designs could not perform);
      4. `ContextReflectsRename.consConv` extends the Kripke condition under the binder;
      5. the body IH fires at `lift ρ` with the codomain pin;
      6. `Conv.reflectLiftRename` (term-level rename injectivity) re-pins the reflected body
         classifier to `codomainBase`, and `HasTypeDescPi.conv` + `piIntro` rebuild.

## Zero-axiom verification

Every ingredient is a shipped zero-axiom brick; the composition adds none.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The route-H pinned-reflection motive.**  For a target judgment `Δ ⊢ subject : classifier`
in a WELL-FORMED target context: for every Fin-injective renaming `ρ` and source context `Γ`
satisfying the Kripke image condition (`ContextReflectsRename`, with `Γ` well-formed), if the
subject is an EXACT `ρ`-image and the classifier is `Conv`-PINNED to a `ρ`-image of a source-TYPED
base, then the source subject is typed at a source classifier whose image is `Conv` to the original
classifier.  Target-side well-formedness is the leading premise: the piElim residual's discharge
routes (whnf-to-head-rigid, the Abel-reflection spine) need TARGET-side SN and subject reduction,
both `WfContextDescPi`-conditional; STR-9's strengthening instance has it freely. -/
def PinnedReflectionConclusion (profile : PolyProfile) {targetScope : Nat}
    (targetContext : TypingContext profile targetScope)
    (subject classifier : RawTerm targetScope) : Prop :=
  WfContextDescPi targetContext →
  ∀ {sourceScope : Nat} (rho : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope),
    Function.Injective rho →
    ContextReflectsRename profile rho sourceContext targetContext →
    WfContextDescPi sourceContext →
    ∀ {sourceSubject pinBase : RawTerm sourceScope},
      subject = RawTerm.rename rho sourceSubject →
      Conv classifier (RawTerm.rename rho pinBase) →
      IsTypeDescPi profile sourceContext pinBase →
      ∃ reflectedClassifier : RawTerm sourceScope,
        Conv classifier (RawTerm.rename rho reflectedClassifier) ∧
        HasTypeDescPi profile sourceContext sourceSubject reflectedClassifier

/-- **The enriched directed context-conversion condition from a head conversion (prefix unchanged).**
The grown twin of `ConvContextWithOldValid.ofHeadStep` for a `Conv` between the two head bindings rather
than a `Step`: the prefix `restContext` is identical, so every prefix entry keeps its target-validity by
weakening (index `k+1` reflexive), and the head pair is the supplied `Conv` (index `0`) with the OLD head
`oldHead` valid in the new context (`headValid` weakened).  This is what re-types the codomain / body across
a domain change `oldHead ≅ newHead` — exactly the move the piIntro arm needs to push `codomainBase` / `body`
off the classifier-pinned `domainBase` onto the subject's syntactic domain annotation. -/
theorem ConvContextWithOldValid.ofHeadConv {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {oldHead newHead : RawTerm scope}
    (oldHeadValid : IsTypeDescPi profile restContext oldHead)
    (restValid : ∀ index : Fin scope, IsTypeDescPi profile restContext (restContext.lookup index))
    (headConv : Conv oldHead newHead) :
    ConvContextWithOldValid (restContext.cons oldHead) (restContext.cons newHead) := by
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      refine ⟨?_, ?_⟩
      · show Conv (RawTerm.rename RawRenaming.weaken oldHead)
          (RawTerm.rename RawRenaming.weaken newHead)
        exact Conv.rename RawRenaming.weaken headConv
      · show IsTypeDescPi profile (restContext.cons newHead)
          (RawTerm.rename RawRenaming.weaken oldHead)
        exact oldHeadValid.weakenUnderBinding newHead
  | succ k =>
      refine ⟨?_, ?_⟩
      · show Conv (RawTerm.rename RawRenaming.weaken
            (restContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
          (RawTerm.rename RawRenaming.weaken
            (restContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
        exact Conv.refl _
      · show IsTypeDescPi profile (restContext.cons newHead)
          (RawTerm.rename RawRenaming.weaken
            (restContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
        exact (restValid ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding newHead

/-- **Source-side universe-classification flag uniqueness, threaded as a premise.**  Convertible
source subjects classified at universe codes carry the SAME flag.  This is exactly
`HasTypeDescPi.convUniverseClassificationUnique`, which is TRUE but lives ARCHITECTURALLY DOWNSTREAM of
this file (it routes through `NormalAppNeutral → PinnedReflectionPiElimDispatcher → … →
PinnedReflectionPiIntro`, a genuine import cycle).  Threading it as a hypothesis is the honest discharge of
the T2 domain/codomain flag-coherence obligation: the λ's domain annotation is reflected at the rule's own
`flag`, while the classifier-pinned codomain comes from the source chain at the inverted Π-code's flag, and
the `piIntro` rule demands BOTH at one flag — their equality is precisely this uniqueness at the
`Conv`-related domain/`domainBase` pair.  The consumer instantiates it once the downstream uniqueness is in
scope (it is supplied to the dispatcher above the cycle). -/
def SourceUniverseFlagUnique (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope}
    {firstSubject secondSubject : RawTerm scope}
    {firstLevel secondLevel : LevelExpr} {firstFlag secondFlag : UniverseFlag},
    WfContextDescPi context →
    Conv firstSubject secondSubject →
    HasTypeDescPi profile context firstSubject (universeCodeCell firstLevel firstFlag) →
    HasTypeDescPi profile context secondSubject (universeCodeCell secondLevel secondFlag) →
    firstFlag = secondFlag

/-- **The piIntro arm of the pinned reflection** — the historical strengthening wall, closed by the
brick-1..5 kit (see the module docstring for the six-step composition) PLUS the T2 domain reflection.

Under T2 the λ carries its domain annotation as a syntactic child, so the reflected subject is
`lamCell sourceDomain sourceBody` with `sourceDomain` PINNED to the subject — not free.  The `piIntro` rule
demands the λ's annotation BE the Π domain and be a valid type, but the classifier pin only delivers a
`Conv`-related `domainBase` (and `IsTypeDescPi` is provably NOT `Conv`-invariant,
`ClassifierRespectsConvRefuted`).  The fix mirrors the grown telescope reflection: the domain is itself a
universe-typed sub-derivation, so it carries its OWN reflection IH (`domainIH`).  Reflecting `domainTyped`
through `domainIH` (then an INLINED `retypeAtUniverse` — `Conv.reflectRenameOfFinInjective` + `conv` +
`ofFormation universeFormation`, all upstream of this file) types `sourceDomain` at `Type@domainLevel` on the
SOURCE side; the body and codomain are re-typed from the classifier-pinned `domainBase` binder onto
`sourceDomain` by the EXACT directed context conversion (`contextConversionExact` fed `ofHeadConv` on
`Conv sourceDomain domainBase`, the rename-reflection of the inverted domain image).  `piIntro` rebuilds at
`lamCell sourceDomain sourceBody : piTyCodeCell sourceDomain codomainBase`.

★ HONESTLY RESTATED: the rule demands the domain annotation and the codomain at ONE shared universe flag.  The
domain is reflected at the λ rule's own `flag`; the codomain comes from the source chain at the inverted
Π-code's flag `baseFlag'`.  These are equal by universe-classification uniqueness, which is architecturally
DOWNSTREAM of this file (import cycle through the piElim dispatcher) — so it is threaded as the explicit
premise `flagUnique : SourceUniverseFlagUnique profile`.  This is the minimal honest extra hypothesis; with
it the arm is fully closed, zero-axiom. -/
theorem pinnedReflectionPiIntroArm (profile : PolyProfile)
    (flagUnique : SourceUniverseFlagUnique profile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {domainCode : RawTerm targetScope} {codomainCode body : RawTerm (targetScope + 1)}
    {domainLevel : LevelExpr} {flag : UniverseFlag}
    (targetDomainTyped :
      HasTypeDescPi profile targetContext domainCode (universeCodeCell domainLevel flag))
    (domainIH :
      PinnedReflectionConclusion profile targetContext domainCode
        (universeCodeCell domainLevel flag))
    (bodyIH :
      PinnedReflectionConclusion profile (targetContext.cons domainCode) body codomainCode) :
    PinnedReflectionConclusion profile targetContext
      (lamCell domainCode body) (piTyCodeCell domainCode codomainCode) := by
  intro targetWellFormed sourceScope rho sourceContext rhoInjective condition wellFormed
    sourceSubject pinBase subjectInImage pinned pinBaseTyped
  obtain ⟨sourceDomain, sourceBody, hSubject, hDomain, hBody⟩ :=
    renameEqLamCellInversion rho subjectInImage.symm
  subst hSubject
  obtain ⟨domainBase, codomainBase, sourceChain, domainConv, codomainConv⟩ :=
    Conv.pinnedPiComponentsWithSourceChain rho pinned
  obtain ⟨baseLevel, baseFlag, baseTyped⟩ := pinBaseTyped
  have piTyped : HasTypeDescPi profile sourceContext
      (piTyCodeCell domainBase codomainBase) (universeCodeCell baseLevel baseFlag) :=
    HasTypeDescPi.subjectReductionStar wellFormed baseTyped sourceChain
  obtain ⟨baseDomainLevel, codomainLevel, baseFlag', domainBaseTyped, codomainTyped, _convToOutput⟩ :=
    HasTypeDescPi.invertPiTyCode piTyped
  -- (1) DOMAIN reflection: reflect the λ's domain annotation through its own IH, re-pinned to the
  --     rename-invariant universe code (typed by `universeFormation`), then an INLINED `retypeAtUniverse`
  --     lands `sourceDomain` at the SOURCE-side universe — the validity `IsTypeDescPi` cannot grant via Conv.
  have domainPin :
      Conv (universeCodeCell domainLevel flag)
        (RawTerm.rename rho (universeCodeCell domainLevel flag)) := by
    rw [rename_universeCodeCell]
    exact Conv.refl _
  obtain ⟨reflectedDomainClassifier, reflectedDomainConv, reflectedDomainTyped⟩ :=
    domainIH targetWellFormed rho sourceContext rhoInjective condition wellFormed
      hDomain domainPin
      ⟨domainLevel.lsucc, flag,
        HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation sourceContext domainLevel flag)⟩
  have reflectedDomainImagesConv :
      Conv (RawTerm.rename rho reflectedDomainClassifier)
        (RawTerm.rename rho (universeCodeCell domainLevel flag)) := by
    rw [rename_universeCodeCell]
    exact reflectedDomainConv.sym
  have reflectedDomainConvCode :
      Conv reflectedDomainClassifier (universeCodeCell domainLevel flag) :=
    Conv.reflectRenameOfFinInjective rho rhoInjective reflectedDomainImagesConv
  have sourceDomainTyped :
      HasTypeDescPi profile sourceContext sourceDomain (universeCodeCell domainLevel flag) :=
    HasTypeDescPi.conv domainLevel.lsucc flag reflectedDomainTyped reflectedDomainConvCode
      (HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation sourceContext domainLevel flag))
  -- (2) `Conv sourceDomain domainBase`: the inverted domain image (`domainCode = rename rho sourceDomain`)
  --     fed into the classifier pin (`Conv domainCode (rename rho domainBase)`), reflected through `rho`.
  have sourceDomainConvBase : Conv sourceDomain domainBase :=
    Conv.reflectRenameOfFinInjective rho rhoInjective (hDomain ▸ domainConv)
  -- ★ flag coherence: domain (at `flag`) and source-chain codomain (at `baseFlag'`) share a flag, by the
  --   threaded downstream universe-classification uniqueness applied to the `Conv`-related domain pair.
  have flagsAgree : flag = baseFlag' :=
    flagUnique wellFormed sourceDomainConvBase sourceDomainTyped domainBaseTyped
  subst flagsAgree
  -- (3) push the codomain / body off the classifier-pinned `domainBase` binder onto `sourceDomain` by the
  --     EXACT directed context conversion (prefix unchanged, head `Conv`).
  have restValid : ∀ index : Fin sourceScope,
      IsTypeDescPi profile sourceContext (sourceContext.lookup index) :=
    fun index => WfContextDescPi.lookupIsType sourceContext wellFormed index
  have enriched :
      ConvContextWithOldValid (sourceContext.cons domainBase) (sourceContext.cons sourceDomain) :=
    ConvContextWithOldValid.ofHeadConv ⟨baseDomainLevel, flag, domainBaseTyped⟩ restValid
      sourceDomainConvBase.sym
  have codomainUnderSourceDomain :
      HasTypeDescPi profile (sourceContext.cons sourceDomain) codomainBase
        (universeCodeCell codomainLevel flag) :=
    HasTypeDescPi.contextConversionExact codomainTyped (sourceContext.cons sourceDomain) enriched
  -- (4) body IH at `lift rho` over the `sourceDomain` binder (domain image EXACT), re-pinned to
  --     `codomainBase` via `reflectLiftRename`, lands `sourceBody` at `codomainBase`.
  have condition' :
      ContextReflectsRename profile (RawRenaming.lift rho)
        (sourceContext.cons sourceDomain) (targetContext.cons domainCode) :=
    ContextReflectsRename.consConv profile condition (hDomain ▸ Conv.refl _)
  have wellFormed' : WfContextDescPi (sourceContext.cons sourceDomain) :=
    ⟨wellFormed, domainLevel, flag, sourceDomainTyped⟩
  have targetWellFormed' : WfContextDescPi (targetContext.cons domainCode) :=
    ⟨targetWellFormed, domainLevel, flag, targetDomainTyped⟩
  obtain ⟨reflectedCodomain, codomainConvReflected, bodyTyped⟩ :=
    bodyIH targetWellFormed' (RawRenaming.lift rho) (sourceContext.cons sourceDomain)
      (RawRenaming.lift_injective rhoInjective) condition' wellFormed'
      hBody codomainConv ⟨codomainLevel, flag, codomainUnderSourceDomain⟩
  have imagesConv :
      Conv (RawTerm.rename (RawRenaming.lift rho) reflectedCodomain)
        (RawTerm.rename (RawRenaming.lift rho) codomainBase) :=
    codomainConvReflected.sym.trans codomainConv
  have reflectedToBase : Conv reflectedCodomain codomainBase :=
    Conv.reflectLiftRename rho rhoInjective imagesConv
  have bodyAtCodomainBase :
      HasTypeDescPi profile (sourceContext.cons sourceDomain) sourceBody codomainBase :=
    HasTypeDescPi.conv codomainLevel flag bodyTyped reflectedToBase codomainUnderSourceDomain
  refine ⟨piTyCodeCell sourceDomain codomainBase, ?_, ?_⟩
  · rw [rename_piTyCodeCell]
    exact Conv.piTyCode_cong (hDomain ▸ Conv.refl _) codomainConv
  · exact HasTypeDescPi.piIntro domainLevel codomainLevel flag
      sourceDomainTyped codomainUnderSourceDomain bodyAtCodomainBase

end FX1Poly.Typed
