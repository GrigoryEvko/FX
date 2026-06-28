import FX1Poly.Typed.Metatheory.Strengthening.PinnedReflectionContext
import FX1Poly.Typed.Engine.WfContext.WfContextDescPiLookup
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiWeakening
import FX1Poly.Typed.Engine.Classifier.DimensionLockAccessibility

/-! # FX1Poly/Typed/FlagCoherentReflectionCondition — the flag-coherent reflection condition
     (route-H reflection, enrichment brick E1)

The flag wall (campaign log): component-wise Π-pin assembly dies on uncoordinated
`UniverseFlag`s — `piIntro`/Π-formation demand domain and codomain validity at a SHARED flag,
while every independent pin producer concludes an uncontrolled ∃-flag `IsTypeDescPi`.  The
enrichment carries, per context variable, a SHARED-universe validity pair: the target lookup and
the source lookup are both valid at ONE common (level, flag).

  * `SharedUniverseValidity` — the flag-coherence payload (one (level, flag) serving both sides).
  * `ContextReflectsRenameFlagCoherent` — the shipped Conv condition strengthened with the pair,
    plus the projection `toContextReflectsRename`.
  * `ofWeakenCons` — the strengthening base instance, from wf-lookup validity + weakening alone.
    NO strengthening circularity: the implication-form payload ("every target validity reflects")
    would BE universe-classified strengthening at the root, so the ∃-shared pair is exactly the
    strongest payload with a non-circular base instance.
  * `consConv` — the Kripke extension step: a binder whose (target domain, source base) pair is
    Conv-pinned AND shared-valid extends the condition; both sides weaken at the same (level,
    flag) (universe classifiers are rename-invariant).

## Zero-axiom verification

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

/-- A SHARED-universe validity pair: `sourceType` and `targetType` are valid types at ONE common
universe (level, flag) in their respective contexts — the flag-coherence payload the Π-pin
reassembly needs (`piIntro`/Π-formation demand a shared flag). -/
def SharedUniverseValidity (profile : PolyProfile) {sourceScope targetScope : Nat}
    (sourceContext : TypingContext profile sourceScope)
    (targetContext : TypingContext profile targetScope)
    (sourceType : RawTerm sourceScope) (targetType : RawTerm targetScope) : Prop :=
  ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
    HasTypeDescPi profile targetContext targetType (universeCodeCell levelExpr flag) ∧
    HasTypeDescPi profile sourceContext sourceType (universeCodeCell levelExpr flag)

/-- The shared-universe validity TRIPLE: the pair plus the IMAGE validity — `rename rho
sourceType` is valid in the target context at the SAME (level, flag).  The image component is
the conv-rule reclassifier the forward renaming lemma's variable arm needs (the renamed source
lookup must be classified in the target to re-classify the target variable at it), and the
direct Δ-side classification the caller-pair negotiation (`convUniverseClassificationUnique`)
compares against. -/
def SharedUniverseValidityWithImage (profile : PolyProfile) {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope)
    (targetContext : TypingContext profile targetScope)
    (sourceType : RawTerm sourceScope) (targetType : RawTerm targetScope) : Prop :=
  ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
    HasTypeDescPi profile targetContext targetType (universeCodeCell levelExpr flag) ∧
    HasTypeDescPi profile sourceContext sourceType (universeCodeCell levelExpr flag) ∧
    HasTypeDescPi profile targetContext (RawTerm.rename rho sourceType)
      (universeCodeCell levelExpr flag)

/-- The triple projects onto the pair. -/
theorem SharedUniverseValidityWithImage.toSharedUniverseValidity
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    {rho : RawRenaming sourceScope targetScope}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    {sourceType : RawTerm sourceScope} {targetType : RawTerm targetScope}
    (triple : SharedUniverseValidityWithImage profile rho sourceContext targetContext
      sourceType targetType) :
    SharedUniverseValidity profile sourceContext targetContext sourceType targetType :=
  let ⟨levelExpr, flag, targetValid, sourceValid, _imageValid⟩ := triple
  ⟨levelExpr, flag, targetValid, sourceValid⟩

/-- **The flag-coherent reflection condition**: `ContextReflectsRename` strengthened so every
variable ALSO carries (a) a shared-universe validity TRIPLE for its (source lookup, target lookup,
renamed source lookup) and (b) a MODALITY-GENERAL ACCESSIBILITY-REFLECTION conjunct (A1-RESTRICT,
#1795): if the renamed image `rho index` is accessible at a use-modality in the target, then the
source `index` is accessible at the SAME use-modality in the source.  The accessibility conjunct is
what the var-arm of `reflectsRenameAtUniverse` needs to re-emit the source `var` (the modality-parametric
`var` rule now demands accessibility at the var's OWN use-modality, fibrant OR dimensional), and it
reflects at every modality because `rho` is built from `weaken` / `lift` over matching lock spines (the
lock is CX/EXTEND, so a plain `cons` is transparent to the suffix). -/
def ContextReflectsRenameFlagCoherent (profile : PolyProfile) {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope)
    (targetContext : TypingContext profile targetScope) : Prop :=
  ∀ index : Fin sourceScope,
    Conv (targetContext.lookup (rho index))
      (RawTerm.rename rho (sourceContext.lookup index)) ∧
    SharedUniverseValidityWithImage profile rho sourceContext targetContext
      (sourceContext.lookup index) (targetContext.lookup (rho index)) ∧
    (∀ modality : ObligationModality,
      targetContext.isAccessibleAtModality (rho index) modality = true →
      sourceContext.isAccessibleAtModality index modality = true)

/-- The flag-coherent condition projects onto the shipped Conv-only condition. -/
theorem ContextReflectsRenameFlagCoherent.toContextReflectsRename
    {profile : PolyProfile} {sourceScope targetScope : Nat}
    {rho : RawRenaming sourceScope targetScope}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (coherent : ContextReflectsRenameFlagCoherent profile rho sourceContext targetContext) :
    ContextReflectsRename profile rho sourceContext targetContext :=
  fun index => (coherent index).1

/-- **The strengthening base instance, flag-coherently**: weakening into a one-binder extension
satisfies the flag-coherent condition — the Conv half is definitional (`ofWeakenCons`), and the
validity pair comes from wf-lookup validity weakened across the new binder (universe codes are
rename-invariant, so the SAME (level, flag) serves both sides).  NO strengthening needed: this is
exactly why the ∃-shared form is the strongest payload with a non-circular root. -/
theorem ContextReflectsRenameFlagCoherent.ofWeakenCons (profile : PolyProfile) {scope : Nat}
    {sourceContext : TypingContext profile scope} (bindingType : RawTerm scope)
    (wellFormed : WfContextDescPi sourceContext) :
    ContextReflectsRenameFlagCoherent profile RawRenaming.weaken
      sourceContext (sourceContext.cons bindingType) := by
  intro index
  refine ⟨ContextReflectsRename.ofWeakenCons profile sourceContext bindingType index, ?_, ?_⟩
  · obtain ⟨levelExpr, flag, lookupValid⟩ :=
      WfContextDescPi.lookupIsType sourceContext wellFormed index
    have weakenedValid : HasTypeDescPi profile (sourceContext.cons bindingType)
        (RawTerm.rename RawRenaming.weaken (sourceContext.lookup index))
        (universeCodeCell levelExpr flag) := by
      have raw := HasTypeDescPi.weakenUnderBinding bindingType lookupValid
      rwa [rename_universeCodeCell] at raw
    exact ⟨levelExpr, flag, weakenedValid, lookupValid, weakenedValid⟩
  · -- accessibility reflection (`rho = weaken`), at EVERY modality: `(source.cons _).isAccessibleAtModality
    -- (weaken index) modality` is DEFEQ `source.isAccessibleAtModality index modality` (a plain `cons` is
    -- suffix-lock-transparent, for the fibrant AND the dimensional accessibility check alike), so the
    -- target-image accessibility IS the source accessibility after destructuring the `Fin` and the modality.
    intro modality accessibleImage
    obtain ⟨indexValue, indexBound⟩ := index
    cases modality with
    | fibrant => exact accessibleImage
    | dimensional => exact accessibleImage

/-- **The flag-coherent Kripke extension step**: the condition survives entering a binder whose
(target domain, source base) pair is Conv-pinned AND shared-universe valid WITH image.  Index 0
is the new triple weakened on both sides (the image component crosses the binder via
`rename_lift_weaken_commute`); index `k + 1` weakens the prior triple (universe classifiers are
rename-invariant, preserving the shared (level, flag)). -/
theorem ContextReflectsRenameFlagCoherent.consConv (profile : PolyProfile)
    {sourceScope targetScope : Nat} {rho : RawRenaming sourceScope targetScope}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    {domainBase : RawTerm sourceScope} {domainCode : RawTerm targetScope}
    (coherent : ContextReflectsRenameFlagCoherent profile rho sourceContext targetContext)
    (domainPinned : Conv domainCode (RawTerm.rename rho domainBase))
    (domainShared : SharedUniverseValidityWithImage profile rho sourceContext targetContext
      domainBase domainCode) :
    ContextReflectsRenameFlagCoherent profile (RawRenaming.lift rho)
      (sourceContext.cons domainBase) (targetContext.cons domainCode) := by
  intro index
  refine ⟨ContextReflectsRename.consConv profile
    (ContextReflectsRenameFlagCoherent.toContextReflectsRename coherent)
    domainPinned index, ?_⟩
  obtain ⟨position, isLt⟩ := index
  cases position with
  | zero =>
      obtain ⟨levelExpr, flag, targetValid, sourceValid, imageValid⟩ := domainShared
      refine ⟨⟨levelExpr, flag, ?_, ?_, ?_⟩, ?_⟩
      · have raw := HasTypeDescPi.weakenUnderBinding domainCode targetValid
        rwa [rename_universeCodeCell] at raw
      · have raw := HasTypeDescPi.weakenUnderBinding domainBase sourceValid
        rwa [rename_universeCodeCell] at raw
      · have raw := HasTypeDescPi.weakenUnderBinding domainCode imageValid
        rw [rename_universeCodeCell] at raw
        show HasTypeDescPi profile (targetContext.cons domainCode)
          (RawTerm.rename (RawRenaming.lift rho)
            (RawTerm.rename RawRenaming.weaken domainBase))
          (universeCodeCell levelExpr flag)
        rw [rename_lift_weaken_commute rho domainBase]
        exact raw
      · -- the fresh `cons`-bound binder `var 0`: at `.fibrant` it is accessible on BOTH sides (`cons`-zero,
        -- `rfl`); at `.dimensional` it is INACCESSIBLE on both sides, so the target-image hypothesis is
        -- absurd (`false = true`) and discharges the implication.
        intro modality accessibleImage
        cases modality with
        | fibrant => rfl
        | dimensional => exact Bool.noConfusion accessibleImage
  | succ priorPosition =>
      obtain ⟨levelExpr, flag, targetValid, sourceValid, imageValid⟩ :=
        (coherent ⟨priorPosition, Nat.lt_of_succ_lt_succ isLt⟩).2.1
      refine ⟨⟨levelExpr, flag, ?_, ?_, ?_⟩, ?_⟩
      · have raw := HasTypeDescPi.weakenUnderBinding domainCode targetValid
        rwa [rename_universeCodeCell] at raw
      · have raw := HasTypeDescPi.weakenUnderBinding domainBase sourceValid
        rwa [rename_universeCodeCell] at raw
      · have raw := HasTypeDescPi.weakenUnderBinding domainCode imageValid
        rw [rename_universeCodeCell] at raw
        show HasTypeDescPi profile (targetContext.cons domainCode)
          (RawTerm.rename (RawRenaming.lift rho)
            (RawTerm.rename RawRenaming.weaken
              (sourceContext.lookup ⟨priorPosition, Nat.lt_of_succ_lt_succ isLt⟩)))
          (universeCodeCell levelExpr flag)
        rw [rename_lift_weaken_commute rho
          (sourceContext.lookup ⟨priorPosition, Nat.lt_of_succ_lt_succ isLt⟩)]
        exact raw
      · -- deeper variable, at EVERY modality: `lift rho (k+1)` is `(rho k).succ`, so target-image
        -- accessibility is DEFEQ `target.isAccessibleAtModality (rho k) modality` and the source side is
        -- DEFEQ `source.isAccessibleAtModality k modality` (the `cons_succ` recursion is modality-uniform);
        -- the prior coherence entry's modality-general accessibility reflection bridges them.
        exact (coherent ⟨priorPosition, Nat.lt_of_succ_lt_succ isLt⟩).2.2

end FX1Poly.Typed

