import FX1Poly.Typed.PinnedReflectionContext
import FX1Poly.Typed.WfContextDescPiLookup
import FX1Poly.Typed.HasTypeDescPiWeakening

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

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

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
variable ALSO carries a shared-universe validity TRIPLE for its (source lookup, target lookup,
renamed source lookup). -/
def ContextReflectsRenameFlagCoherent (profile : PolyProfile) {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope)
    (targetContext : TypingContext profile targetScope) : Prop :=
  ∀ index : Fin sourceScope,
    Conv (targetContext.lookup (rho index))
      (RawTerm.rename rho (sourceContext.lookup index)) ∧
    SharedUniverseValidityWithImage profile rho sourceContext targetContext
      (sourceContext.lookup index) (targetContext.lookup (rho index))

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
  refine ⟨ContextReflectsRename.ofWeakenCons profile sourceContext bindingType index, ?_⟩
  obtain ⟨levelExpr, flag, lookupValid⟩ :=
    WfContextDescPi.lookupIsType sourceContext wellFormed index
  have weakenedValid : HasTypeDescPi profile (sourceContext.cons bindingType)
      (RawTerm.rename RawRenaming.weaken (sourceContext.lookup index))
      (universeCodeCell levelExpr flag) := by
    have raw := HasTypeDescPi.weakenUnderBinding bindingType lookupValid
    rwa [rename_universeCodeCell] at raw
  exact ⟨levelExpr, flag, weakenedValid, lookupValid, weakenedValid⟩

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
      refine ⟨levelExpr, flag, ?_, ?_, ?_⟩
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
  | succ priorPosition =>
      obtain ⟨levelExpr, flag, targetValid, sourceValid, imageValid⟩ :=
        (coherent ⟨priorPosition, Nat.lt_of_succ_lt_succ isLt⟩).2
      refine ⟨levelExpr, flag, ?_, ?_, ?_⟩
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

end FX1Poly.Typed

