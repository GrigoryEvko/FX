import FX1Poly.Typed.PinnedReflectionContext
import FX1Poly.Typed.WfContextDescPiLookup
import FX1Poly.Typed.HasTypeDescPiWeakening

/-! Probe: STR-8b enrichment brick E1 — the FLAG-COHERENT reflection condition.  The flag wall
(firing log 2026-06-10 (4)) showed component-wise Π-pin assembly dies on uncoordinated
`UniverseFlag`s; the enrichment carries, per context variable, a SHARED-universe validity pair:
the target lookup and the source lookup are both valid at ONE common (level, flag).  The base
instance is provable from wf + weakening alone (no strengthening circularity — the ∃-shared form
is exactly the strongest payload with a non-circular root), and the Kripke extension step pushes
pairs under binders by weakening both sides. -/

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

/-- **The flag-coherent reflection condition**: `ContextReflectsRename` strengthened so every
variable ALSO carries a shared-universe validity pair for its (source lookup, target lookup). -/
def ContextReflectsRenameFlagCoherent (profile : PolyProfile) {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope)
    (targetContext : TypingContext profile targetScope) : Prop :=
  ∀ index : Fin sourceScope,
    Conv (targetContext.lookup (rho index))
      (RawTerm.rename rho (sourceContext.lookup index)) ∧
    SharedUniverseValidity profile sourceContext targetContext
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
  exact ⟨levelExpr, flag, weakenedValid, lookupValid⟩

/-- **The flag-coherent Kripke extension step**: the condition survives entering a binder whose
(target domain, source base) pair is Conv-pinned AND shared-universe valid.  Index 0 is the new
pair weakened on both sides; index `k + 1` weakens the prior pair (universe classifiers are
rename-invariant, preserving the shared (level, flag)). -/
theorem ContextReflectsRenameFlagCoherent.consConv (profile : PolyProfile)
    {sourceScope targetScope : Nat} {rho : RawRenaming sourceScope targetScope}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    {domainBase : RawTerm sourceScope} {domainCode : RawTerm targetScope}
    (coherent : ContextReflectsRenameFlagCoherent profile rho sourceContext targetContext)
    (domainPinned : Conv domainCode (RawTerm.rename rho domainBase))
    (domainShared : SharedUniverseValidity profile sourceContext targetContext
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
      obtain ⟨levelExpr, flag, targetValid, sourceValid⟩ := domainShared
      refine ⟨levelExpr, flag, ?_, ?_⟩
      · have raw := HasTypeDescPi.weakenUnderBinding domainCode targetValid
        rwa [rename_universeCodeCell] at raw
      · have raw := HasTypeDescPi.weakenUnderBinding domainBase sourceValid
        rwa [rename_universeCodeCell] at raw
  | succ priorPosition =>
      obtain ⟨levelExpr, flag, targetValid, sourceValid⟩ :=
        (coherent ⟨priorPosition, Nat.lt_of_succ_lt_succ isLt⟩).2
      refine ⟨levelExpr, flag, ?_, ?_⟩
      · have raw := HasTypeDescPi.weakenUnderBinding domainCode targetValid
        rwa [rename_universeCodeCell] at raw
      · have raw := HasTypeDescPi.weakenUnderBinding domainBase sourceValid
        rwa [rename_universeCodeCell] at raw

end FX1Poly.Typed

#print axioms FX1Poly.Typed.ContextReflectsRenameFlagCoherent.toContextReflectsRename
#print axioms FX1Poly.Typed.ContextReflectsRenameFlagCoherent.ofWeakenCons
#print axioms FX1Poly.Typed.ContextReflectsRenameFlagCoherent.consConv
