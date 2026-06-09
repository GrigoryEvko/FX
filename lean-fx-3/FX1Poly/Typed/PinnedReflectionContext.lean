import FX1Poly.Typed.PinnedPiRenameImage
import FX1Poly.Typed.CellRenaming
import FX1Poly.Core.RawTermRenameInjective

/-! # FX1Poly/Typed/PinnedReflectionContext — the pinned reflection's context condition + leaf arms
     (route-H reflection brick 4)

The strengthening campaign's three refutations force the route-H reflection motive: induction over
engine derivations of an IN-IMAGE subject with an image-PINNED classifier.  This file ships the
motive's CONTEXT INVARIANT and the formation-engine leaf arms:

  * `ContextReflectsRename` — the Kripke/Conv-relaxed image context condition: every source
    variable's type, looked up through `ρ` in the big context, is `Conv` to the `ρ`-image of its
    source type.  Conv-slack (not exact image equality) is what survives binders: the piIntro arm
    swaps in a domain that is only `Conv` to an image (the 592ded0c analysis).
  * `ContextReflectsRename.ofWeakenCons` — the strengthening base instance
    (`ρ := weaken`, `Δ := Γ.cons B`): definitional, `Conv.refl`.
  * `ContextReflectsRename.consConv` — the Kripke extension step: the condition survives entering a
    binder with a merely Conv-pinned domain, via `rename_lift_weaken_commute` + `Conv.rename`.
  * `renameEqVariableCellInversion` / `renameEqUniverseCodeCellInversion` — the var/universe head
    rename inversions (the leaf-arm subject destructuring; STR-1 drilling).
  * `HasTypeDesc.varArmPinnedReflection` / `HasTypeDesc.universeArmPinnedReflection` — the two
    formation-engine LEAF arms of the reflection, in the motive's conclusion shape
    `∃ S₀, Conv classifier (rename ρ S₀) ∧ Γ ⊢ src : S₀`.  The var arm's `Conv`-to-image IS the
    context condition; the universe arm is rename-invariant on both sides.  Leaves need NO pin —
    the pin exists to propagate through `conv`/`piIntro`/`piElim`.

## Zero-axiom verification

The context lemmas are definitional lookup computation + `rename_lift_weaken_commute` +
`Conv.rename`; the inversions are the STR-1 mkGen drilling (the universe payload's scope-invariance
cast is defeq-transparent at the literal generator).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The Kripke/Conv-relaxed image context condition**: every source variable's type, looked up
through `rho` in the big context, is `Conv` to the `rho`-image of its source type.  The reflection's
context invariant: EXACT image entries (the strengthening base, `ofWeakenCons`) satisfy it by
`Conv.refl`, and the piIntro arm extends it with a merely-Conv-pinned domain (`consConv`) — the slack
that survives binders, where the swapped-in domain is only `Conv` to an image. -/
def ContextReflectsRename (profile : PolyProfile) {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope)
    (targetContext : TypingContext profile targetScope) : Prop :=
  ∀ index : Fin sourceScope,
    Conv (targetContext.lookup (rho index))
      (RawTerm.rename rho (sourceContext.lookup index))

/-- **The strengthening base instance**: weakening into a one-binder extension reflects exactly —
`(Γ.cons B).lookup (weaken i)` IS `weaken (Γ.lookup i)` definitionally. -/
theorem ContextReflectsRename.ofWeakenCons (profile : PolyProfile) {scope : Nat}
    (sourceContext : TypingContext profile scope) (bindingType : RawTerm scope) :
    ContextReflectsRename profile RawRenaming.weaken
      sourceContext (sourceContext.cons bindingType) := by
  intro index
  obtain ⟨position, isLt⟩ := index
  exact Conv.refl _

/-- **The Kripke extension step**: the condition survives entering a binder with a merely
Conv-pinned domain.  Index `0` is the pinned domain through `rename_lift_weaken_commute`; index
`k + 1` is the prior condition weakened by one. -/
theorem ContextReflectsRename.consConv (profile : PolyProfile)
    {sourceScope targetScope : Nat} {rho : RawRenaming sourceScope targetScope}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    {domainBase : RawTerm sourceScope} {domainCode : RawTerm targetScope}
    (condition : ContextReflectsRename profile rho sourceContext targetContext)
    (domainPinned : Conv domainCode (RawTerm.rename rho domainBase)) :
    ContextReflectsRename profile (RawRenaming.lift rho)
      (sourceContext.cons domainBase) (targetContext.cons domainCode) := by
  intro index
  obtain ⟨position, isLt⟩ := index
  cases position with
  | zero =>
      show Conv (RawTerm.rename RawRenaming.weaken domainCode)
        (RawTerm.rename (RawRenaming.lift rho)
          (RawTerm.rename RawRenaming.weaken domainBase))
      rw [rename_lift_weaken_commute]
      exact Conv.rename RawRenaming.weaken domainPinned
  | succ priorPosition =>
      show Conv
        (RawTerm.rename RawRenaming.weaken
          (targetContext.lookup (rho ⟨priorPosition, Nat.lt_of_succ_lt_succ isLt⟩)))
        (RawTerm.rename (RawRenaming.lift rho)
          (RawTerm.rename RawRenaming.weaken
            (sourceContext.lookup ⟨priorPosition, Nat.lt_of_succ_lt_succ isLt⟩)))
      rw [rename_lift_weaken_commute]
      exact Conv.rename RawRenaming.weaken
        (condition ⟨priorPosition, Nat.lt_of_succ_lt_succ isLt⟩)

/-- **Variable-head rename inversion**: an image term that IS a variable comes from a variable at a
preimage index. -/
theorem renameEqVariableCellInversion {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {sourceTerm : RawTerm sourceScope} {index : Fin targetScope}
    (imageIsVar : RawTerm.rename rho sourceTerm = variableCell index) :
    ∃ sourceIndex : Fin sourceScope,
      sourceTerm = variableCell sourceIndex ∧ index = rho sourceIndex := by
  cases sourceTerm with
  | mkGen generator payload children =>
    by_cases hVar : generator = .gen_var
    · subst hVar
      cases children with
      | childNil =>
        rw [RawTerm.rename_var_reduces] at imageIsVar
        injection imageIsVar with hScope hGenerator hPayload hChildren
        exact ⟨payload, rfl, hPayload.symm⟩
    · rw [RawTerm.rename_mkGen_of_ne_var rho hVar] at imageIsVar
      injection imageIsVar with hScope hGenerator hPayload hChildren
      exact absurd hGenerator hVar

/-- **Universe-head rename inversion**: an image term that IS a universe code is that universe code
(universe cells are payload-only and rename-invariant). -/
theorem renameEqUniverseCodeCellInversion {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    {sourceTerm : RawTerm sourceScope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (imageIsUniverse :
      RawTerm.rename rho sourceTerm = universeCodeCell levelExpr flag) :
    sourceTerm = universeCodeCell levelExpr flag := by
  cases sourceTerm with
  | mkGen generator payload children =>
    by_cases hVar : generator = .gen_var
    · subst hVar
      cases children with
      | childNil =>
        rw [RawTerm.rename_var_reduces] at imageIsUniverse
        injection imageIsUniverse with hScope hGenerator hPayload hChildren
        exact Generator.noConfusion hGenerator
    · rw [RawTerm.rename_mkGen_of_ne_var rho hVar] at imageIsUniverse
      injection imageIsUniverse with hScope hGenerator hPayload hChildren
      subst hGenerator
      cases children with
      | childNil =>
        have payloadCastEq := eq_of_heq hPayload
        have payloadEq : payload = (levelExpr, flag) := payloadCastEq
        rw [payloadEq]
        rfl

/-- **The var arm of the pinned reflection** (formation engine): an in-image variable reflects to
the source variable, classified at the source lookup — the conclusion's `Conv`-to-image is EXACTLY
the context condition.  No pin needed at the leaf. -/
theorem HasTypeDesc.varArmPinnedReflection (profile : PolyProfile)
    {sourceScope targetScope : Nat} (rho : RawRenaming sourceScope targetScope)
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (condition : ContextReflectsRename profile rho sourceContext targetContext)
    {sourceSubject : RawTerm sourceScope} {index : Fin targetScope}
    (subjectInImage : RawTerm.rename rho sourceSubject = variableCell index) :
    ∃ sourceClassifier : RawTerm sourceScope,
      Conv (targetContext.lookup index) (RawTerm.rename rho sourceClassifier) ∧
      HasTypeDesc profile sourceContext sourceSubject sourceClassifier := by
  obtain ⟨sourceIndex, hSubject, hIndex⟩ :=
    renameEqVariableCellInversion rho subjectInImage
  subst hSubject
  subst hIndex
  exact ⟨sourceContext.lookup sourceIndex, condition sourceIndex,
    HasTypeDesc.var sourceContext sourceIndex⟩

/-- **The universeFormation arm of the pinned reflection** (formation engine): an in-image universe
code reflects to itself, classified at its successor universe (rename-invariant on both sides). -/
theorem HasTypeDesc.universeArmPinnedReflection (profile : PolyProfile)
    {sourceScope targetScope : Nat} (rho : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope)
    {sourceSubject : RawTerm sourceScope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectInImage :
      RawTerm.rename rho sourceSubject = universeCodeCell levelExpr flag) :
    ∃ sourceClassifier : RawTerm sourceScope,
      Conv (universeCodeCell levelExpr.lsucc flag)
        (RawTerm.rename rho sourceClassifier) ∧
      HasTypeDesc profile sourceContext sourceSubject sourceClassifier := by
  have hSubject := renameEqUniverseCodeCellInversion rho subjectInImage
  subst hSubject
  refine ⟨universeCodeCell levelExpr.lsucc flag, ?_,
    HasTypeDesc.universeFormation sourceContext levelExpr flag⟩
  rw [rename_universeCodeCell]
  exact Conv.refl _

end FX1Poly.Typed
