import FX1Poly.Typed.FlagCoherentReflectionCondition
import FX1Poly.Typed.HasTypeDescWeakening
import FX1Poly.Typed.CellRenaming

/-! # Forward renaming along the flag-coherent condition (E3 core)

Grown typing is preserved along ANY renaming satisfying the flag-coherent Conv condition — the
Conv-condition twin of `renameRespectingContext` (whose condition demands EXACT lookup
commutation).  The formation companion renames a formation derivation into a GROWN derivation:
the variable arm re-classifies the target variable across the condition's Conv half with the
IMAGE half as the conv-rule reclassifier — the exact consumer the image component of
`SharedUniverseValidityWithImage` was added for.  Binder crossings extend the condition via
`ContextReflectsRenameFlagCoherent.consConv` with the renamed component as the new target domain
(`Conv.refl` pin; the image and target halves coincide syntactically).

Consumers (the E3/E4 negotiations): a source-side validity renames into the target context,
where `convUniverseClassificationUnique` compares it against the caller's (level, flag) pair —
collapsing every flag negotiation of the pinned-reflection campaign to a one-step application. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

mutual

/-- **Formation typing renames to GROWN typing along the flag-coherent condition.**  The variable
arm re-classifies the target variable across the condition's Conv half with the IMAGE half as the
conv-rule reclassifier — the exact consumer the image component was added for. -/
theorem HasTypeDesc.renameAlongFlagCoherentToGrown {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDesc profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rho : RawRenaming sourceScope targetScope),
      ContextReflectsRenameFlagCoherent profile rho sourceContext targetContext →
      HasTypeDescPi profile targetContext
        (RawTerm.rename rho subject) (RawTerm.rename rho classifier) :=
  match derivation with
  | .var _sourceContext index => fun targetContext rho condition => by
      obtain ⟨lookupConv, levelExpr, flag, _targetValid, _sourceValid, imageValid⟩ :=
        condition index
      rw [rename_variableCell]
      exact HasTypeDescPi.conv levelExpr flag
        (HasTypeDescPi.ofFormation (HasTypeDesc.var targetContext (rho index)))
        lookupConv imageValid
  | .conv levelExpr flag typedPremise converts reclassifierTyped =>
      fun targetContext rho condition => by
        have premiseTyped := HasTypeDesc.renameAlongFlagCoherentToGrown typedPremise
          targetContext rho condition
        have reclassifierRenamed := HasTypeDesc.renameAlongFlagCoherentToGrown
          reclassifierTyped targetContext rho condition
        rw [rename_universeCodeCell] at reclassifierRenamed
        exact HasTypeDescPi.conv levelExpr flag premiseTyped
          (Conv.rename rho converts) reclassifierRenamed
  | .universeFormation _sourceContext levelExpr flag =>
      fun targetContext rho _condition => by
        rw [rename_universeCodeCell, rename_universeCodeCell]
        exact HasTypeDescPi.ofFormation
          (HasTypeDesc.universeFormation targetContext levelExpr flag)
  | .genFormation _sourceContext generator payload children levels flag rule
      isFormation premises => fun targetContext rho condition => by
      have renamedPremises := DescTelescope.renameAlongFlagCoherentToGrownTelescope
        premises targetContext rho condition
      have hNotVar : generator ≠ Generator.gen_var :=
        formationRuleImpliesNotVariable isFormation
      -- ROW-SHAPE-AGNOSTIC: rather than pinning `rule` to `universeFormerOutput`, rewrite the
      -- ABSTRACT rule's renamed output via `typingRuleDescOf_output_renameStable` (universe codes
      -- are scope-polymorphic leaves for every row shape) and reconstruct with the ORIGINAL abstract
      -- `rule`/`isFormation`.  Survives the nullary-row table flip with no edits.
      rw [typingRuleDescOf_output_renameStable isFormation rho levels flag,
        RawTerm.rename_mkGen_of_ne_var rho hNotVar]
      exact HasTypeDescPi.genFormationPi targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.rename rho children) levels flag
        rule isFormation renamedPremises

/-- The formation premise telescope renames to a GROWN telescope along the flag-coherent
condition; binder crossings extend the condition via `consConv` (the new pair is the renamed
head with a `Conv.refl` pin; the image and target halves coincide). -/
theorem DescTelescope.renameAlongFlagCoherentToGrownTelescope {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile sourceContext levels flag children) :
    ∀ {targetBaseScope : Nat}
      (targetContext : TypingContext profile (targetBaseScope + currentDepth))
      (rho : RawRenaming baseScope targetBaseScope),
      ContextReflectsRenameFlagCoherent profile (iterateLiftRaw rho currentDepth)
        sourceContext targetContext →
      DescTelescopePi profile targetContext levels flag
        (RawTermChildren.rename rho children) :=
  match telescope with
  | .nil _sourceContext flag => fun targetContext _rho _condition =>
      DescTelescopePi.nil targetContext flag
  | .cons _sourceContext head headLevel restLevels flag rest headTyped restTyped =>
      fun targetContext rho condition => by
        have renamedHeadTyped : HasTypeDescPi profile targetContext
            (RawTerm.rename (iterateLiftRaw rho currentDepth) head)
            (universeCodeCell headLevel flag) := by
          have headRenamed := HasTypeDesc.renameAlongFlagCoherentToGrown headTyped
            targetContext (iterateLiftRaw rho currentDepth) condition
          rwa [rename_universeCodeCell] at headRenamed
        refine DescTelescopePi.cons targetContext
          (RawTerm.rename (iterateLiftRaw rho currentDepth) head) headLevel
          restLevels flag (RawTermChildren.rename rho rest) renamedHeadTyped ?_
        exact DescTelescope.renameAlongFlagCoherentToGrownTelescope restTyped
          (targetContext.cons (RawTerm.rename (iterateLiftRaw rho currentDepth) head))
          rho
          (ContextReflectsRenameFlagCoherent.consConv profile condition
            (Conv.refl _)
            ⟨headLevel, flag, renamedHeadTyped,
              HasTypeDescPi.ofFormation headTyped, renamedHeadTyped⟩)

end

mutual

/-- **GROWN typing is preserved along any flag-coherent renaming** — the Conv-condition twin of
`renameRespectingContext`, the forward fibration leg of the route-H reflection.  The negotiation
consumer: a source-side validity renames into the target context, where
`convUniverseClassificationUnique` compares it against the caller's pair. -/
theorem HasTypeDescPi.renameAlongFlagCoherent {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescPi profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rho : RawRenaming sourceScope targetScope),
      ContextReflectsRenameFlagCoherent profile rho sourceContext targetContext →
      HasTypeDescPi profile targetContext
        (RawTerm.rename rho subject) (RawTerm.rename rho classifier) :=
  match derivation with
  | .ofFormation formationTyped => fun targetContext rho condition =>
      HasTypeDesc.renameAlongFlagCoherentToGrown formationTyped targetContext rho condition
  | .conv levelExpr flag typed converts reclassifierTyped =>
      fun targetContext rho condition => by
        have typedRenamed := HasTypeDescPi.renameAlongFlagCoherent typed
          targetContext rho condition
        have reclassifierRenamed := HasTypeDescPi.renameAlongFlagCoherent reclassifierTyped
          targetContext rho condition
        rw [rename_universeCodeCell] at reclassifierRenamed
        exact HasTypeDescPi.conv levelExpr flag typedRenamed
          (Conv.rename rho converts) reclassifierRenamed
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => fun targetContext rho condition => by
      have domainRenamed := HasTypeDescPi.renameAlongFlagCoherent domainTyped
        targetContext rho condition
      rw [rename_universeCodeCell] at domainRenamed
      have extendedCondition := ContextReflectsRenameFlagCoherent.consConv profile condition
        (Conv.refl (RawTerm.rename rho domainCode))
        ⟨domainLevel, flag, domainRenamed, domainTyped, domainRenamed⟩
      have codomainRenamed := HasTypeDescPi.renameAlongFlagCoherent codomainTyped
        (targetContext.cons (RawTerm.rename rho domainCode))
        (iterateLiftRaw rho 1) extendedCondition
      rw [rename_universeCodeCell] at codomainRenamed
      have bodyRenamed := HasTypeDescPi.renameAlongFlagCoherent bodyTyped
        (targetContext.cons (RawTerm.rename rho domainCode))
        (iterateLiftRaw rho 1) extendedCondition
      rw [rename_lamCell, rename_piTyCodeCell]
      exact HasTypeDescPi.piIntro domainLevel codomainLevel flag domainRenamed
        codomainRenamed bodyRenamed
  | @HasTypeDescPi.piElim _ _ _ functionTerm argument domainCode codomainCode
      functionTyped argumentTyped => fun targetContext rho condition => by
      have functionRenamed := HasTypeDescPi.renameAlongFlagCoherent functionTyped
        targetContext rho condition
      rw [rename_piTyCodeCell] at functionRenamed
      have argumentRenamed := HasTypeDescPi.renameAlongFlagCoherent argumentTyped
        targetContext rho condition
      rw [rename_appCell, RawTerm.rename_subst0_commute]
      exact HasTypeDescPi.piElim functionRenamed argumentRenamed
  | .genFormationPi _sourceContext generator payload children levels flag rule
      isFormation premises => fun targetContext rho condition => by
      have renamedPremises := DescTelescopePi.renameAlongFlagCoherentTelescope premises
        targetContext rho condition
      have hNotVar : generator ≠ Generator.gen_var :=
        formationRuleImpliesNotVariable isFormation
      -- ROW-SHAPE-AGNOSTIC: rewrite the ABSTRACT rule's renamed output via
      -- `typingRuleDescOf_output_renameStable` and reconstruct over the ORIGINAL abstract `rule`;
      -- the flag is merely forwarded into `genFormationPi` (not pinned), so the nullary-row flip
      -- absorbs here unchanged.
      rw [typingRuleDescOf_output_renameStable isFormation rho levels flag,
        RawTerm.rename_mkGen_of_ne_var rho hNotVar]
      exact HasTypeDescPi.genFormationPi targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.rename rho children) levels flag
        rule isFormation renamedPremises

/-- The grown premise telescope renames along the flag-coherent condition (heads are grown
already — the source half of the `consConv` triple is the head premise itself). -/
theorem DescTelescopePi.renameAlongFlagCoherentTelescope {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile sourceContext levels flag children) :
    ∀ {targetBaseScope : Nat}
      (targetContext : TypingContext profile (targetBaseScope + currentDepth))
      (rho : RawRenaming baseScope targetBaseScope),
      ContextReflectsRenameFlagCoherent profile (iterateLiftRaw rho currentDepth)
        sourceContext targetContext →
      DescTelescopePi profile targetContext levels flag
        (RawTermChildren.rename rho children) :=
  match telescope with
  | .nil _sourceContext flag => fun targetContext _rho _condition =>
      DescTelescopePi.nil targetContext flag
  | .cons _sourceContext head headLevel restLevels flag rest headTyped restTyped =>
      fun targetContext rho condition => by
        have renamedHeadTyped : HasTypeDescPi profile targetContext
            (RawTerm.rename (iterateLiftRaw rho currentDepth) head)
            (universeCodeCell headLevel flag) := by
          have headRenamed := HasTypeDescPi.renameAlongFlagCoherent headTyped
            targetContext (iterateLiftRaw rho currentDepth) condition
          rwa [rename_universeCodeCell] at headRenamed
        refine DescTelescopePi.cons targetContext
          (RawTerm.rename (iterateLiftRaw rho currentDepth) head) headLevel
          restLevels flag (RawTermChildren.rename rho rest) renamedHeadTyped ?_
        exact DescTelescopePi.renameAlongFlagCoherentTelescope restTyped
          (targetContext.cons (RawTerm.rename (iterateLiftRaw rho currentDepth) head))
          rho
          (ContextReflectsRenameFlagCoherent.consConv profile condition
            (Conv.refl _)
            ⟨headLevel, flag, renamedHeadTyped, headTyped, renamedHeadTyped⟩)

end

end FX1Poly.Typed

