import FX1Poly.Typed.TypedTypeValidityBoxedRelation
import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Core.NeutralTermRename

/-! Probe: LR-weakening — TypedTypeValidityBoxed respects context renaming (piType recurses with lift ρ on
    the codomain). Existential box conclusion. Mirrors HasTypeDescPi.renameRespectingContext. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

theorem IsTypeDescPi.renameRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {classifier : RawTerm sourceScope}
    (isType : IsTypeDescPi profile sourceContext classifier)
    {targetScope : Nat} (targetContext : TypingContext profile targetScope)
    (rawRenaming : RawRenaming sourceScope targetScope)
    (contextCondition : ∀ index : Fin sourceScope,
      RawTerm.rename rawRenaming (sourceContext.lookup index)
        = targetContext.lookup (rawRenaming index)) :
    IsTypeDescPi profile targetContext (RawTerm.rename rawRenaming classifier) := by
  obtain ⟨levelExpr, flag, typed⟩ := isType
  have renamed := typed.renameRespectingContext targetContext rawRenaming contextCondition
  rw [rename_universeCodeCell] at renamed
  exact ⟨levelExpr, flag, renamed⟩

theorem TypedTypeValidityBoxed.renameRespectingContextExists {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {typeCode : RawTerm sourceScope} {box : KripkeCandBox sourceScope}
    (relation : TypedTypeValidityBoxed profile sourceContext typeCode box) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
      (∀ index : Fin sourceScope,
        RawTerm.rename rawRenaming (sourceContext.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      ∃ box' : KripkeCandBox targetScope,
        TypedTypeValidityBoxed profile targetContext (RawTerm.rename rawRenaming typeCode) box' :=
  match relation with
  | .neutral neutralCode validity => fun targetContext rawRenaming contextCondition =>
      ⟨KripkeCandBox.mk snKripkeCand,
        TypedTypeValidityBoxed.neutral (neutralCode.rename rawRenaming)
          (validity.renameRespectingContext targetContext rawRenaming contextCondition)⟩
  | .universeType validity => fun targetContext rawRenaming contextCondition => by
      have validityRenamed :=
        validity.renameRespectingContext targetContext rawRenaming contextCondition
      rw [rename_universeCodeCell] at validityRenamed ⊢
      exact ⟨KripkeCandBox.mk snKripkeCand, TypedTypeValidityBoxed.universeType validityRenamed⟩
  | @TypedTypeValidityBoxed.piType _ _ _ domainCode codomainCode _ _ _codomainFamily
      domainValid codomainValid validity =>
      fun targetContext rawRenaming contextCondition => by
        have validityRenamed :=
          validity.renameRespectingContext targetContext rawRenaming contextCondition
        rw [rename_piTyCodeCell] at validityRenamed ⊢
        obtain ⟨_domainBox, domainRenamed⟩ :=
          domainValid.renameRespectingContextExists targetContext rawRenaming contextCondition
        obtain ⟨_codomainBox, codomainRenamed⟩ :=
          codomainValid.renameRespectingContextExists
            (targetContext.cons (RawTerm.rename rawRenaming domainCode))
            (iterateLiftRaw rawRenaming 1)
            (renameContextCondition_cons domainCode rawRenaming contextCondition)
        exact ⟨_, piTypeViaSnCodFamily domainRenamed codomainRenamed validityRenamed⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.IsTypeDescPi.renameRespectingContext
#print axioms FX1Poly.Typed.TypedTypeValidityBoxed.renameRespectingContextExists
