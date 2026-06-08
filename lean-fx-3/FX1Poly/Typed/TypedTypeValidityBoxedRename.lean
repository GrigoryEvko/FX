import FX1Poly.Typed.TypedTypeValidityBoxedRelation
import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Core.NeutralTermRename

/-! # FX1Poly/Typed/TypedTypeValidityBoxedRename — LR-weakening (the boxed typed LR respects renaming)

The boxed typed logical relation `TypedTypeValidityBoxed` (#1110) is stable under context renaming: a typed-LR-valid
type code stays typed-LR-valid (at SOME candidate box) under any renaming respecting the context-lookup condition.
This is the genuinely-NEW proof the lookup lemma needs (a context entry typed at a prefix scope must be transported
to the full scope), and the substrate the Abel-reflection neutral arm of the grown context-conversion piElim crux
(GrownCtxConv-5, #842) ultimately consumes.

## The structure

`renameRespectingContextExists` mirrors `HasTypeDescPi.renameRespectingContext` (the formation-side template) over
the three LR arms, wrapping the conclusion in an EXISTENTIAL candidate box (the exact transported candidate is not
needed — the consumers, `WfContextTypedLrValid` etc., only require `∃ box`).

  * `neutral` — `IsNeutral.rename` for the neutral code + the formation rename for the validity; candidate stays
    `snKripkeCand` (context-invariant).
  * `universeType` — `rename_universeCodeCell` (universe codes are rename-invariant) + the formation rename.
  * `piType` — the load-bearing arm: recurse on the domain (renaming `ρ`) and the codomain (renaming `lift ρ`,
    target context extended by the renamed domain, condition extended via `renameContextCondition_cons`), rename the
    `Π`-validity via `rename_piTyCodeCell`, and REASSEMBLE via `piTypeViaSnCodFamily` (#1111). The `lift ρ` codomain
    recursion is exactly why a single-step `weaken`-only statement does not suffice — weakening must go through the
    binder, so the general renaming version is the necessary substrate.

`IsTypeDescPi.renameRespectingContext` is the existential-over-`HasTypeDescPi` helper (the grown validity carried in
each LR arm), the renaming twin of the shipped `IsTypeDescPi.weakenUnderBinding`.

`TypedTypeValidityBoxed.weakenUnderBinding` is the single-step corollary at `ρ = RawRenaming.weaken` (the
context-condition holds definitionally) — the form the lookup lemma threads when descending a context telescope.

## Zero-axiom verification

`match`-form structural recursion + the shipped `IsNeutral.rename` / `HasTypeDescPi.renameRespectingContext` /
`rename_{universeCodeCell,piTyCodeCell}` / `renameContextCondition_cons` / `piTypeViaSnCodFamily`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- `IsTypeDescPi` respects context renaming: the existential-over-`HasTypeDescPi` twin of
`HasTypeDescPi.renameRespectingContext` (apply the grown rename, rewrite the rename-invariant universe-code
classifier, re-wrap the existential). The grown-validity rename each LR arm delegates to. -/
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

/-- **★ LR-weakening (general renaming).**  A typed-LR-valid type code is typed-LR-valid (at SOME candidate box)
under any context renaming respecting the lookup condition.  The `piType` arm recurses with `lift ρ` on the
codomain (the reason a `weaken`-only statement is insufficient — weakening must descend the binder), reassembling
via `piTypeViaSnCodFamily`.  The genuinely-new proof feeding the lookup lemma + the Abel-reflection neutral arm. -/
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
  | @TypedTypeValidityBoxed.piType _ _ _ domainCode _codomainCode _ _ _codomainFamily
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

/-- **★ LR-weakening (single step).**  A typed-LR-valid type code stays typed-LR-valid under one binding
extension (`ρ = RawRenaming.weaken`, the context-condition holds definitionally).  The form the lookup lemma
threads when descending a context telescope; the typed-LR twin of `IsTypeDescPi.weakenUnderBinding`. -/
theorem TypedTypeValidityBoxed.weakenUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope} {box : KripkeCandBox scope}
    (relation : TypedTypeValidityBoxed profile context typeCode box) (newBinding : RawTerm scope) :
    ∃ box' : KripkeCandBox (scope + 1),
      TypedTypeValidityBoxed profile (context.cons newBinding)
        (RawTerm.rename RawRenaming.weaken typeCode) box' :=
  relation.renameRespectingContextExists (context.cons newBinding) RawRenaming.weaken (fun _ => rfl)

end FX1Poly.Typed
