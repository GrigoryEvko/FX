import LeanFX2.Term.PartialStrengthen.Weaken

/-! # Term/PartialStrengthen/RenameImage/Core

Shared rename-image infrastructure for the T1 strengthening equations.
-/

namespace LeanFX2

namespace Term

/-- Canonical `StrengtheningResult` for the rename-image case.

Given an injective renaming `forwardRename : RawRenaming sourceScope
targetScope` with typed companion `typedRenaming`, a partial inverse
`renameInverse`, and an original typed term `original` living in the
source context, build the canonical `StrengtheningResult` for
`Term.rename typedRenaming original` (which lives in the target
context) through the `ContextStrengthening.ofRenaming`-induced
strengthening (which goes back from target to source).

Mechanical content:
* `targetType := originalTy` — the strengthening recovers the original
  type.
* `targetRaw := originalRaw` — analogous at the raw layer.
* `targetTerm := original` — the original typed term itself.
* `typeStrengthens` — discharges via `Ty.partialStrengthen?_rename_some`
  applied at `targetRenaming := RawRenaming.identity`, then closed via
  `Ty.rename_identity`.
* `rawStrengthens` — analogous at raw, via
  `RawTerm.partialStrengthen?_rename_some` + `RawTerm.rename_identity`.
* `typeRenames` / `rawRenames` — both `rfl` because the
  `ContextStrengthening.ofRenaming`'s `forward` field IS `forwardRename`
  by definition.

This is the canonical witness consumed by strength-T1
(`Term.strengthenTyped?_rename_eq`): the headline asserts that the
dispatcher produces exactly this StrengtheningResult on a renamed
input. -/
def StrengtheningResult.fromRename
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (forwardRename : RawRenaming sourceScope targetScope)
    (typedRenaming : TermRenaming sourceCtx targetCtx forwardRename)
    (renameInverse : PartialRawRenaming targetScope sourceScope)
    (renameInverseLeft :
      ∀ sourcePosition,
        renameInverse (forwardRename sourcePosition) = some sourcePosition)
    (renameInverseInjects :
      ∀ targetPosition sourcePosition,
        renameInverse targetPosition = some sourcePosition →
        targetPosition = forwardRename sourcePosition)
    {originalTy : Ty level sourceScope}
    {originalRaw : RawTerm sourceScope}
    (original : Term sourceCtx originalTy originalRaw) :
    StrengtheningResult
      (ContextStrengthening.ofRenaming forwardRename typedRenaming
        renameInverse renameInverseLeft renameInverseInjects)
      (Term.rename typedRenaming original) where
  targetType := originalTy
  targetRaw := originalRaw
  targetTerm := original
  typeStrengthens := by
    show (originalTy.rename forwardRename).partialStrengthen? renameInverse =
      some originalTy
    rw [Ty.partialStrengthen?_rename_some originalTy forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      Ty.rename_identity originalTy]
  rawStrengthens := by
    show (originalRaw.rename forwardRename).partialStrengthen? renameInverse =
      some originalRaw
    rw [RawTerm.partialStrengthen?_rename_some originalRaw forwardRename
      (@RawRenaming.identity sourceScope) renameInverse renameInverseLeft,
      RawTerm.rename_identity originalRaw]
  typeRenames := rfl
  rawRenames := rfl

/-! ## strength-T1: per-ctor renaming-image dispatcher equations.

For each Term constructor, the dispatcher `partialStrengthenTyped?`
applied to the renamed term through the `ContextStrengthening.ofRenaming`-
induced strengthening produces exactly the canonical `StrengtheningResult`
recovering the original.

These per-ctor lemmas compose into the full strength-T1 universal
headline `Term.strengthenTyped?_rename_eq` (78-case structural
induction).  This block starts the closed-atomic family (unit /
boolTrue / boolFalse / natZero / interval0 / interval1 /
universeCode) and the var case; recursive ctors land in follow-up
ticks. -/

/-- Cast-invariance for `partialStrengthenTyped?` `.isSome` at the
Ty index.

When the source Term is wrapped in a type-equality cast `typeEq ▸
sourceTerm`, the dispatcher's `.isSome` result is the same as the
un-cast form.  The transport is structural on Eq: `cases typeEq`
peels the cast cleanly.  This is the `partialStrengthen?` analog of
`strengthenTyped?_isSome_castInvariant` in StrengtheningImage. -/
theorem partialStrengthenTyped?_isSome_castInvariant
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {someTypeA someTypeB : Ty level sourceScope}
    {someRaw : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx someTypeA someRaw)
    (typeEq : someTypeA = someTypeB)
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    (partialStrengthenTyped? (typeEq ▸ sourceTerm) strengthening).isSome
      = (partialStrengthenTyped? sourceTerm strengthening).isSome := by
  cases typeEq
  rfl

/-- Cast-invariance of `partialStrengthenTyped?` via `HEq`.

When the source Term is wrapped in a type-equality cast `typeEq ▸
sourceTerm`, the dispatcher's result is HEq-related to the un-cast
form.  HEq abstracts over the differing result types
(`Option (StrengtheningResult σ (typeEq ▸ sourceTerm))` vs
`Option (StrengtheningResult σ sourceTerm)`).  Used to bridge the
cast-wrapped dispatcher invocation back to the un-cast IH. -/
theorem partialStrengthenTyped?_castInvariantHEq
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {someTypeA someTypeB : Ty level sourceScope}
    {someRaw : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx someTypeA someRaw)
    (typeEq : someTypeA = someTypeB)
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    HEq
      (partialStrengthenTyped? (typeEq ▸ sourceTerm) strengthening)
      (partialStrengthenTyped? sourceTerm strengthening) := by
  cases typeEq
  rfl

/-- A type-index cast on a typed term is heterogeneously equal to the
uncast term.  Kept local to typed strengthening so this file can reason
about `Term.rename` arms with inner casts without importing the heavier
pointwise substitution layer. -/
theorem termTypeCastHEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw : RawTerm scope}
    (typeEq : sourceType = targetType)
    (sourceTerm : Term context sourceType sourceRaw) :
    HEq (typeEq ▸ sourceTerm) sourceTerm := by
  cases typeEq
  rfl

/-- `Term.rename` arm reshape for `Term.oeqFunext`.

The rename arm wraps the `pointwiseProof` argument in
`oeqFunextPointwiseType_rename rho domainType codomainType
leftFunctionRaw rightFunctionRaw ▸ Term.rename termRenaming
pointwiseProof` to align the result type with the renamed
`oeqFunextPointwiseType`.  This lemma exposes the cast equation as
an explicit (non-internal) proof so downstream rewriting can
manipulate the cast structurally.

Proved by `rfl` because `Term.rename`'s `oeqFunext` arm normalises
to the cast-wrapped form. -/
theorem rename_oeqFunext_unfolds {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (typedRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    (leftFunctionRaw rightFunctionRaw : RawTerm sourceScope)
    {pointwiseRaw : RawTerm sourceScope}
    (pointwiseProof :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseRaw) :
    Term.rename typedRenaming
        (Term.oeqFunext (context := sourceCtx) domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseProof) =
      Term.oeqFunext (context := targetCtx)
        (domainType.rename rho)
        (codomainType.rename rho)
        (leftFunctionRaw.rename rho)
        (rightFunctionRaw.rename rho)
        ((oeqFunextPointwiseType_rename rho
          domainType codomainType leftFunctionRaw rightFunctionRaw) ▸
          (Term.rename typedRenaming pointwiseProof :
            Term targetCtx
              ((oeqFunextPointwiseType domainType codomainType
                leftFunctionRaw rightFunctionRaw).rename rho)
              (pointwiseRaw.rename rho))) := by
  rfl

end Term

end LeanFX2
