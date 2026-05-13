import LeanFX2.Reduction.ParRed.ParInductive

/-! # LeanFX2.Reduction.ParRed.ParCasts

Propositional-transport helpers for the six index positions of
`Step.par`: source type, target type, source raw, target raw,
source term, target term.  Each helper rewrites one index via an
equality hypothesis while preserving the `Step.par` witness.

## Root status

Zero-axiom — pure `cases` on equality. -/

namespace LeanFX2


/-! ## Cast helpers — propositional transport for indices. -/

theorem Step.par.castSourceType
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceTypeOriginal sourceTypeReplacement targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : sourceTypeOriginal = sourceTypeReplacement)
    {sourceTerm : Term context sourceTypeOriginal sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (parallelStep : Step.par sourceTerm targetTerm) :
    Step.par (typeEquality ▸ sourceTerm) targetTerm := by
  cases typeEquality
  exact parallelStep

theorem Step.par.castTargetType
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetTypeOriginal targetTypeReplacement : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : targetTypeOriginal = targetTypeReplacement)
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetTypeOriginal targetRaw}
    (parallelStep : Step.par sourceTerm targetTerm) :
    Step.par sourceTerm (typeEquality ▸ targetTerm) := by
  cases typeEquality
  exact parallelStep

theorem Step.par.castSourceRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRawOriginal sourceRawReplacement targetRaw : RawTerm scope}
    (rawEquality : sourceRawOriginal = sourceRawReplacement)
    {sourceTerm : Term context sourceType sourceRawOriginal}
    {targetTerm : Term context targetType targetRaw}
    (parallelStep : Step.par sourceTerm targetTerm) :
    Step.par (rawEquality ▸ sourceTerm) targetTerm := by
  cases rawEquality
  exact parallelStep

theorem Step.par.castTargetRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRawOriginal targetRawReplacement : RawTerm scope}
    (rawEquality : targetRawOriginal = targetRawReplacement)
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRawOriginal}
    (parallelStep : Step.par sourceTerm targetTerm) :
    Step.par sourceTerm (rawEquality ▸ targetTerm) := by
  cases rawEquality
  exact parallelStep

theorem Step.par.castSourceTerm
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceOriginal sourceReplacement : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (sourceEquality : sourceOriginal = sourceReplacement)
    (parallelStep : Step.par sourceOriginal targetTerm) :
    Step.par sourceReplacement targetTerm := by
  cases sourceEquality
  exact parallelStep

theorem Step.par.castTargetTerm
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetOriginal targetReplacement : Term context targetType targetRaw}
    (targetEquality : targetOriginal = targetReplacement)
    (parallelStep : Step.par sourceTerm targetOriginal) :
    Step.par sourceTerm targetReplacement := by
  cases targetEquality
  exact parallelStep


end LeanFX2
