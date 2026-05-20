import LeanFX2.Reduction.Step.Inductive

/-! ## Cast helpers

When source/target indices need to be transported across propositional
equalities (e.g., when bridging Step proofs through Ty/RawTerm
commute lemmas), these helpers swap the indexed Term values without
touching the underlying Step witness.  Each is `cases equality;
exact step`. -/

namespace LeanFX2

/-- Replace the source Ty by a propositionally equal Ty. -/
theorem Step.castSourceType
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceTypeOriginal sourceTypeReplacement targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : sourceTypeOriginal = sourceTypeReplacement)
    {sourceTerm : Term context sourceTypeOriginal sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (singleStep : Step sourceTerm targetTerm) :
    Step (typeEquality ▸ sourceTerm) targetTerm := by
  cases typeEquality
  exact singleStep

/-- Replace the target Ty by a propositionally equal Ty. -/
theorem Step.castTargetType
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetTypeOriginal targetTypeReplacement : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : targetTypeOriginal = targetTypeReplacement)
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetTypeOriginal targetRaw}
    (singleStep : Step sourceTerm targetTerm) :
    Step sourceTerm (typeEquality ▸ targetTerm) := by
  cases typeEquality
  exact singleStep

/-- Replace the source raw index by a propositionally equal raw term. -/
theorem Step.castSourceRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRawOriginal sourceRawReplacement targetRaw : RawTerm scope}
    (rawEquality : sourceRawOriginal = sourceRawReplacement)
    {sourceTerm : Term context sourceType sourceRawOriginal}
    {targetTerm : Term context targetType targetRaw}
    (singleStep : Step sourceTerm targetTerm) :
    Step (rawEquality ▸ sourceTerm) targetTerm := by
  cases rawEquality
  exact singleStep

/-- Replace the target raw index by a propositionally equal raw term. -/
theorem Step.castTargetRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRawOriginal targetRawReplacement : RawTerm scope}
    (rawEquality : targetRawOriginal = targetRawReplacement)
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRawOriginal}
    (singleStep : Step sourceTerm targetTerm) :
    Step sourceTerm (rawEquality ▸ targetTerm) := by
  cases rawEquality
  exact singleStep

/-- Replace the source Term by a propositionally equal Term (same Ty). -/
theorem Step.castSourceTerm
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceOriginal sourceReplacement : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (sourceEquality : sourceOriginal = sourceReplacement)
    (singleStep : Step sourceOriginal targetTerm) :
    Step sourceReplacement targetTerm := by
  cases sourceEquality
  exact singleStep

/-- Replace the target Term by a propositionally equal Term (same Ty). -/
theorem Step.castTargetTerm
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetOriginal targetReplacement : Term context targetType targetRaw}
    (targetEquality : targetOriginal = targetReplacement)
    (singleStep : Step sourceTerm targetOriginal) :
    Step sourceTerm targetReplacement := by
  cases targetEquality
  exact singleStep

end LeanFX2
