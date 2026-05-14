import LeanFX2.Reducibility.Kripke.Basic

/-! Forward parProgress-step closure for closed-leaf ReducibleK. -/

namespace LeanFX2

/-- SN under any parProgress step gives SN of target. -/
theorem RawTerm.isStronglyNormalizing.step_closure
    {scope : Nat} {source target : RawTerm scope}
    (sourceIsSN : RawTerm.isStronglyNormalizing source)
    (progress : RawStep.parProgress source target) :
    RawTerm.isStronglyNormalizing target :=
  match sourceIsSN with
  | RawTerm.isStronglyNormalizing.intro _ closure => closure target progress

/-- Typed forward closure for closed leaves: SN preserved by raw step. -/
theorem Term.isStronglyNormalizing.step_closure
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context sourceType targetRaw}
    (sourceIsSN : Term.isStronglyNormalizing sourceTerm)
    (progress : RawStep.parProgress sourceRaw targetRaw) :
    Term.isStronglyNormalizing targetTerm :=
  RawTerm.isStronglyNormalizing.step_closure sourceIsSN progress

/-- CR2 at Ty.unit: forward parProgress step preserves ReducibleK. -/
theorem ReducibleK.cr2_unit
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context Ty.unit sourceRaw}
    {targetTerm : Term context Ty.unit targetRaw}
    (sourceIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.unit sourceRaw sourceTerm)
    (progress : RawStep.parProgress sourceRaw targetRaw) :
    @ReducibleK mode level scope context (stepCount + 1) Ty.unit targetRaw targetTerm := by
  have isSN : Term.isStronglyNormalizing sourceTerm := sourceIsR
  exact Term.isStronglyNormalizing.step_closure (sourceTerm := sourceTerm)
    (targetTerm := targetTerm) isSN progress

theorem ReducibleK.cr2_bool
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context Ty.bool sourceRaw}
    {targetTerm : Term context Ty.bool targetRaw}
    (sourceIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.bool sourceRaw sourceTerm)
    (progress : RawStep.parProgress sourceRaw targetRaw) :
    @ReducibleK mode level scope context (stepCount + 1) Ty.bool targetRaw targetTerm := by
  have isSN : Term.isStronglyNormalizing sourceTerm := sourceIsR
  exact Term.isStronglyNormalizing.step_closure (sourceTerm := sourceTerm)
    (targetTerm := targetTerm) isSN progress

theorem ReducibleK.cr2_nat
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context Ty.nat sourceRaw}
    {targetTerm : Term context Ty.nat targetRaw}
    (sourceIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.nat sourceRaw sourceTerm)
    (progress : RawStep.parProgress sourceRaw targetRaw) :
    @ReducibleK mode level scope context (stepCount + 1) Ty.nat targetRaw targetTerm := by
  have isSN : Term.isStronglyNormalizing sourceTerm := sourceIsR
  exact Term.isStronglyNormalizing.step_closure (sourceTerm := sourceTerm)
    (targetTerm := targetTerm) isSN progress

theorem ReducibleK.cr2_empty
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context Ty.empty sourceRaw}
    {targetTerm : Term context Ty.empty targetRaw}
    (sourceIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.empty sourceRaw sourceTerm)
    (progress : RawStep.parProgress sourceRaw targetRaw) :
    @ReducibleK mode level scope context (stepCount + 1) Ty.empty targetRaw targetTerm := by
  have isSN : Term.isStronglyNormalizing sourceTerm := sourceIsR
  exact Term.isStronglyNormalizing.step_closure (sourceTerm := sourceTerm)
    (targetTerm := targetTerm) isSN progress

theorem ReducibleK.cr2_interval
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context Ty.interval sourceRaw}
    {targetTerm : Term context Ty.interval targetRaw}
    (sourceIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.interval sourceRaw sourceTerm)
    (progress : RawStep.parProgress sourceRaw targetRaw) :
    @ReducibleK mode level scope context (stepCount + 1) Ty.interval targetRaw targetTerm := by
  have isSN : Term.isStronglyNormalizing sourceTerm := sourceIsR
  exact Term.isStronglyNormalizing.step_closure (sourceTerm := sourceTerm)
    (targetTerm := targetTerm) isSN progress

end LeanFX2
