import LeanFX2.Reducibility.Kripke.Basic

/-! # ReducibleK step monotonicity (downward).

If a term is reducible at step `n+1`, it is reducible at every smaller
step.  Closed-leaf arms reduce to SN regardless of step (trivial).
Arrow arm: closure at step `n` is weaker than closure at step `n+1`
(the closure body is the same but the post-renaming sub-predicate
recurses at step `n-1` vs `n`). -/

namespace LeanFX2

/-- Closed-leaf step monotonicity collapses to identity: closed
leaves don't gate by step, so any positive step gives the same SN. -/
theorem ReducibleK.mono_unit
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.unit raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.unit raw term) :
    @ReducibleK mode level scope context stepCount Ty.unit raw term := by
  cases stepCount with
  | zero => trivial
  | succ subCount => exact termIsR

theorem ReducibleK.mono_bool
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.bool raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.bool raw term) :
    @ReducibleK mode level scope context stepCount Ty.bool raw term := by
  cases stepCount with
  | zero => trivial
  | succ subCount => exact termIsR

theorem ReducibleK.mono_nat
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.nat raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.nat raw term) :
    @ReducibleK mode level scope context stepCount Ty.nat raw term := by
  cases stepCount with
  | zero => trivial
  | succ subCount => exact termIsR

theorem ReducibleK.mono_empty
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.empty raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.empty raw term) :
    @ReducibleK mode level scope context stepCount Ty.empty raw term := by
  cases stepCount with
  | zero => trivial
  | succ subCount => exact termIsR

theorem ReducibleK.mono_interval
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.interval raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.interval raw term) :
    @ReducibleK mode level scope context stepCount Ty.interval raw term := by
  cases stepCount with
  | zero => trivial
  | succ subCount => exact termIsR

end LeanFX2
