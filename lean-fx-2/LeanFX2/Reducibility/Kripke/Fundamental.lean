import LeanFX2.Reducibility.Kripke.Basic
import LeanFX2.Reducibility.FundamentalAliases

/-! Kripke fundamental theorem — closed-leaf base cases.

Every canonical closed-leaf value is `ReducibleK n` at its type
for every step `n`.  Closed leaves reduce to SN; canonical values
have empty progress graphs, so SN is trivial. -/

namespace LeanFX2

/-- The unit value is ReducibleK at Ty.unit for any step. -/
theorem ReducibleK.fundamental_unit
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.unit
      RawTerm.unit Term.unit := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.unit_isStronglyNormalizing (sourceCtx := sourceCtx))

theorem ReducibleK.fundamental_boolTrue
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.bool
      RawTerm.boolTrue Term.boolTrue := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.boolTrue_isStronglyNormalizing (sourceCtx := sourceCtx))

theorem ReducibleK.fundamental_boolFalse
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.bool
      RawTerm.boolFalse Term.boolFalse := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.boolFalse_isStronglyNormalizing (sourceCtx := sourceCtx))

theorem ReducibleK.fundamental_natZero
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.nat
      RawTerm.natZero Term.natZero := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.natZero_isStronglyNormalizing (sourceCtx := sourceCtx))

end LeanFX2
