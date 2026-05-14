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

/-- Variables at any closed-leaf type are ReducibleK.  Demonstrated for
the five shipped closed-leaf arms. -/
theorem ReducibleK.fundamental_var_unit
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) (position : Fin scope)
    (typesAt : varType sourceCtx position = Ty.unit) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.unit
      (RawTerm.var position) (typesAt ▸ Term.var (context := sourceCtx) position) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact RawTerm.var_isStronglyNormalizing position

theorem ReducibleK.fundamental_var_bool
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) (position : Fin scope)
    (typesAt : varType sourceCtx position = Ty.bool) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.bool
      (RawTerm.var position) (typesAt ▸ Term.var (context := sourceCtx) position) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact RawTerm.var_isStronglyNormalizing position

theorem ReducibleK.fundamental_var_nat
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) (position : Fin scope)
    (typesAt : varType sourceCtx position = Ty.nat) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.nat
      (RawTerm.var position) (typesAt ▸ Term.var (context := sourceCtx) position) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact RawTerm.var_isStronglyNormalizing position

theorem ReducibleK.fundamental_var_empty
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) (position : Fin scope)
    (typesAt : varType sourceCtx position = Ty.empty) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.empty
      (RawTerm.var position) (typesAt ▸ Term.var (context := sourceCtx) position) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact RawTerm.var_isStronglyNormalizing position

theorem ReducibleK.fundamental_var_interval
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) (position : Fin scope)
    (typesAt : varType sourceCtx position = Ty.interval) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.interval
      (RawTerm.var position) (typesAt ▸ Term.var (context := sourceCtx) position) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact RawTerm.var_isStronglyNormalizing position

end LeanFX2
