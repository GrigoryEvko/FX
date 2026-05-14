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

/-- natSucc preserves ReducibleK at Ty.nat: SN(pred) → SN(natSucc pred). -/
theorem ReducibleK.fundamental_natSucc
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {stepCount : Nat} {predecessorRaw : RawTerm scope}
    {predecessorTerm : Term sourceCtx Ty.nat predecessorRaw}
    (predIsR :
      @ReducibleK mode level scope sourceCtx stepCount Ty.nat
        predecessorRaw predecessorTerm) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.nat
      (RawTerm.natSucc predecessorRaw) (Term.natSucc predecessorTerm) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    have predSN : Term.isStronglyNormalizing predecessorTerm := predIsR
    exact RawTerm.natSucc_isStronglyNormalizing predSN

/-- listNil at any element type: SN at the SN-fallback Kripke arm. -/
theorem ReducibleK.fundamental_listNil
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope}
    (stepCount : Nat) :
    @ReducibleK mode level scope sourceCtx stepCount (Ty.listType elementType)
      RawTerm.listNil (Term.listNil) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.listNil_isStronglyNormalizing
      (sourceCtx := sourceCtx) (elementType := elementType))

/-- optionNone at any element type. -/
theorem ReducibleK.fundamental_optionNone
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope}
    (stepCount : Nat) :
    @ReducibleK mode level scope sourceCtx stepCount (Ty.optionType elementType)
      RawTerm.optionNone (Term.optionNone) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.optionNone_isStronglyNormalizing
      (sourceCtx := sourceCtx) (elementType := elementType))

/-- listCons preserves ReducibleK at Ty.listType (SN-fallback arm).
SN-only variant; takes SN witnesses for both sub-terms directly
because the elementType arm is unrestricted and head reducibility
doesn't immediately project to SN at compound elementType. -/
theorem ReducibleK.fundamental_listCons_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope}
    {stepCount : Nat}
    {headRaw tailRaw : RawTerm scope}
    {headTerm : Term sourceCtx elementType headRaw}
    {tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw}
    (headIsSN : Term.isStronglyNormalizing headTerm)
    (tailIsSN : Term.isStronglyNormalizing tailTerm) :
    @ReducibleK mode level scope sourceCtx stepCount
      (Ty.listType elementType) (RawTerm.listCons headRaw tailRaw)
      (Term.listCons headTerm tailTerm) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact Term.listCons_isStronglyNormalizing headIsSN tailIsSN

/-- optionSome preserves ReducibleK at Ty.optionType (SN-fallback). -/
theorem ReducibleK.fundamental_optionSome_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope}
    {stepCount : Nat}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx elementType valueRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm) :
    @ReducibleK mode level scope sourceCtx stepCount
      (Ty.optionType elementType) (RawTerm.optionSome valueRaw)
      (Term.optionSome valueTerm) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact Term.optionSome_isStronglyNormalizing valueIsSN

/-- eitherInl preserves ReducibleK at Ty.eitherType (SN-fallback). -/
theorem ReducibleK.fundamental_eitherInl_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (leftType rightType : Ty level scope)
    {stepCount : Nat}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx leftType valueRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm) :
    @ReducibleK mode level scope sourceCtx stepCount
      (Ty.eitherType leftType rightType) (RawTerm.eitherInl valueRaw)
      (Term.eitherInl (rightType := rightType) valueTerm) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.eitherInl_isStronglyNormalizing (rightType := rightType) valueIsSN)

/-- eitherInr preserves ReducibleK at Ty.eitherType (SN-fallback). -/
theorem ReducibleK.fundamental_eitherInr_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (leftType rightType : Ty level scope)
    {stepCount : Nat}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx rightType valueRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm) :
    @ReducibleK mode level scope sourceCtx stepCount
      (Ty.eitherType leftType rightType) (RawTerm.eitherInr valueRaw)
      (Term.eitherInr (leftType := leftType) valueTerm) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.eitherInr_isStronglyNormalizing (leftType := leftType) valueIsSN)

end LeanFX2
