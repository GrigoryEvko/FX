import LeanFX2.Reducibility.Kripke.Project
import LeanFX2.Reducibility.Kripke.Fundamental

/-! Kripke-derived SN of closed-leaf canonical values.

Headline shape demonstrating fundamental ∘ sn_of_X composition:
every canonical closed-leaf value is strongly normalizing via the
Kripke fundamental theorem. -/

namespace LeanFX2

/-- SN of unit via the Kripke fundamental theorem. -/
theorem Term.unit_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing (Term.unit (context := sourceCtx)) :=
  ReducibleK.sn_of_unit (ReducibleK.fundamental_unit (sourceCtx := sourceCtx) 1)

theorem Term.boolTrue_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing (Term.boolTrue (context := sourceCtx)) :=
  ReducibleK.sn_of_bool (ReducibleK.fundamental_boolTrue (sourceCtx := sourceCtx) 1)

theorem Term.boolFalse_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing (Term.boolFalse (context := sourceCtx)) :=
  ReducibleK.sn_of_bool (ReducibleK.fundamental_boolFalse (sourceCtx := sourceCtx) 1)

theorem Term.natZero_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing (Term.natZero (context := sourceCtx)) :=
  ReducibleK.sn_of_nat (ReducibleK.fundamental_natZero (sourceCtx := sourceCtx) 1)

end LeanFX2
