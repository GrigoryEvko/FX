import LeanFX2.Reducibility.Kripke.Basic

/-! # ReducibleK closed-leaf SN projection.

Every reducible closed-leaf term is strongly normalizing.  Directly
extracts the SN from the predicate's closed-leaf definition. -/

namespace LeanFX2

theorem ReducibleK.sn_of_unit
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.unit raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.unit raw term) :
    Term.isStronglyNormalizing term := termIsR

theorem ReducibleK.sn_of_bool
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.bool raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.bool raw term) :
    Term.isStronglyNormalizing term := termIsR

theorem ReducibleK.sn_of_nat
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.nat raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.nat raw term) :
    Term.isStronglyNormalizing term := termIsR

theorem ReducibleK.sn_of_empty
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.empty raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.empty raw term) :
    Term.isStronglyNormalizing term := termIsR

theorem ReducibleK.sn_of_interval
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.interval raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1) Ty.interval raw term) :
    Term.isStronglyNormalizing term := termIsR

end LeanFX2
