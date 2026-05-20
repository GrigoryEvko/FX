import LeanFX2.Reducibility.Kripke.Basic
import LeanFX2.Reducibility.SN.Helpers

/-! # LeanFX2.Reducibility.Kripke.Weaken — world weakening for Kripke ReducibleK

The headline architectural win of Kripke over single-world: world
weakening becomes derivable, where it failed in single-world
`Reducible` at compound arms (`Reducible.weaken_arrow` etc).

This file ships the closed-leaf instances; the arrow / sigmaTy /
piTy etc. world-weakening lemmas land in follow-up.

For closed leaves (unit / bool / nat / empty / interval), the
predicate is just SN, and `Term.isStronglyNormalizing_weaken`
already exists in `Reducibility/Foundation.lean`.  So world
weakening reduces to direct SN preservation. -/

namespace LeanFX2

/-- World weakening at `Ty.unit`: ReducibleK is preserved under
one-binder weakening. -/
theorem ReducibleK.weaken_unit
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {stepCount : Nat}
    {raw : RawTerm scope}
    {term : Term context Ty.unit raw}
    (termIsReducible :
      @ReducibleK mode level scope context stepCount Ty.unit raw term) :
    @ReducibleK mode level (scope + 1) (context.cons newType) stepCount
      Ty.unit (raw.weaken) (Term.weaken newType term) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    have isSN : Term.isStronglyNormalizing term := termIsReducible
    exact Term.isStronglyNormalizing_weaken (newType := newType) isSN

/-- World weakening at `Ty.bool`. -/
theorem ReducibleK.weaken_bool
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {stepCount : Nat}
    {raw : RawTerm scope}
    {term : Term context Ty.bool raw}
    (termIsReducible :
      @ReducibleK mode level scope context stepCount Ty.bool raw term) :
    @ReducibleK mode level (scope + 1) (context.cons newType) stepCount
      Ty.bool (raw.weaken) (Term.weaken newType term) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    have isSN : Term.isStronglyNormalizing term := termIsReducible
    exact Term.isStronglyNormalizing_weaken (newType := newType) isSN

/-- World weakening at `Ty.nat`. -/
theorem ReducibleK.weaken_nat
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {stepCount : Nat}
    {raw : RawTerm scope}
    {term : Term context Ty.nat raw}
    (termIsReducible :
      @ReducibleK mode level scope context stepCount Ty.nat raw term) :
    @ReducibleK mode level (scope + 1) (context.cons newType) stepCount
      Ty.nat (raw.weaken) (Term.weaken newType term) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    have isSN : Term.isStronglyNormalizing term := termIsReducible
    exact Term.isStronglyNormalizing_weaken (newType := newType) isSN

/-- World weakening at `Ty.empty`. -/
theorem ReducibleK.weaken_empty
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {stepCount : Nat}
    {raw : RawTerm scope}
    {term : Term context Ty.empty raw}
    (termIsReducible :
      @ReducibleK mode level scope context stepCount Ty.empty raw term) :
    @ReducibleK mode level (scope + 1) (context.cons newType) stepCount
      Ty.empty (raw.weaken) (Term.weaken newType term) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    have isSN : Term.isStronglyNormalizing term := termIsReducible
    exact Term.isStronglyNormalizing_weaken (newType := newType) isSN

/-- World weakening at `Ty.interval`. -/
theorem ReducibleK.weaken_interval
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {newType : Ty level scope}
    {stepCount : Nat}
    {raw : RawTerm scope}
    {term : Term context Ty.interval raw}
    (termIsReducible :
      @ReducibleK mode level scope context stepCount Ty.interval raw term) :
    @ReducibleK mode level (scope + 1) (context.cons newType) stepCount
      Ty.interval (raw.weaken) (Term.weaken newType term) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    have isSN : Term.isStronglyNormalizing term := termIsReducible
    exact Term.isStronglyNormalizing_weaken (newType := newType) isSN

end LeanFX2
