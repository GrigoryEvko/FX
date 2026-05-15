import LeanFX2.Reducibility.Kripke.Predicate

/-! # LeanFX2.Reducibility.Kripke.Basic — extraction lemmas for ReducibleK

Trivial unfolding lemmas exposing the per-Ty arm definitions of
`ReducibleK` to downstream callers without requiring them to know
the internal `ReducibleKBody` factorization.

All ship by `rfl` (the def is computationally transparent). -/

namespace LeanFX2

/-- `ReducibleK 0 _ _` is `True`. -/
@[simp] theorem ReducibleK.zero_eq_true
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    {term : Term context ty raw} :
    @ReducibleK mode level scope context 0 ty raw term ↔ True := by
  unfold ReducibleK
  exact Iff.rfl

/-- Closed-leaf extraction: `ReducibleK (n+1) Ty.unit _` is SN. -/
theorem ReducibleK.succ_unit_iff_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.unit raw} :
    @ReducibleK mode level scope context (stepCount + 1) Ty.unit raw term
      ↔ Term.isStronglyNormalizing term := by
  unfold ReducibleK
  exact Iff.rfl

/-- Closed-leaf extraction: `ReducibleK (n+1) Ty.bool _` is SN. -/
theorem ReducibleK.succ_bool_iff_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.bool raw} :
    @ReducibleK mode level scope context (stepCount + 1) Ty.bool raw term
      ↔ Term.isStronglyNormalizing term := by
  unfold ReducibleK
  exact Iff.rfl

/-- Closed-leaf extraction: `ReducibleK (n+1) Ty.nat _` is SN. -/
theorem ReducibleK.succ_nat_iff_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.nat raw} :
    @ReducibleK mode level scope context (stepCount + 1) Ty.nat raw term
      ↔ Term.isStronglyNormalizing term := by
  unfold ReducibleK
  exact Iff.rfl

/-- Closed-leaf extraction: `ReducibleK (n+1) Ty.empty _` is SN. -/
theorem ReducibleK.succ_empty_iff_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.empty raw} :
    @ReducibleK mode level scope context (stepCount + 1) Ty.empty raw term
      ↔ Term.isStronglyNormalizing term := by
  unfold ReducibleK
  exact Iff.rfl

/-- Closed-leaf extraction: `ReducibleK (n+1) Ty.interval _` is SN. -/
theorem ReducibleK.succ_interval_iff_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat} {raw : RawTerm scope}
    {term : Term context Ty.interval raw} :
    @ReducibleK mode level scope context (stepCount + 1) Ty.interval raw term
      ↔ Term.isStronglyNormalizing term := by
  unfold ReducibleK
  exact Iff.rfl

/-- Effect arm SN extraction.

The effect Kripke closure (`Predicate.lean`) is a conjunction of
SN of the effect-typed value with a uniform renaming-stability
clause.  This extractor projects the SN component directly. -/
theorem ReducibleK.sn_of_effect
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {carrierType : Ty level scope} {effectTag : RawTerm scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.effect carrierType effectTag) raw}
    (termIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.effect carrierType effectTag) raw term) :
    Term.isStronglyNormalizing term := termIsR.1

end LeanFX2
