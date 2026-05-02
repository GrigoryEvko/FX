import LeanFX2.Algo.Check

/-! Phase 9.D — Term.check zero-axiom audit + concrete examples.

Bidirectional check uses an expected type to disambiguate the
parametric leaf forms (`listNil`, `optionNone`) and recursive
parametric forms (`listCons`, `optionSome`, `eitherInl/Inr`).
The atomic + nat-recursive forms behave like `Term.infer` with
explicit-type confirmation. -/

namespace LeanFX2.SmokePhase9DCheck

#print axioms LeanFX2.Term.check

open LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-- `check Ty.unit .unit = some Term.unit`. -/
example :
    Term.check context (Ty.unit (level := level) (scope := scope))
                       (RawTerm.unit (scope := scope)) =
      some Term.unit := rfl

/-- `check Ty.bool .unit = none` (type mismatch). -/
example :
    Term.check context (Ty.bool (level := level) (scope := scope))
                       (RawTerm.unit (scope := scope)) =
      none := rfl

/-- `check (Ty.listType Ty.nat) .listNil = some Term.listNil`. -/
example :
    Term.check context (Ty.listType (Ty.nat (level := level) (scope := scope)))
                       (RawTerm.listNil (scope := scope)) =
      some Term.listNil := rfl

/-- `check Ty.unit .listNil = none` (type former mismatch). -/
example :
    Term.check context (Ty.unit (level := level) (scope := scope))
                       (RawTerm.listNil (scope := scope)) =
      none := rfl

/-- Parametric recursive: `check (Ty.optionType Ty.nat) (.optionSome .natZero)`
gives the right typed term. -/
example :
    Term.check context (Ty.optionType (Ty.nat (level := level) (scope := scope)))
                       (RawTerm.optionSome (RawTerm.natZero (scope := scope))) =
      some (Term.optionSome Term.natZero) := rfl

/-- Inner-type mismatch: `check (Ty.optionType Ty.bool) (.optionSome .natZero)`
fails because `.natZero` is not bool-typed. -/
example :
    Term.check context (Ty.optionType (Ty.bool (level := level) (scope := scope)))
                       (RawTerm.optionSome (RawTerm.natZero (scope := scope))) =
      none := rfl

/-- Either-inl: `check (Ty.eitherType Ty.nat Ty.bool) (.eitherInl .natZero)`. -/
example :
    Term.check context
        (Ty.eitherType (Ty.nat (level := level) (scope := scope)) Ty.bool)
        (RawTerm.eitherInl (RawTerm.natZero (scope := scope))) =
      some (Term.eitherInl Term.natZero) := rfl

end LeanFX2.SmokePhase9DCheck
