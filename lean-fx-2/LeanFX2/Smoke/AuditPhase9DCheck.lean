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

/-- App synth-then-check: a bare `.lam` returns `none` from infer, so
the wrapping `app` returns `none` too — even when the expected type
matches what the result *would* be. -/
example :
    Term.check context (Ty.unit (level := level) (scope := scope))
        (RawTerm.app (RawTerm.lam (RawTerm.unit (scope := scope + 1)))
                     (RawTerm.unit (scope := scope))) =
      none := rfl

/-- App synth-then-check fails on type mismatch: a variable applied to
itself (raw form `app (var 0) (var 0)`) — the inner `infer` on the
function position returns the variable's type, which won't be an
arrow without explicit context lookup.  Without an arrow function
shape, the outer `app` returns `none`. -/
example :
    Term.check context (Ty.bool (level := level) (scope := scope))
        (RawTerm.app (RawTerm.unit (scope := scope))
                     (RawTerm.unit (scope := scope))) =
      none := rfl

/-- Σ pair check at sigma type: `check (Ty.sigmaTy Ty.nat Ty.bool)
(.pair .natZero .boolTrue)` works — `secondType.subst0 firstType
firstRaw = Ty.bool` (the second type doesn't depend on the bound var,
so subst is identity). -/
example :
    Term.check context
        (Ty.sigmaTy (Ty.nat (level := level) (scope := scope)) Ty.bool.weaken)
        (RawTerm.pair (RawTerm.natZero (scope := scope)) RawTerm.boolTrue) =
      some (Term.pair Term.natZero Term.boolTrue) := rfl

/-- Σ pair check at non-sigma fails. -/
example :
    Term.check context
        (Ty.unit (level := level) (scope := scope))
        (RawTerm.pair (RawTerm.natZero (scope := scope)) RawTerm.boolTrue) =
      none := rfl

/-- Boolean eliminator at motive `Ty.unit`: scrutinee bool, both
branches unit. -/
example :
    Term.check context (Ty.unit (level := level) (scope := scope))
        (RawTerm.boolElim RawTerm.boolTrue RawTerm.unit RawTerm.unit) =
      some
        ((Ty.weaken_subst_singleton Ty.unit Ty.bool RawTerm.boolTrue) ▸
          Term.boolElim
            (motiveType := Ty.unit.weaken)
            Term.boolTrue
            ((Ty.weaken_subst_singleton Ty.unit Ty.bool RawTerm.boolTrue).symm ▸
              Term.unit)
            ((Ty.weaken_subst_singleton Ty.unit Ty.bool RawTerm.boolFalse).symm ▸
              Term.unit)) := rfl

/-- Nat eliminator at motive `Ty.unit`: scrutinee nat, zero branch
unit, succ branch `λ_:nat. unit`. -/
example :
    Term.check context (Ty.unit (level := level) (scope := scope))
        (RawTerm.natElim RawTerm.natZero RawTerm.unit
          (RawTerm.lam RawTerm.unit)) =
      some (Term.natElim Term.natZero Term.unit
        (Term.lam (codomainType := Ty.unit) Term.unit)) := rfl

/-- Bad scrutinee: boolElim with `unit` scrutinee — fails because
unit isn't bool. -/
example :
    Term.check context (Ty.unit (level := level) (scope := scope))
        (RawTerm.boolElim RawTerm.unit RawTerm.unit RawTerm.unit) =
      none := rfl

/-- listElim where scrutinee can't be inferred: bare `.lam` defaults
to none from infer.  Compare with a synthesizable scrutinee form. -/
example :
    Term.check context (Ty.unit (level := level) (scope := scope))
        (RawTerm.listElim
          (RawTerm.lam (RawTerm.unit (scope := scope + 1)))
          RawTerm.unit
          (RawTerm.lam (RawTerm.lam RawTerm.unit))) =
      none := rfl

/-- Identity refl: `check (Ty.id Ty.unit unit unit) (refl unit) = some Term.refl`. -/
example :
    Term.check context
        (Ty.id (Ty.unit (level := level) (scope := scope))
               RawTerm.unit RawTerm.unit)
        (RawTerm.refl RawTerm.unit) =
      some (Term.refl Ty.unit RawTerm.unit) := rfl

/-- Refl with mismatched endpoints: `check (Ty.id Ty.unit unit boolTrue)
(refl unit)` fails because endpointA ≠ endpointB. -/
example :
    Term.check context
        (Ty.id (Ty.unit (level := level) (scope := scope))
               RawTerm.unit RawTerm.boolTrue)
        (RawTerm.refl RawTerm.unit) =
      none := rfl

/-- Refl where witness ≠ endpoint: `check (Ty.id Ty.unit unit unit)
(refl boolTrue)` fails — witness must equal endpoint. -/
example :
    Term.check context
        (Ty.id (Ty.unit (level := level) (scope := scope))
               RawTerm.unit RawTerm.unit)
        (RawTerm.refl RawTerm.boolTrue) =
      none := rfl

/-- Modal markers preserve the inner type (per Layer-1 raw-side
scaffolding).  `check Ty.unit (modIntro unit)` succeeds. -/
example :
    Term.check context (Ty.unit (level := level) (scope := scope))
        (RawTerm.modIntro RawTerm.unit) =
      some (Term.modIntro Term.unit) := rfl

/-- Subsume marker also preserves inner type. -/
example :
    Term.check context (Ty.bool (level := level) (scope := scope))
        (RawTerm.subsume RawTerm.boolTrue) =
      some (Term.subsume Term.boolTrue) := rfl

end LeanFX2.SmokePhase9DCheck
