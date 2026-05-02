import LeanFX2.Algo.Eval

/-! Phase 9.E — Term.eval zero-axiom audit + concrete reductions.

`Term.eval` iterates head ι-reductions up to a fuel bound, returning
the reduced raw form alongside the witnessed typed term at the same
type.  Type preservation is built into the return type: `Term context
someType resultRaw`.

This file pins:
* Zero-axiom audit for `Term.headStep?` and `Term.eval`
* Boolean ι-reduction:
  `boolElim true unit unit` evaluates to `unit`
* Boolean ι-reduction (else branch):
  `boolElim false unit unit` evaluates to `unit`
* Nat ι-reduction (zero branch):
  `natElim zero unit (λ_:nat.unit)` evaluates to `unit`
* List ι-reduction (nil branch):
  `listElim nil unit (λ_.λ_.unit)` evaluates to `unit`
* Option ι-reduction (none branch):
  `optionMatch none unit (λ_.unit)` evaluates to `unit`
* No-progress: a term in WHNF returns unchanged
* Zero-fuel returns the input unchanged

Coverage matches the propext-clean subset documented in
`Algo/Eval.lean`.  β-rules (app, appPi, fst/snd) and payload-carrying
ι-rules (succ, cons, some, inl/inr) are deferred — see file docstring
for the deferral rationale and resolution paths.
-/

namespace LeanFX2.SmokePhase9EEval

#print axioms LeanFX2.Term.headStep?
#print axioms LeanFX2.Term.eval

open LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-- ι-reduction: `boolElim true unit unit ⟶ unit` (then-branch).
The motive is `Ty.unit`, both branches are `Term.unit`. -/
example :
    let boolElimTerm : Term context
        (Ty.unit (level := level) (scope := scope))
        (RawTerm.boolElim RawTerm.boolTrue RawTerm.unit RawTerm.unit) :=
      Term.boolElim (motiveType := Ty.unit) Term.boolTrue Term.unit Term.unit
    (Term.eval 1 boolElimTerm).fst = RawTerm.unit := rfl

/-- ι-reduction: `boolElim false unit unit ⟶ unit` (else-branch). -/
example :
    let boolElimTerm : Term context
        (Ty.unit (level := level) (scope := scope))
        (RawTerm.boolElim RawTerm.boolFalse RawTerm.unit RawTerm.unit) :=
      Term.boolElim (motiveType := Ty.unit) Term.boolFalse Term.unit Term.unit
    (Term.eval 1 boolElimTerm).fst = RawTerm.unit := rfl

/-- ι-reduction nat-zero: `natElim zero z s ⟶ z`.  Motive `Ty.unit`,
zeroBranch is `unit`, succBranch is `λ_:nat. unit`. -/
example :
    let natElimTerm : Term context
        (Ty.unit (level := level) (scope := scope))
        (RawTerm.natElim RawTerm.natZero RawTerm.unit (RawTerm.lam RawTerm.unit)) :=
      Term.natElim (motiveType := Ty.unit) Term.natZero Term.unit
        (Term.lam (codomainType := Ty.unit) Term.unit)
    (Term.eval 1 natElimTerm).fst = RawTerm.unit := rfl

/-- ι-reduction nat-rec on zero: `natRec zero z s ⟶ z`. -/
example :
    let natRecTerm : Term context
        (Ty.unit (level := level) (scope := scope))
        (RawTerm.natRec RawTerm.natZero RawTerm.unit
          (RawTerm.lam (RawTerm.lam RawTerm.unit))) :=
      Term.natRec (motiveType := Ty.unit) Term.natZero Term.unit
        (Term.lam (codomainType := Ty.arrow Ty.unit Ty.unit)
          (Term.lam (codomainType := Ty.unit) Term.unit))
    (Term.eval 1 natRecTerm).fst = RawTerm.unit := rfl

/-- ι-reduction list-nil: `listElim nil n c ⟶ n`. -/
example :
    let listElimTerm : Term context
        (Ty.unit (level := level) (scope := scope))
        (RawTerm.listElim RawTerm.listNil RawTerm.unit
          (RawTerm.lam (RawTerm.lam RawTerm.unit))) :=
      Term.listElim (elementType := Ty.unit) (motiveType := Ty.unit)
        Term.listNil Term.unit
        (Term.lam (codomainType := Ty.arrow (Ty.listType Ty.unit) Ty.unit)
          (Term.lam (codomainType := Ty.unit) Term.unit))
    (Term.eval 1 listElimTerm).fst = RawTerm.unit := rfl

/-- ι-reduction option-none: `optionMatch none n s ⟶ n`. -/
example :
    let optionMatchTerm : Term context
        (Ty.unit (level := level) (scope := scope))
        (RawTerm.optionMatch RawTerm.optionNone RawTerm.unit
          (RawTerm.lam RawTerm.unit)) :=
      Term.optionMatch (elementType := Ty.unit) (motiveType := Ty.unit)
        Term.optionNone Term.unit
        (Term.lam (codomainType := Ty.unit) Term.unit)
    (Term.eval 1 optionMatchTerm).fst = RawTerm.unit := rfl

/-- No-progress: a term in WHNF (`unit`) returns unchanged regardless
of fuel. -/
example :
    let unitTerm : Term context
        (Ty.unit (level := level) (scope := scope))
        RawTerm.unit := Term.unit
    (Term.eval 5 unitTerm).fst = RawTerm.unit := rfl

/-- Zero-fuel: any term returns unchanged. -/
example :
    let boolElimTerm : Term context
        (Ty.bool (level := level) (scope := scope))
        (RawTerm.boolElim RawTerm.boolTrue RawTerm.boolFalse RawTerm.boolTrue) :=
      Term.boolElim (motiveType := Ty.bool) Term.boolTrue Term.boolFalse Term.boolTrue
    (Term.eval 0 boolElimTerm).fst =
      RawTerm.boolElim RawTerm.boolTrue RawTerm.boolFalse RawTerm.boolTrue := rfl

/-- Multi-step: apply `boolElim true (boolElim false unit unit) unit`
which reduces in 2 fuel to `unit`.  Outer fires first to give the
inner `boolElim false unit unit`, then inner fires to `unit`. -/
example :
    let outerTerm : Term context
        (Ty.unit (level := level) (scope := scope))
        (RawTerm.boolElim RawTerm.boolTrue
          (RawTerm.boolElim RawTerm.boolFalse RawTerm.unit RawTerm.unit)
          RawTerm.unit) :=
      Term.boolElim (motiveType := Ty.unit) Term.boolTrue
        (Term.boolElim (motiveType := Ty.unit) Term.boolFalse Term.unit Term.unit)
        Term.unit
    (Term.eval 2 outerTerm).fst = RawTerm.unit := rfl

end LeanFX2.SmokePhase9EEval
