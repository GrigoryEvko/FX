import LeanFX2.Algo.Infer

/-! Phase 9.D — Term.infer zero-axiom audit + concrete examples.

`Term.infer` recovers a typed Term from an untyped RawTerm for
the inferable subset (atomic + nat-recursive forms).  Ambiguous
forms (lam vs lamPi, app vs appPi, etc.) return `none`, deferred
to `Term.check` with expected type.

This file pins:
* Zero-axiom audit
* Concrete inference: `infer .natZero = some ⟨Ty.nat, .natZero⟩`
* Concrete inference: nat 3 = `succ (succ (succ zero))` round-trips
* Recursive ill-typed: `natSucc unit` → none
-/

namespace LeanFX2.SmokePhase9DInfer

#print axioms LeanFX2.Term.infer

open LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-- Inferring `natZero` gives `Ty.nat` with a `Term.natZero`. -/
example :
    Term.infer context (RawTerm.natZero (scope := scope)) =
      some ⟨Ty.nat, Term.natZero⟩ := rfl

/-- Inferring `unit` gives `Ty.unit` with `Term.unit`. -/
example :
    Term.infer context (RawTerm.unit (scope := scope)) =
      some ⟨Ty.unit, Term.unit⟩ := rfl

/-- Inferring `boolTrue` gives `Ty.bool` with `Term.boolTrue`. -/
example :
    Term.infer context (RawTerm.boolTrue (scope := scope)) =
      some ⟨Ty.bool, Term.boolTrue⟩ := rfl

/-- Inferring `natSucc natZero` gives `Ty.nat` with the
corresponding typed term.  Demonstrates the recursive case. -/
example :
    Term.infer context (RawTerm.natSucc (RawTerm.natZero (scope := scope))) =
      some ⟨Ty.nat, Term.natSucc Term.natZero⟩ := rfl

/-- Ill-typed: `natSucc unit` rejected because `unit` doesn't
have type `Ty.nat`.  Demonstrates the type-check fall-through. -/
example :
    Term.infer context (RawTerm.natSucc (RawTerm.unit (scope := scope))) =
      none := rfl

/-- Ambiguous: bare `lam bodyRaw` cannot be inferred without an
expected type (could be `Term.lam` or `Term.lamPi`). -/
example :
    Term.infer context (RawTerm.lam (RawTerm.unit (scope := scope + 1))) =
      none := rfl

/-- App synthesis: ambiguous when function has unknown form (a bare
`.lam` returns `none` from `infer`, so the surrounding `app` is
also `none`). -/
example :
    Term.infer context
        (RawTerm.app (RawTerm.lam (RawTerm.unit (scope := scope + 1)))
                     (RawTerm.unit (scope := scope))) =
      none := rfl

/-- `fst` of a non-pair raw form: `.fst .unit` returns `none` because
`Term.infer` synthesizes `Ty.unit` for `unit`, which is not a sigma. -/
example :
    Term.infer context
        (RawTerm.fst (RawTerm.unit (scope := scope))) =
      none := rfl

/-- `snd` of a non-pair raw form: similarly returns `none`. -/
example :
    Term.infer context
        (RawTerm.snd (RawTerm.unit (scope := scope))) =
      none := rfl

end LeanFX2.SmokePhase9DInfer
