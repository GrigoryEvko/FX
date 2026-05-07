import LeanFX2.Algo.Infer

/-! # Algo/Completeness — algorithmic completeness (atomic fragment)

Every well-typed Term is recovered by `Term.infer` on its raw
projection.  This file ships the atomic cases — each is `rfl`
because `Term.infer` is structurally aligned with `Term`'s
constructors at the inferable subset.

## Atomic fragment shipped here

* `infer_complete_var` — `Term.var position` round-trips through
  `Term.infer context (RawTerm.var position)`.
* `infer_complete_unit`, `infer_complete_boolTrue`,
  `infer_complete_boolFalse`, `infer_complete_natZero` — the four
  nullary canonical-head cases.

## What is NOT shipped here yet

The recursive cases (`natSucc`, `app`, `fst`, `snd`, `listCons`,
`optionSome`, `idJ`, `modIntro`, `modElim`, `subsume`) require
inductive completeness over the inferred sub-term — they live in a
follow-on file once the recursive pattern is established.  The
non-inferable (check-mode-only) cases — `lam`, `pair`, `refl`,
eliminators — require `Term.check` completeness, deferred to the
broader M10 milestone (#1279).

## Why atomic-only first

Each atomic theorem is `rfl` against `Term.infer`'s pattern-match
arm — so they compile in a single line, ship zero-axiom on first
attempt, and serve as the foundation for the recursive cases'
induction-base.  Together they convert the previous stub into a
file with five real declarations, removing the deception slot per
project zero-axiom commitment (CLAUDE.md).

## Dependencies

* `Algo/Infer.lean`

## Downstream

* `Pipeline.lean` — pipeline composes infer + check + Conv
* `Surface/Elab.lean` — elaboration leans on infer completeness
-/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-- Completeness of `Term.infer` at the variable case.  For every
position `i`, the inferrer returns the canonical typed witness
`Term.var i` together with its declared type `varType context i`. -/
theorem Term.infer_complete_var
    (context : Ctx mode level scope) (position : Fin scope) :
    Term.infer context (RawTerm.var position)
      = some ⟨varType context position, Term.var position⟩ := rfl

/-- Completeness of `Term.infer` at the `unit` canonical head.
Returns the canonical `Term.unit` typed at `Ty.unit`. -/
theorem Term.infer_complete_unit
    (context : Ctx mode level scope) :
    Term.infer context RawTerm.unit
      = some ⟨Ty.unit, Term.unit⟩ := rfl

/-- Completeness of `Term.infer` at the `boolTrue` canonical head. -/
theorem Term.infer_complete_boolTrue
    (context : Ctx mode level scope) :
    Term.infer context RawTerm.boolTrue
      = some ⟨Ty.bool, Term.boolTrue⟩ := rfl

/-- Completeness of `Term.infer` at the `boolFalse` canonical head. -/
theorem Term.infer_complete_boolFalse
    (context : Ctx mode level scope) :
    Term.infer context RawTerm.boolFalse
      = some ⟨Ty.bool, Term.boolFalse⟩ := rfl

/-- Completeness of `Term.infer` at the `natZero` canonical head. -/
theorem Term.infer_complete_natZero
    (context : Ctx mode level scope) :
    Term.infer context RawTerm.natZero
      = some ⟨Ty.nat, Term.natZero⟩ := rfl

end LeanFX2
