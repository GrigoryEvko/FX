import LeanFX2.Algo.Infer

/-! # Algo/Completeness — algorithmic completeness (atomic + single-recurse)

Every well-typed Term is recovered by `Term.infer` on its raw
projection.  This file ships the atomic cases (each `rfl`) and the
single-recurse cases (`unfold`/`rw [innerIH]` after structural IH).

## Atomic fragment

* `infer_complete_var` — `Term.var position` round-trips through
  `Term.infer context (RawTerm.var position)`.
* `infer_complete_unit`, `infer_complete_boolTrue`,
  `infer_complete_boolFalse`, `infer_complete_natZero` — the four
  nullary canonical-head cases.

## Single-recurse fragment (Phase 4 partial)

Each of these takes the inner term's completeness as a hypothesis
(structural IH) and pushes through one match-arm of `Term.infer`:

* `infer_complete_natSucc` — DecidableEq dispatch on `Ty.nat`.
* `infer_complete_optionSome` — pure pass-through (no DecEq).
* `infer_complete_modIntro` / `_modElim` / `_subsume` — modal-marker
  pass-through (type unchanged).

## What is NOT shipped yet

Multi-recurse cases (`app`, `fst`, `snd`, `listCons`, `idJ`)
require destructuring on inferred sub-term Ty shape and cross-
arm coordination (e.g. `app` synth's fn at `.arrow domainType
codomainType` then synth's arg at `domainType`).  Pending Phase 4
remaining items.  The non-inferable (check-mode-only) cases
— `lam`, `pair`, `refl`, eliminators — require `Term.check`
completeness, deferred to the broader M10 milestone (#1279).

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

/-- Completeness of `Term.infer` at `natSucc`.  Given that the
inner term `innerTerm : Term context Ty.nat innerRaw` is recovered
by `Term.infer context innerRaw`, the wrapping `Term.natSucc
innerTerm` is recovered by `Term.infer context (RawTerm.natSucc
innerRaw)`.  The DecidableEq dispatch on `Ty.nat = Ty.nat` reduces
on `rfl`. -/
theorem Term.infer_complete_natSucc
    (context : Ctx mode level scope)
    {innerRaw : RawTerm scope}
    (innerTerm : Term context Ty.nat innerRaw)
    (innerIH : Term.infer context innerRaw = some ⟨Ty.nat, innerTerm⟩) :
    Term.infer context (RawTerm.natSucc innerRaw)
      = some ⟨Ty.nat, Term.natSucc innerTerm⟩ := by
  unfold Term.infer
  rw [innerIH]
  rfl

/-- Completeness of `Term.infer` at `optionSome`.  Given that the
inner term is recovered, the wrapping `Term.optionSome` is
recovered.  Pure pass-through arm — no DecEq dispatch needed. -/
theorem Term.infer_complete_optionSome
    (context : Ctx mode level scope)
    {elementType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context elementType innerRaw)
    (innerIH : Term.infer context innerRaw = some ⟨elementType, innerTerm⟩) :
    Term.infer context (RawTerm.optionSome innerRaw)
      = some ⟨Ty.optionType elementType, Term.optionSome innerTerm⟩ := by
  unfold Term.infer
  rw [innerIH]

/-- Completeness of `Term.infer` at `modIntro`.  Modal markers
preserve inner type — the inferrer threads the inner result through
unchanged. -/
theorem Term.infer_complete_modIntro
    (context : Ctx mode level scope)
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerIH : Term.infer context innerRaw = some ⟨innerType, innerTerm⟩) :
    Term.infer context (RawTerm.modIntro innerRaw)
      = some ⟨innerType, Term.modIntro innerTerm⟩ := by
  unfold Term.infer
  rw [innerIH]

/-- Completeness of `Term.infer` at `modElim`.  Mirror of
`infer_complete_modIntro`. -/
theorem Term.infer_complete_modElim
    (context : Ctx mode level scope)
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerIH : Term.infer context innerRaw = some ⟨innerType, innerTerm⟩) :
    Term.infer context (RawTerm.modElim innerRaw)
      = some ⟨innerType, Term.modElim innerTerm⟩ := by
  unfold Term.infer
  rw [innerIH]

/-- Completeness of `Term.infer` at `subsume`.  Cumulativity-marker
pass-through; same shape as the modal markers. -/
theorem Term.infer_complete_subsume
    (context : Ctx mode level scope)
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerIH : Term.infer context innerRaw = some ⟨innerType, innerTerm⟩) :
    Term.infer context (RawTerm.subsume innerRaw)
      = some ⟨innerType, Term.subsume innerTerm⟩ := by
  unfold Term.infer
  rw [innerIH]

end LeanFX2
