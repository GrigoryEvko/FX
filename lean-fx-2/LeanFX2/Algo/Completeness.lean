import LeanFX2.Algo.Infer

/-! # Algo/Completeness — algorithmic completeness (full inferable subset)

Every well-typed Term is recovered by `Term.infer` on its raw
projection.  This file ships the full inferable subset of M10:
atomic, single-recurse, and multi-recurse cases.

## Three proof patterns

* **Atomic cases (5)**: each is `rfl` against `Term.infer`'s pattern-
  match arm — `var`, `unit`, `boolTrue`, `boolFalse`, `natZero`.
* **Single-recurse (5)**: structural IH on inner sub-term plus one
  match-arm; tactic shape `unfold Term.infer; rw [innerIH]`
  (sometimes followed by `rfl` for the DecEq positive branch).
  Covers `natSucc`, `optionSome`, `modIntro`, `modElim`, `subsume`.
* **Multi-recurse (5)**: `unfold Term.infer; rw [fnIH, argIH];
  dsimp only; exact dif_pos rfl` — the recipe relies on `dsimp only`
  reducing the deeply-nested match decision tree definitionally
  (no propext leak), and `dif_pos rfl` discharging the
  type-equality dispatch with the IH-supplied reflexivity.  Covers
  `app`, `fst`, `snd`, `listCons`, `idJ`.

## Inferable-subset coverage complete

Every `RawTerm` ctor that `Term.infer` can synthesize without an
expected type is covered.  Closure of the inferable subset.

The non-inferable (check-mode-only) cases — `lam`, `pair`, `refl`,
all eliminators, all modal/cubical/HOTT primitives — require the
expected-type check side of bidirectional checking.  Their
counterpart `Term.check_complete_X` family belongs to the
check-mode portion of M10 (#1279), shipping when `Algo/Check.lean`
gets the matching completeness treatment.

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

/-- Completeness of `Term.infer` at `app`.  Multi-recurse: the
function position synthesizes `Ty.arrow domainType codomainType`,
then the argument synthesizes a Term at `domainType`, and the
result is the codomain.  Recipe: `dsimp only` reduces the
deep-nested match decision tree definitionally; `dif_pos rfl`
discharges the type-equality dispatch using the IH-supplied
reflexivity (`domainType = domainType`). -/
theorem Term.infer_complete_app
    (context : Ctx mode level scope)
    {domainType codomainType : Ty level scope}
    {fnRaw argRaw : RawTerm scope}
    (fnTerm : Term context (Ty.arrow domainType codomainType) fnRaw)
    (argTerm : Term context domainType argRaw)
    (fnIH : Term.infer context fnRaw
              = some ⟨Ty.arrow domainType codomainType, fnTerm⟩)
    (argIH : Term.infer context argRaw = some ⟨domainType, argTerm⟩) :
    Term.infer context (RawTerm.app fnRaw argRaw)
      = some ⟨codomainType, Term.app fnTerm argTerm⟩ := by
  unfold Term.infer
  rw [fnIH, argIH]
  dsimp only
  exact dif_pos rfl

/-- Completeness of `Term.infer` at `fst`.  The pair synthesizes
`Ty.sigmaTy firstType secondType`; the result is the first
component's type. -/
theorem Term.infer_complete_fst
    (context : Ctx mode level scope)
    {firstType : Ty level scope}
    {secondType : Ty level (scope+1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw)
    (pairIH : Term.infer context pairRaw
                = some ⟨Ty.sigmaTy firstType secondType, pairTerm⟩) :
    Term.infer context (RawTerm.fst pairRaw)
      = some ⟨firstType, Term.fst pairTerm⟩ := by
  unfold Term.infer
  rw [pairIH]

/-- Completeness of `Term.infer` at `snd`.  Returns the second
component's type substituted with the projected raw `RawTerm.fst
pairRaw` term — the result type carries the un-fired raw fst-of-pair
(propositionally equal to `secondType.subst0 firstType firstRaw`
after a β-step at the type level). -/
theorem Term.infer_complete_snd
    (context : Ctx mode level scope)
    {firstType : Ty level scope}
    {secondType : Ty level (scope+1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw)
    (pairIH : Term.infer context pairRaw
                = some ⟨Ty.sigmaTy firstType secondType, pairTerm⟩) :
    Term.infer context (RawTerm.snd pairRaw)
      = some ⟨secondType.subst0 firstType (RawTerm.fst pairRaw),
              Term.snd pairTerm⟩ := by
  unfold Term.infer
  rw [pairIH]

/-- Completeness of `Term.infer` at `listCons`.  Multi-recurse with
DecEq dispatch: the head's element type must match the tail's list
element type.  Same `dsimp only + dif_pos rfl` recipe as `app`. -/
theorem Term.infer_complete_listCons
    (context : Ctx mode level scope)
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    (headTerm : Term context elementType headRaw)
    (tailTerm : Term context (Ty.listType elementType) tailRaw)
    (headIH : Term.infer context headRaw = some ⟨elementType, headTerm⟩)
    (tailIH : Term.infer context tailRaw
                = some ⟨Ty.listType elementType, tailTerm⟩) :
    Term.infer context (RawTerm.listCons headRaw tailRaw)
      = some ⟨Ty.listType elementType,
              Term.listCons headTerm tailTerm⟩ := by
  unfold Term.infer
  rw [headIH, tailIH]
  dsimp only
  exact dif_pos rfl

/-- Completeness of `Term.infer` at `idJ`.  The witness synthesizes
an `Ty.id` type; the base synthesizes the motive type; the result
is the motive type (the J eliminator computes to the base case at
the trivial path argument). -/
theorem Term.infer_complete_idJ
    (context : Ctx mode level scope)
    {carrierType : Ty level scope}
    {leftEnd rightEnd : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (witnessTerm : Term context (Ty.id carrierType leftEnd rightEnd) witnessRaw)
    (baseTerm : Term context motiveType baseRaw)
    (witnessIH : Term.infer context witnessRaw
                   = some ⟨Ty.id carrierType leftEnd rightEnd, witnessTerm⟩)
    (baseIH : Term.infer context baseRaw = some ⟨motiveType, baseTerm⟩) :
    Term.infer context (RawTerm.idJ baseRaw witnessRaw)
      = some ⟨motiveType, Term.idJ baseTerm witnessTerm⟩ := by
  unfold Term.infer
  rw [witnessIH, baseIH]

end LeanFX2
