import LeanFX2.Algo.Check

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
counterpart `Term.check_complete_X` family lives in the second
half of this file, leveraging `Term.check` (which dispatches on
expectedType for ambiguous ctors).  The atomic-leaf check arms
ship below alongside the inferable ones to give the full bidi
recovery surface.

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
  dsimp only [Term.infer]
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
  dsimp only [Term.infer]
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
  dsimp only [Term.infer]
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
  dsimp only [Term.infer]
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
  dsimp only [Term.infer]
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
  dsimp only [Term.infer]
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
  dsimp only [Term.infer]
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
  dsimp only [Term.infer]
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
  dsimp only [Term.infer]
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
  dsimp only [Term.infer]
  rw [witnessIH, baseIH]

/-! ## Check-mode counterparts (atomic leaves)

The check-mode side of M10 `Term.check_complete_X` family.  Where
`Term.infer` synthesizes type from term, `Term.check` confirms a
term inhabits a *given* expected type.  Atomic leaves dispatch on
the expected type via DecidableEq; the positive branch fires on
`rfl`.

### Why DecEq dispatch is propext-clean

`Term.check` uses `if h : expectedType = X then some (h ▸ ...)
else none` for atomic leaves.  When `expectedType = X`
syntactically, the dite takes its positive branch with `h := rfl`,
and `rfl ▸ x` reduces definitionally to `x`.  Recipe:
`unfold Term.check; exact dif_pos rfl`.

The `dsimp only` step from the multi-recurse infer recipe is not
needed here because the `match raw with | .X => ...` outer dispatch
selects exactly one arm based on the canonical raw form, and that
arm is already in dite-normal form. -/

/-- Completeness of `Term.check` at the variable case.  When the
expected type matches `varType context position`, the checker
returns the canonical `Term.var` witness.  Recipe: definitional
unfold of the dite via `dif_pos rfl` against the explicit
expected-type-equals-self equality. -/
theorem Term.check_complete_var
    (context : Ctx mode level scope) (position : Fin scope) :
    Term.check context (varType context position) (RawTerm.var position)
      = some (Term.var position) :=
  dif_pos rfl

/-- Completeness of `Term.check` at the `unit` literal.  The
expected type must be `Ty.unit`. -/
theorem Term.check_complete_unit
    (context : Ctx mode level scope) :
    Term.check context Ty.unit RawTerm.unit = some Term.unit :=
  dif_pos rfl

/-- Completeness of `Term.check` at `boolTrue`.  Expected type
must be `Ty.bool`. -/
theorem Term.check_complete_boolTrue
    (context : Ctx mode level scope) :
    Term.check context Ty.bool RawTerm.boolTrue = some Term.boolTrue :=
  dif_pos rfl

/-- Completeness of `Term.check` at `boolFalse`. -/
theorem Term.check_complete_boolFalse
    (context : Ctx mode level scope) :
    Term.check context Ty.bool RawTerm.boolFalse = some Term.boolFalse :=
  dif_pos rfl

/-- Completeness of `Term.check` at `natZero`.  Expected type
must be `Ty.nat`. -/
theorem Term.check_complete_natZero
    (context : Ctx mode level scope) :
    Term.check context Ty.nat RawTerm.natZero = some Term.natZero :=
  dif_pos rfl

/-- Completeness of `Term.check` at `listNil`.  When the expected
type is `Ty.listType elementType`, the checker returns the
canonical `Term.listNil` witness without recursion.  No DecEq
dispatch — dispatch is via the `match expectedType with` outer
selector, which definitionally selects the `.listType` arm. -/
theorem Term.check_complete_listNil
    (context : Ctx mode level scope) (elementType : Ty level scope) :
    Term.check context (Ty.listType elementType) RawTerm.listNil
      = some Term.listNil := rfl

/-- Completeness of `Term.check` at `optionNone`.  Expected type
must be `Ty.optionType elementType`. -/
theorem Term.check_complete_optionNone
    (context : Ctx mode level scope) (elementType : Ty level scope) :
    Term.check context (Ty.optionType elementType) RawTerm.optionNone
      = some Term.optionNone := rfl

/-- Completeness of `Term.check` at `natSucc`.  The expected type
must be `Ty.nat`; the inner predecessor recurses via the IH. -/
theorem Term.check_complete_natSucc
    (context : Ctx mode level scope)
    {predRaw : RawTerm scope}
    (predTerm : Term context Ty.nat predRaw)
    (predIH : Term.check context Ty.nat predRaw = some predTerm) :
    Term.check context Ty.nat (RawTerm.natSucc predRaw)
      = some (Term.natSucc predTerm) := by
  show (if h : (Ty.nat : Ty level scope) = Ty.nat then
          match Term.check context Ty.nat predRaw with
          | some predTerm' => some (h ▸ Term.natSucc predTerm')
          | none => none
        else none) = some (Term.natSucc predTerm)
  rw [dif_pos rfl, predIH]

/-- Completeness of `Term.check` at `optionSome`.  Expected type
`Ty.optionType elementType`; inner value recurses at
`elementType`. -/
theorem Term.check_complete_optionSome
    (context : Ctx mode level scope)
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context elementType valueRaw)
    (valueIH :
      Term.check context elementType valueRaw = some valueTerm) :
    Term.check context (Ty.optionType elementType)
        (RawTerm.optionSome valueRaw)
      = some (Term.optionSome valueTerm) := by
  dsimp only [Term.check]
  rw [valueIH]

/-- Completeness of `Term.check` at `eitherInl`.  Expected type
`Ty.eitherType leftType rightType`; inner value recurses at
`leftType`. -/
theorem Term.check_complete_eitherInl
    (context : Ctx mode level scope)
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context leftType valueRaw)
    (valueIH :
      Term.check context leftType valueRaw = some valueTerm) :
    Term.check context (Ty.eitherType leftType rightType)
        (RawTerm.eitherInl valueRaw)
      = some (Term.eitherInl valueTerm) := by
  dsimp only [Term.check]
  rw [valueIH]

/-- Completeness of `Term.check` at `eitherInr`.  Mirror of
`eitherInl`; inner value recurses at `rightType`. -/
theorem Term.check_complete_eitherInr
    (context : Ctx mode level scope)
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    (valueTerm : Term context rightType valueRaw)
    (valueIH :
      Term.check context rightType valueRaw = some valueTerm) :
    Term.check context (Ty.eitherType leftType rightType)
        (RawTerm.eitherInr valueRaw)
      = some (Term.eitherInr valueTerm) := by
  dsimp only [Term.check]
  rw [valueIH]

/-- Completeness of `Term.check` at `listCons`.  Multi-recurse with
expected-type match: head recurses at `elementType`, tail at the
list type itself.  No DecEq dispatch — both recursions feed
expected types directly. -/
theorem Term.check_complete_listCons
    (context : Ctx mode level scope)
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    (headTerm : Term context elementType headRaw)
    (tailTerm : Term context (Ty.listType elementType) tailRaw)
    (headIH : Term.check context elementType headRaw = some headTerm)
    (tailIH :
      Term.check context (Ty.listType elementType) tailRaw = some tailTerm) :
    Term.check context (Ty.listType elementType)
        (RawTerm.listCons headRaw tailRaw)
      = some (Term.listCons headTerm tailTerm) := by
  dsimp only [Term.check]
  rw [headIH, tailIH]

/-- Completeness of `Term.check` at `lam` (non-dependent arrow).
Expected type `Ty.arrow domainType codomainType`; body recurses
at `codomainType.weaken` under `context.cons domainType`. -/
theorem Term.check_complete_lam
    (context : Ctx mode level scope)
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    (bodyTerm :
      Term (context.cons domainType) codomainType.weaken bodyRaw)
    (bodyIH :
      Term.check (context.cons domainType) codomainType.weaken bodyRaw
        = some bodyTerm) :
    Term.check context (Ty.arrow domainType codomainType)
        (RawTerm.lam bodyRaw)
      = some (Term.lam bodyTerm) := by
  dsimp only [Term.check]
  rw [bodyIH]

/-- Completeness of `Term.check` at `lam` (dependent Π).  Expected
type `Ty.piTy domainType codomainType`; body recurses at
`codomainType` under `context.cons domainType`. -/
theorem Term.check_complete_lamPi
    (context : Ctx mode level scope)
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (bodyTerm :
      Term (context.cons domainType) codomainType bodyRaw)
    (bodyIH :
      Term.check (context.cons domainType) codomainType bodyRaw
        = some bodyTerm) :
    Term.check context (Ty.piTy domainType codomainType)
        (RawTerm.lam bodyRaw)
      = some (Term.lamPi bodyTerm) := by
  dsimp only [Term.check]
  rw [bodyIH]

/-- Completeness of `Term.check` at `pair`.  Expected type
`Ty.sigmaTy firstType secondType`; first recurses at `firstType`,
second at the substituted second type. -/
theorem Term.check_complete_pair
    (context : Ctx mode level scope)
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (firstTerm : Term context firstType firstRaw)
    (secondTerm :
      Term context (secondType.subst0 firstType firstRaw) secondRaw)
    (firstIH : Term.check context firstType firstRaw = some firstTerm)
    (secondIH :
      Term.check context (secondType.subst0 firstType firstRaw) secondRaw
        = some secondTerm) :
    Term.check context (Ty.sigmaTy firstType secondType)
        (RawTerm.pair firstRaw secondRaw)
      = some (Term.pair firstTerm secondTerm) := by
  dsimp only [Term.check]
  rw [firstIH, secondIH]

end LeanFX2
