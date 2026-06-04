import FX1Poly.Typed.HasTypeDescPiConsistency
import FX1Poly.Typed.HasTypeDescPiRootGeneric

/-! # FX1Poly/Typed/HasTypeDescPiDataHeadUntyped
    — the grown engine types no data constructor and no data eliminator (the canonical-forms
    boundary; the SR dispatcher's iota-vacuity leg, toward SN-055 / #558)

`HasTypeDescPi.subjectRootGenerator` (in `HasTypeDescPiConsistency`) classifies a grown-typed subject's
ROOT GENERATOR: it is one of the six the engine can introduce — `gen_var` (`var`), `gen_universeCode`
(`ofFormation ∘ universeFormation`), `gen_piTyCode` / `gen_sigmaTyCode` (`genFormationPi`), `gen_lam`
(`piIntro`), or `gen_app` (`piElim`).  This file packages the NEGATIVE-USE consequence: a cell whose root
is NONE of those six has no grown typing derivation.

That negative form is exactly the **canonical-forms boundary** of the grown engine — it is the pure
Π/formation fragment.  None of the data CONSTRUCTORS (`gen_pair`, `gen_boolTrue`, `gen_natZero`, …) and none
of the data ELIMINATORS (`gen_boolElim`, `gen_fst`, `gen_natElim`, `gen_idJ`, …) is among the six, so the
grown engine types none of them.

## Why this is the SR dispatcher's iota leg

The subject-reduction master dispatcher (`HasTypeDescPi.subjectReduction`, SN-055 / #558) cases on the
`Step` relation.  Every `Step.iota*` constructor (`iotaBoolTrue`, `iotaFstPair`, `iotaNatElimZero`,
`iotaIdJRefl`, …) has a redex `.mkGen ELIM_GEN _ _` rooted at a data eliminator.  In each such case the
dispatcher holds `HasTypeDescPi … (.mkGen ELIM_GEN …) …`; the generic refutation below turns that into
`False`, discharging the entire iota family vacuously — the grown engine simply does not type the redexes
those rules fire on.  The dispatcher cites the table-generic `cellHasNoTypingWhenRootGenericallyExcluded`
(`HasTypeDescPiRootGeneric`) once per iota case.

## What this file ships

  * The reusable refutation itself — `HasTypeDescPi.cellHasNoTypingWhenRootGenericallyExcluded` — now lives in
    `HasTypeDescPiRootGeneric` (the table-generic successor; this file's earlier six-inequality
    `cellHasNoTypingWhenRootNotGrownHead` was retired as unsound once the formation table grows).
  * A representative smoke corpus proving the refutation FIRES on the real iota-redex heads across every
    eliminator shape class — branch selection (`gen_boolElim`), projection (`gen_fst`), recursion
    (`gen_natElim`), path induction (`gen_idJ`) — and on a data constructor (`gen_pair`), witnessing that
    the boundary excludes constructors as well as eliminators.  The remaining eliminator heads
    (`gen_snd` / `gen_natRec` / `gen_listElim` / `gen_optionMatch` / `gen_eitherMatch` / `gen_idStrictRec`)
    and all other data constructors are refuted by the identical one-line application of the generic lemma.

## Zero-axiom verification

The generic lemma is an `rcases` on the `subjectRootGenerator` six-way disjunction, each branch closed by an
inequality hypothesis applied to the (definitional) `rootGenerator` equation.  Each smoke witness applies it
and discharges the six distinct-flat-constructor inequalities by `intro … ; cases …` (the established
zero-axiom refutation for distinct `Generator` constructors — no `decide`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

-- The six-inequality refutation `cellHasNoTypingWhenRootNotGrownHead` was RETIRED here: it was unsound once
-- the formation table grows (a new former's generator differs from all six heads yet its cell IS typed via
-- `genFormationPi`, so the conclusion would be false).  Its table-generic successor
-- `HasTypeDescPi.cellHasNoTypingWhenRootGenericallyExcluded` (`HasTypeDescPiRootGeneric`, which requires
-- `typingRuleDescOf generator = none` — permanent for data constructors/eliminators) is what the smoke
-- corpus below cites.

/-- **`gen_boolElim` (branch-selection eliminator) is untyped in the grown engine.**  The redex head of the
`iotaBoolTrue` / `iotaBoolFalse` reductions; the grown engine types no `boolElim` cell. -/
theorem HasTypeDescPi.boolElimCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {payload : Generator.gen_boolElim.payload scope}
    {children : RawTermChildren Generator.gen_boolElim.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen .gen_boolElim payload children) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootGenericallyExcluded <;> (first | (intro contra; cases contra) | rfl)

/-- **`gen_fst` (projection eliminator) is untyped in the grown engine.**  The redex head of the
`iotaFstPair` reduction; the grown engine types no `fst` cell. -/
theorem HasTypeDescPi.fstCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {payload : Generator.gen_fst.payload scope}
    {children : RawTermChildren Generator.gen_fst.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen .gen_fst payload children) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootGenericallyExcluded <;> (first | (intro contra; cases contra) | rfl)

/-- **`gen_natElim` (recursive eliminator) is untyped in the grown engine.**  The redex head of the
`iotaNatElimZero` / `iotaNatElimSucc` reductions; the grown engine types no `natElim` cell. -/
theorem HasTypeDescPi.natElimCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {payload : Generator.gen_natElim.payload scope}
    {children : RawTermChildren Generator.gen_natElim.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen .gen_natElim payload children) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootGenericallyExcluded <;> (first | (intro contra; cases contra) | rfl)

/-- **`gen_idJ` (path-induction eliminator) is untyped in the grown engine.**  The redex head of the
`iotaIdJRefl` reduction; the grown engine types no `idJ` cell. -/
theorem HasTypeDescPi.idJCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {payload : Generator.gen_idJ.payload scope}
    {children : RawTermChildren Generator.gen_idJ.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen .gen_idJ payload children) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootGenericallyExcluded <;> (first | (intro contra; cases contra) | rfl)

/-- **`gen_pair` (data constructor) is untyped in the grown engine.**  Witnesses that the boundary excludes
data CONSTRUCTORS as well as eliminators — the grown engine types no `pair` cell (pair lives in the data
layer, not the pure Π fragment). -/
theorem HasTypeDescPi.pairCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {payload : Generator.gen_pair.payload scope}
    {children : RawTermChildren Generator.gen_pair.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen .gen_pair payload children) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootGenericallyExcluded <;> (first | (intro contra; cases contra) | rfl)

end FX1Poly.Typed
