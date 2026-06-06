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

  * The reusable refutation itself — `HasTypeDescPi.cellHasNoTypingWhenRootGenericallyExcluded` — lives in
    `HasTypeDescPiRootGeneric` (the table-generic form, which stays sound as the formation table grows).
  * The COMPLETE iota-redex-head corpus proving the refutation FIRES on every eliminator shape class — branch
    selection (`gen_boolElim`), projection (`gen_fst` / `gen_snd`), recursion (`gen_natElim` / `gen_natRec` /
    `gen_listElim`), non-recursive branch matching (`gen_optionMatch` / `gen_eitherMatch`), path induction
    (`gen_idJ` / `gen_idStrictRec`) — on a data constructor (`gen_pair`, witnessing the boundary excludes
    constructors too), and on the Empty TYPE-CODE cell (`gen_emptyCode`, the CON-A1 deferred-row generator).
    Every redex head the β+ι iota family fires on is now an EXPLICIT shipped refutation.  The Empty case
    additionally yields `noConvReclassifierAtEmptyType` — the `conv` arm of the SN-050 consistency inversion.

## Zero-axiom verification

The generic lemma is an `rcases` on the `subjectRootGenerator` six-way disjunction, each branch closed by an
inequality hypothesis applied to the (definitional) `rootGenerator` equation.  Each smoke witness applies it
and discharges the six distinct-flat-constructor inequalities by `intro … ; cases …` (the established
zero-axiom refutation for distinct `Generator` constructors — no `decide`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

-- The smoke corpus below cites the table-generic refutation
-- `HasTypeDescPi.cellHasNoTypingWhenRootGenericallyExcluded` (`HasTypeDescPiRootGeneric`), which requires
-- `typingRuleDescOf generator = none` — permanent for data constructors/eliminators.  A six-inequality
-- refutation enumerating grown heads would be unsound as the formation table grows (a new former's generator
-- differs from all six heads yet its cell IS typed via `genFormationPi`, so the conclusion would be false).

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

/-! ### Completing the canonical-forms boundary — the deferred eliminator heads + the Empty type code.

The representative smoke corpus above (`boolElim` / `fst` / `natElim` / `idJ` / `pair`) is extended below to the
remaining data ELIMINATORS — projection (`gen_snd`), recursion (`gen_natRec` / `gen_listElim`), non-recursive
branch matching (`gen_optionMatch` / `gen_eitherMatch`), and strict path recursion (`gen_idStrictRec`) — and to
the Empty TYPE-CODE cell (`gen_emptyCode`, whose `typingRuleDescOf` is `none` — CON-A1's deferred-row generator).
Every redex head of the β+ι system's iota family is now an EXPLICIT shipped refutation, not a docstring promise.
Each is the SAME one-line application of `cellHasNoTypingWhenRootGenericallyExcluded`. -/

/-- **`gen_snd` (projection eliminator) is untyped in the grown engine.**  Redex head of `iotaSndPair`. -/
theorem HasTypeDescPi.sndCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {payload : Generator.gen_snd.payload scope}
    {children : RawTermChildren Generator.gen_snd.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen .gen_snd payload children) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootGenericallyExcluded <;> (first | (intro contra; cases contra) | rfl)

/-- **`gen_natRec` (dependent recursive eliminator) is untyped in the grown engine.**  Redex head of
`iotaNatRecZero` / `iotaNatRecSucc`; the `natElim` twin. -/
theorem HasTypeDescPi.natRecCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {payload : Generator.gen_natRec.payload scope}
    {children : RawTermChildren Generator.gen_natRec.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen .gen_natRec payload children) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootGenericallyExcluded <;> (first | (intro contra; cases contra) | rfl)

/-- **`gen_listElim` (recursive eliminator) is untyped in the grown engine.**  Redex head of `iotaListElimNil`
/ `iotaListElimCons`. -/
theorem HasTypeDescPi.listElimCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {payload : Generator.gen_listElim.payload scope}
    {children : RawTermChildren Generator.gen_listElim.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen .gen_listElim payload children) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootGenericallyExcluded <;> (first | (intro contra; cases contra) | rfl)

/-- **`gen_optionMatch` (non-recursive branch eliminator) is untyped in the grown engine.**  Redex head of
`iotaOptionMatchSome` / `iotaOptionMatchNone`. -/
theorem HasTypeDescPi.optionMatchCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {payload : Generator.gen_optionMatch.payload scope}
    {children : RawTermChildren Generator.gen_optionMatch.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen .gen_optionMatch payload children) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootGenericallyExcluded <;> (first | (intro contra; cases contra) | rfl)

/-- **`gen_eitherMatch` (non-recursive branch eliminator) is untyped in the grown engine.**  Redex head of
`iotaEitherMatchLeft` / `iotaEitherMatchRight`. -/
theorem HasTypeDescPi.eitherMatchCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {payload : Generator.gen_eitherMatch.payload scope}
    {children : RawTermChildren Generator.gen_eitherMatch.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen .gen_eitherMatch payload children) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootGenericallyExcluded <;> (first | (intro contra; cases contra) | rfl)

/-- **`gen_idStrictRec` (strict path recursor) is untyped in the grown engine.**  Redex head of
`iotaIdStrictRecRefl`; the `idJ` twin. -/
theorem HasTypeDescPi.idStrictRecCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {payload : Generator.gen_idStrictRec.payload scope}
    {children : RawTermChildren Generator.gen_idStrictRec.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen .gen_idStrictRec payload children) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootGenericallyExcluded <;> (first | (intro contra; cases contra) | rfl)

/-- **The Empty TYPE-CODE cell `emptyTypeCell` is untyped in the grown engine.**  `gen_emptyCode`'s
`typingRuleDescOf` is `none` (CON-A1's deferred row), so no `genFormation` / `genFormationPi` fires; it is
neither `gen_var`, `gen_universeCode`, `gen_lam`, nor `gen_app`.  Distinct from the data CONSTRUCTORS/eliminators
above, this is the type-CODE for the empty type — the grown engine does not name it as a type (the CON-A0
engine↔candidate finding, mechanized). -/
theorem HasTypeDescPi.emptyTypeCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (emptyTypeCell (scope := scope)) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootGenericallyExcluded <;> (first | (intro contra; cases contra) | rfl)

/-- **The `conv`-rule route to `_ : emptyTypeCell` is impossible (toward SN-050).**  The grown `conv` rule
concludes `subject : reclassifier` only with a premise `reclassifier : universeCodeCell _ _`.  At
`reclassifier = emptyTypeCell` that premise is `HasTypeDescPi … emptyTypeCell (universeCodeCell …)`, refuted by
`emptyTypeCellHasNoTyping`.  So a closed term cannot acquire the classifier `emptyTypeCell` through `conv` — the
`conv` arm of the consistency (SN-050) inversion is discharged; the residual is the `piElim` arm (the SR/model
crux GCC-5 / CON-A3). -/
theorem HasTypeDescPi.noConvReclassifierAtEmptyType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {levelExpr : FX1Poly.Universe.LevelExpr}
    {flag : FX1Poly.Universe.UniverseFlag}
    (reclassifierTyped :
      HasTypeDescPi profile context (emptyTypeCell (scope := scope))
        (universeCodeCell levelExpr flag)) :
    False :=
  reclassifierTyped.emptyTypeCellHasNoTyping

end FX1Poly.Typed
