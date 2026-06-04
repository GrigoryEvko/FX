import FX1Poly.Typed.HasTypeDescPiConsistency

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
those rules fire on.  The dispatcher cites `cellHasNoTypingWhenRootNotGrownHead` once per iota case.

## What this file ships

  * `HasTypeDescPi.cellHasNoTypingWhenRootNotGrownHead` — the reusable refutation: a cell whose root
    generator differs from all six grown-introducible heads cannot be grown-typed.  The contrapositive of
    `subjectRootGenerator`, packaged for the dispatcher's negative use.
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

/-- **No grown typing for a cell whose root is none of the six grown heads.**  A grown-typed subject is
rooted at `gen_var` / `gen_universeCode` / `gen_piTyCode` / `gen_sigmaTyCode` / `gen_lam` / `gen_app`
(`subjectRootGenerator`); so a cell whose root generator differs from all six has no grown typing
derivation.  `(.mkGen generator …).rootGenerator` is `generator` definitionally, so each disjunct of
`subjectRootGenerator` reduces to `generator = gen_X` and contradicts the matching inequality.  The
contrapositive of `subjectRootGenerator`, the reusable refutation the SR dispatcher's iota cases cite. -/
theorem HasTypeDescPi.cellHasNoTypingWhenRootNotGrownHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    {classifier : RawTerm scope}
    (rootNotVar : generator ≠ Generator.gen_var)
    (rootNotUniverse : generator ≠ Generator.gen_universeCode)
    (rootNotPi : generator ≠ Generator.gen_piTyCode)
    (rootNotSigma : generator ≠ Generator.gen_sigmaTyCode)
    (rootNotLam : generator ≠ Generator.gen_lam)
    (rootNotApp : generator ≠ Generator.gen_app)
    (typed : HasTypeDescPi profile context (.mkGen generator payload children) classifier) :
    False := by
  rcases typed.subjectRootGenerator with isVar | isUniverse | isPi | isSigma | isLam | isApp
  · exact rootNotVar isVar
  · exact rootNotUniverse isUniverse
  · exact rootNotPi isPi
  · exact rootNotSigma isSigma
  · exact rootNotLam isLam
  · exact rootNotApp isApp

/-- **`gen_boolElim` (branch-selection eliminator) is untyped in the grown engine.**  The redex head of the
`iotaBoolTrue` / `iotaBoolFalse` reductions; the grown engine types no `boolElim` cell. -/
theorem HasTypeDescPi.boolElimCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {payload : Generator.gen_boolElim.payload scope}
    {children : RawTermChildren Generator.gen_boolElim.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen .gen_boolElim payload children) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootNotGrownHead <;> (intro contra; cases contra)

/-- **`gen_fst` (projection eliminator) is untyped in the grown engine.**  The redex head of the
`iotaFstPair` reduction; the grown engine types no `fst` cell. -/
theorem HasTypeDescPi.fstCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {payload : Generator.gen_fst.payload scope}
    {children : RawTermChildren Generator.gen_fst.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen .gen_fst payload children) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootNotGrownHead <;> (intro contra; cases contra)

/-- **`gen_natElim` (recursive eliminator) is untyped in the grown engine.**  The redex head of the
`iotaNatElimZero` / `iotaNatElimSucc` reductions; the grown engine types no `natElim` cell. -/
theorem HasTypeDescPi.natElimCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {payload : Generator.gen_natElim.payload scope}
    {children : RawTermChildren Generator.gen_natElim.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen .gen_natElim payload children) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootNotGrownHead <;> (intro contra; cases contra)

/-- **`gen_idJ` (path-induction eliminator) is untyped in the grown engine.**  The redex head of the
`iotaIdJRefl` reduction; the grown engine types no `idJ` cell. -/
theorem HasTypeDescPi.idJCellHasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {payload : Generator.gen_idJ.payload scope}
    {children : RawTermChildren Generator.gen_idJ.binderShifts scope}
    {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (.mkGen .gen_idJ payload children) classifier) :
    False := by
  apply typed.cellHasNoTypingWhenRootNotGrownHead <;> (intro contra; cases contra)

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
  apply typed.cellHasNoTypingWhenRootNotGrownHead <;> (intro contra; cases contra)

end FX1Poly.Typed
