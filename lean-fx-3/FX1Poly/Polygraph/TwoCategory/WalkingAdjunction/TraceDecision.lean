import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellWordProblem
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionTwoCellDecidable
import FX1Poly.Polygraph.Rewriting.Confluence.ConvergentNormalizerOfReducer

/-! # mode-3 floor — the trace word problem, wired to the convergent-reducer decision engine

`AdjunctionTwoCellWordProblem` reduced the seed's full `TwoCellConv` decision to two named obligations — a
`traceDecision` (`Decidable (SpineTraceEquiv … cellFirst.spine cellSecond.spine)`, the list-level
Mazurkiewicz / partially-commutative-monoid word problem) and a `reconstruct` (the readback past the `spine`
quotient) — with the whole NO-direction already discharged by the shipped soundness `TwoCellConv.spineTraceEquiv`.
This file attacks `traceDecision`: it WIRES the abstract Knuth-Bendix decision engine
(`Core/Rewriting/Confluence/ConvergentNormalizerOfReducer`) to `SpineTraceEquiv`, discharging EVERY ingredient
the engine needs EXCEPT the convergent reducer itself — which is precisely the documented hard core (the
source-anchored Foata / lexicographic canonicalization over the context-shifting atoms, with its strong
normalization and confluence).

## What this file ships (each piece zero-axiom, machine-checked)

  ★ `spineAtomDecEq` / `adjunctionSpineAtomDecEq` / `adjunctionSpineListDecEq` — the **carrier decidable
    equality**: `DecidableEq` on a `SpineAtom` (a generating 2-cell with a left/right whiskering context) and
    hence on `List (SpineAtom …)`, the engine's `DecidableEq Carrier`.  The atom is a dependent record (its
    path / generator fields are typed by its boundary modes), so the decision substitutes the decided mode
    equalities before comparing the paths and the generator — the same propext-clean idiom
    (`modalityPathDecEq` + `injection` + `subst`) the free-2-cell `decEq` uses.  Two `rfl` smokes witness it
    COMPUTES (the unit's spine decides equal to itself, distinct from the identity's empty spine).
  ★ `SpineGodementAtAnyPosition` + `spineTraceEquiv_iff_equationalTheory` — the **trace-equivalence bridge**:
    the positionwise closure of the Godement spine step (`here` at the head, `under` past an independent prefix
    atom) whose abstract `EquationalTheory` (the equivalence closure the engine decides) coincides with
    `SpineTraceEquiv`.  The bridge absorbs `SpineTraceEquiv`'s head-cons congruence into the relation, so the
    two equivalences are literally equal — `decidable_of_iff` transports the engine's decision onto
    `SpineTraceEquiv`.
  ★ `singleAtomGodementStep` / `singleAtomTraceEquiv` — the **single-transposition soundness core**: two
    adjacent spine atoms in recognized-redex shape (the left atom's right context factoring through the right
    atom's source generator and tail context; the right atom's left context factoring through the left atom's
    left context and target generator) form ONE `SpineGodementStep` — hence one `SpineTraceEquiv`.  Cast-free:
    the `SpineGodementStep.godement` constructor at the single-generator instance (`id ⊟ gen` on each side)
    computes its two spine difference-lists to EXACTLY the pre/post-swap atom lists by definitional reduction.
    This is the reusable atom the deferred reducer's soundness is built from.
  ★ `adjunctionTraceDecisionOfReducer` (★) — the **end-to-end engine wiring**: a sound + complete + terminating
    + confluent deterministic reducer for the positionwise Godement step (universally over the boundary modes)
    DECIDES `SpineTraceEquiv` on every cell pair — i.e. inhabits the `traceDecision` type
    `AdjunctionSpineTraceDecision` exactly.  Built by feeding the reducer bundle to the engine's
    `decidableEquationalTheoryOfReducerSN` (the `Acc.rec` normalizer + Church-Rosser, no `WellFounded.fix`) and
    transporting along the bridge.
  ★ `adjunctionTwoCellWordProblemViaGodementReducer` — the **assembly hook**: feeding
    `adjunctionTraceDecisionOfReducer`'s output into the predecessors' `adjunctionTwoCellWordProblemModuloTraceRoute`
    inhabits the full `DecidableTwoCellConvFor adjunctionModeSignature` modulo `(reducer bundle, reconstruct)` —
    exhibiting this file's contribution as exactly the `traceDecision` slot of the keystone assembly.

## What is DEFERRED (the precise residual) — gates stay `false`

`traceDecision` is NOT fully discharged.  What `adjunctionTraceDecisionOfReducer` still demands is the
CONVERGENT REDUCER for the positionwise Godement step:

  * a DETERMINISTIC `reduceStep : List (SpineAtom …) → Option (List (SpineAtom …))` that scans for the first
    adjacent independent redex pair and fires the `singleAtomGodementStep` swap (recognizing an arbitrary atom
    pair against the redex shape is a decidable path-factorization plus a `subst` into `singleAtomGodementStep`);
  * its SOUNDNESS (each fired step is a `SpineGodementAtAnyPosition` step — built from `singleAtomGodementStep`);
  * its COMPLETENESS (`none` exactly at the canonical / Foata normal form — every Godement redex is fired);
  * its TERMINATION (`Acc` of the flipped step — the Guiraud–Malbos polygraphic measure for the
    interchange-normal-form orientation; NOTE the naive sum-of-context-lengths is NOT monotone, since passing a
    counit LENGTHENS the moved atom's whisker context — the measure is the genuine remaining content);
  * its CONFLUENCE (`Confluent` — the trace-monoid hexagon / Yang–Baxter coherence WITH the context shifts).

These are exactly "the genuine Gratzer confluence-modulo-interchange core" the spine-floor docstrings name.
Until they are supplied, `fxMode_hasSpineTraceDecision` (and the predecessors'
`fxMode_hasModeRelativeConvDecision` / `fxMode_hasDecidableTwoCellEquality`) stay `false`.

Raw Lean 4 + Init; every declaration `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free
(the carrier decision is `modalityPathDecEq` + `injection` + `subst`; the bridge is induction on the
`Prop`-valued closures; the soundness core is one `godement` constructor whose spines compute by `rfl`; the
wiring is `decidable_of_iff` over the engine).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Tier0

open FX1Poly.Core (EquationalTheory Confluent decidableEquationalTheoryOfReducerSN)

/-! ## The carrier decidable equality -/

/-- Decidable equality of spine atoms, given decidable equality on the signature's modes, modality generators,
and 2-cell generators.  The atom's path / generator fields are typed by its boundary modes, so the decision
decides those modes first and substitutes them before comparing the remaining (now homogeneous) fields — the
`modalityPathDecEq` + `injection` + `subst` idiom, propext-clean. -/
def spineAtomDecEq {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {sourceMode targetMode : signature.graph.Mode} :
    DecidableEq (SpineAtom signature sourceMode targetMode) := by
  intro leftAtom rightAtom
  obtain ⟨leftMidL, rightMidL, leftContextL, genDomL, genCodL, genL, rightContextL⟩ := leftAtom
  obtain ⟨leftMidR, rightMidR, leftContextR, genDomR, genCodR, genR, rightContextR⟩ := rightAtom
  cases modeDecEq leftMidL leftMidR with
  | isFalse leftMidDiffer => exact isFalse (fun atomsEqual => leftMidDiffer (by injection atomsEqual))
  | isTrue leftMidEqual =>
    subst leftMidEqual
    cases modeDecEq rightMidL rightMidR with
    | isFalse rightMidDiffer => exact isFalse (fun atomsEqual => rightMidDiffer (by injection atomsEqual))
    | isTrue rightMidEqual =>
      subst rightMidEqual
      cases modalityPathDecEq modeDecEq modalityDecEq leftContextL leftContextR with
      | isFalse leftContextDiffer =>
          exact isFalse (fun atomsEqual => leftContextDiffer (by injection atomsEqual))
      | isTrue leftContextEqual =>
        subst leftContextEqual
        cases modalityPathDecEq modeDecEq modalityDecEq genDomL genDomR with
        | isFalse genDomDiffer => exact isFalse (fun atomsEqual => genDomDiffer (by injection atomsEqual))
        | isTrue genDomEqual =>
          subst genDomEqual
          cases modalityPathDecEq modeDecEq modalityDecEq genCodL genCodR with
          | isFalse genCodDiffer => exact isFalse (fun atomsEqual => genCodDiffer (by injection atomsEqual))
          | isTrue genCodEqual =>
            subst genCodEqual
            cases twoCellDecEq genDomL genCodL genL genR with
            | isFalse genDiffer => exact isFalse (fun atomsEqual => genDiffer (by injection atomsEqual))
            | isTrue genEqual =>
              subst genEqual
              cases modalityPathDecEq modeDecEq modalityDecEq rightContextL rightContextR with
              | isFalse rightContextDiffer =>
                  exact isFalse (fun atomsEqual => rightContextDiffer (by injection atomsEqual))
              | isTrue rightContextEqual => subst rightContextEqual; exact isTrue rfl

/-- Decidable equality of the adjunction seed's spine atoms. -/
def adjunctionSpineAtomDecEq {sourceMode targetMode : AdjunctionMode} :
    DecidableEq (SpineAtom adjunctionModeSignature sourceMode targetMode) :=
  spineAtomDecEq adjunctionModeDecEq adjunctionModalityDecEq adjunctionTwoCellDecEq

/-- ★ The engine's carrier `DecidableEq`: decidable equality of spine LISTS at the adjunction seed. -/
def adjunctionSpineListDecEq {sourceMode targetMode : AdjunctionMode} :
    DecidableEq (List (SpineAtom adjunctionModeSignature sourceMode targetMode)) :=
  @instDecidableEqList _ adjunctionSpineAtomDecEq

/-- Smoke: the carrier decision COMPUTES — the unit's spine decides equal to itself. -/
theorem unitSpine_eq_self_decidably :
    (adjunctionSpineListDecEq adjunctionUnitTwoCell.spine adjunctionUnitTwoCell.spine).decide = true := rfl

/-- Smoke: and it distinguishes the unit's one-atom spine from the identity's empty spine. -/
theorem unitSpine_ne_idSpine_decidably :
    (adjunctionSpineListDecEq adjunctionUnitTwoCell.spine
      (RawTwoCellExpr.id (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)).spine).decide
      = false := rfl

/-! ## The positionwise Godement step + the trace-equivalence bridge -/

/-- The Godement spine step allowed at ANY position: `here` fires it at the head; `under` slides it past an
independent prefix atom.  This is the positionwise closure whose `EquationalTheory` coincides with
`SpineTraceEquiv` — the head-cons congruence of `SpineTraceEquiv` is absorbed into the relation, so the abstract
Knuth-Bendix engine (which decides `EquationalTheory`) settles `SpineTraceEquiv`. -/
inductive SpineGodementAtAnyPosition (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} :
    List (SpineAtom signature overallSource overallTarget) →
    List (SpineAtom signature overallSource overallTarget) → Prop where
  /-- A Godement step at the head of the list. -/
  | here {firstList secondList : List (SpineAtom signature overallSource overallTarget)} :
      SpineGodementStep signature firstList secondList →
      SpineGodementAtAnyPosition signature firstList secondList
  /-- Slide a positionwise step past one independent prefix atom. -/
  | under (atom : SpineAtom signature overallSource overallTarget)
      {firstList secondList : List (SpineAtom signature overallSource overallTarget)} :
      SpineGodementAtAnyPosition signature firstList secondList →
      SpineGodementAtAnyPosition signature (atom :: firstList) (atom :: secondList)

/-- A positionwise Godement step is a trace equivalence (recursion on the position: `here` is one step,
`under` is one head-cons congruence). -/
theorem SpineGodementAtAnyPosition.toSpineTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (step : SpineGodementAtAnyPosition signature firstList secondList) :
    SpineTraceEquiv signature firstList secondList := by
  induction step with
  | here godementStep => exact SpineTraceEquiv.ofStep godementStep
  | under atom _ inductionHypothesis => exact SpineTraceEquiv.consCongr atom inductionHypothesis

/-- The equational theory of the positionwise step is closed under prepending a head atom (induction on the
conversion, threading `under` through the single-step case). -/
theorem equationalTheory_consCongr {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (atom : SpineAtom signature overallSource overallTarget)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (conv : EquationalTheory (SpineGodementAtAnyPosition signature) firstList secondList) :
    EquationalTheory (SpineGodementAtAnyPosition signature) (atom :: firstList) (atom :: secondList) := by
  induction conv with
  | rule step => exact EquationalTheory.rule (SpineGodementAtAnyPosition.under atom step)
  | refl _ => exact EquationalTheory.refl _
  | symm _ inductionHypothesis => exact EquationalTheory.symm inductionHypothesis
  | trans _ _ firstHypothesis secondHypothesis => exact EquationalTheory.trans firstHypothesis secondHypothesis

/-- ★ **Trace equivalence IS the equational theory of the positionwise Godement step.**  The bridge that lets
the abstract Knuth-Bendix decision engine (which decides `EquationalTheory`) settle `SpineTraceEquiv`: forward,
`SpineTraceEquiv`'s reflexivity / symmetry / transitivity map across and its single step / head-cons congruence
land in `rule (here …)` / `equationalTheory_consCongr`; backward, a positionwise step is a trace equivalence
(`toSpineTraceEquiv`) and the equivalence-closure constructors map across. -/
theorem spineTraceEquiv_iff_equationalTheory {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)} :
    SpineTraceEquiv signature firstList secondList ↔
      EquationalTheory (SpineGodementAtAnyPosition signature) firstList secondList := by
  constructor
  · intro traceEquiv
    induction traceEquiv with
    | ofStep godementStep => exact EquationalTheory.rule (SpineGodementAtAnyPosition.here godementStep)
    | refl _ => exact EquationalTheory.refl _
    | symm _ inductionHypothesis => exact EquationalTheory.symm inductionHypothesis
    | trans _ _ firstHypothesis secondHypothesis => exact EquationalTheory.trans firstHypothesis secondHypothesis
    | consCongr atom _ inductionHypothesis => exact equationalTheory_consCongr atom inductionHypothesis
  · intro conv
    induction conv with
    | rule step => exact step.toSpineTraceEquiv
    | refl _ => exact SpineTraceEquiv.refl _
    | symm _ inductionHypothesis => exact SpineTraceEquiv.symm inductionHypothesis
    | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-! ## The single-transposition soundness core -/

/-- ★ **A single independent transposition of two adjacent spine atoms is a `SpineGodementStep`.**  The two
atoms are presented in recognized-redex shape: the left atom's right context is `genDomY ∘ rightContextY` (it
factors through the right atom's SOURCE generator and the right atom's right context), and the right atom's left
context is `leftContextX ∘ genCodX` (it factors through the left atom's left context and the left atom's TARGET
generator).  The swap moves the right atom before the left, shifting the left atom's right context (`genDomY →
genCodY`, the right atom's source-generator boundary to its target-generator boundary) and the right atom's left
context (`genCodX → genDomX`, the left atom's target boundary to its source boundary).  Cast-free: this is the
`SpineGodementStep.godement` constructor instantiated at the single-generator Godement square (`id ⊟ gen` on each
side), whose two spine difference-lists compute to exactly these atom lists by definitional reduction. -/
theorem singleAtomGodementStep {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {leftMidX middleMode rightMidY : signature.graph.Mode}
    (leftContextX : ModalityPath signature.graph overallSource leftMidX)
    (genDomX genCodX : ModalityPath signature.graph leftMidX middleMode)
    (genX : signature.twoCell genDomX genCodX)
    (genDomY genCodY : ModalityPath signature.graph middleMode rightMidY)
    (genY : signature.twoCell genDomY genCodY)
    (rightContextY : ModalityPath signature.graph rightMidY overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget)) :
    SpineGodementStep signature
      (⟨leftMidX, middleMode, leftContextX, genDomX, genCodX, genX,
          composePath genDomY rightContextY⟩ ::
        ⟨middleMode, rightMidY, composePath leftContextX genCodX, genDomY, genCodY, genY,
          rightContextY⟩ :: rest)
      (⟨middleMode, rightMidY, composePath leftContextX genDomX, genDomY, genCodY, genY,
          rightContextY⟩ ::
        ⟨leftMidX, middleMode, leftContextX, genDomX, genCodX, genX,
          composePath genCodY rightContextY⟩ :: rest) :=
  SpineGodementStep.godement (RawTwoCellExpr.id genDomX) (RawTwoCellExpr.gen genX)
    (RawTwoCellExpr.gen genY) (RawTwoCellExpr.id genCodY) leftContextX rightContextY rest

/-- ★ Hence a single recognized transposition is a `SpineTraceEquiv` — the atom the deferred reducer's
soundness is assembled from (lifted to a positionwise step under any prefix by `SpineTraceEquiv.consCongr`). -/
theorem singleAtomTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {leftMidX middleMode rightMidY : signature.graph.Mode}
    (leftContextX : ModalityPath signature.graph overallSource leftMidX)
    (genDomX genCodX : ModalityPath signature.graph leftMidX middleMode)
    (genX : signature.twoCell genDomX genCodX)
    (genDomY genCodY : ModalityPath signature.graph middleMode rightMidY)
    (genY : signature.twoCell genDomY genCodY)
    (rightContextY : ModalityPath signature.graph rightMidY overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget)) :
    SpineTraceEquiv signature
      (⟨leftMidX, middleMode, leftContextX, genDomX, genCodX, genX,
          composePath genDomY rightContextY⟩ ::
        ⟨middleMode, rightMidY, composePath leftContextX genCodX, genDomY, genCodY, genY,
          rightContextY⟩ :: rest)
      (⟨middleMode, rightMidY, composePath leftContextX genDomX, genDomY, genCodY, genY,
          rightContextY⟩ ::
        ⟨leftMidX, middleMode, leftContextX, genDomX, genCodX, genX,
          composePath genCodY rightContextY⟩ :: rest) :=
  SpineTraceEquiv.ofStep (singleAtomGodementStep leftContextX genDomX genCodX genX genDomY genCodY genY
    rightContextY rest)

/-! ## The end-to-end engine wiring -/

/-- ★ **The trace word problem, wired to the convergent-reducer decision engine.**  A deterministic reducer for
the positionwise Godement step that is SOUND (each fired step is a real step), COMPLETE (it halts exactly at the
canonical normal form), TERMINATING (the step is strongly normalizing), and whose step relation is CONFLUENT —
universally over the boundary modes — DECIDES `SpineTraceEquiv` on every cell pair, hence inhabits the exact
`traceDecision` type `AdjunctionSpineTraceDecision`.  The engine
(`decidableEquationalTheoryOfReducerSN`) builds the normal-form function by `Acc.rec` over the termination
witness (no `WellFounded.fix`) and decides the equational theory by Church-Rosser; the bridge
`spineTraceEquiv_iff_equationalTheory` transports that decision onto `SpineTraceEquiv`.  Supplying the reducer
bundle is the SOLE remaining obligation (the Foata canonicalization with context shifts + its SN + confluence —
see the module header). -/
@[reducible] def adjunctionTraceDecisionOfReducer
    (reduceStep : {sourceMode targetMode : AdjunctionMode} →
      List (SpineAtom adjunctionModeSignature sourceMode targetMode) →
      Option (List (SpineAtom adjunctionModeSignature sourceMode targetMode)))
    (reduceStep_sound : {sourceMode targetMode : AdjunctionMode} →
      {origin reduct : List (SpineAtom adjunctionModeSignature sourceMode targetMode)} →
      reduceStep origin = some reduct → SpineGodementAtAnyPosition adjunctionModeSignature origin reduct)
    (reduceStep_complete : {sourceMode targetMode : AdjunctionMode} →
      {origin : List (SpineAtom adjunctionModeSignature sourceMode targetMode)} →
      reduceStep origin = none →
      ∀ next, ¬ SpineGodementAtAnyPosition adjunctionModeSignature origin next)
    (terminating : {sourceMode targetMode : AdjunctionMode} →
      ∀ value : List (SpineAtom adjunctionModeSignature sourceMode targetMode),
      Acc (fun reduct origin => SpineGodementAtAnyPosition adjunctionModeSignature origin reduct) value)
    (confluent : {sourceMode targetMode : AdjunctionMode} →
      Confluent (SpineGodementAtAnyPosition (overallSource := sourceMode) (overallTarget := targetMode)
        adjunctionModeSignature)) :
    AdjunctionSpineTraceDecision :=
  fun {_sourceMode _targetMode} {_sourcePath _targetPath} cellFirst cellSecond =>
    letI : Decidable (EquationalTheory (SpineGodementAtAnyPosition adjunctionModeSignature)
        cellFirst.spine cellSecond.spine) :=
      @decidableEquationalTheoryOfReducerSN _ _ adjunctionSpineListDecEq
        reduceStep reduceStep_sound reduceStep_complete terminating confluent
        cellFirst.spine cellSecond.spine
    decidable_of_iff
      (EquationalTheory (SpineGodementAtAnyPosition adjunctionModeSignature)
        cellFirst.spine cellSecond.spine)
      (spineTraceEquiv_iff_equationalTheory).symm

/-- ★ **The assembly hook.**  Feeding `adjunctionTraceDecisionOfReducer`'s output into the predecessors'
`adjunctionTwoCellWordProblemModuloTraceRoute` inhabits the full `DecidableTwoCellConvFor adjunctionModeSignature`
modulo `(reducer bundle, reconstruct)` — exhibiting this file's contribution as exactly the `traceDecision` slot
of the keystone assembly (the whole NO-direction is already free from soundness, the YES-direction is the
supplied `reconstruct`). -/
def adjunctionTwoCellWordProblemViaGodementReducer
    (reduceStep : {sourceMode targetMode : AdjunctionMode} →
      List (SpineAtom adjunctionModeSignature sourceMode targetMode) →
      Option (List (SpineAtom adjunctionModeSignature sourceMode targetMode)))
    (reduceStep_sound : {sourceMode targetMode : AdjunctionMode} →
      {origin reduct : List (SpineAtom adjunctionModeSignature sourceMode targetMode)} →
      reduceStep origin = some reduct → SpineGodementAtAnyPosition adjunctionModeSignature origin reduct)
    (reduceStep_complete : {sourceMode targetMode : AdjunctionMode} →
      {origin : List (SpineAtom adjunctionModeSignature sourceMode targetMode)} →
      reduceStep origin = none →
      ∀ next, ¬ SpineGodementAtAnyPosition adjunctionModeSignature origin next)
    (terminating : {sourceMode targetMode : AdjunctionMode} →
      ∀ value : List (SpineAtom adjunctionModeSignature sourceMode targetMode),
      Acc (fun reduct origin => SpineGodementAtAnyPosition adjunctionModeSignature origin reduct) value)
    (confluent : {sourceMode targetMode : AdjunctionMode} →
      Confluent (SpineGodementAtAnyPosition (overallSource := sourceMode) (overallTarget := targetMode)
        adjunctionModeSignature))
    (reconstruct : AdjunctionSpineTraceReconstruction) :
    DecidableTwoCellConvFor adjunctionModeSignature :=
  adjunctionTwoCellWordProblemModuloTraceRoute
    (adjunctionTraceDecisionOfReducer reduceStep reduceStep_sound reduceStep_complete terminating confluent)
    reconstruct

/-! ## Honesty marker -/

/-- **Honesty marker.**  `traceDecision` is NOT fully discharged: this file ships the carrier `DecidableEq`, the
`SpineTraceEquiv` ⟷ `EquationalTheory` bridge, the single-transposition soundness core, and the engine wiring
(`adjunctionTraceDecisionOfReducer`) — reducing `traceDecision` to a single named obligation: a sound + complete
+ terminating + confluent deterministic reducer for the positionwise Godement step (the source-anchored Foata
canonicalization with context shifts, its strong normalization, and its confluence — the documented Gratzer
confluence-modulo-interchange core).  Until that reducer is supplied, `fxMode_hasSpineTraceDecision` /
`fxMode_hasModeRelativeConvDecision` / `fxMode_hasDecidableTwoCellEquality` stay `false`.  `= false`. -/
def fxMode_hasSpineTraceDecision : Bool := false

end FX1Poly.Tier0
