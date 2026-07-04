import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TraceNormalForm
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SwapInversion

/-! # TraceNormalFormNonInvariance — ★★ the Eckmann–Hilton bubble falsification (FREE-6b)

THE FINDING.  The minimal-extraction normal form (`normalizeSpine`) is NOT invariant
across a single `SpineAtomSwap` — the open FREE-6b invariance theorem is FALSE as stated.
This file mechanizes the minimal counterexample and the structural root cause.

The signature: one mode, one 1-generator `strand`, two 2-generators — a CREATION
`creation : nil ⇒ strand` and a SCALAR BUBBLE `bubble : nil ⇒ nil` — keyed
creation < bubble.  The counterexample pair:

  * source trace `l` = [creation@(nil,nil), bubble@(strand,nil)] — create the strand,
    then the bubble floats to its RIGHT;
  * target trace `m` = [bubble@(nil,nil), creation@(nil,nil)] — one swap away.

`fronts(l)` sees exactly two candidates and keeps its head: `nf(l) = l` (bubble RIGHT of
the strand).  But `fronts(m)` recognizes the pair (bubble, creation) in BOTH directions:
the forward lift RE-SWAPS the pair and lands the bubble LEFT of the strand
(`bubbleRepeatSwapStep`), the reverse lift reconstructs `l`'s bubble-RIGHT placement.
Both lifts carry the same front atom at the same measure, the fold is first-wins on
ties, the forward lift enumerates first:
`nf(m) = [creation@(nil,nil), bubble@(nil,strand)] ≠ nf(l)`.

Root cause (also mechanized): `AtomicTraceEquiv` is NOT left-cancellable —
`creation :: [bubble@(strand,nil)] ~ creation :: [bubble@(nil,strand)]` (the bubble
slides around the creation event through its nil source boundary — Eckmann–Hilton), yet
the singleton tails are inequivalent (a singleton trace admits no swap, by the
`atomicTraceEquiv_forcesSingletonEqual` inversion).  Consequently the same-front
remainder-agreement step of the planned exchange/invariance argument is unprovable, and
the two-lift enumeration is not class-complete at (front, remainder) granularity: the
bubble-LEFT decomposition of `l` is a valid extraction of `l` (through the two-swap
zigzag `l ⇝ m ⇝ ·`) but is NOT in `frontExtractions l`, which crosses the head at most
once per level.

ROUTE CONSEQUENCE.  Invariance, completeness, and the FREE-7 decision cannot go through
per-level minimal extraction.  The corrected route is CLASS SATURATION: the ~-class of a
trace is finite (fixed length; each atom's contexts are prefixes of the swap-invariant
stage composites), so bounded reachability search decides `AtomicTraceEquiv`, and the
canonical form — if wanted — is the class's least element under a total atom order.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The bubble signature: one mode, one strand, a creation and a scalar bubble -/

/-- The single mode. -/
inductive BubbleMode where
  /-- The only mode. -/
  | onlyMode

/-- The single 1-cell generator: the strand. -/
inductive BubbleModality : BubbleMode → BubbleMode → Type where
  /-- The strand generator. -/
  | strand : BubbleModality BubbleMode.onlyMode BubbleMode.onlyMode

/-- The bubble-signature quiver. -/
def bubbleGraph : ModeGraph :=
  { Mode := BubbleMode, Modality := BubbleModality }

/-- The empty 1-cell at the only mode. -/
def bubbleNilPath : ModalityPath bubbleGraph BubbleMode.onlyMode BubbleMode.onlyMode :=
  @ModalityPath.nil bubbleGraph BubbleMode.onlyMode

/-- The strand as a length-1 free 1-cell. -/
def bubbleStrandPath : ModalityPath bubbleGraph BubbleMode.onlyMode BubbleMode.onlyMode :=
  @ModalityPath.cons bubbleGraph BubbleMode.onlyMode BubbleMode.onlyMode
    BubbleMode.onlyMode BubbleModality.strand bubbleNilPath

/-- The two generating 2-cells: the strand CREATION (`nil ⇒ strand`) and the scalar
BUBBLE (`nil ⇒ nil`). -/
inductive BubbleTwoCell : {sourceMode targetMode : BubbleMode} →
    ModalityPath bubbleGraph sourceMode targetMode →
    ModalityPath bubbleGraph sourceMode targetMode → Type where
  /-- The strand creation. -/
  | creation : BubbleTwoCell bubbleNilPath bubbleStrandPath
  /-- The floating scalar bubble. -/
  | bubble : BubbleTwoCell bubbleNilPath bubbleNilPath

/-- The bubble 2-polygraph. -/
def bubbleSignature : ModeSignature :=
  { graph := bubbleGraph,
    twoCell := fun {_sourceMode _targetMode} domPath codPath =>
      BubbleTwoCell domPath codPath }

/-- Decidable mode equality (single constructor). -/
def bubbleModeDecEq : DecidableEq BubbleMode
  | BubbleMode.onlyMode, BubbleMode.onlyMode => Decidable.isTrue rfl

/-- Decidable modality equality (single constructor). -/
def bubbleModalityDecEq : (sourceMode targetMode : BubbleMode) →
    DecidableEq (BubbleModality sourceMode targetMode)
  | _, _, BubbleModality.strand, BubbleModality.strand => Decidable.isTrue rfl

/-- The key: creation before bubble. -/
def bubbleKeyOf {sourceMode targetMode : BubbleMode}
    {domPath codPath : ModalityPath bubbleGraph sourceMode targetMode}
    (generator : BubbleTwoCell domPath codPath) : Nat :=
  match generator with
  | BubbleTwoCell.creation => 0
  | BubbleTwoCell.bubble => 1

/-- Each boundary fiber holds at most one generator, so the key separates trivially. -/
theorem bubbleKeyOf_injectiveOnFiber {sourceMode targetMode : BubbleMode}
    {domPath codPath : ModalityPath bubbleGraph sourceMode targetMode}
    (firstGenerator secondGenerator : BubbleTwoCell domPath codPath)
    (_keysEqual : bubbleKeyOf firstGenerator = bubbleKeyOf secondGenerator) :
    firstGenerator = secondGenerator := by
  cases firstGenerator with
  | creation => cases secondGenerator with | creation => rfl
  | bubble => cases secondGenerator with | bubble => rfl

/-- The keying: creation (0) precedes bubble (1). -/
def bubbleKeying : GeneratorKeying bubbleSignature where
  keyOf := bubbleKeyOf
  keyOf_injectiveOnFiber := bubbleKeyOf_injectiveOnFiber

/-! ## The counterexample traces -/

/-- The creation atom at the origin (empty contexts). -/
def bubbleCreationAtom :
    SpineAtom bubbleSignature BubbleMode.onlyMode BubbleMode.onlyMode :=
  ⟨BubbleMode.onlyMode, BubbleMode.onlyMode, bubbleNilPath, bubbleNilPath,
    bubbleStrandPath, BubbleTwoCell.creation, bubbleNilPath⟩

/-- The bubble floating RIGHT of the strand (left context = strand). -/
def bubbleRightOfStrandAtom :
    SpineAtom bubbleSignature BubbleMode.onlyMode BubbleMode.onlyMode :=
  ⟨BubbleMode.onlyMode, BubbleMode.onlyMode, bubbleStrandPath, bubbleNilPath,
    bubbleNilPath, BubbleTwoCell.bubble, bubbleNilPath⟩

/-- The bubble at the origin, before the strand exists (empty contexts). -/
def bubbleAtOriginAtom :
    SpineAtom bubbleSignature BubbleMode.onlyMode BubbleMode.onlyMode :=
  ⟨BubbleMode.onlyMode, BubbleMode.onlyMode, bubbleNilPath, bubbleNilPath,
    bubbleNilPath, BubbleTwoCell.bubble, bubbleNilPath⟩

/-- The bubble floating LEFT of the strand (right context = strand) — the placement the
source trace's enumeration can never reach. -/
def bubbleLeftOfStrandAtom :
    SpineAtom bubbleSignature BubbleMode.onlyMode BubbleMode.onlyMode :=
  ⟨BubbleMode.onlyMode, BubbleMode.onlyMode, bubbleNilPath, bubbleNilPath,
    bubbleNilPath, BubbleTwoCell.bubble, bubbleStrandPath⟩

/-- The source trace: create the strand, the bubble floats to its right. -/
def bubbleSourceTrace :
    List (SpineAtom bubbleSignature BubbleMode.onlyMode BubbleMode.onlyMode) :=
  [bubbleCreationAtom, bubbleRightOfStrandAtom]

/-- The target trace: the bubble first, then create the strand — one swap away. -/
def bubbleTargetTrace :
    List (SpineAtom bubbleSignature BubbleMode.onlyMode BubbleMode.onlyMode) :=
  [bubbleAtOriginAtom, bubbleCreationAtom]

/-- The source pair (creation, bubble-right) forward-recognizes: the bubble crosses the
creation leftward (all factorizations empty-or-strand, definitional). -/
def bubbleSourceSwapWitness :
    AdjacentSwapWitness bubbleCreationAtom bubbleRightOfStrandAtom where
  inertPath := bubbleNilPath
  leftContextFactors := rfl
  rightContextFactors := rfl

/-- The two traces are one adjacent swap apart (the source witness's own swap: all
whiskering accumulators and the inert zone empty). -/
theorem bubbleSwapStep :
    SpineAtomSwap bubbleSignature bubbleSourceTrace bubbleTargetTrace :=
  bubbleSourceSwapWitness.toSwap []

/-- The target's adjacent pair (bubble, creation) FORWARD-recognizes AGAIN — the
Eckmann–Hilton re-swap whose reconstruction places the bubble LEFT of the strand. -/
def bubbleRepeatSwapWitness :
    AdjacentSwapWitness bubbleAtOriginAtom bubbleCreationAtom where
  inertPath := bubbleNilPath
  leftContextFactors := rfl
  rightContextFactors := rfl

/-- The target trace swaps AGAIN, onto the bubble-LEFT placement: the two-swap zigzag
`l ⇝ m ⇝ [creation, bubble-left]` whose endpoint the source's enumeration misses. -/
theorem bubbleRepeatSwapStep :
    SpineAtomSwap bubbleSignature bubbleTargetTrace
      [bubbleCreationAtom, bubbleLeftOfStrandAtom] :=
  bubbleRepeatSwapWitness.toSwap []

/-! ## ★★ The falsification: the normal form is not swap-invariant -/

/-- The source trace is already its own normal form: the bubble stays RIGHT of the
strand (computed). -/
theorem bubbleSourceNormalFormComputes :
    normalizeSpine bubbleKeying bubbleModeDecEq bubbleModalityDecEq bubbleSourceTrace
      = [bubbleCreationAtom, bubbleRightOfStrandAtom] := rfl

/-- The target trace normalizes with the bubble LEFT of the strand: the forward re-swap
lift wins the fold first at the same measure as the reverse lift (computed). -/
theorem bubbleTargetNormalFormComputes :
    normalizeSpine bubbleKeying bubbleModeDecEq bubbleModalityDecEq bubbleTargetTrace
      = [bubbleCreationAtom, bubbleLeftOfStrandAtom] := rfl

/-- The two normal forms differ: the bubble's left context is the strand on one side and
empty on the other. -/
theorem bubbleNormalFormsDiffer :
    normalizeSpine bubbleKeying bubbleModeDecEq bubbleModalityDecEq bubbleSourceTrace
      ≠ normalizeSpine bubbleKeying bubbleModeDecEq bubbleModalityDecEq
          bubbleTargetTrace := by
  intro normalFormsEqual
  have literalListsEqual : [bubbleCreationAtom, bubbleRightOfStrandAtom]
      = [bubbleCreationAtom, bubbleLeftOfStrandAtom] :=
    bubbleSourceNormalFormComputes.symm.trans
      (normalFormsEqual.trans bubbleTargetNormalFormComputes)
  injection literalListsEqual with _ tailsEqual
  injection tailsEqual with secondAtomsEqual _
  have lengthClash : (1 : Nat) = 0 :=
    congrArg (fun atom => atom.leftContext.length) secondAtomsEqual
  exact Nat.noConfusion lengthClash

/-- ★★ **`normalizeSpine` is NOT trace-invariant**: a single adjacent swap changes the
normal form.  The FREE-6b invariance theorem is FALSE for per-level minimal
extraction. -/
theorem normalizeSpine_isNotSwapInvariant :
    ∃ (sourceTrace targetTrace :
        List (SpineAtom bubbleSignature BubbleMode.onlyMode BubbleMode.onlyMode)),
      SpineAtomSwap bubbleSignature sourceTrace targetTrace
        ∧ normalizeSpine bubbleKeying bubbleModeDecEq bubbleModalityDecEq sourceTrace
            ≠ normalizeSpine bubbleKeying bubbleModeDecEq bubbleModalityDecEq
                targetTrace :=
  ⟨bubbleSourceTrace, bubbleTargetTrace, bubbleSwapStep, bubbleNormalFormsDiffer⟩

/-! ## The structural root cause: trace equivalence is not left-cancellable -/

/-- Singleton traces admit no swap: a trace equivalence between singletons forces the
atoms equal (derivation induction; the swap case dies on length, the trans case
threads a singleton middle by `lengthEq`). -/
theorem atomicTraceEquiv_forcesSingletonEqual {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (traceEquiv : AtomicTraceEquiv signature firstList secondList) :
    ∀ {firstAtom secondAtom : SpineAtom signature overallSource overallTarget},
      firstList = [firstAtom] → secondList = [secondAtom] → firstAtom = secondAtom := by
  induction traceEquiv with
  | ofSwap swapStep =>
      intro firstAtom secondAtom firstShape _secondShape
      obtain ⟨leftAtom, rightAtom, restList, _witness, lhsShape, _rhsShape⟩ :=
        swapStep.forwardInversion
      have listsClash : [firstAtom] = leftAtom :: rightAtom :: restList :=
        firstShape.symm.trans lhsShape
      injection listsClash with _ tailClash
      injection tailClash
  | refl spineList =>
      intro firstAtom secondAtom firstShape secondShape
      exact Option.some.inj
        (congrArg List.head? (firstShape.symm.trans secondShape))
  | symm _innerEquiv innerHypothesis =>
      intro firstAtom secondAtom firstShape secondShape
      exact (innerHypothesis secondShape firstShape).symm
  | @trans _startList middleList _finishList firstLeg _secondLeg firstHypothesis
      secondHypothesis =>
      intro firstAtom secondAtom firstShape secondShape
      have middleLengthOne : middleList.length = 1 :=
        ((congrArg List.length firstShape).symm.trans firstLeg.lengthEq).symm
      cases middleList with
      | nil =>
          have zeroEqualsOne : (0 : Nat) = 1 := middleLengthOne
          exact Nat.noConfusion zeroEqualsOne
      | cons middleAtom middleRest =>
          cases middleRest with
          | nil =>
              have firstEqualsMiddle : firstAtom = middleAtom :=
                firstHypothesis firstShape rfl
              have middleEqualsSecond : middleAtom = secondAtom :=
                secondHypothesis rfl secondShape
              exact firstEqualsMiddle.trans middleEqualsSecond
          | cons secondMiddleAtom deeperRest =>
              have lengthsClash : deeperRest.length + 2 = 1 := middleLengthOne
              have succClash : deeperRest.length + 1 = 0 := Nat.succ.inj lengthsClash
              exact Nat.noConfusion succClash
  | consCongr atom _innerEquiv _innerHypothesis =>
      intro firstAtom secondAtom firstShape secondShape
      have headEqualsFirst : atom = firstAtom :=
        Option.some.inj (congrArg List.head? firstShape)
      have headEqualsSecond : atom = secondAtom :=
        Option.some.inj (congrArg List.head? secondShape)
      exact headEqualsFirst.symm.trans headEqualsSecond

/-- ★★ **`AtomicTraceEquiv` is NOT left-cancellable**: the bubble slides around the
creation event through its nil source boundary (Eckmann–Hilton), so the cons-traces are
equivalent while the singleton tails — bubble RIGHT of the strand vs bubble LEFT of it —
are not.  This kills any same-front remainder-agreement lemma. -/
theorem atomicTraceEquiv_isNotLeftCancellable :
    ∃ (headAtom : SpineAtom bubbleSignature BubbleMode.onlyMode BubbleMode.onlyMode)
      (firstTail secondTail :
        List (SpineAtom bubbleSignature BubbleMode.onlyMode BubbleMode.onlyMode)),
      AtomicTraceEquiv bubbleSignature (headAtom :: firstTail) (headAtom :: secondTail)
        ∧ ¬ AtomicTraceEquiv bubbleSignature firstTail secondTail := by
  have consEquiv : AtomicTraceEquiv bubbleSignature
      (bubbleCreationAtom :: [bubbleRightOfStrandAtom])
      (bubbleCreationAtom :: [bubbleLeftOfStrandAtom]) :=
    AtomicTraceEquiv.trans (AtomicTraceEquiv.ofSwap bubbleSwapStep)
      (AtomicTraceEquiv.ofSwap bubbleRepeatSwapStep)
  refine ⟨bubbleCreationAtom, [bubbleRightOfStrandAtom], [bubbleLeftOfStrandAtom],
    consEquiv, ?_⟩
  intro tailsEquiv
  have atomsEqual : bubbleRightOfStrandAtom = bubbleLeftOfStrandAtom :=
    atomicTraceEquiv_forcesSingletonEqual tailsEquiv rfl rfl
  have lengthClash : (1 : Nat) = 0 :=
    congrArg (fun atom => atom.leftContext.length) atomsEqual
  exact Nat.noConfusion lengthClash

end FX1Poly.Polygraph
