import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap
import FX1Poly.Polygraph.Rewriting.Orders.TerminationOrders

/-! # OrientedAtomSwap — the oriented atomic swap + its termination (FREE-6a)

The atomic swap closure (`AtomicTraceEquiv`, FREE-5) is symmetric; deciding it needs a
CANONICAL FORM, hence an ORIENTATION.  This file ships the oriented rewriting system and its
termination:

  * `GeneratorKeying` — the decision's parameter: a `Nat` key for the signature's generating
    2-cells, injective on each fiber.  The key breaks the one genuinely structureless tie —
    two adjacent SCALAR atoms (empty boundaries) at the same column with identical contexts
    (the Eckmann–Hilton-adjacent configuration), where no context measure can distinguish
    the two orders;
  * `spineTraceVector` — the measure: each atom contributes the triple
    (left-context length, right-context length, generator key), flattened in list order.
    Comparing flattened vectors lexicographically IS the per-position triple-lex;
  * `OrientedAtomStep` — the oriented step: an adjacent swap (in whichever direction),
    anywhere in the list, REQUIRED to descend in the trace-vector order.  Orientation is BY
    the measure, so termination is by construction and all case analysis (which swaps
    descend which way, totality on swappable pairs) moves to the normal-form legs
    (FREE-6b/c);
  * `OrientedAtomStep.toAtomicTraceEquiv` — oriented steps are sound for the closure;
  * `OrientedAtomStep.decreasesTraceVector` + `orientedAtomStep_isTerminating` — the measure
    strictly decreases through the deep congruence, so the system is terminating
    (`wellFounded_of_lexMeasure` over `Nat.lt`).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

open FX1Poly.Core (LexListStep wellFounded_of_lexMeasure)

/-! ## The keying parameter -/

/-- A `Nat` key for the signature's generating 2-cells, injective on each fiber
(fixed boundary 1-cells).  This is the decision's tiebreak parameter: two adjacent scalar
atoms with identical contexts commute with NO structural difference between the two orders,
so a canonical form must order them by generator identity — which is only possible with
choice data on the generators.  Concrete signatures (the FX mode signature's finite
generator enumeration) key trivially. -/
structure GeneratorKeying (signature : ModeSignature) where
  /-- The key of a generating 2-cell. -/
  keyOf : {sourceMode targetMode : signature.graph.Mode} →
    {domPath codPath : ModalityPath signature.graph sourceMode targetMode} →
    signature.twoCell domPath codPath → Nat
  /-- Keys separate generators within each fiber. -/
  keyOf_injectiveOnFiber : ∀ {sourceMode targetMode : signature.graph.Mode}
    {domPath codPath : ModalityPath signature.graph sourceMode targetMode}
    (firstGenerator secondGenerator : signature.twoCell domPath codPath),
    keyOf firstGenerator = keyOf secondGenerator → firstGenerator = secondGenerator

/-! ## The trace-vector measure -/

/-- The measure of a spine: each atom contributes (left-context length, right-context
length, generator key), flattened in list order.  Lexicographic comparison of flattened
vectors is exactly the per-position lexicographic comparison of the triples. -/
def spineTraceVector {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (keying : GeneratorKeying signature) :
    List (SpineAtom signature overallSource overallTarget) → List Nat
  | [] => []
  | atom :: rest =>
      atom.leftContext.length :: atom.rightContext.length :: keying.keyOf atom.generator ::
        spineTraceVector keying rest

/-- A lexicographic descent is stable under a shared three-entry prefix — the deep-congruence
transport for the trace vector (a cons atom contributes exactly three shared entries). -/
theorem lexListStep_prependTriple {smallList bigList : List Nat}
    (columnEntry rightEntry keyEntry : Nat)
    (step : LexListStep Nat.lt smallList bigList) :
    LexListStep Nat.lt (columnEntry :: rightEntry :: keyEntry :: smallList)
      (columnEntry :: rightEntry :: keyEntry :: bigList) := by
  obtain ⟨commonPrefix, smallHead, bigHead, smallTail, bigTail,
    bigEq, smallEq, tailLenEq, headLt⟩ := step
  refine ⟨columnEntry :: rightEntry :: keyEntry :: commonPrefix, smallHead, bigHead,
    smallTail, bigTail, ?_, ?_, tailLenEq, headLt⟩
  · rw [bigEq]; rfl
  · rw [smallEq]; rfl

/-! ## The oriented step -/

/-- **The oriented atomic swap step**: an adjacent atom swap (in whichever direction),
anywhere in the list, that DESCENDS in the trace-vector order.  Orientation is by the
measure itself — the side condition both orients the swap and certifies termination;
which swaps descend which way is the normal-form legs' case analysis (FREE-6b/c). -/
inductive OrientedAtomStep {signature : ModeSignature} (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode} :
    List (SpineAtom signature overallSource overallTarget) →
    List (SpineAtom signature overallSource overallTarget) → Prop where
  /-- Fire a head-position swap along its constructor direction (left-zone atom first →
  right-zone atom first) when that direction descends. -/
  | hereForward {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
      (swapStep : SpineAtomSwap signature firstList secondList)
      (descends : LexListStep Nat.lt (spineTraceVector keying secondList)
        (spineTraceVector keying firstList)) :
      OrientedAtomStep keying firstList secondList
  /-- Fire a head-position swap against its constructor direction when THAT direction
  descends. -/
  | hereBackward {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
      (swapStep : SpineAtomSwap signature secondList firstList)
      (descends : LexListStep Nat.lt (spineTraceVector keying secondList)
        (spineTraceVector keying firstList)) :
      OrientedAtomStep keying firstList secondList
  /-- Fire deeper in the list (an untouched head atom passes through). -/
  | deeper (atom : SpineAtom signature overallSource overallTarget)
      {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
      (innerStep : OrientedAtomStep keying firstList secondList) :
      OrientedAtomStep keying (atom :: firstList) (atom :: secondList)

/-- Oriented steps are sound for the atomic closure. -/
theorem OrientedAtomStep.toAtomicTraceEquiv {signature : ModeSignature}
    {keying : GeneratorKeying signature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (step : OrientedAtomStep keying firstList secondList) :
    AtomicTraceEquiv signature firstList secondList := by
  induction step with
  | hereForward swapStep _ => exact AtomicTraceEquiv.ofSwap swapStep
  | hereBackward swapStep _ => exact AtomicTraceEquiv.symm (AtomicTraceEquiv.ofSwap swapStep)
  | deeper atom _ innerHypothesis => exact AtomicTraceEquiv.consCongr atom innerHypothesis

/-- The trace vector strictly descends along every oriented step — the head cases carry the
descent, the deep case transports it under the shared three-entry prefix. -/
theorem OrientedAtomStep.decreasesTraceVector {signature : ModeSignature}
    {keying : GeneratorKeying signature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (step : OrientedAtomStep keying firstList secondList) :
    LexListStep Nat.lt (spineTraceVector keying secondList)
      (spineTraceVector keying firstList) := by
  induction step with
  | hereForward _ descends => exact descends
  | hereBackward _ descends => exact descends
  | deeper atom _ innerHypothesis =>
      exact lexListStep_prependTriple atom.leftContext.length atom.rightContext.length
        (keying.keyOf atom.generator) innerHypothesis

/-- ★ **The oriented system terminates**: every oriented step strictly decreases the
trace vector in the lexicographic order over `Nat.lt`, which is well-founded. -/
theorem orientedAtomStep_isTerminating {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode} :
    WellFounded (fun secondList firstList :
        List (SpineAtom signature overallSource overallTarget) =>
      OrientedAtomStep keying firstList secondList) :=
  wellFounded_of_lexMeasure Nat.lt_wfRel.wf
    (fun _ _ step => step.decreasesTraceVector)

/-! ## Honesty marker -/

/-- **Honesty marker — oriented step + termination SHIPPED; the normal form is OPEN.**
Shipped: the keyed trace-vector measure, the measure-oriented adjacent swap step (deep
congruence included), soundness for `AtomicTraceEquiv`, and termination
(`orientedAtomStep_isTerminating`).  OPEN (FREE-6b/c): orientation TOTALITY on swappable
pairs (every adjacent swap instance descends in exactly one direction unless the two lists
are equal — the tie-tower analysis over (|fMid|+|inert|, |gLow|, keys, |fHigh|, |gMid|),
needing `keyOf_injectiveOnFiber` at the scalar tie), unique normal forms (Newman or the
functional Foata/insertion route), and completeness (trace-equivalent iff equal normal
forms) — whence the decision (FREE-7).  `= true` records exactly the shipped half. -/
def fxMode_hasOrientedAtomSwapTermination : Bool := true

end FX1Poly.Polygraph
