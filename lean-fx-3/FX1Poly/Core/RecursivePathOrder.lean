import FX1Poly.Core.TerminationOrders

/-! # FX1Poly/Core/RecursivePathOrder
    — the RPO termination certificate: precedence × argument-order, lexicographically

The recursive path ordering (RPO) decides termination of a non-length-decreasing rewrite system by comparing
terms with a PRECEDENCE on the head symbols and, on equal heads, a multiset- or lexicographic-status comparison
of the arguments.  This file builds the RPO TERMINATION CERTIFICATE: the well-founded lexicographic product of a
precedence with an argument order (the multiset or the lex order), and the measure-based termination it yields.

The lexicographic product is formulated as a DISJUNCTION (`LexPair`), not the indexed `Prod.Lex` (whose `cases`
leaks propext via the pair-index match) — inversion is by `obtain`/`rcases` on the `Or`, clean.

## What is proved

* `LexPair` — the lexicographic product of two relations on a pair (first decreases, or first equal and second
  decreases).
* `LexPair.pairAccessible` / `isWellFounded` — the lex product over two well-founded relations is well-founded
  (the standard nested accessibility: outer on the first component, inner on the second).
* `wellFounded_of_lexPairMeasure` — termination by a lexicographic-pair measure.
* `wellFounded_of_precedenceMultisetMeasure` — **the RPO certificate (multiset-status)**: a step terminates if a
  precedence rank decreases, or stays equal while the multiset measure over the arguments decreases.
* `wellFounded_of_precedenceLexMeasure` — **the RPO certificate (lexicographic-status)**: the same with the
  lexicographic argument order.

These are the precedence-then-status comparison of RPO, made measure-based termination certificates.  The full
RECURSIVE path ordering on the FX term structure (the recursive subterm comparison, composing these certificates
through the 203-generator tree) is a downstream construction (typed-SN-gated); this file supplies the
precedence + argument-order core it builds on.

## Zero-axiom verification

`LexPair` is a `∨`; its WF is nested `Acc` induction with `rcases` on the disjunction (no indexed `cases`); the
certificates are `Subrelation.wf` + `InvImage.wf` of the lex product, instantiated at the multiset / lex orders.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

universe firstUniverse secondUniverse carrierUniverse elemUniverse
variable {FirstComponent : Type firstUniverse} {SecondComponent : Type secondUniverse}

/-- The **lexicographic product** of two relations on a pair (disjunction form, NOT the indexed `Prod.Lex`): the
first component strictly decreases, or it is equal and the second component strictly decreases. -/
def LexPair (firstRel : FirstComponent → FirstComponent → Prop)
    (secondRel : SecondComponent → SecondComponent → Prop)
    (smallPair bigPair : FirstComponent × SecondComponent) : Prop :=
  firstRel smallPair.1 bigPair.1
    ∨ (smallPair.1 = bigPair.1 ∧ secondRel smallPair.2 bigPair.2)

/-- Every pair with an accessible first component (and a well-founded second relation) is lex-accessible.  Nested
accessibility: outer induction on the first component's accessibility, inner on the second's. -/
theorem LexPair.pairAccessible
    (firstRel : FirstComponent → FirstComponent → Prop)
    (secondRel : SecondComponent → SecondComponent → Prop)
    (secondWellFounded : WellFounded secondRel)
    {firstValue : FirstComponent} (accFirst : Acc firstRel firstValue) :
    ∀ secondValue : SecondComponent,
      Acc (LexPair firstRel secondRel) (firstValue, secondValue) := by
  induction accFirst with
  | intro firstValue _accFirstPred ihFirst =>
    intro secondValue
    induction (secondWellFounded.apply secondValue) with
    | intro secondValue _accSecondPred ihSecond =>
      apply Acc.intro
      intro candidatePair step
      obtain ⟨candidateFirst, candidateSecond⟩ := candidatePair
      rcases step with firstStep | ⟨firstEq, secondStep⟩
      · exact ihFirst candidateFirst firstStep candidateSecond
      · subst firstEq
        exact ihSecond candidateSecond secondStep

/-- **The lexicographic product over two well-founded relations is well-founded.** -/
theorem LexPair.isWellFounded
    (firstRel : FirstComponent → FirstComponent → Prop)
    (secondRel : SecondComponent → SecondComponent → Prop)
    (firstWellFounded : WellFounded firstRel)
    (secondWellFounded : WellFounded secondRel) :
    WellFounded (LexPair firstRel secondRel) := by
  apply WellFounded.intro
  intro pairValue
  obtain ⟨firstValue, secondValue⟩ := pairValue
  exact LexPair.pairAccessible firstRel secondRel secondWellFounded
    (firstWellFounded.apply firstValue) secondValue

variable {Carrier : Type carrierUniverse} {Elem : Type elemUniverse}

/-- **Termination by a lexicographic-pair measure**: a step relation whose `(first, second)` measure strictly
decreases lexicographically at every step is well-founded (terminating). -/
theorem wellFounded_of_lexPairMeasure
    {stepRel : Carrier → Carrier → Prop}
    {measure : Carrier → FirstComponent × SecondComponent}
    {firstRel : FirstComponent → FirstComponent → Prop}
    {secondRel : SecondComponent → SecondComponent → Prop}
    (firstWellFounded : WellFounded firstRel)
    (secondWellFounded : WellFounded secondRel)
    (measureDecreases : ∀ source target, stepRel source target →
      LexPair firstRel secondRel (measure target) (measure source)) :
    WellFounded (fun target source => stepRel source target) := by
  apply Subrelation.wf (r := InvImage (LexPair firstRel secondRel) measure)
  · intro target source step
    exact measureDecreases source target step
  · exact InvImage.wf measure
      (LexPair.isWellFounded firstRel secondRel firstWellFounded secondWellFounded)

/-- **The RPO termination certificate (multiset-status)**: a step relation terminates if a precedence rank (a
well-founded order on the head symbol) decreases, or stays equal while a Dershowitz-Manna multiset measure
over the arguments decreases.  The precedence-then-multiset-status comparison of the recursive path
ordering, made a measure-based certificate. -/
theorem wellFounded_of_precedenceMultisetMeasure
    {stepRel : Carrier → Carrier → Prop}
    {precedenceRank : Carrier → FirstComponent} {argumentMeasure : Carrier → List Elem}
    {precedenceRel : FirstComponent → FirstComponent → Prop} {baseRel : Elem → Elem → Prop}
    (precedenceWellFounded : WellFounded precedenceRel)
    (baseWellFounded : WellFounded baseRel)
    (measureDecreases : ∀ source target, stepRel source target →
      LexPair precedenceRel (MultisetRedOne baseRel)
        (precedenceRank target, argumentMeasure target)
        (precedenceRank source, argumentMeasure source)) :
    WellFounded (fun target source => stepRel source target) :=
  wellFounded_of_lexPairMeasure precedenceWellFounded
    (MultisetRedOne.isWellFounded baseRel baseWellFounded) measureDecreases

/-- **The RPO termination certificate (lexicographic-status)**: the same, with the lexicographic argument
order in place of the multiset order. -/
theorem wellFounded_of_precedenceLexMeasure
    {stepRel : Carrier → Carrier → Prop}
    {precedenceRank : Carrier → FirstComponent} {argumentMeasure : Carrier → List Elem}
    {precedenceRel : FirstComponent → FirstComponent → Prop} {baseRel : Elem → Elem → Prop}
    (precedenceWellFounded : WellFounded precedenceRel)
    (baseWellFounded : WellFounded baseRel)
    (measureDecreases : ∀ source target, stepRel source target →
      LexPair precedenceRel (LexListStep baseRel)
        (precedenceRank target, argumentMeasure target)
        (precedenceRank source, argumentMeasure source)) :
    WellFounded (fun target source => stepRel source target) :=
  wellFounded_of_lexPairMeasure precedenceWellFounded
    (LexListStep.isWellFounded baseRel baseWellFounded) measureDecreases

end FX1Poly.Core
