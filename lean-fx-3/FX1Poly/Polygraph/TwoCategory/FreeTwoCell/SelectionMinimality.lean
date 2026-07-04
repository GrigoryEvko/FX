import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TraceNormalForm

/-! # SelectionMinimality — the measure order kit + the selection's certificates (FREE-6b)

`normalizeSpine` recurses on whatever `selectMinimalExtraction` returns; its SOUNDNESS
needed nothing about the fold (the self-certifying discipline).  The INVARIANCE theorem
does: it must know the selected candidate is (a) ONE OF the candidates and (b)
measure-LEAST among them, and it must turn measure TIES into the three component
equalities `SpineAtom.eqOfStageCompositeAndMeasureEq` consumes.  This file ships that
kit:

  * zero-axiom `Nat.blt` / `==` bridges (`natLtOfBltIsTrue`, `natBltIsTrueOfLt`,
    `natBltSelfIsFalse`, `natBeqSelfIsTrue`, `natBeqIsTrueOfEq`) and the `Nat`
    trichotomy `natLtOrEqOrGt`;
  * `MeasureLexBelow` — the Prop-level strict triple-lex measure order on atoms, with
    the Bool bridge in both directions, transitivity, irreflexivity, and trichotomy
    (the middle branch delivers exactly the determinacy layer's inputs);
  * Bool-level corollaries: `isMeasureLexSmaller_trans` / `_irrefl`, the two
    fold-invariant transfer shapes (`smallerIsFalse_ofBeatenBelow`,
    `smallerIsFalse_chain`), and `measureComponentsEq_ofNeitherSmaller`;
  * ★ the selection certificates: `selectMinimalExtraction_isMemberOfCandidates` (the
    selected extraction IS a candidate — so it carries a genuine trace-equivalence
    certificate AND its front is one of the enumerated fronts) and
    `selectMinimalExtraction_isUnbeatenByMember` (no candidate is measure-smaller than
    the selected one — the least-front agreement lever of the invariance argument).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The Nat comparison bridges -/

/-- `Nat.blt` truth transports to the strict order (definitional `blt`-to-`ble`
unfolding). -/
theorem natLtOfBltIsTrue {first second : Nat}
    (isBelow : Nat.blt first second = true) : first < second :=
  Nat.le_of_ble_eq_true isBelow

/-- The strict order transports to `Nat.blt` truth. -/
theorem natBltIsTrueOfLt {first second : Nat}
    (isBelow : first < second) : Nat.blt first second = true :=
  Nat.ble_eq_true_of_le isBelow

/-- `Nat.blt` is irreflexive, computed structurally. -/
theorem natBltSelfIsFalse : (number : Nat) → Nat.blt number number = false
  | 0 => rfl
  | predecessor + 1 => natBltSelfIsFalse predecessor

/-- `Nat`'s `==` is decide-based; reflexivity is `decide_eq_true` of `rfl`. -/
theorem natBeqSelfIsTrue (number : Nat) : (number == number) = true :=
  decide_eq_true rfl

/-- Propositional equality transports to `Nat.beq` truth. -/
theorem natBeqIsTrueOfEq {first second : Nat}
    (areEqual : first = second) : (first == second) = true := by
  rw [areEqual]
  exact natBeqSelfIsTrue second

/-- Zero-axiom trichotomy on `Nat`, assembled from `Nat.lt_or_ge` and
`Nat.eq_or_lt_of_le`. -/
theorem natLtOrEqOrGt (first second : Nat) :
    first < second ∨ first = second ∨ second < first :=
  match Nat.lt_or_ge first second with
  | .inl isBelow => .inl isBelow
  | .inr isAtLeast =>
      match Nat.eq_or_lt_of_le isAtLeast with
      | .inl equalReversed => .inr (.inl equalReversed.symm)
      | .inr strictlyAbove => .inr (.inr strictlyAbove)

/-! ## The Bool assembly helpers -/

/-- A disjunction with a true left arm is true. -/
theorem boolOrLeftIsTrue {leftSide rightSide : Bool}
    (leftIsTrue : leftSide = true) : (leftSide || rightSide) = true := by
  cases leftSide with
  | true => rfl
  | false => exact Bool.noConfusion leftIsTrue

/-- A disjunction with a true right arm is true. -/
theorem boolOrRightIsTrue {leftSide rightSide : Bool}
    (rightIsTrue : rightSide = true) : (leftSide || rightSide) = true := by
  cases leftSide with
  | true => rfl
  | false => exact rightIsTrue

/-- A conjunction of two true arms is true. -/
theorem boolAndIsTrueOfBoth {leftSide rightSide : Bool}
    (leftIsTrue : leftSide = true) (rightIsTrue : rightSide = true) :
    (leftSide && rightSide) = true := by
  cases leftSide with
  | true => exact rightIsTrue
  | false => exact Bool.noConfusion leftIsTrue

/-! ## The Prop-level measure order -/

/-- The strict triple-lex measure order on atoms at the Prop level: left-context length,
then right-context length, then generator key — the Prop mirror of
`isMeasureLexSmaller`. -/
def MeasureLexBelow {signature : ModeSignature} (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    (firstAtom secondAtom : SpineAtom signature overallSource overallTarget) : Prop :=
  firstAtom.leftContext.length < secondAtom.leftContext.length
    ∨ (firstAtom.leftContext.length = secondAtom.leftContext.length
        ∧ (firstAtom.rightContext.length < secondAtom.rightContext.length
            ∨ (firstAtom.rightContext.length = secondAtom.rightContext.length
                ∧ keying.keyOf firstAtom.generator
                    < keying.keyOf secondAtom.generator)))

/-- The Bool comparison reflects into the Prop order. -/
theorem measureLexBelow_ofSmallerIsTrue {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    {firstAtom secondAtom : SpineAtom signature overallSource overallTarget}
    (isSmaller : isMeasureLexSmaller keying firstAtom secondAtom = true) :
    MeasureLexBelow keying firstAtom secondAtom := by
  dsimp only [isMeasureLexSmaller] at isSmaller
  cases hLeftBlt : Nat.blt firstAtom.leftContext.length
      secondAtom.leftContext.length with
  | true => exact Or.inl (natLtOfBltIsTrue hLeftBlt)
  | false =>
      rw [hLeftBlt] at isSmaller
      have leftTie : (firstAtom.leftContext.length == secondAtom.leftContext.length
          && (Nat.blt firstAtom.rightContext.length secondAtom.rightContext.length
              || (firstAtom.rightContext.length == secondAtom.rightContext.length
                  && Nat.blt (keying.keyOf firstAtom.generator)
                      (keying.keyOf secondAtom.generator)))) = true := isSmaller
      cases hLeftBeq : firstAtom.leftContext.length
          == secondAtom.leftContext.length with
      | false =>
          rw [hLeftBeq] at leftTie
          have collapsed : false = true := leftTie
          exact Bool.noConfusion collapsed
      | true =>
          rw [hLeftBeq] at leftTie
          have rightRest : (Nat.blt firstAtom.rightContext.length
              secondAtom.rightContext.length
              || (firstAtom.rightContext.length == secondAtom.rightContext.length
                  && Nat.blt (keying.keyOf firstAtom.generator)
                      (keying.keyOf secondAtom.generator))) = true := leftTie
          cases hRightBlt : Nat.blt firstAtom.rightContext.length
              secondAtom.rightContext.length with
          | true =>
              exact Or.inr ⟨of_decide_eq_true hLeftBeq,
                Or.inl (natLtOfBltIsTrue hRightBlt)⟩
          | false =>
              rw [hRightBlt] at rightRest
              have rightTie : (firstAtom.rightContext.length
                  == secondAtom.rightContext.length
                  && Nat.blt (keying.keyOf firstAtom.generator)
                      (keying.keyOf secondAtom.generator)) = true := rightRest
              cases hRightBeq : firstAtom.rightContext.length
                  == secondAtom.rightContext.length with
              | false =>
                  rw [hRightBeq] at rightTie
                  have collapsed : false = true := rightTie
                  exact Bool.noConfusion collapsed
              | true =>
                  rw [hRightBeq] at rightTie
                  have keyBelow : Nat.blt (keying.keyOf firstAtom.generator)
                      (keying.keyOf secondAtom.generator) = true := rightTie
                  exact Or.inr ⟨of_decide_eq_true hLeftBeq,
                    Or.inr ⟨of_decide_eq_true hRightBeq,
                      natLtOfBltIsTrue keyBelow⟩⟩

/-- The Prop order computes back to the Bool comparison. -/
theorem smallerIsTrue_ofMeasureLexBelow {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    {firstAtom secondAtom : SpineAtom signature overallSource overallTarget}
    (isBelow : MeasureLexBelow keying firstAtom secondAtom) :
    isMeasureLexSmaller keying firstAtom secondAtom = true := by
  dsimp only [MeasureLexBelow] at isBelow
  dsimp only [isMeasureLexSmaller]
  rcases isBelow with leftBelow | ⟨leftTie, rightBelow | ⟨rightTie, keyBelow⟩⟩
  · exact boolOrLeftIsTrue (natBltIsTrueOfLt leftBelow)
  · exact boolOrRightIsTrue (boolAndIsTrueOfBoth (natBeqIsTrueOfEq leftTie)
      (boolOrLeftIsTrue (natBltIsTrueOfLt rightBelow)))
  · exact boolOrRightIsTrue (boolAndIsTrueOfBoth (natBeqIsTrueOfEq leftTie)
      (boolOrRightIsTrue (boolAndIsTrueOfBoth (natBeqIsTrueOfEq rightTie)
        (natBltIsTrueOfLt keyBelow))))

/-- The Prop order is irreflexive. -/
theorem measureLexBelow_irrefl {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    {atom : SpineAtom signature overallSource overallTarget}
    (selfBelow : MeasureLexBelow keying atom atom) : False := by
  dsimp only [MeasureLexBelow] at selfBelow
  rcases selfBelow with leftBelow | ⟨_, rightBelow | ⟨_, keyBelow⟩⟩
  · exact Nat.lt_irrefl atom.leftContext.length leftBelow
  · exact Nat.lt_irrefl atom.rightContext.length rightBelow
  · exact Nat.lt_irrefl (keying.keyOf atom.generator) keyBelow

/-- The Prop order is transitive (lexicographic case analysis, ties chained through
`Nat.le_of_eq`). -/
theorem measureLexBelow_trans {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    {firstAtom secondAtom thirdAtom : SpineAtom signature overallSource overallTarget}
    (firstBelow : MeasureLexBelow keying firstAtom secondAtom)
    (secondBelow : MeasureLexBelow keying secondAtom thirdAtom) :
    MeasureLexBelow keying firstAtom thirdAtom := by
  dsimp only [MeasureLexBelow] at firstBelow secondBelow ⊢
  rcases firstBelow with leftBelowOne | ⟨leftTieOne, restOne⟩
  · rcases secondBelow with leftBelowTwo | ⟨leftTieTwo, _⟩
    · exact Or.inl (Nat.lt_trans leftBelowOne leftBelowTwo)
    · exact Or.inl (Nat.lt_of_lt_of_le leftBelowOne (Nat.le_of_eq leftTieTwo))
  · rcases secondBelow with leftBelowTwo | ⟨leftTieTwo, restTwo⟩
    · exact Or.inl (Nat.lt_of_le_of_lt (Nat.le_of_eq leftTieOne) leftBelowTwo)
    · refine Or.inr ⟨leftTieOne.trans leftTieTwo, ?innerRest⟩
      rcases restOne with rightBelowOne | ⟨rightTieOne, keyBelowOne⟩
      · rcases restTwo with rightBelowTwo | ⟨rightTieTwo, _⟩
        · exact Or.inl (Nat.lt_trans rightBelowOne rightBelowTwo)
        · exact Or.inl (Nat.lt_of_lt_of_le rightBelowOne (Nat.le_of_eq rightTieTwo))
      · rcases restTwo with rightBelowTwo | ⟨rightTieTwo, keyBelowTwo⟩
        · exact Or.inl (Nat.lt_of_le_of_lt (Nat.le_of_eq rightTieOne) rightBelowTwo)
        · exact Or.inr ⟨rightTieOne.trans rightTieTwo,
            Nat.lt_trans keyBelowOne keyBelowTwo⟩

/-- ★ Trichotomy: strictly below, or ALL THREE measure components equal (exactly the
inputs `SpineAtom.eqOfStageCompositeAndMeasureEq` consumes), or strictly above. -/
theorem measureLexBelow_trichotomy {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    (firstAtom secondAtom : SpineAtom signature overallSource overallTarget) :
    MeasureLexBelow keying firstAtom secondAtom
      ∨ (firstAtom.leftContext.length = secondAtom.leftContext.length
          ∧ firstAtom.rightContext.length = secondAtom.rightContext.length
          ∧ keying.keyOf firstAtom.generator = keying.keyOf secondAtom.generator)
      ∨ MeasureLexBelow keying secondAtom firstAtom := by
  dsimp only [MeasureLexBelow]
  rcases natLtOrEqOrGt firstAtom.leftContext.length secondAtom.leftContext.length with
    leftBelow | leftTie | leftAbove
  · exact Or.inl (Or.inl leftBelow)
  · rcases natLtOrEqOrGt firstAtom.rightContext.length
        secondAtom.rightContext.length with rightBelow | rightTie | rightAbove
    · exact Or.inl (Or.inr ⟨leftTie, Or.inl rightBelow⟩)
    · rcases natLtOrEqOrGt (keying.keyOf firstAtom.generator)
          (keying.keyOf secondAtom.generator) with keyBelow | keyTie | keyAbove
      · exact Or.inl (Or.inr ⟨leftTie, Or.inr ⟨rightTie, keyBelow⟩⟩)
      · exact Or.inr (Or.inl ⟨leftTie, rightTie, keyTie⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨leftTie.symm, Or.inr ⟨rightTie.symm, keyAbove⟩⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨leftTie.symm, Or.inl rightAbove⟩))
  · exact Or.inr (Or.inr (Or.inl leftAbove))

/-! ## Bool-level corollaries -/

/-- The Bool comparison is irreflexive. -/
theorem isMeasureLexSmaller_irrefl {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    (atom : SpineAtom signature overallSource overallTarget) :
    isMeasureLexSmaller keying atom atom = false := by
  cases selfCase : isMeasureLexSmaller keying atom atom with
  | false => rfl
  | true => exact (measureLexBelow_irrefl keying
      (measureLexBelow_ofSmallerIsTrue keying selfCase)).elim

/-- The Bool comparison is transitive. -/
theorem isMeasureLexSmaller_trans {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    {firstAtom secondAtom thirdAtom : SpineAtom signature overallSource overallTarget}
    (firstSmaller : isMeasureLexSmaller keying firstAtom secondAtom = true)
    (secondSmaller : isMeasureLexSmaller keying secondAtom thirdAtom = true) :
    isMeasureLexSmaller keying firstAtom thirdAtom = true :=
  smallerIsTrue_ofMeasureLexBelow keying
    (measureLexBelow_trans keying
      (measureLexBelow_ofSmallerIsTrue keying firstSmaller)
      (measureLexBelow_ofSmallerIsTrue keying secondSmaller))

/-- Fold-invariant shape 1: if `lowerAtom` beats `midAtom` but does not beat
`targetAtom`, then `midAtom` does not beat `targetAtom` either (else transitivity would
carry `lowerAtom` past it). -/
theorem smallerIsFalse_ofBeatenBelow {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    {lowerAtom midAtom targetAtom : SpineAtom signature overallSource overallTarget}
    (lowerBeatsMid : isMeasureLexSmaller keying lowerAtom midAtom = true)
    (lowerMissesTarget : isMeasureLexSmaller keying lowerAtom targetAtom = false) :
    isMeasureLexSmaller keying midAtom targetAtom = false := by
  cases targetCase : isMeasureLexSmaller keying midAtom targetAtom with
  | false => rfl
  | true =>
      have lowerBeatsTarget : isMeasureLexSmaller keying lowerAtom targetAtom = true :=
        isMeasureLexSmaller_trans keying lowerBeatsMid targetCase
      rw [lowerBeatsTarget] at lowerMissesTarget
      exact lowerMissesTarget

/-- Fold-invariant shape 2: not-beating is transitive.  Trichotomy on the first pair —
a strict reverse chains through transitivity; a full measure tie transports the beat
across equal components. -/
theorem smallerIsFalse_chain {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    {firstAtom midAtom targetAtom : SpineAtom signature overallSource overallTarget}
    (firstMissesMid : isMeasureLexSmaller keying firstAtom midAtom = false)
    (midMissesTarget : isMeasureLexSmaller keying midAtom targetAtom = false) :
    isMeasureLexSmaller keying firstAtom targetAtom = false := by
  cases targetCase : isMeasureLexSmaller keying firstAtom targetAtom with
  | false => rfl
  | true =>
      have firstBelowTarget : MeasureLexBelow keying firstAtom targetAtom :=
        measureLexBelow_ofSmallerIsTrue keying targetCase
      rcases measureLexBelow_trichotomy keying firstAtom midAtom with
        firstBelowMid | ⟨leftTie, rightTie, keyTie⟩ | midBelowFirst
      · rw [smallerIsTrue_ofMeasureLexBelow keying firstBelowMid] at firstMissesMid
        exact firstMissesMid
      · dsimp only [MeasureLexBelow] at firstBelowTarget
        rw [leftTie, rightTie, keyTie] at firstBelowTarget
        have midBelowTarget : MeasureLexBelow keying midAtom targetAtom :=
          firstBelowTarget
        rw [smallerIsTrue_ofMeasureLexBelow keying midBelowTarget] at midMissesTarget
        exact midMissesTarget
      · have midBelowTarget : MeasureLexBelow keying midAtom targetAtom :=
          measureLexBelow_trans keying midBelowFirst firstBelowTarget
        rw [smallerIsTrue_ofMeasureLexBelow keying midBelowTarget] at midMissesTarget
        exact midMissesTarget

/-- ★ Measure ties are component equalities: if neither atom beats the other, all three
measure components coincide — the determinacy layer's inputs. -/
theorem measureComponentsEq_ofNeitherSmaller {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    {firstAtom secondAtom : SpineAtom signature overallSource overallTarget}
    (firstMissesSecond : isMeasureLexSmaller keying firstAtom secondAtom = false)
    (secondMissesFirst : isMeasureLexSmaller keying secondAtom firstAtom = false) :
    firstAtom.leftContext.length = secondAtom.leftContext.length
      ∧ firstAtom.rightContext.length = secondAtom.rightContext.length
      ∧ keying.keyOf firstAtom.generator = keying.keyOf secondAtom.generator := by
  rcases measureLexBelow_trichotomy keying firstAtom secondAtom with
    firstBelow | components | secondBelow
  · rw [smallerIsTrue_ofMeasureLexBelow keying firstBelow] at firstMissesSecond
    exact Bool.noConfusion firstMissesSecond
  · exact components
  · rw [smallerIsTrue_ofMeasureLexBelow keying secondBelow] at secondMissesFirst
    exact Bool.noConfusion secondMissesFirst

/-! ## The selection's cons steps -/

/-- One cons step of the selection when the incoming candidate beats the running best:
the selection advances with the candidate as the new best. -/
theorem selectMinimalExtraction_consWinner {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    {originalList : List (SpineAtom signature overallSource overallTarget)}
    (headCandidate candidate : FrontExtraction originalList)
    (remaining : List (FrontExtraction originalList))
    (challengerWins : isMeasureLexSmaller keying candidate.frontAtom
      headCandidate.frontAtom = true) :
    selectMinimalExtraction keying headCandidate (candidate :: remaining)
      = selectMinimalExtraction keying candidate remaining := by
  show selectMinimalExtraction keying
      (if isMeasureLexSmaller keying candidate.frontAtom headCandidate.frontAtom
        then candidate else headCandidate) remaining
    = selectMinimalExtraction keying candidate remaining
  rw [challengerWins]
  rfl

/-- One cons step of the selection when the incoming candidate does not beat the running
best: the selection advances keeping the best (first-wins on ties). -/
theorem selectMinimalExtraction_consKeeper {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    {originalList : List (SpineAtom signature overallSource overallTarget)}
    (headCandidate candidate : FrontExtraction originalList)
    (remaining : List (FrontExtraction originalList))
    (challengerLoses : isMeasureLexSmaller keying candidate.frontAtom
      headCandidate.frontAtom = false) :
    selectMinimalExtraction keying headCandidate (candidate :: remaining)
      = selectMinimalExtraction keying headCandidate remaining := by
  show selectMinimalExtraction keying
      (if isMeasureLexSmaller keying candidate.frontAtom headCandidate.frontAtom
        then candidate else headCandidate) remaining
    = selectMinimalExtraction keying headCandidate remaining
  rw [challengerLoses]
  rfl

/-! ## The selection's certificates -/

/-- The selected extraction is the head or one of the other candidates (fold membership,
generalized over the running best). -/
theorem selectMinimalExtraction_isHeadOrMember {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    {originalList : List (SpineAtom signature overallSource overallTarget)} :
    ∀ (otherCandidates : List (FrontExtraction originalList))
      (headCandidate : FrontExtraction originalList),
      selectMinimalExtraction keying headCandidate otherCandidates = headCandidate
        ∨ selectMinimalExtraction keying headCandidate otherCandidates
            ∈ otherCandidates := by
  intro otherCandidates
  induction otherCandidates with
  | nil =>
      intro headCandidate
      exact Or.inl rfl
  | cons candidate remaining innerHypothesis =>
      intro headCandidate
      cases challengerCase : isMeasureLexSmaller keying candidate.frontAtom
          headCandidate.frontAtom with
      | true =>
          rw [selectMinimalExtraction_consWinner keying headCandidate candidate
            remaining challengerCase]
          rcases innerHypothesis candidate with resultIsCandidate | resultInRemaining
          · rw [resultIsCandidate]
            exact Or.inr (List.Mem.head remaining)
          · exact Or.inr (List.Mem.tail candidate resultInRemaining)
      | false =>
          rw [selectMinimalExtraction_consKeeper keying headCandidate candidate
            remaining challengerCase]
          rcases innerHypothesis headCandidate with resultIsHead | resultInRemaining
          · exact Or.inl resultIsHead
          · exact Or.inr (List.Mem.tail candidate resultInRemaining)

/-- ★ The selection is measure-least, generalized over the running best: neither the
best nor any listed candidate beats the fold's result. -/
theorem selectMinimalExtraction_isUnbeaten {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    {originalList : List (SpineAtom signature overallSource overallTarget)} :
    ∀ (otherCandidates : List (FrontExtraction originalList))
      (headCandidate : FrontExtraction originalList),
      isMeasureLexSmaller keying headCandidate.frontAtom
          (selectMinimalExtraction keying headCandidate otherCandidates).frontAtom
        = false
      ∧ ∀ (challenger : FrontExtraction originalList),
          challenger ∈ otherCandidates →
          isMeasureLexSmaller keying challenger.frontAtom
              (selectMinimalExtraction keying headCandidate otherCandidates).frontAtom
            = false := by
  intro otherCandidates
  induction otherCandidates with
  | nil =>
      intro headCandidate
      refine ⟨isMeasureLexSmaller_irrefl keying headCandidate.frontAtom, ?emptyCase⟩
      intro challenger membershipWitness
      cases membershipWitness
  | cons candidate remaining innerHypothesis =>
      intro headCandidate
      cases challengerCase : isMeasureLexSmaller keying candidate.frontAtom
          headCandidate.frontAtom with
      | true =>
          rw [selectMinimalExtraction_consWinner keying headCandidate candidate
            remaining challengerCase]
          refine ⟨smallerIsFalse_ofBeatenBelow keying challengerCase
            (innerHypothesis candidate).left, ?winnerChallengers⟩
          intro challenger membershipWitness
          cases membershipWitness with
          | head => exact (innerHypothesis candidate).left
          | tail _ innerMembership =>
              exact (innerHypothesis candidate).right challenger innerMembership
      | false =>
          rw [selectMinimalExtraction_consKeeper keying headCandidate candidate
            remaining challengerCase]
          refine ⟨(innerHypothesis headCandidate).left, ?keeperChallengers⟩
          intro challenger membershipWitness
          cases membershipWitness with
          | head =>
              exact smallerIsFalse_chain keying challengerCase
                (innerHypothesis headCandidate).left
          | tail _ innerMembership =>
              exact (innerHypothesis headCandidate).right challenger innerMembership

/-- ★ **The selected extraction is one of the candidates** — so it carries a genuine
trace-equivalence certificate and its front is one of the enumerated fronts. -/
theorem selectMinimalExtraction_isMemberOfCandidates {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    {originalList : List (SpineAtom signature overallSource overallTarget)}
    (headCandidate : FrontExtraction originalList)
    (otherCandidates : List (FrontExtraction originalList)) :
    selectMinimalExtraction keying headCandidate otherCandidates
      ∈ headCandidate :: otherCandidates := by
  rcases selectMinimalExtraction_isHeadOrMember keying otherCandidates headCandidate with
    resultIsHead | resultInOthers
  · rw [resultIsHead]
    exact List.Mem.head otherCandidates
  · exact List.Mem.tail headCandidate resultInOthers

/-- ★ **No candidate beats the selected extraction** — the selection is measure-least
over the whole candidate list (the least-front agreement lever of the invariance
argument). -/
theorem selectMinimalExtraction_isUnbeatenByMember {signature : ModeSignature}
    (keying : GeneratorKeying signature)
    {overallSource overallTarget : signature.graph.Mode}
    {originalList : List (SpineAtom signature overallSource overallTarget)}
    (headCandidate : FrontExtraction originalList)
    (otherCandidates : List (FrontExtraction originalList))
    (challenger : FrontExtraction originalList)
    (membershipWitness : challenger ∈ headCandidate :: otherCandidates) :
    isMeasureLexSmaller keying challenger.frontAtom
        (selectMinimalExtraction keying headCandidate otherCandidates).frontAtom
      = false := by
  cases membershipWitness with
  | head => exact (selectMinimalExtraction_isUnbeaten keying otherCandidates
      headCandidate).left
  | tail _ innerMembership =>
      exact (selectMinimalExtraction_isUnbeaten keying otherCandidates
        headCandidate).right challenger innerMembership

end FX1Poly.Polygraph
