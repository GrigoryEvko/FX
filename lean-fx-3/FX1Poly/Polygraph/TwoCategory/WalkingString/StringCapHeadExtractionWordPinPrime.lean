import FX1Poly.Polygraph.TwoCategory.WalkingString.StringPureCapSpineSort
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWordPairSeatedDescentOfDistinct

/-! # WalkingString/StringCapHeadExtractionWordPinPrime — the AllCapArity-augmented cap-head pin + its sort
(FC-3 r25, B3)

The r24 ledger named the pin's conjunct (4) jam: the cancel engine `stringArcCapHeadFolded_extractArc_cancel`
(r21) needs `AllCapArity tailList` / `AllCapArity matchedRemainder`, which the shipped `StringCapHeadExtractionWordPin`
does NOT carry, and the re-founded descent (B2) needs `AllCapArity secondList`.  This file ships the PIN-PRIME —
the shipped pin AUGMENTED with `AllCapArity` on BOTH spines — and re-wires the pure-cap sort to consume it.  The
shipped `StringCapHeadExtractionWordPin` and its conditional sort (`stringPureCapSpineSortFueled` /
`stringPureCapSpine_sort`) stay BYTE-INTACT; this is a NEW additive layer.

  * ★ `StringCapHeadExtractionWordPinPrime` — the pin with `AllCapArity (headAtom :: tailList)` AND
    `AllCapArity secondList` added.  Both are available at the sort's single call site (the fuel driver holds
    `firstPureCap` / `secondPureCap`), so the augmentation costs the sort nothing.

  * `stringPureCapSpineSortFueledOfPrime` / `stringPureCapSpine_sort_ofPrime` — the fuel driver + public wrapper
    re-cloned from the shipped sort (r17–r24 byte-intact), threading the two `AllCapArity` witnesses to the
    pin-prime at each peel.  This proves the whole peel-first recursion still assembles around the AUGMENTED
    discharge — the descent (B2) now has the `AllCapArity secondList` it needs, and conjunct (4)'s cancel has the
    `AllCapArity` it needs.

## The standing residual (honest)

Inhabiting `StringCapHeadExtractionWordPinPrime` (the four-conjunct assembly) is the r26 obligation, now UNBLOCKED
by B2 (the re-founded descent `stringWordPairSeated_bubblesThroughPrefix_ofDistinct` is shipped, zero-axiom): the
assembly runs the located read-off (`StringArcPairCapWindow` / r19-r20) to seat the toucher's two consecutive
untouched legs, feeds the descent to bubble the toucher to the front (`WordBubblesToFront`), and closes the four
conjuncts via the shipped consumers (`spineTraceEquiv_of_wordBubblesToFront`,
`spineBoundaryWordChained_of_wordBubblesToFront`, `spineBoundaryChained_ofWordChained`) plus the three glue seams
(the window-equal glue, the codEq bridge, the identify rewrite `stringCapAtom_eq_of_sharedDom_sameWindow`) and the
r21 cancel fed the pin-prime's `AllCapArity`.  This file does NOT fabricate that inhabitant; it ships the Prop and
the conditional wiring, and flips NO completeness or unconditional-sort marker.

Raw Lean 4 + Init; the fuel driver re-clone is structural on fuel.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The AllCapArity-augmented cap-head pin -/

/-- ★ **The cap-head extraction pin, augmented with `AllCapArity` on BOTH spines.**  Identical to the shipped
`StringCapHeadExtractionWordPin`, plus `AllCapArity (headAtom :: tailList)` and `AllCapArity secondList` as
hypotheses — the augmentation the r24 ledger named for conjunct (4)'s cancel (`AllCapArity tailList` /
`matchedRemainder`) and the B2 descent (`AllCapArity secondList`, kills the cup arm).  Both witnesses are in scope
at the sort's single peel site, so the pin-prime is strictly easier to inhabit than the shipped pin while the sort
consuming it is byte-for-byte the shipped peel recursion plus two threaded arguments. -/
def StringCapHeadExtractionWordPinPrime : Prop :=
  ∀ {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomWord : ModalityPath adjointTripleGraph overallSource overallTarget)
    (headAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget),
    headAtom.generatorDom.length = 2 → headAtom.generatorCod.length = 0 →
    ∀ (tailList secondList :
        List (SpineAtom adjointTripleModeSignature overallSource overallTarget)),
    SpineBoundaryChained bottomCount (headAtom :: tailList) →
    SpineBoundaryChained bottomCount secondList →
    SpineBoundaryWordChained bottomWord (headAtom :: tailList) →
    SpineBoundaryWordChained bottomWord secondList →
    AllCapArity (headAtom :: tailList) →
    AllCapArity secondList →
    arcStructureOfSpineList bottomCount (headAtom :: tailList)
      = arcStructureOfSpineList bottomCount secondList →
    ∃ matchedRemainder,
      SpineTraceEquiv adjointTripleModeSignature secondList (headAtom :: matchedRemainder)
        ∧ SpineBoundaryChained headAtom.codBoundaryLength matchedRemainder
        ∧ SpineBoundaryWordChained
            (composePath headAtom.leftContext
              (composePath headAtom.generatorCod headAtom.rightContext))
            matchedRemainder
        ∧ arcStructureOfSpineList headAtom.codBoundaryLength tailList
            = arcStructureOfSpineList headAtom.codBoundaryLength matchedRemainder

/-! ## The sort re-wired to consume the pin-prime -/

/-- Fuel-driven core of the pure-cap sort re-wired to consume the pin-prime: the peel recursion of the shipped
`stringPureCapSpineSortFueled`, threading the two `AllCapArity` witnesses (`firstPureCap` for the head spine,
`secondPureCap`) to the augmented discharge at each peel. -/
private theorem stringPureCapSpineSortFueledOfPrime
    (headExtract : StringCapHeadExtractionWordPinPrime)
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (fuel : Nat) →
    (bottomCount : Nat) →
    (bottomWord : ModalityPath adjointTripleGraph overallSource overallTarget) →
    (firstList secondList :
      List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    firstList.length ≤ fuel →
    SpineBoundaryChained bottomCount firstList →
    SpineBoundaryChained bottomCount secondList →
    SpineBoundaryWordChained bottomWord firstList →
    SpineBoundaryWordChained bottomWord secondList →
    AllCapArity firstList →
    AllCapArity secondList →
    arcStructureOfSpineList bottomCount firstList
      = arcStructureOfSpineList bottomCount secondList →
    SpineTraceEquiv adjointTripleModeSignature firstList secondList
  | 0, bottomCount, _, firstList, secondList, lengthBound, _, _, _, _, _, secondPureCap, arcEqual => by
      match firstList, lengthBound, arcEqual with
      | [], _, arcEqual =>
          exact stringPureCapSpine_sort_nil bottomCount secondList secondPureCap arcEqual
      | _ :: _, lengthBound, _ => exact absurd lengthBound (Nat.not_succ_le_zero _)
  | fuel + 1, bottomCount, bottomWord, firstList, secondList, lengthBound, chainedFirst, chainedSecond,
      firstWordChained, secondWordChained, firstPureCap, secondPureCap, arcEqual => by
      match firstList, lengthBound, chainedFirst, firstWordChained, firstPureCap, arcEqual with
      | [], _, _, _, _, arcEqual =>
          exact stringPureCapSpine_sort_nil bottomCount secondList secondPureCap arcEqual
      | C1 :: t1, lengthBound, chainedFirst, firstWordChained, firstPureCap, arcEqual =>
          obtain ⟨c1Dom, c1Cod⟩ := stringHeadCapArity firstPureCap
          have t1Pure : AllCapArity t1 := stringAllCapArity_ofCons firstPureCap
          have tailChainedFirst : SpineBoundaryChained C1.codBoundaryLength t1 :=
            (spineBoundaryChained_tail chainedFirst).2
          have tailWordChainedFirst : SpineBoundaryWordChained
              (composePath C1.leftContext (composePath C1.generatorCod C1.rightContext)) t1 :=
            (spineBoundaryWordChained_tail firstWordChained).2
          have t1LenBound : t1.length ≤ fuel := Nat.le_of_succ_le_succ lengthBound
          obtain ⟨matchedRemainder, extractEquiv, remainderChained, remainderWordChained,
            tailArcEqual⟩ :=
            headExtract bottomCount bottomWord C1 c1Dom c1Cod t1 secondList chainedFirst chainedSecond
              firstWordChained secondWordChained firstPureCap secondPureCap arcEqual
          have matchedPure : AllCapArity matchedRemainder :=
            stringAllCapArity_ofArcEqualToPureCap C1.codBoundaryLength t1 matchedRemainder t1Pure
              tailArcEqual
          have tailTrace : SpineTraceEquiv adjointTripleModeSignature t1 matchedRemainder :=
            stringPureCapSpineSortFueledOfPrime headExtract fuel C1.codBoundaryLength
              (composePath C1.leftContext (composePath C1.generatorCod C1.rightContext))
              t1 matchedRemainder t1LenBound tailChainedFirst remainderChained tailWordChainedFirst
              remainderWordChained t1Pure matchedPure tailArcEqual
          exact (SpineTraceEquiv.consCongr C1 tailTrace).trans extractEquiv.symm

/-- ★ **The pure-cap sort re-wired to consume the pin-prime.**  Given the AUGMENTED discharge
`StringCapHeadExtractionWordPinPrime`, two boundary-chained AND boundary-word-chained pure-cap string spines over a
bottom boundary with EQUAL arc structure are trace-equivalent.  The peel-first recursion of the shipped
`stringPureCapSpine_sort`, threading the `AllCapArity` witnesses to the augmented pin.  This proves the sort still
assembles around the augmented discharge — so the r26 inhabitant only has to build the four conjuncts with the
`AllCapArity` it now legitimately carries.  Seeds the fuel at `firstList.length`. -/
theorem stringPureCapSpine_sort_ofPrime (headExtract : StringCapHeadExtractionWordPinPrime)
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (bottomWord : ModalityPath adjointTripleGraph overallSource overallTarget)
    (firstList secondList :
      List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chainedFirst : SpineBoundaryChained bottomCount firstList)
    (chainedSecond : SpineBoundaryChained bottomCount secondList)
    (firstWordChained : SpineBoundaryWordChained bottomWord firstList)
    (secondWordChained : SpineBoundaryWordChained bottomWord secondList)
    (firstPureCap : AllCapArity firstList)
    (secondPureCap : AllCapArity secondList)
    (arcEqual : arcStructureOfSpineList bottomCount firstList
      = arcStructureOfSpineList bottomCount secondList) :
    SpineTraceEquiv adjointTripleModeSignature firstList secondList :=
  stringPureCapSpineSortFueledOfPrime headExtract firstList.length bottomCount bottomWord firstList
    secondList (Nat.le_refl firstList.length) chainedFirst chainedSecond firstWordChained
    secondWordChained firstPureCap secondPureCap arcEqual

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the AllCapArity-augmented cap-head PIN-PRIME and its conditional sort are machine-checked
(FC-3 r25, B3).**  `StringCapHeadExtractionWordPinPrime` augments the shipped pin with `AllCapArity` on BOTH
spines — the augmentation the r24 ledger named for conjunct (4)'s r21 cancel and the B2 descent's cup-arm kill —
and `stringPureCapSpine_sort_ofPrime` re-wires the peel-first pure-cap sort to consume it (the shipped pin +
conditional sort stay byte-intact).  Both `AllCapArity` witnesses are in scope at the sort's peel site, so the
augmentation costs the sort nothing.

  THE STANDING RESIDUAL (honest, NOT fabricated).  Inhabiting `StringCapHeadExtractionWordPinPrime` — the
  four-conjunct assembly — is the r26 obligation, now UNBLOCKED by B2 (`stringWordPairSeated_bubblesThroughPrefix_ofDistinct`,
  the re-founded descent, is shipped zero-axiom): seat the toucher's two consecutive untouched legs via the
  located read-off (`StringArcPairCapWindow`), bubble the toucher to the front with the descent, and close the four
  conjuncts through the shipped `WordBubblesToFront` consumers + the three glue seams (window-equal glue, codEq
  bridge, identify rewrite) + the r21 cancel fed this pin-prime's `AllCapArity`.  This round flips NO completeness
  or unconditional-sort marker (`fxString_hasUnconditionalPureCapSort` stays `false`, the pin-prime uninhabited);
  no inhabitant nor flip was fabricated.  `= true`. -/
def fxString_hasCapHeadExtractionWordPinPrime : Bool := true

end FX1Poly.Polygraph
