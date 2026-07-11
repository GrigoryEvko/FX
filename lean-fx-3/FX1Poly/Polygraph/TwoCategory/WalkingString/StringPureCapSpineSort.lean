import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyDegenerateSplit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineAtomWordPin
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCapSpine

/-! # WalkingString/StringPureCapSpineSort — THE CAP-DUAL: the pure-cap sort machinery ported to the
adjoint-triple seed, assembled MODULO the word-ported cap-head discharge (FC-3 r18)

The r17 assembly (`StringWidthZeroPureCupSort`) inhabited `StringWidthZeroPureCupDeterminacyShared` — the CUP arm
of the mid-zero valley discharge — by porting the walking-adjunction's MATCHING-carrier width-0 cup sort onto the
shipped WORD machinery.  This file lands the CAP arm's scaffolding.  The central recon finding: the cap dual is
NOT a token-swap of the r17 matching template.  Caps are ARC-natural, not matching-natural — there is no
cap-matching engine anywhere in the repo (`stepCapMatching` / a cap `backwardPartner` / a cap chord-shift / a cap
drop-injective on the matching carrier all DO NOT EXIST).  The walking adjunction discharges its CAP arm on the
ARC carrier (`ArcCapSortComplete.pureCapSpine_sort`, peeling the FIRST cap and riding the arc-anchored cap-head
discharge `spineArcHeadExtractionChained_ofCapArity`).  So the string cap arm PORTS the arc cap sort, re-plumbed
onto the four-generator seed — a genuine top↔bottom role flip (peel-first, shared-DOM, `bottomCount`-shrinks),
dual to the cup's peel-last / shared-COD / `bottomCount`-pinned-at-0.

This round lands the self-contained CHEAP pieces of that port, and assembles the fuel-driver skeleton MODULO the
one genuinely-colour-keyed discharge, named honestly:

  * ★ the string cap ARITY kit — `stringCupAtomCount_ofAllCapArity`, `stringCapAtomCount_ofAllCapArity`,
    `stringAllCapArity_ofCupAtomCountZero`, `stringAllCapArity_ofCons`, `stringHeadCapArity` — token-swapped clones
    of `ArcPureCapSpine`'s kit, riding the shipped four-generator classification `adjointTripleSpineAtom_isCupOrCap`
    (`StringArcArity`).  Colour-blind (reads only the `(2, 0)` cap arity), routed through the CUP COUNT exactly as
    `ArcPureCapSpine` (a direct `cases` on the head-indexed `AllCapArity` would leak `propext`).

  * ★ the arc COUNT/TRANSFER/BASE clones — `stringCapCountReflect`, `stringCupCountReflect` (the totals reflect the
    boundary-independent atom counts), `stringAllCapArity_ofArcEqualToPureCap` (the pure-cap regime transfers across
    arc equality, via the cup-count reflection), `stringPureCapSpines_sameLength_ofArcEqual`, and the empty base
    `stringPureCapSpine_sort_nil` — clones of `ArcCapSortComplete`'s count-reflection kit.  Colour-blind.

  * ★★ the CAP WORD PIN `stringCapAtom_eq_of_sharedDom_sameWindow` — the ONE genuine dualization of the identify
    step.  Where the arc discharge's identify (`adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths`) is
    LENGTH-rigid (FALSE at the string), and where the r17 CUP pin needed the COD→DOM adapter
    `stringLastCupDomWord_eq_of_sharedCod_sameWindow` (cups share COD), CAPS share DOM directly — so the pin calls
    the r10 keystone `stringSpineAtom_eq_of_wordReadOffs` DIRECTLY, NO adapter.  Fired concretely on the lower
    counit `ε : G·F ⇒ id` (a real cap, dom length 2).

  * ★ the fuel-driver skeleton `stringPureCapSpineSortFueled` + `stringPureCapSpine_sort` — the peel-first cap
    recursion, ASSEMBLED MODULO the one named residual `StringCapHeadExtractionWordPin` (the word-ported analog of
    `spineArcHeadExtractionChained_ofCapArity`): peel the head cap, extract-and-cancel its partner in the second
    spine via the discharge (delivering the shared DOM word to the cap word pin), transfer the pure-cap regime to
    the remainder, recurse at the SHRUNK boundary, re-glue with `SpineTraceEquiv.consCongr`.

## The named standing residual (the honest wall)

`StringCapHeadExtractionWordPin` — the word-ported cap-head discharge.  Its arc mirror rides a ~600-900 line
`adjunctionModeSignature`-locked, colour-BLIND bubble campaign (`ArcCapWindowSeedReadoff` / `ArcCapHeadTransport` /
`ArcCapHeadCancellation` / `ArcBubbleToFront` / `ArcPairCapWindow`) that is NOT cloned to the string yet, with the
one genuine dualization being the identify step (the length-rigid pin → the DOM word pin shipped here, fed by a
new word-chain invariance lemma).  This is a MULTI-ROUND arc; this file names it and proves the recursion assembles
around it.

What this does NOT flip: `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) stays `false` — the
(ii) sub-producer `StringMidZeroValleyTraceEquiv` (`StringValleyDegenerateSplit`) is NOT inhabited this round (it
additionally needs the whole-valley wiring — the mid-width telescope + the floor-0 cup-block reconstruct, ~770
uncloned lines — on top of this cap sort); and `fxString_hasWordBubbleSortAssembly` stays `false`.  This round
flips the NEW `fxString_hasMidZeroValleyCapSort`, whose docstring states the honest state exactly.

Raw Lean 4 + Init; structural / fuel recursion (fuel `Nat` per the list-length source recursion), no `omega` /
`simp`-AC / `WellFounded.fix`.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (per-file copies, following the codebase pattern) -/

/-- A list of length zero is nil — a `noConfusion` peel, staying `propext`-free where
`List.eq_nil_of_length_eq_zero` (an iff-backed lemma) could leak.  Per-file copy of
`ArcCapSortComplete`'s file-private `listEqNilOfLengthZero`. -/
private theorem stringCapListEqNilOfLengthZero {carrier : Type _} :
    (elems : List carrier) → elems.length = 0 → elems = []
  | [], _ => rfl
  | _ :: _, lengthZero => Nat.noConfusion lengthZero

/-- The right summand of a `Nat` sum that vanishes is itself zero — a `noConfusion` peel, staying `propext`-free
where `Nat.eq_zero_of_add_eq_zero_left` / `Nat.succ_ne_zero` would leak.  Per-file copy of `ArcPureCapSpine`'s
file-private `addRightZero`. -/
private theorem stringCapAddRightZero {leftSummand rightSummand : Nat}
    (sumZero : leftSummand + rightSummand = 0) : rightSummand = 0 := by
  cases rightSummand with
  | zero => rfl
  | succ predRight => exact Nat.noConfusion sumZero

/-! ## The string cap ARITY kit (clones of `ArcPureCapSpine`, colour-blind, cup-count-routed) -/

/-- **A pure-cap string spine has zero cup tally.**  Every atom carries cap arity `(2, 0)`, so its codomain length
is `0`, not `2`, and the cup guard never fires.  By induction on the `AllCapArity` witness — colour-blind.  The
three-generator analog of `cupAtomCount_ofAllCapArity`. -/
theorem stringCupAtomCount_ofAllCapArity
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    AllCapArity atoms → cupAtomCount atoms = 0 := by
  intro allCap
  induction allCap with
  | nil => rfl
  | cons hasCapDomArity hasCapCodArity restAllCap restCupZero =>
      rename_i headAtom rest
      dsimp only [cupAtomCount]
      have guardFalse :
          ¬ (headAtom.generatorDom.length == 0 && headAtom.generatorCod.length == 2) = true := by
        rw [hasCapDomArity]
        exact Bool.noConfusion
      rw [if_neg guardFalse, Nat.zero_add]
      exact restCupZero

/-- **A pure-cap string spine's cap tally is its length.**  Every atom has cap arity `(2, 0)`, so the cap guard
fires at every position and the fold counts one per atom.  By induction on the `AllCapArity` witness — colour-blind.
The three-generator analog of `capAtomCount_ofAllCapArity`. -/
theorem stringCapAtomCount_ofAllCapArity
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    AllCapArity atoms → capAtomCount atoms = atoms.length := by
  intro allCap
  induction allCap with
  | nil => rfl
  | cons hasCapDomArity hasCapCodArity restAllCap restLengthEq =>
      rename_i headAtom rest
      have guardTrue :
          (headAtom.generatorDom.length == 2 && headAtom.generatorCod.length == 0) = true := by
        rw [hasCapDomArity, hasCapCodArity]
        rfl
      show (if (headAtom.generatorDom.length == 2 && headAtom.generatorCod.length == 0) then 1 else 0)
          + capAtomCount rest = (headAtom :: rest).length
      rw [if_pos guardTrue, List.length_cons, restLengthEq]
      exact Nat.add_comm 1 rest.length

/-- ★ **`cupAtomCount` zero forces a pure-cap string spine.**  At the walking adjoint triple every atom is a cup or
a cap (`adjointTripleSpineAtom_isCupOrCap`); if the total cup tally is zero then no atom is a cup, so every atom has
cap arity `(2, 0)` — packaged as `AllCapArity`.  By induction: a cup head would contribute one to the tally
(refuting `= 0`), so the head is a cap and the tail still tallies zero.  The three-generator analog of
`allCapArity_ofCupAtomCountZero`. -/
theorem stringAllCapArity_ofCupAtomCountZero
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    cupAtomCount atoms = 0 → AllCapArity atoms := by
  induction atoms with
  | nil => intro _; exact AllCapArity.nil
  | cons headAtom rest inductionHypothesis =>
      intro noCups
      have headCap : headAtom.generatorDom.length = 2 ∧ headAtom.generatorCod.length = 0 := by
        cases adjointTripleSpineAtom_isCupOrCap headAtom with
        | inr capArity => exact capArity
        | inl cupArity =>
            exfalso
            have guardTrue :
                (headAtom.generatorDom.length == 0 && headAtom.generatorCod.length == 2) = true := by
              rw [cupArity.1, cupArity.2]
              rfl
            dsimp only [cupAtomCount] at noCups
            rw [if_pos guardTrue] at noCups
            exact Nat.noConfusion (Nat.add_comm 1 (cupAtomCount rest) ▸ noCups)
      have restNoCups : cupAtomCount rest = 0 := by
        have guardFalse :
            ¬ (headAtom.generatorDom.length == 0 && headAtom.generatorCod.length == 2) = true := by
          rw [headCap.1]
          exact Bool.noConfusion
        dsimp only [cupAtomCount] at noCups
        rw [if_neg guardFalse, Nat.zero_add] at noCups
        exact noCups
      exact AllCapArity.cons headCap.1 headCap.2 (inductionHypothesis restNoCups)

/-- ★ **`AllCapArity` cons-inversion, `propext`-free.**  A pure-cap string spine's tail is pure cap.  A direct
`cases` on the head-indexed `AllCapArity` would leak `propext` (partial match on an indexed inductive); instead
route through the cup count — the head contributes a non-negative summand, so the tail's cup tally is still zero
(`stringCapAddRightZero`) — and rebuild via `stringAllCapArity_ofCupAtomCountZero`.  The three-generator analog of
`allCapArity_ofCons`. -/
theorem stringAllCapArity_ofCons
    {overallSource overallTarget : adjointTripleGraph.Mode}
    {headAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget}
    {rest : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)}
    (consPureCap : AllCapArity (headAtom :: rest)) : AllCapArity rest := by
  have consCupZero : cupAtomCount (headAtom :: rest) = 0 :=
    stringCupAtomCount_ofAllCapArity (headAtom :: rest) consPureCap
  have restCupZero : cupAtomCount rest = 0 := by
    dsimp only [cupAtomCount] at consCupZero
    exact stringCapAddRightZero consCupZero
  exact stringAllCapArity_ofCupAtomCountZero rest restCupZero

/-- ★ **A pure-cap string head carries cap arity `(2, 0)`.**  Every walking-adjoint-triple atom is a cup or a cap
(`adjointTripleSpineAtom_isCupOrCap`); a cup head would contribute one to the cup tally
(`stringCupAtomCount_ofAllCapArity` forces zero), refuting `= 0`.  Routed through the cup count rather than an
indexed `cases` on `AllCapArity`, so it stays `propext`-free.  The three-generator analog of `headCapArity`. -/
theorem stringHeadCapArity
    {overallSource overallTarget : adjointTripleGraph.Mode}
    {headAtom : SpineAtom adjointTripleModeSignature overallSource overallTarget}
    {rest : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)}
    (consPureCap : AllCapArity (headAtom :: rest)) :
    headAtom.generatorDom.length = 2 ∧ headAtom.generatorCod.length = 0 := by
  have consCupZero : cupAtomCount (headAtom :: rest) = 0 :=
    stringCupAtomCount_ofAllCapArity (headAtom :: rest) consPureCap
  cases adjointTripleSpineAtom_isCupOrCap headAtom with
  | inr capArity => exact capArity
  | inl cupArity =>
      exfalso
      have guardTrue :
          (headAtom.generatorDom.length == 0 && headAtom.generatorCod.length == 2) = true := by
        rw [cupArity.1, cupArity.2]
        rfl
      dsimp only [cupAtomCount] at consCupZero
      rw [if_pos guardTrue] at consCupZero
      exact Nat.noConfusion (Nat.add_comm 1 (cupAtomCount rest) ▸ consCupZero)

/-! ## The arc COUNT reflections (clones of `ArcCapSortComplete`'s private kit, colour-blind) -/

/-- The arc structure's total `capCount` reflects the boundary-independent cap-atom count.  Clone of
`ArcCapSortComplete`'s file-private `capCountReflect` — `arcStructureOfSpineList` / `extractArc` /
`processArcSpine_capEventNodes_length` are all `{signature}`-generic, so the reflection ports verbatim. -/
private theorem stringCapCountReflect
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    (arcStructureOfSpineList bottomCount atoms).capCount = capAtomCount atoms := by
  show (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).capEventNodes.length = capAtomCount atoms
  rw [processArcSpine_capEventNodes_length]
  exact Nat.zero_add _

/-- The dual reflection: the arc structure's total `cupCount` reflects the boundary-independent cup-atom count.
Clone of `ArcCapSortComplete`'s file-private `cupCountReflect`. -/
private theorem stringCupCountReflect
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) :
    (arcStructureOfSpineList bottomCount atoms).cupCount = cupAtomCount atoms := by
  show (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      atoms).cupEventNodes.length = cupAtomCount atoms
  rw [processArcSpine_cupEventNodes_length]
  exact Nat.zero_add _

/-! ## Arc-transfer of the pure-cap regime + the empty base case -/

/-- ★ **The pure-cap regime transfers across arc equality.**  If `firstList` is pure cap and its arc structure
equals `secondList`'s, then `secondList` is pure cap: a pure-cap spine has zero cup tally
(`stringCupAtomCount_ofAllCapArity`), the arc structure's total `cupCount` reflects the cup-atom count
(`stringCupCountReflect`), so arc-equal spines carry equal cup tallies, and a zero tally forces `AllCapArity`
(`stringAllCapArity_ofCupAtomCountZero`).  This supplies `AllCapArity` on the extracted remainder in the peel-first
recursion — no arity-preservation over the trace equivalence needed.  The three-generator analog of
`allCapArity_ofArcEqualToPureCap`. -/
theorem stringAllCapArity_ofArcEqualToPureCap
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (firstPureCap : AllCapArity firstList)
    (arcEqual : arcStructureOfSpineList bottomCount firstList
      = arcStructureOfSpineList bottomCount secondList) :
    AllCapArity secondList := by
  have firstCupZero : cupAtomCount firstList = 0 :=
    stringCupAtomCount_ofAllCapArity firstList firstPureCap
  have cupCountsAgree : cupAtomCount firstList = cupAtomCount secondList := by
    have congrCupCount := congrArg FullArcStructure.cupCount arcEqual
    rw [stringCupCountReflect bottomCount firstList, stringCupCountReflect bottomCount secondList]
      at congrCupCount
    exact congrCupCount
  exact stringAllCapArity_ofCupAtomCountZero secondList (cupCountsAgree.symm.trans firstCupZero)

/-- ★ **Equal-arc pure-cap string spines have equal length.**  The arc structure's total `capCount` reflects the
cap-atom count (`stringCapCountReflect`), and a pure-cap spine's cap count IS its length
(`stringCapAtomCount_ofAllCapArity`), so arc-equal pure-cap spines carry equal length.  The three-generator analog
of `pureCapSpines_sameLength_ofArcEqual`. -/
theorem stringPureCapSpines_sameLength_ofArcEqual
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (firstPureCap : AllCapArity firstList) (secondPureCap : AllCapArity secondList)
    (arcEqual : arcStructureOfSpineList bottomCount firstList
      = arcStructureOfSpineList bottomCount secondList) :
    firstList.length = secondList.length := by
  have capCountsAgree : capAtomCount firstList = capAtomCount secondList := by
    have congrCapCount := congrArg FullArcStructure.capCount arcEqual
    rw [stringCapCountReflect bottomCount firstList, stringCapCountReflect bottomCount secondList]
      at congrCapCount
    exact congrCapCount
  rw [← stringCapAtomCount_ofAllCapArity firstList firstPureCap,
    ← stringCapAtomCount_ofAllCapArity secondList secondPureCap]
  exact capCountsAgree

/-- ★ **The empty base case of the string pure-cap sort.**  A pure-cap spine whose arc structure equals the empty
spine's is itself empty: equal arc forces equal length (`stringPureCapSpines_sameLength_ofArcEqual` with the empty
side pure-cap by `AllCapArity.nil`), a zero-length list is nil (`stringCapListEqNilOfLengthZero`), and trace
equivalence to `[]` collapses to reflexivity.  The three-generator analog of `pureCapSpine_sort_nil`. -/
theorem stringPureCapSpine_sort_nil
    {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat)
    (secondList : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (secondPureCap : AllCapArity secondList)
    (arcEqual : arcStructureOfSpineList bottomCount
        ([] : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
      = arcStructureOfSpineList bottomCount secondList) :
    SpineTraceEquiv adjointTripleModeSignature [] secondList := by
  have secondNil : secondList = [] :=
    stringCapListEqNilOfLengthZero secondList
      (stringPureCapSpines_sameLength_ofArcEqual bottomCount [] secondList AllCapArity.nil
        secondPureCap arcEqual).symm
  rw [secondNil]
  exact SpineTraceEquiv.refl []

/-! ## The CAP WORD PIN — the one genuine dualization of the identify step (shared DOM, no adapter) -/

/-- ★★ **The cap word pin (shared DOM, NO adapter).**  Two string CAP atoms firing at the SAME domain boundary
WORD with equal windows (left-context lengths) are EQUAL.  Because both are caps (dom length `2`), the two
generator-dom read-off lengths agree, so the r10 keystone `stringSpineAtom_eq_of_wordReadOffs` applies DIRECTLY —
NO COD→DOM adapter (the r17 CUP pin needed `stringLastCupDomWord_eq_of_sharedCod_sameWindow` precisely because cups
share COD; caps share DOM, so the keystone fires verbatim).  This is the colour-AWARE replacement for the arc
discharge's LENGTH-rigid identify `adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths` (whose
`adjunctionPath_eq_of_length_eq` upgrade is FALSE at the string). -/
theorem stringCapAtom_eq_of_sharedDom_sameWindow
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (capFirst capSecond : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (domBoundaryWordsEqual :
      composePath capFirst.leftContext (composePath capFirst.generatorDom capFirst.rightContext)
        = composePath capSecond.leftContext
            (composePath capSecond.generatorDom capSecond.rightContext))
    (windowEqual : capFirst.leftContext.length = capSecond.leftContext.length)
    (capDomFirst : capFirst.generatorDom.length = 2)
    (capDomSecond : capSecond.generatorDom.length = 2) :
    capFirst = capSecond :=
  stringSpineAtom_eq_of_wordReadOffs capFirst capSecond domBoundaryWordsEqual windowEqual
    (capDomFirst.trans capDomSecond.symm)

/-! ## The named standing residual — the word-ported cap-head discharge -/

/-- ★ **The word-ported cap-head extraction — the one genuinely colour-keyed residual.**  Mirrors the walking
adjunction's `spineArcHeadExtractionChained_ofCapArity`, but WORD-driven: the head cap and its bubbled partner both
fire at the running DOM boundary WORD `bottomWord`, so the identify step is the DOM word pin
`stringCapAtom_eq_of_sharedDom_sameWindow` (no length rigidity).  Its arc mirror rides the
`adjunctionModeSignature`-locked, colour-blind bubble campaign (`ArcCapWindowSeedReadoff` / `ArcCapHeadTransport` /
`ArcCapHeadCancellation` / `ArcBubbleToFront` / `ArcPairCapWindow`), NOT cloned to the string yet — a multi-round
arc.  This Prop is the EXACT interface the peel-first fuel driver consumes: it returns the remainder chained AND
word-chained at the head's target boundary (the head cap's cod word), so the recursion threads both chains. -/
def StringCapHeadExtractionWordPin : Prop :=
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

/-! ## The fuel-driver skeleton (assembled MODULO the residual) -/

/-- Fuel-driven core of the string pure-cap sort (structural on `fuel ≥ firstList.length`), assembled MODULO the
word-ported cap-head discharge `headExtract`.  Peels the head cap `C1` off `firstList = C1 :: t1`
(`stringHeadCapArity`, `stringAllCapArity_ofCons`), EXTRACTS its partner from `secondList` as `C1 :: matchedRemainder`
via `headExtract` (delivering the shared DOM word to the cap word pin, returning the remainder chained AND
word-chained at `C1`'s cod word), transfers the pure-cap regime to `matchedRemainder`
(`stringAllCapArity_ofArcEqualToPureCap`), recurses on the shrunk boundary `C1.codBoundaryLength`, and re-glues `C1`
with `SpineTraceEquiv.consCongr`.  The peel-first mirror of `pureCapSpineSortFueled`. -/
private theorem stringPureCapSpineSortFueled (headExtract : StringCapHeadExtractionWordPin)
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
          obtain ⟨matchedRemainder, extractEquiv, remainderChained, remainderWordChained, tailArcEqual⟩ :=
            headExtract bottomCount bottomWord C1 c1Dom c1Cod t1 secondList chainedFirst chainedSecond
              firstWordChained secondWordChained arcEqual
          have matchedPure : AllCapArity matchedRemainder :=
            stringAllCapArity_ofArcEqualToPureCap C1.codBoundaryLength t1 matchedRemainder t1Pure
              tailArcEqual
          have tailTrace : SpineTraceEquiv adjointTripleModeSignature t1 matchedRemainder :=
            stringPureCapSpineSortFueled headExtract fuel C1.codBoundaryLength
              (composePath C1.leftContext (composePath C1.generatorCod C1.rightContext))
              t1 matchedRemainder t1LenBound tailChainedFirst remainderChained tailWordChainedFirst
              remainderWordChained t1Pure matchedPure tailArcEqual
          exact (SpineTraceEquiv.consCongr C1 tailTrace).trans extractEquiv.symm

/-- ★ **The string pure-cap sort — ASSEMBLED MODULO the word-ported cap-head discharge.**  Given the residual
`StringCapHeadExtractionWordPin`, two boundary-chained AND boundary-word-chained pure-cap string spines over a
bottom boundary with EQUAL arc structure are trace-equivalent.  The peel-first mirror of `pureCapSpine_sort`
(`ArcCapSortComplete`), re-plumbed onto the four-generator seed with the DOM word pin.  Seeds the fuel at
`firstList.length`.  This proves the whole peel-first recursion assembles around the ONE colour-keyed discharge
— what remains is inhabiting that discharge (the uncloned arc bubble campaign, a later round). -/
theorem stringPureCapSpine_sort (headExtract : StringCapHeadExtractionWordPin)
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
  stringPureCapSpineSortFueled headExtract firstList.length bottomCount bottomWord firstList secondList
    (Nat.le_refl firstList.length) chainedFirst chainedSecond firstWordChained secondWordChained
    firstPureCap secondPureCap arcEqual

/-! ## Concrete truth-probes (anti-vacuity) -/

/-- A concrete CAP spine atom: the lower counit `ε : G·F ⇒ id_tip` with empty whiskering contexts.  Dom
`G·F` (length `2`), cod `id_tip` (length `0`), window `0` — a genuine cap. -/
def stringProbeCapAtom :
    SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip :=
  ⟨AdjointTripleMode.tip, AdjointTripleMode.tip,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip, stringGF,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip,
    StringTwoCell.counitLower,
    ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip⟩

/-- ★ **The cap word pin FIRES on the lower counit.**  Pinning the concrete cap atom `ε` against itself (shared dom
word, equal window, both dom length `2`) runs `stringCapAtom_eq_of_sharedDom_sameWindow` — hence the r10 keystone —
on a genuine cap, a machine-checked non-vacuity witness that the DOM word pin applies to a real cap (dom length 2),
NOT a vacuous statement. -/
theorem stringProbeCapAtom_pinFires : stringProbeCapAtom = stringProbeCapAtom :=
  stringCapAtom_eq_of_sharedDom_sameWindow stringProbeCapAtom stringProbeCapAtom rfl rfl rfl rfl

/-- A concrete three-CAP spine (three copies of `ε` at `tip`), a genuine multi-cap witness for the count/transfer
kit. -/
def stringProbeThreeCapSpine :
    List (SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip) :=
  [stringProbeCapAtom, stringProbeCapAtom, stringProbeCapAtom]

/-- The three-cap probe is pure cap (`AllCapArity`) — each `ε` has cap arity `(2, 0)`. -/
theorem stringProbeThreeCap_allCap : AllCapArity stringProbeThreeCapSpine :=
  AllCapArity.cons rfl rfl (AllCapArity.cons rfl rfl (AllCapArity.cons rfl rfl AllCapArity.nil))

/-- ★ **The head cap arity FIRES on the three-cap probe.**  `stringHeadCapArity` reads the head `ε`'s cap arity
`(2, 0)` off the concrete `AllCapArity` witness — the peel-first head read-off, machine-checked. -/
theorem stringProbeThreeCap_headArity :
    stringProbeCapAtom.generatorDom.length = 2 ∧ stringProbeCapAtom.generatorCod.length = 0 :=
  stringHeadCapArity stringProbeThreeCap_allCap

/-- ★ **The arc-transfer FIRES on the three-cap probe (reflexive arc).**  Transferring the pure-cap regime across
the reflexive arc equality on the concrete three-cap spine runs `stringAllCapArity_ofArcEqualToPureCap` — hence the
cup-count reflection — end-to-end, recovering `AllCapArity`.  A machine-checked non-vacuity witness for the
arc-transfer machinery on a genuine multi-cap spine. -/
theorem stringProbeThreeCap_transferReflexive : AllCapArity stringProbeThreeCapSpine :=
  stringAllCapArity_ofArcEqualToPureCap 2 stringProbeThreeCapSpine stringProbeThreeCapSpine
    stringProbeThreeCap_allCap rfl

/-- ★ **The length reflection FIRES on the three-cap probe.**  The equal-length reflection on the concrete
three-cap spine (reflexive arc) runs `stringPureCapSpines_sameLength_ofArcEqual` — hence `stringCapCountReflect` +
`stringCapAtomCount_ofAllCapArity` — end-to-end. -/
theorem stringProbeThreeCap_sameLengthReflexive :
    stringProbeThreeCapSpine.length = stringProbeThreeCapSpine.length :=
  stringPureCapSpines_sameLength_ofArcEqual 2 stringProbeThreeCapSpine stringProbeThreeCapSpine
    stringProbeThreeCap_allCap stringProbeThreeCap_allCap rfl

/-- ★ **The recursion base FIRES unconditionally.**  The empty base case `stringPureCapSpine_sort_nil` (with an
empty second list, reflexive arc) produces `SpineTraceEquiv [] []` with NO residual — the peel-first sort's floor,
machine-checked. -/
theorem stringProbeCapSortNilFires :
    SpineTraceEquiv adjointTripleModeSignature
      ([] : List (SpineAtom adjointTripleModeSignature AdjointTripleMode.tip AdjointTripleMode.tip)) [] :=
  stringPureCapSpine_sort_nil 2 [] AllCapArity.nil rfl

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — THE CAP-DUAL: the pure-cap sort machinery is ported to the adjoint-triple seed, ASSEMBLED
MODULO the word-ported cap-head discharge (FC-3 r18).**  The string cap ARITY kit
(`stringCupAtomCount_ofAllCapArity`, `stringCapAtomCount_ofAllCapArity`, `stringAllCapArity_ofCupAtomCountZero`,
`stringAllCapArity_ofCons`, `stringHeadCapArity` — colour-blind, cup-count-routed clones of `ArcPureCapSpine`), the
arc COUNT/TRANSFER/BASE clones (`stringCapCountReflect`, `stringCupCountReflect`,
`stringAllCapArity_ofArcEqualToPureCap`, `stringPureCapSpines_sameLength_ofArcEqual`,
`stringPureCapSpine_sort_nil`), the CAP WORD PIN `stringCapAtom_eq_of_sharedDom_sameWindow` (the direct r10-keystone
call — caps share DOM, so NO adapter, unlike the r17 cup pin), and the fuel-driver skeleton
`stringPureCapSpineSortFueled` / `stringPureCapSpine_sort` all land, zero-axiom.  The concrete probes
(`stringProbeCapAtom_pinFires`, `stringProbeThreeCap_headArity`, `stringProbeThreeCap_transferReflexive`,
`stringProbeThreeCap_sameLengthReflexive`, `stringProbeCapSortNilFires`) fire the pin, the head read-off, the
transfer, the length reflection, and the base concretely on the lower counit `ε`.  The peel-first cap recursion is
proven to ASSEMBLE around the ONE colour-keyed discharge.

  The named standing residual: `StringCapHeadExtractionWordPin` — the word-ported cap-head discharge (the analog of
  the adjunction's `spineArcHeadExtractionChained_ofCapArity`, whose arc mirror rides a ~600-900 line
  `adjunctionModeSignature`-locked, colour-blind bubble campaign NOT cloned to the string yet, plus the one genuine
  dualization = the DOM word pin shipped here).  A multi-round arc.

  What this does NOT flip (honestly): `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) stays
  `false` — the (ii) sub-producer `StringMidZeroValleyTraceEquiv` (`StringValleyDegenerateSplit`) is NOT inhabited
  this round; even with the cap sort in hand it additionally needs the whole-valley wiring (the mid-width telescope
  `stringSurvivorTopTotal_eq_midWidth` + the floor-0 cup-block reconstruct `midZeroCupBlockReconstruct` analogs,
  ~770 uncloned lines) plus the still-uninhabited `StringCapHeadExtractionWordPin` residual.  And
  `fxString_hasWordBubbleSortAssembly` (`StringDisjointWordBubble`) stays `false` (its docstring demands the pure
  block sort INTO `StringCellValleyTraceEquiv` plus the #2186 valley-append split — strictly more).  This round
  flips ONLY this NEW marker: the cap-sort machinery for the mid-zero valley cap arm, assembled modulo one named
  discharge.  `= true`. -/
def fxString_hasMidZeroValleyCapSort : Bool := true

end FX1Poly.Polygraph
