import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescClosedDiagramRoundtripClose
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescWithCapValidInvolutionScope
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardForm
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingComplete
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStagedDescent

/-! # BRAUER — the indexed-conv standard-form bridge: `classRepresentativeOf` is a NORMAL FORM for the
boundary-indexed word problem on the valid-involution scope

The r55 complete roundtrip (`ext5CorrectedRoundtrip_complete`: `standardFormDiagramExt5
(reconstructStandardFormExt5Corrected d) = d` for every well-formed boundary involution, all `bottomCount`)
is a FOLD-level read-back fact.  This file lifts it to the CONV layer — through the boundary-INDEXED
`BrauerConv`, exactly as the r52 architectural fact demands (`not_brauerConvFree8_diagramInvariant`: the FREE
relation is boundary-count-blind and NOT diagram-invariant, so no completeness statement may route through it;
`BrauerConv` threads `bottomCount` through every constructor).

## What this file ships (each zero-axiom, structural)

  * ★ **`classRepresentative_realizesDiagram`** — the r55 roundtrip in WORD form: on the r53 valid-involution
    scope (`realizesValidInvolution`), the r51 class representative REALIZES the word's own diagram,
    `brauerDiagramOf b (classRepresentativeOf b word) = brauerDiagramOf b word`.  The only missing ingredient
    of the conv lift, supplied by `ext5CorrectedRoundtrip_completeOfValidCensus` + the partner-length reading
    of the extract (`brauerDiagramOf_partnerLength`).
  * ★★ **THE BRIDGE — `brauerConv_toClassRepresentative`** — every valid-involution word is `BrauerConv`-equal
    AT ITS BOUNDARY INDEX to the standard form of its own diagram: `BrauerConv b word (classRepresentativeOf b
    word)`.  Fired through the shipped completeness `brauerConv_complete` (r1, the connectivity-congruence
    whisker at the empty prefix) on the realization equality.  The boundary is threaded through every step —
    the exact indexed lift the free relation cannot express.
  * ★ **The normal-form laws** — `classRepresentative_realizesValidInvolution` (the representative stays on the
    valid scope) and `classRepresentative_idempotentOnValidScope` (re-representing returns it unchanged — the
    r52 `representativeIdempotent_ofDiagramEq` with its diagram-equality hypothesis now DISCHARGED by the
    roundtrip; the representative is a genuine fixed point everywhere on the scope, not only cap-free).
  * ★★★ **THE NORMAL FORM — `brauerConv_iff_classRepresentativeEq`** — on the valid-involution scope, two words
    are `BrauerConv`-convertible IFF their class representatives are EQUAL WORDS.  Forward: soundness +
    Bergman/Jones well-definedness (`classRepresentativeOf_dependsOnDiagram`).  Backward: the roundtrip
    realization on both sides + `brauerConv_complete`.  So `classRepresentativeOf` is a computable, idempotent,
    scope-preserving COMPLETE INVARIANT — a genuine normal-form function for the indexed Brauer word problem.
    UNIFORM IN CUP COUNT: the single-cup and multi-cup cases are literal specializations — the FC-3-style peel
    induction on cup count is SUBSUMED (no per-cup-count driver is needed at the indexed level; the peel walls
    were artifacts of the free-relation route).
  * **THE DECISION, fired both ways** — the shipped `decidableBrauerConv` / `decideBrauerConvBool` (decide
    diagram equality, cite completeness + soundness) exercised on TEN concrete pairs: distant-commute,
    nested-vs-sequential circles (loop-carrying), loop-count separation, the snake, Temperley–Lieb `e` vs
    identity, the TL delta-loop `e ∘ e ~ e ⊗ circle` (cap + loop), the two-cup slide (multi-cup),
    triple-crossing reduction, crossing-order separation, and the double distant cancel (crossing-heavy) —
    kernel `decide` theorems plus committed `#eval` pins, both verdicts represented.
  * **General-path firings** — the bridge fired on the straddle single-cup word (landing on the r51 jam-residue
    representative `[cupAt 1, crossingAt 0]` via `straddleRepresentativeIsJamResidue`), on a TWO-CUP word
    (multi-cup, no induction), and on the with-cap loop-carrying TL word; the normal-form iff fired forward on
    the two-cup slide pair; the overrun negative control (`censusFails_overrunWord` +
    `overrunWord_representativeFailsToRealize`) shows the census gate is load-bearing (the r53 exact cut).

## The honest masters adjudication (THE FLIP LAW; no weakened variants under master names)

What flips here are NEW content markers.  The standing completeness masters' VERBATIM demands are all on the
FREE side and are NOT met by this file: `fxBrauer_hasBrauerCompleteness` (`Brauer/WiringDesc.lean:499` — its
ledger-defined honest sense is the WHISKER-FREE generation of all diagram equalities from the five relations,
`WiringDescStandardForm.lean` `fxBrauer_hasFreeBrauerStraighteningNF` docstring), `fxBrauer_hasBrauerV2FullCompleteness`
(equal diagram ⟹ `BrauerConvFree8`), `fxBrauer_hasValidInvolutionFoldDischarged` (the
`BrauerExt5CorrectedFoldReachesValidInvolution` FREE drive), `fxBrauer_hasFreeBrauerStraighteningNF`, and the
R3-B `fxBrauer_hasStagedInnerDescentDischarged` ALL STAY `false`; `fxBrauer_hasExt5CorrectedRoundtripProof`
(`WiringDescArcExtractorRec.lean:217`) stays byte-intact `false` per the marker law (9 rfl-pins across 7 frozen
ledgers).  The free-side drive remains the standing wall (pass-5-arc interleave / straddle-measure ascent);
this file changes its STATUS: the indexed word problem is now closed end-to-end (sound + complete + decidable +
normal form), so the free straightening is a presentation-theoretic refinement, no longer the gate on the
Brauer decision itself.

Raw Lean 4 + Init; structural throughout; no `omega` / `native_decide` / `WellFounded.fix` / `sorry`.
Per-declaration `#assert_no_axioms` in the audit twin + an independent `#print axioms` witness file. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The partner-length reading of the extract -/

/-- ★ **The extracted partner list spans the whole boundary** — `brauerDiagramOf b word` reads its partner
matching off `List.range (b + topCount)`, so its length is exactly `bottomCount + topCount`.  The
boundary-length equation the r54 census decoder consumes, supplied for EVERY word (definitional unfolding of
`extractDiagram` + `mapLength` + `rangeLength_local`). -/
theorem brauerDiagramOf_partnerLength (bottomCount : Nat) (word : List BrauerAtom) :
    (brauerDiagramOf bottomCount word).partner.length
      = (brauerDiagramOf bottomCount word).bottomCount + (brauerDiagramOf bottomCount word).topCount := by
  show ((List.range (bottomCount + (processBrauer (brauerSeed bottomCount) word).openWires.length)).map
      (partnerIndexOf (processBrauer (brauerSeed bottomCount) word).links
        (List.range bottomCount ++ (processBrauer (brauerSeed bottomCount) word).openWires)
        (bottomCount + (processBrauer (brauerSeed bottomCount) word).openWires.length))).length
    = bottomCount + (processBrauer (brauerSeed bottomCount) word).openWires.length
  rw [mapLength, rangeLength_local]

/-! ## The r55 roundtrip in word form — the representative REALIZES on the valid scope -/

/-- ★ **The class representative realizes the word's own diagram** — for every word on the r53
valid-involution scope, `classRepresentativeOf b word` induces EXACTLY the word's `brauerDiagramOf` diagram.
This is the r55 complete roundtrip (`ext5CorrectedRoundtrip_completeOfValidCensus`, all `bottomCount`
included) read at the WORD level: `classRepresentativeOf` and `standardFormDiagramExt5 ∘
reconstructStandardFormExt5Corrected` are definitionally the same composite, and the census hypothesis is
definitionally the r53 `isInvolutionPartner` gate. -/
theorem classRepresentative_realizesDiagram (bottomCount : Nat) (word : List BrauerAtom)
    (census : realizesValidInvolution bottomCount word = true) :
    brauerDiagramOf bottomCount (classRepresentativeOf bottomCount word)
      = brauerDiagramOf bottomCount word :=
  ext5CorrectedRoundtrip_completeOfValidCensus (brauerDiagramOf bottomCount word)
    (brauerDiagramOf_partnerLength bottomCount word) census

/-! ## THE BRIDGE — the indexed-conv lift of the roundtrip -/

/-- ★★ **THE INDEXED-CONV STANDARD-FORM BRIDGE.**  Every word whose diagram is a valid Brauer involution is
`BrauerConv`-convertible AT ITS BOUNDARY INDEX to the standard form of its own diagram — the r51
Kudryavtseva–Mazorchuk sandwich word `classRepresentativeOf b word`.  The r55 roundtrip supplies the
realization equality; the shipped r1 completeness (`brauerConv_complete`, the connectivity-congruence whisker
at the empty prefix) turns it into the indexed convertibility.  The boundary `b` is threaded through every
step — the exact lift the FREE relation cannot express (`not_brauerConvFree8_diagramInvariant`, r52 §B). -/
theorem brauerConv_toClassRepresentative (bottomCount : Nat) (word : List BrauerAtom)
    (census : realizesValidInvolution bottomCount word = true) :
    BrauerConv bottomCount word (classRepresentativeOf bottomCount word) :=
  brauerConv_complete bottomCount word (classRepresentativeOf bottomCount word)
    (classRepresentative_realizesDiagram bottomCount word census).symm

/-! ## The normal-form laws — scope preservation + idempotence -/

/-- ★ **The representative stays on the valid scope** — `classRepresentativeOf` maps the valid-involution
arena into itself: the realized diagram IS the word's diagram, whose partner passes the census by
hypothesis. -/
theorem classRepresentative_realizesValidInvolution (bottomCount : Nat) (word : List BrauerAtom)
    (census : realizesValidInvolution bottomCount word = true) :
    realizesValidInvolution bottomCount (classRepresentativeOf bottomCount word) = true := by
  show isInvolutionPartner
      (brauerDiagramOf bottomCount (classRepresentativeOf bottomCount word)).partner = true
  rw [classRepresentative_realizesDiagram bottomCount word census]
  exact census

/-- ★ **Idempotence on the valid scope** — re-representing the representative returns it unchanged.  The r52
`representativeIdempotent_ofDiagramEq` had this GATED on the diagram-equality hypothesis; the r55 roundtrip
(via `classRepresentative_realizesDiagram`) discharges that gate on the whole valid-involution arena, caps and
`bottomCount = 0` included — the representative is a genuine normal-form fixed point everywhere on the
scope. -/
theorem classRepresentative_idempotentOnValidScope (bottomCount : Nat) (word : List BrauerAtom)
    (census : realizesValidInvolution bottomCount word = true) :
    classRepresentativeOf bottomCount (classRepresentativeOf bottomCount word)
      = classRepresentativeOf bottomCount word :=
  representativeIdempotent_ofDiagramEq bottomCount word
    (classRepresentative_realizesDiagram bottomCount word census)

/-! ## THE NORMAL FORM — `classRepresentativeOf` is a complete invariant on the valid scope -/

/-- ★★★ **THE CLASS-REPRESENTATIVE NORMAL FORM.**  On the valid-involution scope, two words are
`BrauerConv`-convertible IFF their class representatives are EQUAL WORDS.  Forward: `brauerConv_sound` turns
convertibility into diagram equality and the Bergman/Jones well-definedness
(`classRepresentativeOf_dependsOnDiagram`) into representative equality.  Backward: the roundtrip realization
on both sides turns representative equality into diagram equality, and `brauerConv_complete` closes.  So
`classRepresentativeOf` is a computable, idempotent, scope-preserving COMPLETE INVARIANT — a genuine
normal-form function for the boundary-indexed Brauer word problem.  UNIFORM IN CUP COUNT: single-cup and
multi-cup words are literal specializations; no peel induction on the cup count is needed at the indexed
level. -/
theorem brauerConv_iff_classRepresentativeEq (bottomCount : Nat) (wordLeft wordRight : List BrauerAtom)
    (censusLeft : realizesValidInvolution bottomCount wordLeft = true)
    (censusRight : realizesValidInvolution bottomCount wordRight = true) :
    BrauerConv bottomCount wordLeft wordRight
      ↔ classRepresentativeOf bottomCount wordLeft = classRepresentativeOf bottomCount wordRight :=
  Iff.intro
    (fun conv =>
      classRepresentativeOf_dependsOnDiagram bottomCount wordLeft wordRight (brauerConv_sound conv))
    (fun representativeEq =>
      brauerConv_complete bottomCount wordLeft wordRight
        ((classRepresentative_realizesDiagram bottomCount wordLeft censusLeft).symm.trans
          ((congrArg (brauerDiagramOf bottomCount) representativeEq).trans
            (classRepresentative_realizesDiagram bottomCount wordRight censusRight))))

/-! ## The census gates for the general-path firings (kernel `decide`, small arenas) -/

/-- The straddle single-cup word `[cupAt 0, crossingAt 1]` over one bottom wire passes the census. -/
theorem censusHolds_straddleSingleCup : realizesValidInvolution 1 [cupAt 0, crossingAt 1] = true := by
  decide

/-- The two-cup word `[cupAt 0, cupAt 0]` (a closed multi-cup diagram) passes the census. -/
theorem censusHolds_twoCupWord : realizesValidInvolution 0 [cupAt 0, cupAt 0] = true := by decide

/-- The Temperley–Lieb loop word `e ∘ e = [capAt 0, cupAt 0, capAt 0, cupAt 0]` over two bottom wires
(with-cap AND loop-carrying) passes the census. -/
theorem censusHolds_temperleyLiebLoopWord :
    realizesValidInvolution 2 [capAt 0, cupAt 0, capAt 0, cupAt 0] = true := by decide

/-- ★ **The overrun NEGATIVE control** — `[cupAt 0, crossingAt 3]` over one bottom wire fires the crossing
past its live width; the census REJECTS it (the r53 exact cut).  The bridge's census hypothesis is
load-bearing. -/
theorem censusFails_overrunWord : realizesValidInvolution 1 [cupAt 0, crossingAt 3] = false := by decide

/-- The overrun word's representative fails to realize its diagram — the r53 iff instantiated on the negative
control: OUTSIDE the valid-involution scope the representative is not a faithful target, which is exactly why
the normal-form theorems gate on the census. -/
theorem overrunWord_representativeFailsToRealize :
    representativeRealizesOwnDiagram 1 [cupAt 0, crossingAt 3] = false := by decide

/-! ## The bridge FIRED through the general path (not `decide`) -/

/-- ★ The bridge fired on the SINGLE-CUP straddle word: `[cupAt 0, crossingAt 1]` is `BrauerConv`-equal at
boundary `1` to its class representative. -/
theorem bridgeFired_straddleSingleCup :
    BrauerConv 1 [cupAt 0, crossingAt 1] (classRepresentativeOf 1 [cupAt 0, crossingAt 1]) :=
  brauerConv_toClassRepresentative 1 [cupAt 0, crossingAt 1] censusHolds_straddleSingleCup

/-- ★ The straddle bridge LANDS ON THE r51 JAM RESIDUE: composing with the frozen pin
`straddleRepresentativeIsJamResidue` (`classRepresentativeOf 1 [cupAt 0, crossingAt 1] = [cupAt 1,
crossingAt 0]`), the straddle word is `BrauerConv`-equal to the concrete standard form `[cupAt 1,
crossingAt 0]` — the r50 jam pair, now a THEOREM of the indexed conv layer through the general path. -/
theorem bridgeFired_straddleLandsOnJamResidue :
    BrauerConv 1 [cupAt 0, crossingAt 1] [cupAt 1, crossingAt 0] :=
  straddleRepresentativeIsJamResidue ▸ bridgeFired_straddleSingleCup

/-- ★ The bridge fired on a MULTI-CUP word (two cups, closed diagram) — through the SAME general theorem, no
cup-count induction: the peel pattern is subsumed at the indexed level. -/
theorem bridgeFired_twoCupMultiCup :
    BrauerConv 0 [cupAt 0, cupAt 0] (classRepresentativeOf 0 [cupAt 0, cupAt 0]) :=
  brauerConv_toClassRepresentative 0 [cupAt 0, cupAt 0] censusHolds_twoCupWord

/-- ★ The bridge fired on the WITH-CAP LOOP-CARRYING Temperley–Lieb word `e ∘ e` (one cap arc, one cup arc,
one closed loop) — caps and loops ride the same general path. -/
theorem bridgeFired_temperleyLiebLoopWord :
    BrauerConv 2 [capAt 0, cupAt 0, capAt 0, cupAt 0]
      (classRepresentativeOf 2 [capAt 0, cupAt 0, capAt 0, cupAt 0]) :=
  brauerConv_toClassRepresentative 2 [capAt 0, cupAt 0, capAt 0, cupAt 0]
    censusHolds_temperleyLiebLoopWord

/-- The normal-form iff fired FORWARD on the two-cup slide pair: `[cupAt 0, cupAt 0]` and `[cupAt 0, cupAt 2]`
are convertible (equal diagrams), so their representatives are the SAME WORD. -/
theorem normalFormFired_twoCupSlide :
    classRepresentativeOf 0 [cupAt 0, cupAt 0] = classRepresentativeOf 0 [cupAt 0, cupAt 2] :=
  (brauerConv_iff_classRepresentativeEq 0 [cupAt 0, cupAt 0] [cupAt 0, cupAt 2]
      censusHolds_twoCupWord (by decide)).mp
    (brauerConv_complete 0 [cupAt 0, cupAt 0] [cupAt 0, cupAt 2] (by decide))

/-! ## THE DECISION fired on ten concrete pairs (kernel `decide`, both verdicts)

`decideBrauerConvBool` decides the indexed word problem outright (extract both diagrams, compare;
completeness + soundness cited by the shipped `decidableBrauerConv`).  Ten pairs, both verdicts, all four
generator families exercised. -/

/-- DECISION (true) — distant crossings commute (four strands). -/
theorem decisionFired_distantCommute :
    decideBrauerConvBool 4 [crossingAt 0, crossingAt 2] [crossingAt 2, crossingAt 0] = true := by decide

set_option maxHeartbeats 1600000 in
/-- DECISION (true) — LOOP-CARRYING: the nested circle pair `[cup, cup, cap, cap]` equals the sequential
double circle `[cup, cap, cup, cap]` (two closed loops each, distinct words). -/
theorem decisionFired_nestedCirclePair :
    decideBrauerConvBool 0 [cupAt 0, cupAt 0, capAt 0, capAt 0]
      [cupAt 0, capAt 0, cupAt 0, capAt 0] = true := by decide

/-- DECISION (false) — the loop count SEPARATES: one circle is not two circles. -/
theorem decisionFired_loopCountSeparates :
    decideBrauerConvBool 0 (circleWord 1) (circleWord 2) = false := by decide

/-- DECISION (true) — THE SNAKE: `[cupAt 1, capAt 0]` over one strand straightens to the identity. -/
theorem decisionFired_snakeStraightens :
    decideBrauerConvBool 1 [cupAt 1, capAt 0] [] = true := by decide

/-- DECISION (false) — the Temperley–Lieb idempotent `e = [capAt 0, cupAt 0]` is NOT the identity (two
strands). -/
theorem decisionFired_temperleyLiebNotIdentity :
    decideBrauerConvBool 2 [capAt 0, cupAt 0] [] = false := by decide

/-- DECISION (true) — the TL delta-loop relation: `e ∘ e` equals `e` with one free circle (with-cap AND
loop-carrying). -/
theorem decisionFired_temperleyLiebDeltaLoop :
    decideBrauerConvBool 2 [capAt 0, cupAt 0, capAt 0, cupAt 0]
      ([capAt 0, cupAt 0] ++ circleWord 1) = true := by decide

/-- DECISION (true) — the two-cup slide (multi-cup): nested-at-0 equals side-by-side. -/
theorem decisionFired_twoCupSlide :
    decideBrauerConvBool 0 [cupAt 0, cupAt 0] [cupAt 0, cupAt 2] = true := by decide

/-- DECISION (true) — CROSSING-HEAVY: the triple crossing reduces to the single crossing (R2 in context). -/
theorem decisionFired_tripleCrossingReduces :
    decideBrauerConvBool 2 [crossingAt 0, crossingAt 0, crossingAt 0] [crossingAt 0] = true := by decide

/-- DECISION (false) — adjacent crossing ORDER separates: `s0 s1 ≠ s1 s0` on three strands. -/
theorem decisionFired_crossingOrderSeparates :
    decideBrauerConvBool 3 [crossingAt 0, crossingAt 1] [crossingAt 1, crossingAt 0] = false := by decide

set_option maxHeartbeats 800000 in
/-- DECISION (true) — CROSSING-HEAVY: two interleaved distant cancels `s0 s2 s2 s0` collapse to the identity
on four strands. -/
theorem decisionFired_doubleDistantCancel :
    decideBrauerConvBool 4 [crossingAt 0, crossingAt 2, crossingAt 2, crossingAt 0] [] = true := by decide

/-! ### The committed `#eval` census pins (re-run: `lake build` this module) -/

-- THE DECISION pins — must match the ten kernel theorems above.
#eval decideBrauerConvBool 4 [crossingAt 0, crossingAt 2] [crossingAt 2, crossingAt 0]           -- true
#eval decideBrauerConvBool 0 [cupAt 0, cupAt 0, capAt 0, capAt 0] [cupAt 0, capAt 0, cupAt 0, capAt 0]  -- true
#eval decideBrauerConvBool 0 (circleWord 1) (circleWord 2)                                       -- false
#eval decideBrauerConvBool 1 [cupAt 1, capAt 0] []                                               -- true
#eval decideBrauerConvBool 2 [capAt 0, cupAt 0] []                                               -- false
#eval decideBrauerConvBool 2 [capAt 0, cupAt 0, capAt 0, cupAt 0] ([capAt 0, cupAt 0] ++ circleWord 1)  -- true
#eval decideBrauerConvBool 0 [cupAt 0, cupAt 0] [cupAt 0, cupAt 2]                               -- true
#eval decideBrauerConvBool 2 [crossingAt 0, crossingAt 0, crossingAt 0] [crossingAt 0]           -- true
#eval decideBrauerConvBool 3 [crossingAt 0, crossingAt 1] [crossingAt 1, crossingAt 0]           -- false
#eval decideBrauerConvBool 4 [crossingAt 0, crossingAt 2, crossingAt 2, crossingAt 0] []         -- true

-- THE CENSUS pins — the three positive gates and the overrun rejection.
#eval realizesValidInvolution 1 [cupAt 0, crossingAt 1]                    -- true
#eval realizesValidInvolution 0 [cupAt 0, cupAt 0]                         -- true
#eval realizesValidInvolution 2 [capAt 0, cupAt 0, capAt 0, cupAt 0]       -- true
#eval realizesValidInvolution 1 [cupAt 0, crossingAt 3]                    -- false

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — THE INDEXED-CONV STANDARD-FORM BRIDGE is SHIPPED.**  On the r53 valid-involution
scope, every word is `BrauerConv`-convertible AT ITS BOUNDARY INDEX to the standard form of its own diagram
(`brauerConv_toClassRepresentative`), by composing the r55 complete roundtrip
(`ext5CorrectedRoundtrip_completeOfValidCensus`, all `bottomCount`) with the r1 connectivity-congruence
completeness (`brauerConv_complete`).  The lift routes through the boundary-INDEXED relation exactly as the
r52 architectural fact demands (`not_brauerConvFree8_diagramInvariant`); fired through the general path on
single-cup, multi-cup, and with-cap loop-carrying words.  `= true`. -/
def fxBrauer_hasIndexedConvStandardFormBridge : Bool := true

/-- ★★★ **Honesty marker — `classRepresentativeOf` is a NORMAL FORM for the indexed Brauer word problem on
the valid-involution scope.**  Computable, idempotent (`classRepresentative_idempotentOnValidScope`),
scope-preserving (`classRepresentative_realizesValidInvolution`), and a COMPLETE INVARIANT
(`brauerConv_iff_classRepresentativeEq`: convertible iff equal representative words), uniform in cup count
(the peel induction is subsumed).  HONEST SCOPE: `BrauerConv` includes the connectivity-view `whisker`
congruence — this is the indexed relation the lane's decision layer is built on, NOT the whisker-free
five-relation generation (see the masters marker below).  `= true`. -/
def fxBrauer_hasClassRepresentativeNormalForm : Bool := true

/-- ★ **Honesty marker — THE DECISION is fired on ten concrete pairs, both verdicts.**  The shipped
`decidableBrauerConv` / `decideBrauerConvBool` (extract both diagrams, compare — completeness + soundness)
exercised as kernel `decide` theorems on distant-commute, nested circles, loop separation, the snake, TL `e`
vs identity, the TL delta-loop, the two-cup slide, triple-crossing reduction, crossing-order separation, and
the double distant cancel — crossing-heavy and loop-carrying pairs included, with committed `#eval` pins.
`= true`. -/
def fxBrauer_hasIndexedConvRepresentativeDecisionFired : Bool := true

/-- **Honesty marker — the FREE-side completeness masters STAY `false` (THE FLIP LAW; no weakened variants
under master names).**  This file closes the INDEXED word problem end-to-end (sound + complete + decidable +
normal form), but the verbatim demands of `fxBrauer_hasBrauerCompleteness` (whisker-free generation),
`fxBrauer_hasBrauerV2FullCompleteness` (equal diagram ⟹ `BrauerConvFree8`),
`fxBrauer_hasValidInvolutionFoldDischarged` (the FREE `BrauerExt5CorrectedFoldReachesValidInvolution` drive),
`fxBrauer_hasFreeBrauerStraighteningNF`, and `fxBrauer_hasStagedInnerDescentDischarged` (R3-B) are all on the
FREE relation and are NOT met here; `fxBrauer_hasExt5CorrectedRoundtripProof` stays byte-intact `false` per
the marker law.  STATUS CHANGE recorded: with the indexed decision closed, the free straightening is a
presentation-theoretic refinement (that the five relations + interchange GENERATE the whisker move), no longer
the gate on the Brauer decision.  `= true` (the marker records the adjudication, not a flip). -/
def fxBrauer_hasIndexedConvMastersAdjudication : Bool := true

/-! ## The machine-checked terminal state -/

/-- ★★ **The class-representative normal-form terminal state — MACHINE-CHECKED.**  The three new content
markers are `true` on top of the r55 roundtrip and the r1 decision; every FREE-side master and the pinned
:217 wall marker STAY `false`, kernel-checked same-commit by this `rfl`-conjunction.  Purely additive: no
frozen file is touched. -/
theorem fxBrauer_classRepresentativeNormalFormTerminalState :
    fxBrauer_hasIndexedConvStandardFormBridge = true
      ∧ fxBrauer_hasClassRepresentativeNormalForm = true
      ∧ fxBrauer_hasIndexedConvRepresentativeDecisionFired = true
      ∧ fxBrauer_hasIndexedConvMastersAdjudication = true
      ∧ fxBrauer_hasExt5CorrectedRoundtripComplete = true
      ∧ fxBrauer_hasConnectivityCongruenceDecision = true
      ∧ fxBrauer_hasCorrectedExtractorValidInvolutionCoverage = true
      ∧ (fxBrauer_hasBrauerCompleteness = false
        ∧ fxBrauer_hasBrauerV2FullCompleteness = false
        ∧ fxBrauer_hasValidInvolutionFoldDischarged = false
        ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
        ∧ fxBrauer_hasStagedInnerDescentDischarged = false
        ∧ fxBrauer_hasExt5CorrectedRoundtripProof = false) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph
