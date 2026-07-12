import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupTouchingCriterionAmendment

/-! # BRAUER r52 — THE CORRECTED-FOLD CAP-FREE SCOPING: census extended to length 5, the positionsFit guard
quantified, the two-sided-sandwich (cap-side) defect autopsied, and the free-vs-genuine relation gap machine-checked
(the EIGHTH honest zero-flip)

r51 (`WiringDescClassRepresentativeReadjudication.lean`) named the class representative
`classRepresentativeOf b word = standardFormWordExt5 (reconstructStandardFormExt5Corrected (brauerDiagramOf b word))`
— the Kudryavtseva–Mazorchuk two-sided sandwich `u . e_{i,j}` (arXiv:math/0511730, Lemma 22 / Cor. 21), the
walled-Brauer `w_L . (cups) . w_R` (arXiv:1912.12869, eq. 1.8) specialised to a single cup — and shipped the committed
census (`375/375` len 3, `2500/2500` len 4 cap-free at a non-degenerate boundary; `1425/1500` with-cap).  The r52
target `BrauerExt5CorrectedFoldReaches` (`WiringDescCorrectedFold.lean:52`) is the UNCONDITIONAL fold — every word
`BrauerConvFree8`-reaches its own diagram's representative — whose discharge would flip
`fxBrauer_hasBrauerV2FullCompleteness`.

## THE HEADLINE ADJUDICATION

The unconditional fold cannot be discharged this round, and the census now shows WHY it is not merely unproven — it
sharpens on two fronts:

  1. **The cap-free arena is empirically total to length 5** (`15625/15625`) and the representative is idempotent
     everywhere on it (idempotence is a COROLLARY of realization, `representativeIdempotent_ofDiagramEq`), while the
     narrow-boundary degeneracy is quantified: the coverage saturates exactly at `bottomCount = maxCrossingPosition +
     2` (the positionsFit guard `hasBoundaryRoomForPositions`), which is EMPIRICALLY SOUND (0 guard-holds-but-fails at
     every boundary, length 3 and 4).  So the R3-A totality TRUTH is confirmed wider, under an explicit honest guard.

  2. **The with-cap arena is NOT total, and grows worse with length** (`75/1500` at len 3, `3500/20000` at len 4).
     The failures are the two-sided-sandwich complement: the corrected extractor inverts only the cup/top side
     (`permInverse (throughStrandTops ++ cupArcTops)`), leaving the cap/bottom side un-inverted, so a cap arc entangled
     with a through-region crossing realises a different `partner`.  This is the ∗-dual of the nested-cup defect r51's
     R3-B1 fixed on the cup side — an honest, structurally-localised read-off incompleteness of the EXTRACTOR, never a
     truth gap: the diagram identity itself holds classically (Lehrer–Zhang arXiv:1207.5889 Thm 2.6; the two-sided
     normal form `s . e . s'` needs the bottom permutation `s'`, which a cup-only representative lacks).

Additionally the load-bearing structural fact is machine-checked: **the free relation `BrauerConvFree8` is NOT
`brauerDiagramOf`-invariant uniformly in the boundary** (`not_brauerConvFree8_diagramInvariant`) — the free
over-approximation drops the boundary index that the genuine boundary-indexed `BrauerConv n` (diagram-sound via the
shipped `brauerConv_sound`, `WiringDescConv.lean:141`) carries, so at `bottomCount = 0` the cup-slide relates two words
with DIFFERENT diagrams.  Consequently, even were the unconditional fold true, its `BrauerConvFree8`-convertibility
conclusion does NOT bridge to the genuine `BrauerConv bottomCount` decision that
`fxBrauer_hasBrauerV2FullCompleteness` wants: free-convertibility is strictly weaker than sound convertibility.  That
is a named ARCHITECTURAL gap (free over-approximation ≠ boundary-indexed sound relation), the two-sided-sandwich
residual of the literature, not a route gap to paper over.  Either way, no flag flips this round.

## What SHIPS (each zero-axiom, structural; `decide` on small pins only, `#eval` on the census)

  * ★ **THE SCOPED FOLD TARGET** (§A) — `BrauerExt5CorrectedFoldReachesCapFree`, the honestly-guarded fold: cap-free +
    single-cup + positionsFit ⟹ `BrauerConvFree8`-reaches the representative.  Stated, NOT discharged (the R3-A
    `stepWiring`-connectivity structural induction remains the long pole).
  * ★★ **THE FREE-VS-GENUINE ARCHITECTURAL GAP** (§B) — `not_brauerConvFree8_diagramInvariant`, machine-checked: the
    free relation is not n-uniformly diagram-invariant (cup-slide sound at its own boundary 1, unsound at 0).
  * ★ **THE CENSUS EXTENSION** (§C) — len-5 cap-free totality (`15625/15625`), the narrow-boundary sweep quantifying
    the guard, the guard-soundness pins (0 failures), and the with-cap len-4 failure count (`3500/20000`).
  * ★ **THE CAP-SIDE DEFECT AUTOPSY** (§D) — three pinned witnesses that the representative realises a DIFFERENT
    diagram on `[capAt k, crossingAt 3, cupAt 0]` (the ∗-dual cap-side inversion gap).
  * the honest terminal state: purely additive; every dispatch flag and completeness master STAYS `false`.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin + an independent `#print axioms` witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the scoped fold target (the honest positionsFit guard) -/

/-- The maximum boundary position occurring in a word (structural fold; `0` on the empty word). -/
def maxAtomPosition : List BrauerAtom → Nat
  | [] => 0
  | atom :: rest => Nat.max atom.position (maxAtomPosition rest)

/-- ★ **The positionsFit guard.**  Does the boundary have room for every crossing in the word?  A crossing at position
`p` braids wires `p` and `p+1`, so realising the diagram needs `bottomCount ≥ p + 2`; taking the maximum over the word
gives `hasBoundaryRoomForPositions b word = (maxAtomPosition word + 2 ≤ b)`.  Equivalently `b > maxCrossingPosition + 1`
— the census (`capFreeGuardHoldsRealizeFailCount`) confirms this is the exact non-degeneracy threshold on the cap-free
arena. -/
def hasBoundaryRoomForPositions (bottomCount : Nat) (word : List BrauerAtom) : Bool :=
  Nat.ble (maxAtomPosition word + 2) bottomCount

/-- ★ **THE SCOPED FOLD — the honest cap-free target.**  On the cap-free single-cup arena, at a boundary that fits all
crossing positions, every word `BrauerConvFree8`-reaches the corrected extended standard form of its own diagram (its
class representative).  This is the R3-A totality restricted to the arena where the corrected extractor's cup/top-only
inversion is exact — the two-sided sandwich with trivial bottom permutation `s' = id` (Kudryavtseva–Mazorchuk
arXiv:math/0511730; the with-cap complement `s' ≠ id`, autopsied in §D, is genuinely outside this image).  Stated as
the honest scope; NOT discharged unconditionally — the `stepWiring`-connectivity structural induction is the long
pole (`fxBrauer_hasExt5CorrectedRoundtripProof`, `WiringDescArcExtractorRec.lean:217`, stays `false`). -/
def BrauerExt5CorrectedFoldReachesCapFree : Prop :=
  ∀ (bottomCount : Nat) (word : List BrauerAtom),
    isCapFreeWord word = true →
    hasExactlyOneCup word = true →
    hasBoundaryRoomForPositions bottomCount word = true →
    BrauerConvFree8 word (classRepresentativeOf bottomCount word)

/-! ## B — the free-vs-genuine relation architectural gap (machine-checked)

The genuine `BrauerConv : Nat → List BrauerAtom → List BrauerAtom → Prop` (`WiringDescConv.lean:76`) is
boundary-INDEXED — every move is fitted to the boundary — which is why `brauerConv_sound` (`WiringDescConv.lean:141`)
proves it diagram-sound.  `BrauerConvFree8` (`WiringDescCupSlide.lean:104`) is boundary-AGNOSTIC: it fires the cup-slide
row at ANY offset with no boundary-fit check.  The literature's two-sided normal form `s . e . s'` is boundary-indexed
for exactly this reason (arXiv:math/0511730 §3; the generator index `i` ranges `1 ≤ i ≤ n-1`, so a generator at `i`
needs `i + 1 ≤ n`).  The free relation therefore relates words whose diagrams differ at the wrong boundary. -/

/-- The cup-slide row IS diagram-sound at its OWN boundary (`bottomCount = 1`, `cupSlideRelation.boundaryCount`): both
sides read the same nested matching.  This is the shipped `cupSlide_diagram_sound` restated at the literal boundary. -/
theorem cupSlide_diagram_soundAtBoundaryOne :
    brauerDiagramOf 1 [cupAt 0, crossingAt 1] = brauerDiagramOf 1 [cupAt 1, crossingAt 0] := by decide

/-- ★ **The cup-slide row is NOT diagram-sound one boundary lower** (`bottomCount = 0`): with no second bottom wire the
crossing at position 1 degenerates on the left side only, so `[cupAt 0, crossingAt 1]` reads `topCount 3` while
`[cupAt 1, crossingAt 0]` reads `topCount 2`.  The relation's soundness is BOUNDARY-DEPENDENT — the crux the genuine
boundary-indexed `BrauerConv` respects and the free `BrauerConvFree8` does not. -/
theorem cupSlide_diagram_notSoundAtBoundaryZero :
    brauerDiagramOf 0 [cupAt 0, crossingAt 1] ≠ brauerDiagramOf 0 [cupAt 1, crossingAt 0] := by decide

/-- ★★ **THE FREE RELATION IS NOT n-UNIFORMLY DIAGRAM-INVARIANT — machine-checked.**  There is NO diagram-invariant for
`BrauerConvFree8` holding at every boundary: `brauerConvFree8_cupSlide_derivable` relates `[cupAt 0, crossingAt 1]` and
`[cupAt 1, crossingAt 0]`, yet at `bottomCount = 0` their diagrams differ
(`cupSlide_diagram_notSoundAtBoundaryZero`).  Hence the fold's `BrauerConvFree8`-conclusion does NOT entail
genuine `brauerDiagramOf n`-equality, so it does NOT bridge to the boundary-indexed `BrauerConv bottomCount` decision
that completeness needs — the free over-approximation is architecturally weaker than the sound relation (the
two-sided-sandwich residual of the literature).  This is precisely why discharging `BrauerExt5CorrectedFoldReaches`
would not, by itself, flip `fxBrauer_hasBrauerV2FullCompleteness`. -/
theorem not_brauerConvFree8_diagramInvariant :
    ¬ (∀ (boundaryCount : Nat) (leftWord rightWord : List BrauerAtom),
        BrauerConvFree8 leftWord rightWord →
          brauerDiagramOf boundaryCount leftWord = brauerDiagramOf boundaryCount rightWord) :=
  fun invariant => cupSlide_diagram_notSoundAtBoundaryZero
    (invariant 0 [cupAt 0, crossingAt 1] [cupAt 1, crossingAt 0] brauerConvFree8_cupSlide_derivable)

/-! ## C — the committed census extension (named enumerators + frozen `#eval` pins)

Every statistic is an `#eval` over the r51 committed defs (`capFreeSingleCupWords`, `singleCupWords`,
`countRepresentativesRealizing`, `representativeRealizesOwnDiagram`) extended with the guard defs above.  Re-run by
`lake build` of this module. -/

/-- The number of cap-free single-cup words whose positionsFit guard HOLDS yet whose representative FAILS to realise its
own diagram — the guard-soundness census.  `0` everywhere on the cap-free arena means the guard is SOUND: it entails
realisation (the scoped fold's precondition is diagram-consistent). -/
def capFreeGuardHoldsRealizeFailCount (bottomCount wordLength posRange : Nat) : Nat :=
  ((capFreeSingleCupWords wordLength posRange).filter (fun word =>
      hasBoundaryRoomForPositions bottomCount word
        && not (representativeRealizesOwnDiagram bottomCount word))).length

/-- The number of with-cap single-cup words whose representative FAILS to realise its own diagram — the two-sided
sandwich complement (the `s' ≠ id` cap-arc words the cup-only extractor misses). -/
def withCapRepresentativeFailCount (bottomCount wordLength posRange : Nat) : Nat :=
  (singleCupWords wordLength posRange).length
    - countRepresentativesRealizing bottomCount (singleCupWords wordLength posRange)

/-! ### CAP-FREE TOTALITY — the r51 census reproduced (len 3/4) and EXTENDED to len 5 -/

-- Reproduce the r51 cap-free pins (continuity).
#eval countRepresentativesRealizing 6 (capFreeSingleCupWords 3 5)   -- 375  (= 375/375)
#eval countRepresentativesRealizing 6 (capFreeSingleCupWords 4 5)   -- 2500 (= 2500/2500)
-- NEW: the length-5 cap-free arena is 100% total (15625/15625).
#eval (capFreeSingleCupWords 5 5).length                            -- 15625
#eval countRepresentativesRealizing 6 (capFreeSingleCupWords 5 5)   -- 15625 (= 15625/15625)

/-! ### THE NARROW-BOUNDARY SWEEP — the positionsFit guard quantified (cap-free len 3, 375 words) -/

-- Coverage rises with the boundary and SATURATES at b = 6 = maxCrossingPosition (4) + 2 = posRange (5) + 1.
#eval countRepresentativesRealizing 2 (capFreeSingleCupWords 3 5)   -- 65
#eval countRepresentativesRealizing 3 (capFreeSingleCupWords 3 5)   -- 140
#eval countRepresentativesRealizing 4 (capFreeSingleCupWords 3 5)   -- 245
#eval countRepresentativesRealizing 5 (capFreeSingleCupWords 3 5)   -- 305
#eval countRepresentativesRealizing 6 (capFreeSingleCupWords 3 5)   -- 375  (saturated)
#eval countRepresentativesRealizing 7 (capFreeSingleCupWords 3 5)   -- 375  (stays full)

-- THE GUARD IS SOUND: no cap-free word with room-for-positions ever fails to realise (0 at every boundary).
#eval capFreeGuardHoldsRealizeFailCount 2 3 5   -- 0
#eval capFreeGuardHoldsRealizeFailCount 3 3 5   -- 0
#eval capFreeGuardHoldsRealizeFailCount 4 3 5   -- 0
#eval capFreeGuardHoldsRealizeFailCount 5 3 5   -- 0
#eval capFreeGuardHoldsRealizeFailCount 6 3 5   -- 0
#eval capFreeGuardHoldsRealizeFailCount 6 4 5   -- 0  (length 4 too, 2500 words)

/-! ### THE WITH-CAP FAILURE CLASS — grows with length (the two-sided-sandwich complement) -/

-- r51 pin reproduced: 75 of 1500 fail at len 3.
#eval withCapRepresentativeFailCount 6 3 5   -- 75
-- NEW: the failure fraction grows to 3500 of 20000 (17.5%) at len 4.
#eval (singleCupWords 4 5).length                            -- 20000
#eval countRepresentativesRealizing 6 (singleCupWords 4 5)   -- 16500 (of 20000)
#eval withCapRepresentativeFailCount 6 4 5                   -- 3500

/-! ## D — the cap-side defect autopsy (the ∗-dual cap-side inversion gap)

The three with-cap failures `[capAt k, crossingAt 3, cupAt 0]` (k = 0, 1, 2) at `bottomCount = 6` — a cap arc, a
through-region crossing, and a cup — realise a DIFFERENT `partner` than their representative.  Structural cause: the
crossing is entangled with the cap in the through/middle region, but the corrected extractor inverts only the cup/top
side.  The cap/bottom side lacks the ∗-dual inversion, so the representative's `bottomPerm`/`middle` read-off
reproduces the wrong conjugate.  These `bottomCount 6 + 7 = 13` boundary-size cases lie well beyond the extractor's
honest "empirically total up to boundary size 8" range, so they do NOT contradict the size-8 claim; they localise the
∗-dual read-off incompleteness precisely. -/

/-- ★ **Cap-side defect at cap slot 0.**  `[capAt 0, crossingAt 3, cupAt 0]` reads `partner
[1,0,8,9,10,12,7,6,2,3,4,0,5]`, but its representative reads `partner [1,0,8,9,10,11,12,0,2,3,4,5,6]` — a different
diagram.  The representative does NOT realise this word's diagram. -/
theorem capSideDefect_atCapSlot0 :
    brauerDiagramOf 6 [capAt 0, crossingAt 3, cupAt 0]
      ≠ brauerDiagramOf 6 (classRepresentativeOf 6 [capAt 0, crossingAt 3, cupAt 0]) := by decide

/-- ★ **Cap-side defect at cap slot 1** — the same ∗-dual read-off gap one slot over. -/
theorem capSideDefect_atCapSlot1 :
    brauerDiagramOf 6 [capAt 1, crossingAt 3, cupAt 0]
      ≠ brauerDiagramOf 6 (classRepresentativeOf 6 [capAt 1, crossingAt 3, cupAt 0]) := by decide

/-- ★ **Cap-side defect at cap slot 2** — the third witness of the cap-side inversion gap. -/
theorem capSideDefect_atCapSlot2 :
    brauerDiagramOf 6 [capAt 2, crossingAt 3, cupAt 0]
      ≠ brauerDiagramOf 6 (classRepresentativeOf 6 [capAt 2, crossingAt 3, cupAt 0]) := by decide

/-! ## Idempotence of the representative — a COROLLARY of realization (structural, no `decide`) -/

/-- ★ **The representative is idempotent wherever it realises its own diagram.**  Since `classRepresentativeOf` depends
only on the diagram (`classRepresentativeOf_dependsOnDiagram`, the Bergman/Jones uniqueness `congrArg`), if the
representative realises the word's diagram then re-representing it returns it unchanged — it is a genuine normal form.
On the cap-free arena realisation is total (§C), so the representative is idempotent there everywhere; this generalises
the r51 single-witness `straddleRepresentativeIsFixedPoint` to the whole arena via one structural lemma. -/
theorem representativeIdempotent_ofDiagramEq (bottomCount : Nat) (word : List BrauerAtom)
    (diagramEq : brauerDiagramOf bottomCount (classRepresentativeOf bottomCount word)
      = brauerDiagramOf bottomCount word) :
    classRepresentativeOf bottomCount (classRepresentativeOf bottomCount word)
      = classRepresentativeOf bottomCount word :=
  classRepresentativeOf_dependsOnDiagram bottomCount (classRepresentativeOf bottomCount word) word diagramEq

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the CORRECTED-FOLD CAP-FREE SCOPING ships.**  The scoped fold target
`BrauerExt5CorrectedFoldReachesCapFree` names the honest arena (cap-free + single-cup + positionsFit); the census
extends to length 5 (`15625/15625` total, guard sound with 0 failures) and quantifies the narrow-boundary degeneracy
(saturation at `bottomCount = maxCrossingPosition + 2`); the with-cap failure class is measured (`3500/20000` at len 4)
and autopsied as the ∗-dual cap-side inversion gap (three pinned witnesses); the representative's idempotence is a
structural corollary of realization; and the free-vs-genuine relation gap is machine-checked
(`not_brauerConvFree8_diagramInvariant`).  All zero-axiom, purely additive over the r29–r51 family.  `= true`. -/
def fxBrauer_hasCorrectedFoldCapFreeScope : Bool := true

/-- **Honesty WALL marker — the UNCONDITIONAL fold is NOT discharged; the census sharpens WHY (the EIGHTH honest
zero-flip).**  `BrauerExt5CorrectedFoldReaches` (`WiringDescCorrectedFold.lean:52`) is refuted-once-bridged on the
with-cap arena (the extractor's cup-only inversion misses `3500/20000` cap-arc words at len 4) AND, even on words it
covers, its free `BrauerConvFree8`-conclusion does not bridge to the genuine boundary-indexed `BrauerConv` decision
(`not_brauerConvFree8_diagramInvariant`).  So `fxBrauer_hasCorrectedFoldDischarged` (`WiringDescCorrectedFold.lean:137`)
STAYS `false`; the R3-A totality roundtrip PROOF (`fxBrauer_hasExt5CorrectedRoundtripProof`) and R3-B inner descent
(`fxBrauer_hasStagedInnerDescentDischarged`) STAY `false`; the two dispatch flags
(`fxBrauer_hasRegionDriverTotalDispatch`: totality synthesis over `classifyFirstCupNeighbour`;
`fxBrauer_hasSingleCupTotalDecision`: the working-region-factored `cupHasArrived` + the `bottomCount = 0` loop route)
STAY `false`; and the completeness masters (`fxBrauer_hasBrauerV2FullCompleteness`, `fxBrauer_hasBrauerCompleteness`,
multi-cup) STAY `false`.  A route / measure / architectural gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm
2.6).  `= false`. -/
def fxBrauer_hasCorrectedFoldCapFreeDischarged : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r52 corrected-fold cap-free scoping terminal state — MACHINE-CHECKED (the EIGHTH honest
zero-flip).**  The cap-free scoping marker is `true` on top of the r51 class-representative re-adjudication, the
cup-touching criterion amendment, and the shipped corrected fold reduction; the cap-free-scope discharge, the
corrected-fold discharge, the class-representative discharge, the two dispatch flip flags, WALL A, the staged inner
descent, and the two completeness masters ALL STAY `false`.  Every relevant flag is pinned same-commit; no flag flips
on the old, the amended, or the cap-free-scoped criterion.  A `rfl`-conjunction the kernel checks; purely additive. -/
theorem fxBrauer_correctedFoldCapFreeScopeTerminalState :
    fxBrauer_hasCorrectedFoldCapFreeScope = true
      ∧ fxBrauer_hasClassRepresentativeReadjudication = true
      ∧ fxBrauer_hasCupTouchingCriterionAmendment = true
      ∧ fxBrauer_hasCorrectedFoldReduction = true
      ∧ fxBrauer_hasCorrectedFoldCapFreeDischarged = false
      ∧ fxBrauer_hasCorrectedFoldDischarged = false
      ∧ fxBrauer_hasClassRepresentativeDischarged = false
      ∧ fxBrauer_hasRegionDriverTotalDispatch = false
      ∧ fxBrauer_hasSingleCupTotalDecision = false
      ∧ fxBrauer_hasSingleCupPeelDischarged = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph
