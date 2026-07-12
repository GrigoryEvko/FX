import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupTouchingIrreducible
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCorrectedFold

/-! # BRAUER r51 — THE CLASS-REPRESENTATIVE RE-ADJUDICATION: the committed reproducible census + the
(i,j)-representative family named + the corrected-criterion coverage

r50 (`Brauer/WiringDescCupTouchingIrreducible.lean`) proved the STRAW criterion "cup at slot, ZERO cup-touching
crossings" UNREACHABLE for the majority of single-cup survivors, and jammed the straddle drive at the cup-touching
residue `[cupAt 1, crossingAt 0]`.  This round re-adjudicates: that residue is NOT a failure but an ARRIVAL at the
CORRECTED extended-standard-form representative of its own diagram — the shipped `correctedFold_straddle_reaches`
(`WiringDescCorrectedFold.lean`) proves it reaches `[cupAt 1, crossingAt 0]` by one cup-slide.  The flip criterion the
r50 autopsy refuted was the wrong target; the right target is the class representative, which the residue already IS.

## The representative family (Kudryavtseva–Mazorchuk / walled-Brauer two-sided normal form)

Kudryavtseva–Mazorchuk (arXiv:math/0511730, Lemma 22 / Cor. 21) print every Brauer monoid element as a SANDWICH
`x = u . e_{i1,j1} ... e_{ik,jk}` — a permutation `u` times a product of `k` cup-cap idempotents, each cup-idempotent
being the adjacent generator conjugated by a permutation `e_{i,j} = v^{-1} e_{1,2} v` routing the leg pair `{1,2}` to
`{i,j}`.  The walled-Brauer normal form (arXiv:1912.12869, eq. 1.8) prints the two-sided `SL . D . SR` — a
symmetric-group word, the fixed cup/cap generators, a symmetric-group word — with a UNIQUE word per basis element
(Bergman's diamond lemma).  For a SINGLE cup (`k = 1`) this is `u . e_{i,j}`: the cup slid to its nested slot times a
reduced permutation word routing the leg.

FX already realises exactly this factorisation: `standardFormWordExt5 form` emits
`crossingWord bottomPerm ++ capWord capBlock ++ crossingWord middle ++ cupWord cupBlock ++ crossingWord topPerm ++
circleWord loops` (`WiringDescArcExtractor.lean`) — the two-sided `w_L . (cups/caps) . w_R` printed form — and
`reconstructStandardFormExt5Corrected` reads a `DiagramType` back into that 5-block form.  So the representative of a
word is the shipped composition
`classRepresentativeOf b word = standardFormWordExt5 (reconstructStandardFormExt5Corrected (brauerDiagramOf b word))`,
and its well-definedness (the Bergman/Jones uniqueness: one word per class) is `congrArg`: the representative depends
ONLY on the diagram (`classRepresentativeOf_dependsOnDiagram`).

## What SHIPS (each zero-axiom, structural; every census statistic is a NAMED def with an `#eval` pin)

  * ★★ **THE COMMITTED CENSUS** (§A) — named computable enumerators over the shipped alphabet:
    `singleCupWords` (the population), `capFreeSingleCupWords` (the survivor arena), the classifier split
    `countWordsOfKind`, and the coverage `countRepresentativesRealizing`.  Every statistic cited below is FROZEN as an
    `#eval` output — the counts re-run from the committed tree.  The population counts reproduce the r50 prose
    (`singleCupWords 3 5 = 1500`, `4 5 = 20000`); the r50 "77/485 survivor" sub-counts do NOT reproduce (they were a
    prose redex-irreducibility filter never committed) — this file cites only what its defs compute.

  * ★★ **THE (i,j)-REPRESENTATIVE FAMILY** (§B) — `classRepresentativeOf` as the named sandwich composition, its
    diagram-only well-definedness, the shipped straddle arrival re-exported, and the machine-checked pin that the r50
    jam residue `[cupAt 1, crossingAt 0]` IS the straddle class's representative and realises its own diagram
    (well-definedness / at-representative probe).

  * ★ **THE COVERAGE** (§C) — the corrected extractor roundtrips (representative realises its own diagram) for EVERY
    cap-free single-cup word at a non-degenerate boundary: `375/375` at length 3, `2500/2500` at length 4 (frozen
    `#eval`).  The honest boundary: with-cap single-cup diagrams are NOT all total (`1425/1500`) — the extractor's
    `topPerm` read-off is exact on the cap-free arena, incomplete on cap-arcs.

## The honest residual

This file names the representative and the census; it does NOT discharge `BrauerExt5CorrectedFoldReaches`
unconditionally (the R3-A totality roundtrip PROOF + the R3-B inner descent — the r52 target).  Every flip flag and
completeness master STAYS `false`; the amended flip law lives in
`WiringDescCupTouchingCriterionAmendment.lean`.  A route / measure gap, never a truth gap (Lehrer–Zhang
arXiv:1207.5889 Thm 2.6).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin + an independent `#print axioms` witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the committed reproducible census (named enumerators + frozen `#eval` pins) -/

/-- Is this atom a cup? (input block empty — the cup allocates a fresh connected pair). -/
def isCupBrauerAtom (atom : BrauerAtom) : Bool :=
  match atom.wiring.inputCount with
  | 0 => true
  | _ + 1 => false

/-- Is this atom a cap? (output block empty — the cap closes a pair). -/
def isCapBrauerAtom (atom : BrauerAtom) : Bool := Nat.beq atom.wiring.outputCount 0

/-- The number of cup atoms in a word (structural fold). -/
def cupCountOfWord : List BrauerAtom → Nat
  | [] => 0
  | atom :: rest => (cond (isCupBrauerAtom atom) 1 0) + cupCountOfWord rest

/-- Does the word carry exactly one cup? (the single-cup census predicate). -/
def hasExactlyOneCup (word : List BrauerAtom) : Bool := Nat.beq (cupCountOfWord word) 1

/-- Is the word cap-free? (no cap atom anywhere — the r48/r50 survivor arena is single cup + crossings). -/
def isCapFreeWord : List BrauerAtom → Bool
  | [] => true
  | atom :: rest => cond (isCapBrauerAtom atom) false (isCapFreeWord rest)

/-- The census alphabet at a given position range: `{cup, crossing, cap}` at each position `0 .. posRange-1`. -/
def censusAlphabet (posRange : Nat) : List BrauerAtom :=
  (List.range posRange).foldr (fun position atoms => cupAt position :: crossingAt position :: capAt position :: atoms) []

/-- Every word of a fixed length over the census alphabet (structural on the length). -/
def censusWordsOfLength (wordLength : Nat) (alphabet : List BrauerAtom) : List (List BrauerAtom) :=
  match wordLength with
  | 0 => [[]]
  | shorter + 1 =>
      (censusWordsOfLength shorter alphabet).flatMap (fun word => alphabet.map (fun atom => atom :: word))

/-- ★ **The single-cup population** — length-`wordLength` words over the `posRange`-alphabet with exactly one cup. -/
def singleCupWords (wordLength posRange : Nat) : List (List BrauerAtom) :=
  (censusWordsOfLength wordLength (censusAlphabet posRange)).filter hasExactlyOneCup

/-- ★ **The cap-free single-cup survivor arena** — one cup, the rest crossings. -/
def capFreeSingleCupWords (wordLength posRange : Nat) : List (List BrauerAtom) :=
  (singleCupWords wordLength posRange).filter isCapFreeWord

/-- The move-kind index (a full-enumeration map to `Nat`, propext-free — no wildcard). -/
def regionKindIndex : RegionCupMoveKind → Nat
  | .noCup => 0
  | .cupArrivedAlone => 1
  | .untwist => 2
  | .straddleTerminal => 3
  | .distantCrossing => 4
  | .crossingLeft => 5
  | .snakeLeft => 6
  | .snakeRight => 7
  | .loopHere => 8
  | .distantCap => 9
  | .anotherCup => 10

/-- Do two move kinds agree? (index equality via `Nat.beq`). -/
def regionKindsAgree (left right : RegionCupMoveKind) : Bool :=
  Nat.beq (regionKindIndex left) (regionKindIndex right)

/-- The number of words in a list whose leftmost-cup neighbour classifies to a given move kind. -/
def countWordsOfKind (kind : RegionCupMoveKind) (words : List (List BrauerAtom)) : Nat :=
  (words.filter (fun word => regionKindsAgree (classifyFirstCupNeighbour word) kind)).length

/-! ### The census statistics — FROZEN `#eval` outputs (re-run: `lake build` this module) -/

-- POPULATION (single-cup words, caps allowed) — reproduces the r50 prose population counts.
#eval (singleCupWords 3 5).length          -- 1500
#eval (singleCupWords 4 5).length          -- 20000

-- CAP-FREE SURVIVOR ARENA (one cup + crossings) — 375 = 3 slots * 5 cup-pos * 5^2 crossings.
#eval (capFreeSingleCupWords 3 5).length   -- 375
#eval (capFreeSingleCupWords 4 5).length   -- 2500

-- CLASS SPLIT over the cap-free length-3 arena (sums to 375; the leg-adjacent mirror pair is equinumerous 40 = 40).
#eval countWordsOfKind RegionCupMoveKind.cupArrivedAlone (capFreeSingleCupWords 3 5)   -- 125
#eval countWordsOfKind RegionCupMoveKind.untwist (capFreeSingleCupWords 3 5)           -- 50
#eval countWordsOfKind RegionCupMoveKind.straddleTerminal (capFreeSingleCupWords 3 5)  -- 40
#eval countWordsOfKind RegionCupMoveKind.crossingLeft (capFreeSingleCupWords 3 5)      -- 40
#eval countWordsOfKind RegionCupMoveKind.distantCrossing (capFreeSingleCupWords 3 5)   -- 120

/-! ## B — the (i,j)-representative family + its diagram-only well-definedness -/

/-- ★★ **THE CLASS REPRESENTATIVE — the shipped two-sided sandwich, named.**  `classRepresentativeOf b word` reads the
word's `brauerDiagramOf` diagram back into the corrected 5-block extended standard form and realises it: the
Kudryavtseva–Mazorchuk `u . e_{i,j}` printed form (a reduced permutation word `topPerm` times the cup at its nested
slot `cupBlock`), the walled-Brauer `w_L . (cups) . w_R` (arXiv:1912.12869 eq. 1.8), specialised to a single cup.  Its
correctness `BrauerConvFree8 word (classRepresentativeOf b word)` is EXACTLY the shipped open predicate
`BrauerExt5CorrectedFoldReaches` (r52 target). -/
def classRepresentativeOf (bottomCount : Nat) (word : List BrauerAtom) : List BrauerAtom :=
  standardFormWordExt5 (reconstructStandardFormExt5Corrected (brauerDiagramOf bottomCount word))

/-- ★★ **Well-definedness (Bergman/Jones uniqueness: one word per class).**  The representative depends ONLY on the
diagram: two words with equal `brauerDiagramOf` diagram get the SAME representative — by `congrArg`, so
`classRepresentativeOf` is a genuine function of the class, not the word. -/
theorem classRepresentativeOf_dependsOnDiagram
    (bottomCount : Nat) (wordLeft wordRight : List BrauerAtom)
    (diagramEq : brauerDiagramOf bottomCount wordLeft = brauerDiagramOf bottomCount wordRight) :
    classRepresentativeOf bottomCount wordLeft = classRepresentativeOf bottomCount wordRight :=
  congrArg (fun diagram => standardFormWordExt5 (reconstructStandardFormExt5Corrected diagram)) diagramEq

/-- ★★ **THE r50 JAM RESIDUE IS THE STRADDLE CLASS'S REPRESENTATIVE.**  The straddle word `[cupAt 0, crossingAt 1]`
(the exact move r1's `arcMeasure` resisted) has representative `[cupAt 1, crossingAt 0]` — LITERALLY the r50 jam
residue.  The r50 "jam" is an ARRIVAL at the corrected standard form; machine-checked by `decide`, matching the shipped
`correctedFold_straddle_reaches` target pin. -/
theorem straddleRepresentativeIsJamResidue :
    classRepresentativeOf 1 [cupAt 0, crossingAt 1] = [cupAt 1, crossingAt 0] := by decide

/-- ★ **The shipped straddle ARRIVAL, re-exported under the corrected criterion.**  `[cupAt 0, crossingAt 1]`
`BrauerConvFree8`-reaches its class representative via a single cup-slide — the fold `BrauerExt5CorrectedFoldReaches`
instantiated and DISCHARGED on the straddle class.  This is the r50 "jam", re-read as the drive reaching the
representative. -/
theorem straddleReachesItsRepresentative :
    BrauerConvFree8 [cupAt 0, crossingAt 1]
      (standardFormWordExt5 (reconstructStandardFormExt5Corrected (brauerDiagramOf 1 [cupAt 0, crossingAt 1]))) :=
  correctedFold_straddle_reaches

/-! ## C — the coverage: does the representative realise its own diagram? (the R3-A totality probe, empirically) -/

/-- Monadic list-`Nat` equality (monomorphic, full-enumeration — propext-free per the corpus). -/
def natListBeq : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | leftHead :: leftRest, rightHead :: rightRest => Nat.beq leftHead rightHead && natListBeq leftRest rightRest

/-- Diagram equality by field comparison (propext-free — no `decide` on the derived instance). -/
def diagramBeq (left right : DiagramType) : Bool :=
  Nat.beq left.bottomCount right.bottomCount
    && Nat.beq left.topCount right.topCount
    && natListBeq left.partner right.partner
    && Nat.beq left.loops right.loops

/-- ★ **Does the representative realise its own diagram?**  `true` when `classRepresentativeOf b word` induces the SAME
`brauerDiagramOf` diagram as `word` — the empirical R3-A totality roundtrip check (`standardFormDiagramExt5
(reconstruct d) = d`). -/
def representativeRealizesOwnDiagram (bottomCount : Nat) (word : List BrauerAtom) : Bool :=
  diagramBeq (brauerDiagramOf bottomCount (classRepresentativeOf bottomCount word))
    (brauerDiagramOf bottomCount word)

/-- The number of words whose representative realises its own diagram. -/
def countRepresentativesRealizing (bottomCount : Nat) (words : List (List BrauerAtom)) : Nat :=
  (words.filter (representativeRealizesOwnDiagram bottomCount)).length

/-- ★★ **The r50 jam residue realises its own diagram** (the well-definedness / at-representative probe): the straddle's
representative is a genuine class representative — machine-checked `= true`. -/
theorem straddleRepresentativeRealizes :
    representativeRealizesOwnDiagram 1 [cupAt 0, crossingAt 1] = true := by decide

/-- ★ **The straddle representative is a fixed point of the representative map** (idempotence = at-representative):
`classRepresentativeOf` applied to the representative returns it unchanged.  Machine-checked `by decide`. -/
theorem straddleRepresentativeIsFixedPoint :
    classRepresentativeOf 1 (classRepresentativeOf 1 [cupAt 0, crossingAt 1])
      = classRepresentativeOf 1 [cupAt 0, crossingAt 1] := by decide

/-! ### The coverage statistics — FROZEN `#eval` outputs (boundary `b = 6` is non-degenerate for `posRange 5`) -/

-- CAP-FREE ARENA: EVERY word's representative realises its own diagram at a non-degenerate boundary — 100% coverage.
#eval countRepresentativesRealizing 6 (capFreeSingleCupWords 3 5)   -- 375  (= full arena, 375/375)
#eval countRepresentativesRealizing 6 (capFreeSingleCupWords 4 5)   -- 2500 (= full arena, 2500/2500)

-- THE HONEST BOUNDARY: with-cap single-cup diagrams are NOT all total — the extractor's read-off is incomplete on
-- cap-arcs (75 of 1500 fail even at the wide boundary).
#eval countRepresentativesRealizing 6 (singleCupWords 3 5)          -- 1425 (of 1500)

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the class-representative re-adjudication SHIPS.**  The committed census (`singleCupWords`,
`capFreeSingleCupWords`, `countWordsOfKind`, `countRepresentativesRealizing`) makes every cited statistic reproducible;
the (i,j)-representative family (`classRepresentativeOf`) is named as the shipped two-sided sandwich with diagram-only
well-definedness (`classRepresentativeOf_dependsOnDiagram`); the r50 jam residue is proved to BE the straddle class's
representative (`straddleRepresentativeIsJamResidue`), realising its own diagram
(`straddleRepresentativeRealizes`); and the coverage is `375/375` (len 3) / `2500/2500` (len 4) on the cap-free arena
at a non-degenerate boundary.  All zero-axiom.  `= true`. -/
def fxBrauer_hasClassRepresentativeReadjudication : Bool := true

/-- **Honesty WALL marker — the census does NOT flip any master; `BrauerExt5CorrectedFoldReaches` is NOT discharged.**
The census confirms coverage on the cap-free arena empirically, but the unconditional fold (R3-A totality roundtrip
PROOF + R3-B inner descent) is NOT proven, and the with-cap arena is not even empirically total (`1425/1500`).  So the
flip flags `fxBrauer_hasRegionDriverTotalDispatch` / `fxBrauer_hasSingleCupTotalDecision`, WALL A
`fxBrauer_hasSingleCupPeelDischarged`, `fxBrauer_hasCorrectedFoldDischarged`, and the completeness masters ALL STAY
`false` (the amended flip law is recorded in `WiringDescCupTouchingCriterionAmendment.lean`).  `= false`. -/
def fxBrauer_hasClassRepresentativeDischarged : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r51 class-representative re-adjudication terminal state — MACHINE-CHECKED.**  The re-adjudication
marker is `true` on top of the shipped corrected fold (`fxBrauer_hasCorrectedFoldReduction = true`) and the r50
cup-touching irreducibility (`fxBrauer_hasCupTouchingIrreducibility = true`), while the corrected-fold discharge, the
two dispatch flip flags, WALL A, the inner-descent / straightening masters, and the two completeness masters ALL STAY
`false`.  A `rfl`-conjunction the kernel checks; purely additive, no master flip fabricated. -/
theorem fxBrauer_classRepresentativeReadjudicationTerminalState :
    fxBrauer_hasClassRepresentativeReadjudication = true
      ∧ fxBrauer_hasCorrectedFoldReduction = true
      ∧ fxBrauer_hasCupTouchingIrreducibility = true
      ∧ fxBrauer_hasClassRepresentativeDischarged = false
      ∧ fxBrauer_hasCorrectedFoldDischarged = false
      ∧ fxBrauer_hasRegionDriverTotalDispatch = false
      ∧ fxBrauer_hasSingleCupTotalDecision = false
      ∧ fxBrauer_hasSingleCupPeelDischarged = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph
