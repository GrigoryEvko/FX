import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBoundaryPartnered
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescPartnerReadOff

/-! # BRAUER-MIDDLE r12 — the partner-TOTALITY FOLD: `boundaryPartnered` survives the whole `processBrauer` fold

r11 shipped the partner-totality invariant (`boundaryPartnered`, `Brauer/WiringDescBoundaryPartnered.lean`) and its
SEED base case, plus the extraction READ-OFF (`partnerIndexOf_reads_matchingPartner`, uniqueness) over any
T-DISJOINT state.  What remained is the EXISTENCE fold: that partner-totality is preserved by every Brauer atom and
therefore holds at every reachable state of a well-formed word.  This file ships that fold, mirroring the r10
T-DISJOINT template (`Brauer/WiringDescBoundedBoundaryFold.lean`).

The three per-atom preservations (each riding SHIPPED node-level infrastructure — no new bridges):

  * ★ **`boundaryPartnered_stepCup`** — the CUP splices a fresh 2-element component and shifts old indices up by
    two through `capBoundaryReindex`.  A probe reading a fresh leg partners the OTHER fresh leg (they are joined);
    a probe reading an old node inherits its old partner through the fresh-inert join (`cupJoin_inert_oldBBC`).

  * ★ **`boundaryPartnered_stepCrossing`** — the CROSSING relabels the two window reads by the involutive window
    transposition `crossingReindexBBC`.  The post-crossing partner is the transposition-conjugate of the old
    partner, via the shipped pullback `matchingSameComponent_stepCrossing_reindexBBC` — a bijective relabel.

  * ★ **`boundaryPartnered_stepCap`** — THE pole.  The cap merges the two window ports and drops them; the
    post-cap view factors as the single boundary join (`isSameComponent_unionFindJoin`) over the reindexed reads.
    A probe whose old partner is a SURVIVOR keeps it (disjunct 1); a probe whose old partner is a CAPPED PORT `L`
    (resp. `R`) is repaired by the OTHER port's partner `y := partner(R)` (resp. `x := partner(L)`) — the
    `x`-partners-`y` derangement composition — firing disjunct 2 (resp. 3).  Both repair-partners exist because
    partner-totality holds at BOTH ports `L`, `R`; the survivor is distinct from either port by the T-DISJOINT
    forbidden triple.  So `bounded ∧ boundaryPartnered` (= exactly-2, a perfect matching) is threaded together.

The fold lift `boundaryPartnered_processBrauer` threads all three (with `boundedBoundaryComponents` alongside — the
cap totality's other input) over `WellFormedBrauerFold`, and `boundaryPartnered_reachable` reads the payoff off the
seed.  The universal read-off corollary `partnerIndexOf_readsPartner_reachable` combines totality with the r11
uniqueness read-off: at EVERY boundary index of EVERY well-formed fold output, `partnerIndexOf` reads a genuine
distinct same-component partner — hypothesis-free modulo the fold premises.

This flips `fxBrauer_hasBoundaryPartneredFold` (r11's residual, now `true`).  It does NOT flip the masters
`fxBrauer_hasTagCorrDisjoint` / `fxBrauer_hasTagCorrExtraction`: those additionally need the read-off WIRED to a
specific diagram `d` over the six-phase standard-form word — T-ENUM (its own round) + T-CLOSE.  Those stay
honestly `false`; #2013 does NOT close.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Boolean triple-disjunction closers (propext-free `Bool` skeleton) -/

/-- The left disjunct of a left-nested triple `||` forces the whole to `true`. -/
private theorem orTripleOfLeftBP {leftTerm middleTerm rightTerm : Bool} (leftTrue : leftTerm = true) :
    ((leftTerm || middleTerm) || rightTerm) = true := by rw [leftTrue, Bool.true_or, Bool.true_or]

/-- The middle disjunct of a left-nested triple `||` forces the whole to `true`. -/
private theorem orTripleOfMidBP {leftTerm middleTerm rightTerm : Bool} (middleTrue : middleTerm = true) :
    ((leftTerm || middleTerm) || rightTerm) = true := by rw [middleTrue, Bool.or_true, Bool.true_or]

/-- The right disjunct of a left-nested triple `||` forces the whole to `true`. -/
private theorem orTripleOfRightBP {leftTerm middleTerm rightTerm : Bool} (rightTrue : rightTerm = true) :
    ((leftTerm || middleTerm) || rightTerm) = true := by rw [rightTrue, Bool.or_true]

/-! ## Same-component symmetry / transitivity at the boundary matching view -/

/-- The boundary same-component matching is symmetric (a `dsimp`-thin wrapper of `isSameComponent_symm`). -/
private theorem matchingSameComponent_symmBP (bottomCount : Nat) (state : WireState) (indexA indexB : Nat) :
    matchingSameComponent bottomCount state indexA indexB
      = matchingSameComponent bottomCount state indexB indexA := by
  show isSameComponent state.links (natListGetAt (matchingBoundaryNodes bottomCount state) indexA)
        (natListGetAt (matchingBoundaryNodes bottomCount state) indexB)
      = isSameComponent state.links (natListGetAt (matchingBoundaryNodes bottomCount state) indexB)
        (natListGetAt (matchingBoundaryNodes bottomCount state) indexA)
  exact isSameComponent_symm state.links _ _

/-- The boundary same-component matching is transitive (a `dsimp`-thin wrapper of `isSameComponent_trans`). -/
private theorem matchingSameComponent_transBP (bottomCount : Nat) (state : WireState) (indexA indexB indexC : Nat)
    (hAB : matchingSameComponent bottomCount state indexA indexB = true)
    (hBC : matchingSameComponent bottomCount state indexB indexC = true) :
    matchingSameComponent bottomCount state indexA indexC = true :=
  isSameComponent_trans state.links
    (natListGetAt (matchingBoundaryNodes bottomCount state) indexA)
    (natListGetAt (matchingBoundaryNodes bottomCount state) indexB)
    (natListGetAt (matchingBoundaryNodes bottomCount state) indexC) hAB hBC

/-! ## THE CAP preservation -/

/-- The post-cap boundary same-component view, as a flat disjunction over the reindexed reads: the single boundary
join of the two window ports (`stepCap_links_eq_unionFindJoin_boundaryReads`) expands
(`isSameComponent_unionFindJoin`) at the `capBoundaryReindex`-shifted survivor reads. -/
private theorem capViewBP (bottomCount : Nat) (state : WireState) (position newI newJ : Nat)
    (forest : isUnionFindForest state.links)
    (windowInRange : position + 2 ≤ state.openWires.length) :
    matchingSameComponent bottomCount (stepCap state position) newI newJ
      = (matchingSameComponent bottomCount state
            (capBoundaryReindex bottomCount position newI) (capBoundaryReindex bottomCount position newJ)
         || (matchingSameComponent bottomCount state (bottomCount + position)
                (capBoundaryReindex bottomCount position newI)
             && matchingSameComponent bottomCount state (bottomCount + (position + 1))
                (capBoundaryReindex bottomCount position newJ))
         || (matchingSameComponent bottomCount state (bottomCount + position)
                (capBoundaryReindex bottomCount position newJ)
             && matchingSameComponent bottomCount state
                (capBoundaryReindex bottomCount position newI) (bottomCount + (position + 1)))) := by
  show isSameComponent (stepCap state position).links
        (natListGetAt (matchingBoundaryNodes bottomCount (stepCap state position)) newI)
        (natListGetAt (matchingBoundaryNodes bottomCount (stepCap state position)) newJ)
      = (isSameComponent state.links
            (natListGetAt (matchingBoundaryNodes bottomCount state) (capBoundaryReindex bottomCount position newI))
            (natListGetAt (matchingBoundaryNodes bottomCount state) (capBoundaryReindex bottomCount position newJ))
         || (isSameComponent state.links
                (natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + position))
                (natListGetAt (matchingBoundaryNodes bottomCount state) (capBoundaryReindex bottomCount position newI))
             && isSameComponent state.links
                (natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + (position + 1)))
                (natListGetAt (matchingBoundaryNodes bottomCount state) (capBoundaryReindex bottomCount position newJ)))
         || (isSameComponent state.links
                (natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + position))
                (natListGetAt (matchingBoundaryNodes bottomCount state) (capBoundaryReindex bottomCount position newJ))
             && isSameComponent state.links
                (natListGetAt (matchingBoundaryNodes bottomCount state) (capBoundaryReindex bottomCount position newI))
                (natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + (position + 1)))))
  rw [stepCap_links_eq_unionFindJoin_boundaryReads bottomCount state position,
    matchingBoundaryNodes_stepCap_getAt_reindex bottomCount state position newI windowInRange,
    matchingBoundaryNodes_stepCap_getAt_reindex bottomCount state position newJ windowInRange,
    isSameComponent_unionFindJoin state.links forest
      (natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + position))
      (natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + (position + 1)))
      (natListGetAt (matchingBoundaryNodes bottomCount state) (capBoundaryReindex bottomCount position newI))
      (natListGetAt (matchingBoundaryNodes bottomCount state) (capBoundaryReindex bottomCount position newJ))]

/-- The cap reindex is SURJECTIVE onto survivors: any old boundary index distinct from the two window ports and in
range has a post-cap new-index preimage under `capBoundaryReindex`.  Subtraction-free — the preimage is produced
additively through `Nat.le.dest`, dodging the `index - 2` propext wall. -/
private theorem capReindexInvBP (bottomCount : Nat) (state : WireState) (position survivorNode : Nat)
    (windowInRange : position + 2 ≤ state.openWires.length)
    (survivorRange : survivorNode < bottomCount + state.openWires.length)
    (neLeft : survivorNode ≠ bottomCount + position)
    (neRight : survivorNode ≠ bottomCount + (position + 1)) :
    ∃ newIndex, newIndex < bottomCount + (stepCap state position).openWires.length
      ∧ capBoundaryReindex bottomCount position newIndex = survivorNode := by
  have lenRel : (stepCap state position).openWires.length + 2 = state.openWires.length :=
    stepCap_openWiresLength state position windowInRange
  cases Nat.lt_or_ge survivorNode (bottomCount + position) with
  | inl belowWindow =>
      refine ⟨survivorNode, ?_, ?_⟩
      · have posLeNew : position ≤ (stepCap state position).openWires.length := by
          have step : position + 2 ≤ (stepCap state position).openWires.length + 2 := by
            rw [lenRel]; exact windowInRange
          exact Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ step)
        exact Nat.lt_of_lt_of_le belowWindow (Nat.add_le_add_left posLeNew bottomCount)
      · show (if survivorNode < bottomCount + position then survivorNode else survivorNode + 2) = survivorNode
        rw [if_pos belowWindow]
  | inr atWindow =>
      have geTwo : bottomCount + position + 2 ≤ survivorNode := by
        rcases Nat.lt_or_ge survivorNode (bottomCount + position + 2) with hlt | hge
        · exfalso
          rcases Nat.lt_or_ge survivorNode (bottomCount + position + 1) with hlt1 | hge1
          · exact neLeft (Nat.le_antisymm (Nat.le_of_lt_succ hlt1) atWindow)
          · have hEq : survivorNode = bottomCount + position + 1 :=
              Nat.le_antisymm (Nat.le_of_lt_succ hlt) hge1
            exact neRight (by rw [hEq, Nat.add_assoc])
        · exact hge
      obtain ⟨gap, hgap⟩ := Nat.le.dest geTwo
      refine ⟨bottomCount + position + gap, ?_, ?_⟩
      · have survEq : bottomCount + position + gap + 2 = survivorNode := by
          rw [Nat.add_right_comm (bottomCount + position) gap 2]; exact hgap
        have ltPlus2 : bottomCount + position + gap + 2
            < bottomCount + ((stepCap state position).openWires.length + 2) := by
          rw [survEq, lenRel]; exact survivorRange
        rw [← Nat.add_assoc bottomCount (stepCap state position).openWires.length 2] at ltPlus2
        exact Nat.lt_of_add_lt_add_right ltPlus2
      · show (if bottomCount + position + gap < bottomCount + position then bottomCount + position + gap
              else bottomCount + position + gap + 2) = survivorNode
        rw [if_neg (Nat.not_lt.mpr (Nat.le_add_right (bottomCount + position) gap)),
          Nat.add_right_comm (bottomCount + position) gap 2]
        exact hgap

/-- Assemble the cap partner from a SURVIVOR of the pre-cap partner search: map the survivor back to a post-cap new
index (`capReindexInvBP`), whose partner-of-probe view (`capViewBP`) is forced true by the supplied disjunct. -/
private theorem capPartnerFromSurvivorBP (bottomCount : Nat) (state : WireState)
    (position probeIndex survivorNode : Nat)
    (forest : isUnionFindForest state.links)
    (windowInRange : position + 2 ≤ state.openWires.length)
    (survivorRange : survivorNode < bottomCount + state.openWires.length)
    (survivorNeLeft : survivorNode ≠ bottomCount + position)
    (survivorNeRight : survivorNode ≠ bottomCount + (position + 1))
    (survivorNeProbeOld : survivorNode ≠ capBoundaryReindex bottomCount position probeIndex)
    (disjunctTrue :
      (matchingSameComponent bottomCount state (capBoundaryReindex bottomCount position probeIndex) survivorNode
       || (matchingSameComponent bottomCount state (bottomCount + position)
              (capBoundaryReindex bottomCount position probeIndex)
           && matchingSameComponent bottomCount state (bottomCount + (position + 1)) survivorNode)
       || (matchingSameComponent bottomCount state (bottomCount + position) survivorNode
           && matchingSameComponent bottomCount state
              (capBoundaryReindex bottomCount position probeIndex) (bottomCount + (position + 1)))) = true) :
    ∃ partnerIndex, partnerIndex < bottomCount + (stepCap state position).openWires.length
      ∧ partnerIndex ≠ probeIndex
      ∧ matchingSameComponent bottomCount (stepCap state position) probeIndex partnerIndex = true := by
  obtain ⟨partnerIndex, partnerRange, partnerImage⟩ :=
    capReindexInvBP bottomCount state position survivorNode windowInRange survivorRange survivorNeLeft survivorNeRight
  refine ⟨partnerIndex, partnerRange, ?_, ?_⟩
  · intro partnerEqProbe
    apply survivorNeProbeOld
    rw [← partnerImage, partnerEqProbe]
  · rw [capViewBP bottomCount state position probeIndex partnerIndex forest windowInRange, partnerImage]
    exact disjunctTrue

/-- ★ **THE CAP preservation of partner-TOTALITY.**  Given T-DISJOINT (`bounded`) and partner-totality
(`partnered`) at the pre-cap state, every post-cap in-range boundary index has a distinct same-component partner.
The probe's pre-cap image `capBoundaryReindex … probeIndex` has a pre-cap partner `w`; if `w` is a SURVIVOR it is
kept (disjunct 1); if `w` is the left port `L` the repair is `partner(R)` (disjunct 2 — the derangement
composition); if `w` is the right port `R` the repair is `partner(L)` (disjunct 3).  Each repair is a genuine
survivor by the T-DISJOINT forbidden triple, and exists because totality holds at BOTH ports. -/
theorem boundaryPartnered_stepCap (bottomCount : Nat) (state : WireState) (position : Nat)
    (forest : isUnionFindForest state.links)
    (windowInRange : position + 2 ≤ state.openWires.length)
    (bounded : boundedBoundaryComponents bottomCount state)
    (partnered : boundaryPartnered bottomCount state) :
    boundaryPartnered bottomCount (stepCap state position) := by
  intro probeIndex probeBelow
  have leftRange : bottomCount + position < bottomCount + state.openWires.length :=
    Nat.add_lt_add_left (Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt (Nat.lt_add_one position)) windowInRange) bottomCount
  have rightRange : bottomCount + (position + 1) < bottomCount + state.openWires.length :=
    Nat.add_lt_add_left (Nat.lt_of_lt_of_le (Nat.lt_add_one (position + 1)) windowInRange) bottomCount
  have lrNe : bottomCount + position ≠ bottomCount + (position + 1) :=
    Nat.ne_of_lt (Nat.add_lt_add_left (Nat.lt_add_one position) bottomCount)
  have probeOldRange : capBoundaryReindex bottomCount position probeIndex < bottomCount + state.openWires.length :=
    capBoundaryReindex_lt_ofNewRange bottomCount state position probeIndex windowInRange probeBelow
  have probeNeL : capBoundaryReindex bottomCount position probeIndex ≠ bottomCount + position :=
    capBoundaryReindex_ne_leftPort bottomCount position probeIndex
  have probeNeR : capBoundaryReindex bottomCount position probeIndex ≠ bottomCount + (position + 1) :=
    capBoundaryReindex_ne_rightPort bottomCount position probeIndex
  obtain ⟨w, wRange, wNe, wShares⟩ :=
    partnered (capBoundaryReindex bottomCount position probeIndex) probeOldRange
  cases Nat.decEq w (bottomCount + position) with
  | isTrue hwL =>
      subst hwL
      -- w = L; the probe's partner was the left port.  Repair via partner(R).
      obtain ⟨y, yRange, yNe, yShares⟩ := partnered (bottomCount + (position + 1)) rightRange
      have yNeL : y ≠ bottomCount + position := by
        intro hyL
        have hLR : matchingSameComponent bottomCount state (bottomCount + position) (bottomCount + (position + 1))
            = true := by
          rw [matchingSameComponent_symmBP bottomCount state (bottomCount + position) (bottomCount + (position + 1)),
            ← hyL]
          exact yShares
        exact bounded (capBoundaryReindex bottomCount position probeIndex) (bottomCount + position)
          (bottomCount + (position + 1)) probeOldRange leftRange rightRange probeNeL probeNeR lrNe
          ⟨wShares, matchingSameComponent_transBP bottomCount state _ _ _ wShares hLR⟩
      have yNeProbeOld : y ≠ capBoundaryReindex bottomCount position probeIndex := by
        intro hy
        exact bounded (capBoundaryReindex bottomCount position probeIndex) (bottomCount + position)
          (bottomCount + (position + 1)) probeOldRange leftRange rightRange probeNeL probeNeR lrNe
          ⟨wShares, by
            rw [matchingSameComponent_symmBP bottomCount state
              (capBoundaryReindex bottomCount position probeIndex) (bottomCount + (position + 1)), ← hy]
            exact yShares⟩
      have disjunctTrue :
          (matchingSameComponent bottomCount state (capBoundaryReindex bottomCount position probeIndex) y
           || (matchingSameComponent bottomCount state (bottomCount + position)
                  (capBoundaryReindex bottomCount position probeIndex)
               && matchingSameComponent bottomCount state (bottomCount + (position + 1)) y)
           || (matchingSameComponent bottomCount state (bottomCount + position) y
               && matchingSameComponent bottomCount state
                  (capBoundaryReindex bottomCount position probeIndex) (bottomCount + (position + 1)))) = true := by
        apply orTripleOfMidBP
        rw [matchingSameComponent_symmBP bottomCount state (bottomCount + position)
            (capBoundaryReindex bottomCount position probeIndex), wShares, Bool.true_and]
        exact yShares
      exact capPartnerFromSurvivorBP bottomCount state position probeIndex y forest windowInRange yRange yNeL yNe
        yNeProbeOld disjunctTrue
  | isFalse hwNotL =>
      cases Nat.decEq w (bottomCount + (position + 1)) with
      | isTrue hwR =>
          subst hwR
          -- w = R; the probe's partner was the right port.  Repair via partner(L).
          obtain ⟨x, xRange, xNe, xShares⟩ := partnered (bottomCount + position) leftRange
          have xNeR : x ≠ bottomCount + (position + 1) := by
            intro hxR
            have hLR : matchingSameComponent bottomCount state (bottomCount + position)
                (bottomCount + (position + 1)) = true := by rw [← hxR]; exact xShares
            have probeOldL : matchingSameComponent bottomCount state
                (capBoundaryReindex bottomCount position probeIndex) (bottomCount + position) = true :=
              matchingSameComponent_transBP bottomCount state _ _ _ wShares (by
                rw [matchingSameComponent_symmBP bottomCount state (bottomCount + (position + 1))
                  (bottomCount + position)]
                exact hLR)
            exact bounded (capBoundaryReindex bottomCount position probeIndex) (bottomCount + position)
              (bottomCount + (position + 1)) probeOldRange leftRange rightRange probeNeL probeNeR lrNe
              ⟨probeOldL, wShares⟩
          have xNeProbeOld : x ≠ capBoundaryReindex bottomCount position probeIndex := by
            intro hx
            have probeOldL : matchingSameComponent bottomCount state
                (capBoundaryReindex bottomCount position probeIndex) (bottomCount + position) = true := by
              rw [matchingSameComponent_symmBP bottomCount state
                (capBoundaryReindex bottomCount position probeIndex) (bottomCount + position), ← hx]
              exact xShares
            exact bounded (capBoundaryReindex bottomCount position probeIndex) (bottomCount + position)
              (bottomCount + (position + 1)) probeOldRange leftRange rightRange probeNeL probeNeR lrNe
              ⟨probeOldL, wShares⟩
          have disjunctTrue :
              (matchingSameComponent bottomCount state (capBoundaryReindex bottomCount position probeIndex) x
               || (matchingSameComponent bottomCount state (bottomCount + position)
                      (capBoundaryReindex bottomCount position probeIndex)
                   && matchingSameComponent bottomCount state (bottomCount + (position + 1)) x)
               || (matchingSameComponent bottomCount state (bottomCount + position) x
                   && matchingSameComponent bottomCount state
                      (capBoundaryReindex bottomCount position probeIndex) (bottomCount + (position + 1)))) = true := by
            apply orTripleOfRightBP
            rw [xShares, Bool.true_and]
            exact wShares
          exact capPartnerFromSurvivorBP bottomCount state position probeIndex x forest windowInRange xRange xNe xNeR
            xNeProbeOld disjunctTrue
      | isFalse hwNotR =>
          -- w is a genuine survivor; it stays the probe's partner.
          have disjunctTrue :
              (matchingSameComponent bottomCount state (capBoundaryReindex bottomCount position probeIndex) w
               || (matchingSameComponent bottomCount state (bottomCount + position)
                      (capBoundaryReindex bottomCount position probeIndex)
                   && matchingSameComponent bottomCount state (bottomCount + (position + 1)) w)
               || (matchingSameComponent bottomCount state (bottomCount + position) w
                   && matchingSameComponent bottomCount state
                      (capBoundaryReindex bottomCount position probeIndex) (bottomCount + (position + 1)))) = true :=
            orTripleOfLeftBP wShares
          exact capPartnerFromSurvivorBP bottomCount state position probeIndex w forest windowInRange wRange hwNotL
            hwNotR wNe disjunctTrue

/-! ## THE CUP preservation -/

/-- The post-cup boundary read at a `capBoundaryReindex`-shifted OLD index IS the pre-cup boundary read at that
index (the additive up-shift dodges the fresh window on both sides). -/
private theorem cupOldReadBP (bottomCount : Nat) (state : WireState) (position index : Nat)
    (indexRange : index < bottomCount + state.openWires.length)
    (positionLe : position ≤ state.openWires.length) :
    natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position))
        (capBoundaryReindex bottomCount position index)
      = natListGetAt (matchingBoundaryNodes bottomCount state) index := by
  cases Nat.lt_or_ge index (bottomCount + position) with
  | inl belowWindow =>
      rw [show capBoundaryReindex bottomCount position index = index from by
            show (if index < bottomCount + position then index else index + 2) = index
            rw [if_pos belowWindow]]
      cases Nat.lt_or_ge index bottomCount with
      | inl belowBottom =>
          exact matchingBoundaryNodes_getAt_bottomAgrees bottomCount (stepCup state position) state index belowBottom
      | inr atLeastBottom =>
          obtain ⟨offset, rfl⟩ := Nat.le.dest atLeastBottom
          exact matchingBoundaryNodes_stepCup_getAt_below bottomCount state position offset
            (Nat.lt_of_add_lt_add_left belowWindow) (Nat.lt_of_add_lt_add_left indexRange)
  | inr atWindow =>
      obtain ⟨offset, rfl⟩ := Nat.le.dest atWindow
      rw [show capBoundaryReindex bottomCount position (bottomCount + position + offset)
              = bottomCount + (position + offset + 2) from by
            show (if bottomCount + position + offset < bottomCount + position then bottomCount + position + offset
                  else bottomCount + position + offset + 2) = bottomCount + (position + offset + 2)
            rw [if_neg (Nat.not_lt.mpr (Nat.le_add_right (bottomCount + position) offset)),
              Nat.add_assoc bottomCount position offset, Nat.add_assoc bottomCount (position + offset) 2],
        show bottomCount + position + offset = bottomCount + (position + offset) from
          Nat.add_assoc bottomCount position offset]
      exact matchingBoundaryNodes_stepCup_getAt_pastBlock bottomCount state position offset positionLe

/-- ★ **THE CUP preservation of partner-TOTALITY.**  Every post-cup in-range boundary index has a distinct
same-component partner: a probe reading the LEFT (resp. RIGHT) fresh leg partners the RIGHT (resp. LEFT) fresh leg
(joined at the splice); a probe reading an OLD node inherits its pre-cup partner through the fresh-inert join
(`cupJoin_inert_oldBBC`) and the injective up-shift `capBoundaryReindex`. -/
theorem boundaryPartnered_stepCup (bottomCount : Nat) (state : WireState) (position : Nat)
    (fresh : WiringDescStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (bottomLe : bottomCount ≤ state.nextFresh)
    (positionLe : position ≤ state.openWires.length)
    (partnered : boundaryPartnered bottomCount state) :
    boundaryPartnered bottomCount (stepCup state position) := by
  intro probeIndex probeBelow
  rw [stepCup_openWiresLength state position, ← Nat.add_assoc bottomCount state.openWires.length 2] at probeBelow
  rcases cupReadClassBBC bottomCount state position positionLe probeIndex probeBelow with
    ⟨hidx, hread⟩ | ⟨hidx, hread⟩ | ⟨pre, preRange, hidx, hread⟩
  · -- probe reads the LEFT fresh leg; partner is the RIGHT fresh leg.
    refine ⟨bottomCount + (position + 1), ?_, ?_, ?_⟩
    · rw [stepCup_openWiresLength state position]
      exact Nat.add_lt_add_left (Nat.lt_succ_of_le (Nat.succ_le_succ positionLe)) bottomCount
    · rw [hidx]
      exact Ne.symm (Nat.ne_of_lt (Nat.add_lt_add_left (Nat.lt_add_one position) bottomCount))
    · show isSameComponent (stepCup state position).links
          (natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position)) probeIndex)
          (natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position)) (bottomCount + (position + 1)))
          = true
      rw [hread, matchingBoundaryNodes_stepCup_getAt_rightLeg bottomCount state position positionLe,
        stepCup_links state position]
      exact isSameComponent_unionFindJoin_joined state.links forest state.nextFresh (state.nextFresh + 1)
  · -- probe reads the RIGHT fresh leg; partner is the LEFT fresh leg.
    refine ⟨bottomCount + position, ?_, ?_, ?_⟩
    · rw [stepCup_openWiresLength state position]
      exact Nat.add_lt_add_left
        (Nat.lt_of_le_of_lt positionLe (Nat.lt_succ_of_le (Nat.le_succ state.openWires.length))) bottomCount
    · rw [hidx]
      exact Nat.ne_of_lt (Nat.add_lt_add_left (Nat.lt_add_one position) bottomCount)
    · show isSameComponent (stepCup state position).links
          (natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position)) probeIndex)
          (natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position)) (bottomCount + position))
          = true
      rw [hread, matchingBoundaryNodes_stepCup_getAt_leftLeg bottomCount state position positionLe,
        stepCup_links state position,
        isSameComponent_symm (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
          (state.nextFresh + 1) state.nextFresh]
      exact isSameComponent_unionFindJoin_joined state.links forest state.nextFresh (state.nextFresh + 1)
  · -- probe reads an OLD node; it inherits its pre-cup partner.
    obtain ⟨w, wRange, wNe, wShares⟩ := partnered pre preRange
    refine ⟨capBoundaryReindex bottomCount position w, ?_, ?_, ?_⟩
    · rw [stepCup_openWiresLength state position]
      show (if w < bottomCount + position then w else w + 2) < bottomCount + (state.openWires.length + 2)
      cases Nat.lt_or_ge w (bottomCount + position) with
      | inl below =>
          rw [if_pos below]
          exact Nat.lt_of_lt_of_le wRange (Nat.add_le_add_left (Nat.le_add_right state.openWires.length 2) bottomCount)
      | inr atLeast =>
          rw [if_neg (Nat.not_lt.mpr atLeast), ← Nat.add_assoc bottomCount state.openWires.length 2]
          exact Nat.add_lt_add_right wRange 2
    · rw [hidx]
      exact capBoundaryReindex_ne bottomCount position w pre wNe
    · show isSameComponent (stepCup state position).links
          (natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position)) probeIndex)
          (natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position))
            (capBoundaryReindex bottomCount position w))
          = true
      rw [hread, cupOldReadBP bottomCount state position w wRange positionLe, stepCup_links state position,
        cupJoin_inert_oldBBC state forest fresh
          (natListGetAt (matchingBoundaryNodes bottomCount state) pre)
          (natListGetAt (matchingBoundaryNodes bottomCount state) w)
          (boundaryRead_lt_nextFreshBBC bottomCount state fresh bottomLe nfPos pre)
          (boundaryRead_lt_nextFreshBBC bottomCount state fresh bottomLe nfPos w)]
      exact wShares

/-! ## THE CROSSING preservation -/

/-- ★ **THE CROSSING preservation of partner-TOTALITY.**  The crossing preserves the open-wire length, so its
boundary range is unchanged; the post-crossing partner of a probe is the transposition-conjugate
`crossingReindexBBC` of its pre-crossing partner, read off the shipped pullback
`matchingSameComponent_stepCrossing_reindexBBC` — a bijective relabel (no pigeonhole). -/
theorem boundaryPartnered_stepCrossing (bottomCount : Nat) (state : WireState) (position : Nat)
    (fresh : WiringDescStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (bottomLe : bottomCount ≤ state.nextFresh)
    (windowInRange : position + 2 ≤ state.openWires.length)
    (partnered : boundaryPartnered bottomCount state) :
    boundaryPartnered bottomCount (stepWiring state position crossingWiring) := by
  have lenEq : (stepWiring state position crossingWiring).openWires.length = state.openWires.length := by
    obtain ⟨rightLen, fitsRaw⟩ := Nat.le.dest windowInRange
    rw [stepWiring_openWires_length_fits state position rightLen crossingWiring fitsRaw.symm]
    exact fitsRaw
  intro probeIndex probeBelow
  rw [lenEq] at probeBelow
  obtain ⟨w, wRange, wNe, wShares⟩ :=
    partnered (crossingReindexBBC bottomCount position probeIndex)
      (crossingReindexBBC_lt bottomCount state position probeIndex windowInRange probeBelow)
  refine ⟨crossingReindexBBC bottomCount position w, ?_, ?_, ?_⟩
  · rw [lenEq]
    exact crossingReindexBBC_lt bottomCount state position w windowInRange wRange
  · intro heq
    apply wNe
    have transported := congrArg (crossingReindexBBC bottomCount position) heq
    rw [crossingReindexBBC_involutive] at transported
    exact transported
  · have distinct : probeIndex ≠ crossingReindexBBC bottomCount position w := by
      intro heq
      apply wNe
      have transported := congrArg (crossingReindexBBC bottomCount position) heq
      rw [crossingReindexBBC_involutive] at transported
      exact transported.symm
    rw [matchingSameComponent_stepCrossing_reindexBBC bottomCount state position fresh forest nfPos bottomLe
        windowInRange probeIndex (crossingReindexBBC bottomCount position w) distinct probeBelow
        (crossingReindexBBC_lt bottomCount state position w windowInRange wRange),
      crossingReindexBBC_involutive bottomCount position w]
    exact wShares

/-! ## The per-atom dispatch + the whole-fold lift -/

/-- ★ **One well-formed Brauer atom preserves partner-TOTALITY.**  Dispatch on the generator: cup / cap route
through the r10 B1 bridges to `boundaryPartnered_stepCup` / `_stepCap`, crossing goes directly to
`_stepCrossing`.  The window-fit supplies each preservation's window premise; the cap additionally consumes
`bounded` (the derangement composition's other input). -/
theorem boundaryPartnered_stepBrauerAtom (bottomCount : Nat) (state : WireState) (atom : BrauerAtom)
    (cond : BrauerStateConditions bottomCount state)
    (gen : isBrauerGenerator atom.wiring)
    (windowFit : atom.position + atom.wiring.inputCount ≤ state.openWires.length)
    (bounded : boundedBoundaryComponents bottomCount state)
    (partnered : boundaryPartnered bottomCount state) :
    boundaryPartnered bottomCount (stepBrauerAtom state atom) := by
  obtain ⟨atomPosition, atomWiring⟩ := atom
  show boundaryPartnered bottomCount (stepWiring state atomPosition atomWiring)
  rcases gen with hcup | hcap | hcross
  · subst hcup
    rw [stepWiring_cupWiring_eq_stepCup state atomPosition cond.fresh]
    exact boundaryPartnered_stepCup bottomCount state atomPosition cond.fresh cond.forest cond.nfPos cond.bottomLe
      windowFit partnered
  · subst hcap
    rw [stepWiring_capWiring_eq_stepCap state atomPosition windowFit]
    exact boundaryPartnered_stepCap bottomCount state atomPosition cond.forest windowFit bounded partnered
  · subst hcross
    exact boundaryPartnered_stepCrossing bottomCount state atomPosition cond.fresh cond.forest cond.nfPos
      cond.bottomLe windowFit partnered

/-- ★ **The WHOLE `processBrauer` fold preserves partner-TOTALITY for a well-formed Brauer word.**  Structural on
the atom list, threading the four reachable-state conditions
(`brauerStateConditions_stepBrauerAtom`), T-DISJOINT (`boundedBoundaryComponents_stepBrauerAtom`, the cap's
other input), and partner-totality (`boundaryPartnered_stepBrauerAtom`) together. -/
theorem boundaryPartnered_processBrauer (bottomCount : Nat) :
    (atoms : List BrauerAtom) → (state : WireState) →
    BrauerStateConditions bottomCount state → WellFormedBrauerFold state atoms →
    boundedBoundaryComponents bottomCount state →
    boundaryPartnered bottomCount state →
    boundaryPartnered bottomCount (processBrauer state atoms)
  | [], _, _, _, _, partnered => partnered
  | atom :: rest, state, cond, wellFormed, bounded, partnered => by
      obtain ⟨gen, windowFit, wellRest⟩ := wellFormed
      exact boundaryPartnered_processBrauer bottomCount rest (stepBrauerAtom state atom)
        (brauerStateConditions_stepBrauerAtom bottomCount state atom cond) wellRest
        (boundedBoundaryComponents_stepBrauerAtom bottomCount state atom cond gen windowFit bounded)
        (boundaryPartnered_stepBrauerAtom bottomCount state atom cond gen windowFit bounded partnered)

/-- ★ **Partner-TOTALITY holds at every reachable state of a well-formed Brauer word.**  Reads the fold lift off
the seed: the fresh seed satisfies the four reachable-state conditions, T-DISJOINT, and partner-totality
(`boundaryPartnered_seed`, for `0 < bottomCount`). -/
theorem boundaryPartnered_reachable (bottomCount : Nat) (bottomPos : 0 < bottomCount)
    (atoms : List BrauerAtom) (wellFormed : WellFormedBrauerFold (brauerSeed bottomCount) atoms) :
    boundaryPartnered bottomCount (processBrauer (brauerSeed bottomCount) atoms) :=
  boundaryPartnered_processBrauer bottomCount atoms (brauerSeed bottomCount)
    (brauerStateConditions_seed bottomCount bottomPos) wellFormed
    (boundedBoundaryComponents_seed bottomCount)
    (boundaryPartnered_seed bottomCount bottomPos)

/-! ## The universal read-off corollary -/

/-- ★ **The UNIVERSAL read-off corollary.**  Combining partner-totality (`boundaryPartnered_reachable`) with the
r11 uniqueness read-off (`partnerIndexOf_reads_matchingPartner`, over the reachable T-DISJOINT state): at EVERY
in-range boundary index of EVERY well-formed fold output, `partnerIndexOf` — the map `extractDiagram` evaluates at
each boundary slot — reads a GENUINE distinct same-component partner.  Hypothesis-free modulo the fold premises
(`0 < bottomCount`, `WellFormedBrauerFold`): the existence witness the read-off needed is now discharged by the
fold, so the correspondence is total AND uniquely read off — the perfect-matching content, carrier-free.  This is
NOT yet the master flip: wiring the read-off to a SPECIFIC diagram `d` over the six-phase standard-form word
(T-ENUM + T-CLOSE) is the standing residual. -/
theorem partnerIndexOf_readsPartner_reachable (bottomCount : Nat) (bottomPos : 0 < bottomCount)
    (atoms : List BrauerAtom) (wellFormed : WellFormedBrauerFold (brauerSeed bottomCount) atoms)
    (probeIndex : Nat)
    (probeInRange : probeIndex < bottomCount + (processBrauer (brauerSeed bottomCount) atoms).openWires.length) :
    ∃ partnerIndex,
      partnerIndex < bottomCount + (processBrauer (brauerSeed bottomCount) atoms).openWires.length
      ∧ partnerIndex ≠ probeIndex
      ∧ partnerIndexOf (processBrauer (brauerSeed bottomCount) atoms).links
          (matchingBoundaryNodes bottomCount (processBrauer (brauerSeed bottomCount) atoms))
          (bottomCount + (processBrauer (brauerSeed bottomCount) atoms).openWires.length) probeIndex
        = partnerIndex := by
  have bounded := boundedBoundaryComponents_reachable bottomCount bottomPos atoms wellFormed
  obtain ⟨partnerIndex, partnerRange, partnerNe, partnerShares⟩ :=
    boundaryPartnered_reachable bottomCount bottomPos atoms wellFormed probeIndex probeInRange
  exact ⟨partnerIndex, partnerRange, partnerNe,
    partnerIndexOf_reads_matchingPartner bottomCount (processBrauer (brauerSeed bottomCount) atoms) bounded
      probeIndex partnerIndex probeInRange partnerRange partnerNe partnerShares⟩

/-! ## Non-vacuity — a well-formed mixed-diagram fold -/

/-- ★ **Non-vacuity — partner-totality at a genuine mixed fold.**  `[capAt 0, cupAt 0]` over `bottomCount = 2`
is well-formed (`wellFormedBrauerFold_capThenCup`), so `boundaryPartnered_reachable` applies non-vacuously — a
mixed cap-then-cup diagram the identity seed does not cover. -/
theorem boundaryPartnered_reachable_capThenCup :
    boundaryPartnered 2 (processBrauer (brauerSeed 2) [capAt 0, cupAt 0]) :=
  boundaryPartnered_reachable 2 (by decide) [capAt 0, cupAt 0] wellFormedBrauerFold_capThenCup

/-- ★ **Cross-check firing — a concrete cap-then-cup partner pair.**  Boundary index `0` and index `1` are
same-component in the cap-then-cup fold (partner list `[1, 0, 3, 2]`), the pair `boundaryPartnered_reachable`
existentially supplies at index `0`. -/
theorem boundaryPartnered_capThenCup_firing :
    matchingSameComponent 2 (processBrauer (brauerSeed 2) [capAt 0, cupAt 0]) 0 1 = true := by decide

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the partner-TOTALITY FOLD is SHIPPED (r12).**  The three per-atom preservations
(`boundaryPartnered_stepCup` / `_stepCrossing` / `_stepCap`) lift through the per-atom dispatch
(`boundaryPartnered_stepBrauerAtom`) and the structural fold (`boundaryPartnered_processBrauer`), so
`boundaryPartnered_reachable` shows partner-totality holds at EVERY reachable state of a well-formed Brauer word.
Combined with the r11 uniqueness read-off, `partnerIndexOf_readsPartner_reachable` gives the universal read-off:
`partnerIndexOf` reads a genuine distinct partner at every boundary index of every well-formed fold output.
Non-vacuous (`boundaryPartnered_reachable_capThenCup`, `boundaryPartnered_capThenCup_firing`).  `= true`. -/
def fxBrauer_hasBoundaryPartneredFoldLift : Bool := true

/-- **Honesty marker — the MASTERS still do NOT close.**  `boundaryPartnered_reachable` completes the
perfect-matching invariant (`bounded ∧ boundaryPartnered` = exactly-2) and
`partnerIndexOf_readsPartner_reachable` reads it off hypothesis-free, but the master flips
`fxBrauer_hasTagCorrDisjoint` / `fxBrauer_hasTagCorrExtraction` additionally demand the read-off WIRED to a
SPECIFIC diagram `d` = `extractDiagram foldState` over the six-phase standard-form word — the two-source
existence assembly (T-CONNECT arc pairs + through-perm connectivity feeding `partnerShares` at every `d`-arc),
which needs **T-ENUM** (its own round: `capArcFeet` / `throughStrandPerm` / `cupArcTops` enumerating `d`'s feet /
perm / tops with the crossing words as conjugators) and **T-CLOSE**
(`extractDiagram_realizes_partner_ofConnectivity`, named only in the R5 ledger).  So the masters, the roundtrip
flags, and the completeness flags stay honestly `false`; #2013 does NOT close.  `= false`. -/
def fxBrauer_hasTagCorrMastersFromTotality : Bool := false

end FX1Poly.Polygraph
