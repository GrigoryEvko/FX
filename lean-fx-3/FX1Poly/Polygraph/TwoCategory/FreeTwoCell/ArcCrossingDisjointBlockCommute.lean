import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingPartnerConjugation

/-! # MODE-COMMUTE r10 — two disjoint crossings commute on the WHOLE extract, UNCONDITIONALLY

`ArcCrossingEquivariantTransport` (r8) proved how ONE faithful `2⇒2` crossing acts on the extract: by the
boundary-index transposition `transposeAdjacent (bottomCount + position)`.  The COUNT-field of that single-crossing
equivariance is unconditional; its PARTNER-field is regime-gated (`ArcCrossingPartnerConjugation`, r9), because a
single crossing σ-conjugates the partner list only in the perfect-matching regime.

This file lands the DISJOINT-BLOCK GODEMENT INDEPENDENCE the general-signature peel's `ofSwap` arm demands: two
faithful crossings at HORIZONTALLY-DISJOINT positions commute.  The crux, truth-probed before proving, is that
this is a much stronger and cleaner fact than the r8/r9 single-crossing equivariance suggested — and it is
UNCONDITIONAL, with NO perfect-matching regime:

  ★ **`stepCrossArc_disjointCommute`** (the state-level headline).  `stepCrossArc` only permutes `openWires`
    (leaving `links`, `nextFresh`, `loops`, and the event lists untouched), so two crossings at disjoint windows
    (`leftPivot + 2 ≤ rightPivot`) produce the SAME `ArcWireState` regardless of order — because two disjoint
    adjacent transpositions commute as permutations of the wire list.

  ★ **`extractArc_stepCrossArc_disjointCommute`** (the whole-extract corollary, `congrArg`).  Equal states have
    equal extracts, so the WHOLE `FullArcStructure` — the `diagram` (including `partner`!), the cup/cap totals,
    AND the per-port internal cup/cap counts — commutes.  No matching hypothesis: unlike the r8/r9 single-crossing
    equivariance (which compares a crossed extract to a σ-conjugate of another), the disjoint commute compares two
    orderings that yield LITERALLY the same state, so the regime gating of the partner field simply does not arise.

  ★ **`internalCupCounts_stepCrossArc_disjointCommute` / `internalCapCounts_…` / `partner_…`** — the field-level
    corollaries the recon named as the count-field deliverable, here delivered for count AND partner, unconditional.

The mechanism.  NODE 1 is the one genuinely-new algebraic fact: `transposeAdjacent_disjointCommute`, that two
adjacent transpositions at disjoint pivots commute pointwise on the naturals (a five-zone case split off the
shipped r8 equational lemmas `transposeAdjacent_pivot` / `_succ` / `_other`).  NODE 2 lifts it to the wire list
by the shipped anchor `natListGetAt_natListSwapTwoAt` and list extensionality (`natListEqOfPointwiseGetAt`).
NODE 3 is the state/extract corollary chain.

Also shipped here (deliverable #1): the GENERAL faithful-step invariants `stepCrossArc` preserves — width
(`stepCrossArc_openWires_length`, off `natListSwapTwoAt_length`) and, `rfl`-clean for every state, the forest
(`stepCrossArc_links`), `nextFresh`, `loops`, and the event lists.  These are the `consCongr`-arm obligations a
faithful general-signature peel threads through a `2⇒2` step.

## What this file does NOT do (the pins stay false)

It does NOT wire the faithful crossing into `arcSwapCorePackage_of_adjunctionSwap` (no builder arm for `crossAtom`)
and it does NOT flip the general-signature keystone.  `fxMode_hasArcPeelGeneralSignature` (the arity ceiling) and
the #2043 / WP-AMALG residual `fxMode_hasArcGodementSamePartitionFreshProof` stay `false`; the shipped
`stepArcAtom` / `extractArc` are never edited.  This certificate is strictly ADDITIVE.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.  `transposeAdjacent` is the
r8 joint-structural transposition (`rfl`-clean equations); the disjoint pivots are separated by `Nat.decEq` cases
(never `by_cases`).  Per-declaration `#assert_no_axioms` AND independent `#print axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (per-file copies, following the codebase pattern) -/

/-- `<` implies `≠` (hand-rolled to avoid name-drift; the r8 copy is `private`). -/
private theorem natNeOfLt {first second : Nat} (isLess : first < second) : first ≠ second :=
  fun areEqual => Nat.lt_irrefl second (areEqual ▸ isLess)

/-- `List.range.loop count acc` has length `count + acc.length`. -/
private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

/-- `(List.range count).length = count`. -/
private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

/-! ## NODE 1 — two adjacent transpositions at DISJOINT pivots commute pointwise (structural)

The one genuinely-new algebraic fact.  For `leftPivot + 2 ≤ rightPivot` the windows `{leftPivot, leftPivot+1}`
and `{rightPivot, rightPivot+1}` are disjoint, so applying the two transpositions in either order sends every
index to the same value.  Five zones (the four window endpoints and everything else), each closed by the shipped
r8 equational lemmas; the pivots are separated by `Nat.decEq` cases. -/

/-- ★ **Disjoint adjacent transpositions commute pointwise.**  With `leftPivot + 2 ≤ rightPivot`,
`transposeAdjacent leftPivot ∘ transposeAdjacent rightPivot = transposeAdjacent rightPivot ∘ transposeAdjacent
leftPivot` at every index. -/
theorem transposeAdjacent_disjointCommute (leftPivot rightPivot target : Nat)
    (disjoint : leftPivot + 2 ≤ rightPivot) :
    transposeAdjacent leftPivot (transposeAdjacent rightPivot target)
      = transposeAdjacent rightPivot (transposeAdjacent leftPivot target) := by
  have l1LtR : leftPivot + 1 < rightPivot :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (leftPivot + 1)) disjoint
  have lLtR : leftPivot < rightPivot := Nat.lt_of_succ_lt l1LtR
  have lLtR1 : leftPivot < rightPivot + 1 := Nat.le_succ_of_le lLtR
  have l1LtR1 : leftPivot + 1 < rightPivot + 1 := Nat.succ_lt_succ lLtR
  have lNeR : leftPivot ≠ rightPivot := natNeOfLt lLtR
  have lNeR1 : leftPivot ≠ rightPivot + 1 := natNeOfLt lLtR1
  have l1NeR : leftPivot + 1 ≠ rightPivot := natNeOfLt l1LtR
  have l1NeR1 : leftPivot + 1 ≠ rightPivot + 1 := natNeOfLt l1LtR1
  cases Nat.decEq target leftPivot with
  | isTrue targetIsLeft =>
      subst targetIsLeft
      rw [transposeAdjacent_other rightPivot target lNeR lNeR1,
        transposeAdjacent_pivot target,
        transposeAdjacent_other rightPivot (target + 1) l1NeR l1NeR1]
  | isFalse targetNeLeft =>
      cases Nat.decEq target (leftPivot + 1) with
      | isTrue targetIsLeftSucc =>
          subst targetIsLeftSucc
          rw [transposeAdjacent_other rightPivot (leftPivot + 1) l1NeR l1NeR1,
            transposeAdjacent_succ leftPivot,
            transposeAdjacent_other rightPivot leftPivot lNeR lNeR1]
      | isFalse targetNeLeftSucc =>
          cases Nat.decEq target rightPivot with
          | isTrue targetIsRight =>
              subst targetIsRight
              rw [transposeAdjacent_pivot target,
                transposeAdjacent_other leftPivot (target + 1) lNeR1.symm l1NeR1.symm,
                transposeAdjacent_other leftPivot target lNeR.symm l1NeR.symm,
                transposeAdjacent_pivot target]
          | isFalse targetNeRight =>
              cases Nat.decEq target (rightPivot + 1) with
              | isTrue targetIsRightSucc =>
                  subst targetIsRightSucc
                  rw [transposeAdjacent_succ rightPivot,
                    transposeAdjacent_other leftPivot rightPivot lNeR.symm l1NeR.symm,
                    transposeAdjacent_other leftPivot (rightPivot + 1) lNeR1.symm l1NeR1.symm,
                    transposeAdjacent_succ rightPivot]
              | isFalse targetNeRightSucc =>
                  rw [transposeAdjacent_other rightPivot target targetNeRight targetNeRightSucc,
                    transposeAdjacent_other leftPivot target targetNeLeft targetNeLeftSucc,
                    transposeAdjacent_other rightPivot target targetNeRight targetNeRightSucc]

/-! ## NODE 2 — the wire-list disjoint swap commutation (list extensionality over NODE 1) -/

/-- ★ **Disjoint adjacent swaps commute on the wire list.**  With `leftPivot + 2 ≤ rightPivot` and the outer
window `rightPivot + 1 < wires.length`, swapping the two disjoint pairs in either order yields the same list —
lifted from `transposeAdjacent_disjointCommute` by the shipped anchor `natListGetAt_natListSwapTwoAt` and list
extensionality. -/
theorem natListSwapTwoAt_disjointCommute (wires : List Nat) (leftPivot rightPivot : Nat)
    (disjoint : leftPivot + 2 ≤ rightPivot) (window : rightPivot + 1 < wires.length) :
    natListSwapTwoAt (natListSwapTwoAt wires leftPivot) rightPivot
      = natListSwapTwoAt (natListSwapTwoAt wires rightPivot) leftPivot := by
  have l1LtR : leftPivot + 1 < rightPivot :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (leftPivot + 1)) disjoint
  have leftWindow : leftPivot + 1 < wires.length :=
    Nat.lt_trans l1LtR (Nat.lt_of_succ_lt window)
  have lenLeftInner : (natListSwapTwoAt wires leftPivot).length = wires.length :=
    natListSwapTwoAt_length wires leftPivot leftWindow
  have lenRightInner : (natListSwapTwoAt wires rightPivot).length = wires.length :=
    natListSwapTwoAt_length wires rightPivot window
  have rightWindowOnLeftInner : rightPivot + 1 < (natListSwapTwoAt wires leftPivot).length := by
    rw [lenLeftInner]; exact window
  have leftWindowOnRightInner : leftPivot + 1 < (natListSwapTwoAt wires rightPivot).length := by
    rw [lenRightInner]; exact leftWindow
  refine natListEqOfPointwiseGetAt _ _ ?_ ?_
  · rw [natListSwapTwoAt_length (natListSwapTwoAt wires leftPivot) rightPivot rightWindowOnLeftInner,
      natListSwapTwoAt_length (natListSwapTwoAt wires rightPivot) leftPivot leftWindowOnRightInner,
      lenLeftInner, lenRightInner]
  · intro index _indexBound
    rw [natListGetAt_natListSwapTwoAt (natListSwapTwoAt wires leftPivot) rightPivot index
        rightWindowOnLeftInner,
      natListGetAt_natListSwapTwoAt wires leftPivot (transposeAdjacent rightPivot index) leftWindow,
      natListGetAt_natListSwapTwoAt (natListSwapTwoAt wires rightPivot) leftPivot index
        leftWindowOnRightInner,
      natListGetAt_natListSwapTwoAt wires rightPivot (transposeAdjacent leftPivot index) window,
      transposeAdjacent_disjointCommute leftPivot rightPivot index disjoint]

/-! ## NODE 3 — the general faithful-step invariants + the state/extract disjoint commute -/

/-- The faithful crossing PRESERVES wire width — general form (off `natListSwapTwoAt_length`), the `consCongr`
tracking obligation for a `2⇒2` atom. -/
theorem stepCrossArc_openWires_length (state : ArcWireState) (position : Nat)
    (window : position + 1 < state.openWires.length) :
    (stepCrossArc state position).openWires.length = state.openWires.length :=
  natListSwapTwoAt_length state.openWires position window

/-- The faithful crossing leaves the union-find forest UNTOUCHED — every state.  `rfl`. -/
theorem stepCrossArc_links (state : ArcWireState) (position : Nat) :
    (stepCrossArc state position).links = state.links := rfl

/-- The faithful crossing allocates NO fresh id — every state.  `rfl`. -/
theorem stepCrossArc_nextFresh (state : ArcWireState) (position : Nat) :
    (stepCrossArc state position).nextFresh = state.nextFresh := rfl

/-- The faithful crossing changes NO loop count — every state.  `rfl`. -/
theorem stepCrossArc_loops (state : ArcWireState) (position : Nat) :
    (stepCrossArc state position).loops = state.loops := rfl

/-- The faithful crossing records NO cup event — every state.  `rfl`. -/
theorem stepCrossArc_cupEventNodes (state : ArcWireState) (position : Nat) :
    (stepCrossArc state position).cupEventNodes = state.cupEventNodes := rfl

/-- The faithful crossing records NO cap event — every state.  `rfl`. -/
theorem stepCrossArc_capEventNodes (state : ArcWireState) (position : Nat) :
    (stepCrossArc state position).capEventNodes = state.capEventNodes := rfl

/-- ★ **Two disjoint crossings commute on the WHOLE state.**  `stepCrossArc` only permutes `openWires`, so with
disjoint windows (`leftPivot + 2 ≤ rightPivot`) the two orderings produce the SAME `ArcWireState` — the wire lists
agree by `natListSwapTwoAt_disjointCommute`, every other field is `state`'s in both orders.  UNCONDITIONAL: no
matching regime. -/
theorem stepCrossArc_disjointCommute (state : ArcWireState) (leftPivot rightPivot : Nat)
    (disjoint : leftPivot + 2 ≤ rightPivot) (window : rightPivot + 1 < state.openWires.length) :
    stepCrossArc (stepCrossArc state leftPivot) rightPivot
      = stepCrossArc (stepCrossArc state rightPivot) leftPivot := by
  show ArcWireState.mk (natListSwapTwoAt (natListSwapTwoAt state.openWires leftPivot) rightPivot)
      state.links state.nextFresh state.loops state.cupEventNodes state.capEventNodes
    = ArcWireState.mk (natListSwapTwoAt (natListSwapTwoAt state.openWires rightPivot) leftPivot)
      state.links state.nextFresh state.loops state.cupEventNodes state.capEventNodes
  rw [natListSwapTwoAt_disjointCommute state.openWires leftPivot rightPivot disjoint window]

/-- ★ **Two disjoint crossings commute on the WHOLE extract.**  Equal states have equal extracts, so the entire
`FullArcStructure` — `diagram` (partner included), the cup/cap totals, and the per-port internal cup/cap counts —
is order-independent.  UNCONDITIONAL: unlike the r8/r9 single-crossing equivariance (which compares a crossed
extract to a σ-conjugate), the disjoint commute equates two orderings yielding literally the same state, so the
partner field's regime gating never arises.  This is the crossing's Godement independence the general peel's
`ofSwap` arm demands (count-field and partner-field at once). -/
theorem extractArc_stepCrossArc_disjointCommute (bottomCount : Nat) (state : ArcWireState)
    (leftPivot rightPivot : Nat) (disjoint : leftPivot + 2 ≤ rightPivot)
    (window : rightPivot + 1 < state.openWires.length) :
    extractArc bottomCount (stepCrossArc (stepCrossArc state leftPivot) rightPivot)
      = extractArc bottomCount (stepCrossArc (stepCrossArc state rightPivot) leftPivot) :=
  congrArg (extractArc bottomCount)
    (stepCrossArc_disjointCommute state leftPivot rightPivot disjoint window)

/-- ★ **The per-port internal CUP counts commute (the recon's named count-field deliverable).**  A `congrArg`
projection of the whole-extract disjoint commute. -/
theorem internalCupCounts_stepCrossArc_disjointCommute (bottomCount : Nat) (state : ArcWireState)
    (leftPivot rightPivot : Nat) (disjoint : leftPivot + 2 ≤ rightPivot)
    (window : rightPivot + 1 < state.openWires.length) :
    (extractArc bottomCount (stepCrossArc (stepCrossArc state leftPivot) rightPivot)).internalCupCounts
      = (extractArc bottomCount (stepCrossArc (stepCrossArc state rightPivot) leftPivot)).internalCupCounts :=
  congrArg FullArcStructure.internalCupCounts
    (extractArc_stepCrossArc_disjointCommute bottomCount state leftPivot rightPivot disjoint window)

/-- ★ **The per-port internal CAP counts commute** — the cap dual. -/
theorem internalCapCounts_stepCrossArc_disjointCommute (bottomCount : Nat) (state : ArcWireState)
    (leftPivot rightPivot : Nat) (disjoint : leftPivot + 2 ≤ rightPivot)
    (window : rightPivot + 1 < state.openWires.length) :
    (extractArc bottomCount (stepCrossArc (stepCrossArc state leftPivot) rightPivot)).internalCapCounts
      = (extractArc bottomCount (stepCrossArc (stepCrossArc state rightPivot) leftPivot)).internalCapCounts :=
  congrArg FullArcStructure.internalCapCounts
    (extractArc_stepCrossArc_disjointCommute bottomCount state leftPivot rightPivot disjoint window)

/-- ★ **The boundary PARTNER matching commutes — UNCONDITIONALLY (no regime).**  The disjoint commute delivers the
partner field for free, because both orderings yield the same state; contrast the r9 single-crossing partner
conjugation, which needs the perfect-matching regime.  A `congrArg` projection of the whole-extract commute. -/
theorem partner_stepCrossArc_disjointCommute (bottomCount : Nat) (state : ArcWireState)
    (leftPivot rightPivot : Nat) (disjoint : leftPivot + 2 ≤ rightPivot)
    (window : rightPivot + 1 < state.openWires.length) :
    (extractArc bottomCount (stepCrossArc (stepCrossArc state leftPivot) rightPivot)).diagram.partner
      = (extractArc bottomCount (stepCrossArc (stepCrossArc state rightPivot) leftPivot)).diagram.partner :=
  congrArg (fun fullArc => fullArc.diagram.partner)
    (extractArc_stepCrossArc_disjointCommute bottomCount state leftPivot rightPivot disjoint window)

/-! ## Non-vacuity witnesses (the commute fires at the fresh seed AND off the perfect-matching regime) -/

/-- ★ **The commute is non-vacuous: it fires at EVERY fresh-seed disjoint crossing pair.**  At the seed
`openWires = List.range bottomCount`, for any disjoint in-window pivots, the whole extract is order-independent.
A parameterized application — not a hand fixture. -/
theorem arcCrossingDisjointBlockCommute_seed_confirms (bottomCount leftPivot rightPivot : Nat)
    (disjoint : leftPivot + 2 ≤ rightPivot) (window : rightPivot + 1 < bottomCount) :
    extractArc bottomCount
        (stepCrossArc (stepCrossArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          leftPivot) rightPivot)
      = extractArc bottomCount
          (stepCrossArc (stepCrossArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            rightPivot) leftPivot) :=
  extractArc_stepCrossArc_disjointCommute bottomCount
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) leftPivot rightPivot disjoint
    (by
      show rightPivot + 1 < (List.range bottomCount).length
      rw [rangeLength bottomCount]
      exact window)

/-- ★ **The commute holds OFF the perfect-matching regime — the unconditionality witness.**  On the hostile
three-port component `crossingTriComponentState` (which violates `ArcPerfectMatching`, so the r8/r9 single-crossing
partner conjugation FAILS there — `crossing_triComponent_partner_ne_conjugate`), two disjoint crossings STILL
commute on the whole extract.  A direct instantiation of the general theorem — no regime hypothesis, no heavy
`decide`.  This is the machine-witness that the disjoint commute is genuinely stronger than the single-crossing
equivariance: the partner field commutes even where its conjugation is refuted. -/
theorem arcCrossingDisjointBlockCommute_offRegime_confirms :
    extractArc 0 (stepCrossArc (stepCrossArc crossingTriComponentState 0) 2)
      = extractArc 0 (stepCrossArc (stepCrossArc crossingTriComponentState 2) 0) :=
  extractArc_stepCrossArc_disjointCommute 0 crossingTriComponentState 0 2 (by decide) (by decide)

/-! ## Honesty marker + pins -/

/-- **Honesty marker — two DISJOINT crossings commute on the WHOLE extract, UNCONDITIONALLY.**  With disjoint
windows (`leftPivot + 2 ≤ rightPivot`) the two orderings of `stepCrossArc` produce the SAME `ArcWireState`
(`stepCrossArc_disjointCommute`, from the pointwise `transposeAdjacent_disjointCommute` lifted by
`natListSwapTwoAt_disjointCommute`), hence the SAME `FullArcStructure` (`extractArc_stepCrossArc_disjointCommute`)
— the per-port internal cup/cap counts (`internalCupCounts_…` / `internalCapCounts_…`, the recon's named
count-field deliverable) AND the boundary partner matching (`partner_stepCrossArc_disjointCommute`) at once, with
NO perfect-matching regime.  This is strictly STRONGER than the recon's split (it anticipated count-unconditional /
partner-regime-gated): the disjoint commute equates two orderings yielding literally the same state, so the
partner field's regime gating never arises.  Non-vacuous at every fresh seed
(`arcCrossingDisjointBlockCommute_seed_confirms`) and, crucially, off the matching regime
(`arcCrossingDisjointBlockCommute_offRegime_confirms`, on the r8 hostile three-port component where the
single-crossing partner conjugation is refuted).  Also shipped: the general `consCongr` faithful-step invariants
(`stepCrossArc_openWires_length` + the `rfl`-clean field-untouched lemmas).  The shipped `stepArcAtom` /
`extractArc` are never edited.  `= true`. -/
def fxMode_hasArcCrossingDisjointBlockCommute : Bool := true

/-- **Honesty pin — the r8 unconditional count-field equivariance stays `true`.**  This disjoint commute is a
distinct fact (order-independence of two crossings, not the action of one); the r8 marker is untouched.  `rfl`. -/
theorem arcCrossingDisjointBlockCommute_countField_stays_true :
    fxMode_hasArcCrossingCountEquivariantTransport = true := rfl

/-- **Honesty pin — the r9 regime-gated partner conjugation stays `true`.**  That marker is the single-crossing
σ-conjugation in the perfect-matching regime, a different statement; untouched.  `rfl`. -/
theorem arcCrossingDisjointBlockCommute_partnerRegime_stays_true :
    fxMode_hasArcCrossingPartnerConjugationInMatchingRegime = true := rfl

/-- **Honesty pin — the r8 UNCONDITIONAL single-crossing partner marker stays `false`.**  A single crossing does
NOT σ-conjugate the partner off the matching regime; only the DISJOINT COMMUTE (two crossings, same state) is
unconditional on the partner.  The r8 marker is untouched.  `rfl`. -/
theorem arcCrossingDisjointBlockCommute_unconditionalSinglePartner_stays_false :
    fxMode_hasArcCrossingPartnerEquivariantTransport = false := rfl

/-- **Honesty pin — the general-signature peel stays the open keystone.**  This arm supplies the crossing's
disjoint-block Godement independence a general-signature peel's `ofSwap` needs, but it does not build the
`arcSwapCorePackage` dispatcher (no builder arm for `crossAtom`).  `fxMode_hasArcPeelGeneralSignature` stays
`false`.  `rfl`. -/
theorem arcCrossingDisjointBlockCommute_generalSignature_stays_false :
    fxMode_hasArcPeelGeneralSignature = false := rfl

/-- **Honesty pin — the #2043 / WP-AMALG fresh-partition keystone is untouched.**
`fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.  `rfl`. -/
theorem arcCrossingDisjointBlockCommute_samePartitionFreshProof_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
