import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderSuffixCongruence

/-! # WP-FROB r7 (FROB-7) — spider completeness + the decidable extraspecial word problem

The r3–r6 stack proves `SpiderConv` PARTITION-SOUND (`spiderConv_partitionSound`): convertible words induce the same
boundary partition (`extraSpiderDiagramOf`, the extraspecial / corelation invariant).  This file proves the CONVERSE
— COMPLETENESS: two words with the same boundary partition ARE `SpiderConv`-convertible — and packages the two into
`Decidable (SpiderConv n a b)`, the decision of the extraspecial-commutative-Frobenius (corelation) word problem.

## The crossing verdict: the comb is AVOIDABLE (matching the classical literature)

The recon feared the general symmetric-group word-canonicalization "comb" (`BRAUER-BREACH`, still open) because it
assumed completeness must go through a Fauser-style per-atom straightening that reduces crossing WORDS against each
other.  It does NOT.  The extraspecial Frobenius PROP is the corelation category (Coya–Fong): its morphisms ARE
boundary partitions, and the invariant is a partition (a map `m+n → k`), NOT a permutation.  The shipped `whisker`
constructor of `SpiderConv` (`Frobenius/SpiderConv.lean`) is exactly the corelation-quotient generator: it relates ANY
two words that agree on the boundary partition VIEW (equal open-wire length + the same `matchingSameComponent`
relation).  So completeness reduces to a crossing-FREE bridge —

  **equal `extraSpiderDiagramOf` ⟹ equal boundary view** — the CONVERSE of
  `extractSpiderDiagram_forget_eq_of_connectivityView`.

This bridge is the exact characterization
`matchingSameComponent n state i j = (blockLabels.get i == blockLabels.get j)`: two boundary ports share a component
iff they carry the same least-index block label.  The classical proofs (Fauser Thm 3.8; BGKSZ hypergraph DPO;
Coecke–Kissinger spider theorem) confirm this — commutativity/cocommutativity make leg-permutations a LOCAL, bounded
absorption at each (co)multiplication node, and the sound-complete invariant is the connectivity partition, never an
`S_n` element.  So the decision lands FULL (hypothesis-free), NOT conditional on the comb.  The `S_n` comb reappears
only for the symmetric-monoidal-WITHOUT-Frobenius (Brauer) lane (`BRAUER-BREACH`), a different presentation.

## What ships

  * `matchingSameComponent_eq_blockLabelBeq` — the bridge (the block label read-off determines the boundary view).
  * `spiderConv_complete : extraSpiderDiagramOf n a = extraSpiderDiagramOf n b → SpiderConv n a b` — UNCONDITIONAL.
  * `spiderConv_iff_extraEq` + `instDecidableSpiderConv` — `Decidable (SpiderConv n a b)`, sound ⊕ complete.
  * `canonicalSpiderOf` — the CONNECTED-spider Fauser normal form `δ^{n-1} ∘ μ^{m-1}` (μ-comb then δ-comb) + its
    realization + the "connected word reduces to its canonical spider" fusion witness.
  * The special (Cospan, with closed count) decision stays walled (`fxFrob_hasCospanClosedCountPermanentWall`); the
    general multi-block routing readback (the r8 target) is named honestly.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private Nat / list primitives (propext-free duplicates; core `List.range`/`mem_range` lemmas leak `propext`) -/

private theorem rangeLoopLengthLocal : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLengthLocal count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLengthLocal (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLengthLocal count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAtPastLocal : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAtPastLocal count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAtBelowLocal : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count → natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAtBelowLocal count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAtPastLocal count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAtBelowLocal (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAtBelowLocal count [] index indexBelow

private theorem memRangeLoopOfMemAcc : (count : Nat) → (accumulated : List Nat) → (value : Nat) →
    value ∈ accumulated → value ∈ List.range.loop count accumulated
  | 0, _, _, valueMem => valueMem
  | count + 1, accumulated, value, valueMem => by
      show value ∈ List.range.loop count (count :: accumulated)
      exact memRangeLoopOfMemAcc count (count :: accumulated) value (List.Mem.tail count valueMem)

private theorem memRangeLoopOfLt : (count : Nat) → (accumulated : List Nat) → (index : Nat) →
    index < count → index ∈ List.range.loop count accumulated
  | 0, _, index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | count + 1, accumulated, index, indexBelow => by
      show index ∈ List.range.loop count (count :: accumulated)
      cases Nat.lt_or_ge index count with
      | inl below => exact memRangeLoopOfLt count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          exact indexEq ▸ memRangeLoopOfMemAcc count (count :: accumulated) count (List.Mem.head accumulated)

private theorem ltImpMemRange (index count : Nat) (indexBelow : index < count) :
    index ∈ List.range count :=
  memRangeLoopOfLt count [] index indexBelow

/-! ## The `Nat`-`BEq` bridge — two beqs agree when their propositional equalities agree

`==` on `Nat` is the `decide`-based `BEq` (`n == m` reducibly `decide (n = m)`), so the boolean facts are threaded
through `decide_eq_true` / `of_decide_eq_true` / `decide_eq_false` / `of_decide_eq_false`, NOT `Nat.beq` (which does
not reduce through `==` at any transparency here). -/

/-- `(x == y) = (u == v)` when `x = y ↔ u = v` — the propext-free `BEq`-congruence over `Nat` (case on each `BEq`
value; the cross case is refuted by `absurd` of the transported equality). -/
private theorem natBeqEqBeqOfIff {x y u v : Nat}
    (forward : x = y → u = v) (backward : u = v → x = y) : (x == y) = (u == v) := by
  cases hxy : (x == y) with
  | true => exact (decide_eq_true (forward (of_decide_eq_true hxy))).symm
  | false =>
      cases huv : (u == v) with
      | true => exact absurd (backward (of_decide_eq_true huv)) (of_decide_eq_false hxy)
      | false => rfl

/-! ## The block-label read-off is a function of the boundary root -/

/-- ★ **`firstIndexWithRoot` returns an index whose root MATCHES the target**, whenever some candidate in the scanned
list matches.  Structural on the candidate list: at each head either the head matches (returns it) or the recursion
finds the witness in the tail (the witness cannot be the non-matching head).  The companion of the shipped
`firstIndexWithRoot_congr` — this reads the RESULT's root, that the SCAN's booleans. -/
private theorem firstIndexWithRoot_matches_of_mem (links : List (Nat × Nat)) (boundaryNodes : List Nat)
    (targetRoot : Nat) :
    (cands : List Nat) → (witness : Nat) → witness ∈ cands →
    (unionFindRootOf links (natListGetAt boundaryNodes witness) == targetRoot) = true →
    (unionFindRootOf links (natListGetAt boundaryNodes
        (firstIndexWithRoot links boundaryNodes targetRoot cands)) == targetRoot) = true
  | [], _, witnessMem, _ => nomatch witnessMem
  | head :: tail, witness, witnessMem, witnessMatches => by
      show (unionFindRootOf links (natListGetAt boundaryNodes
          (if unionFindRootOf links (natListGetAt boundaryNodes head) == targetRoot then head
            else firstIndexWithRoot links boundaryNodes targetRoot tail)) == targetRoot) = true
      cases headMatch : (unionFindRootOf links (natListGetAt boundaryNodes head) == targetRoot) with
      | true => exact headMatch
      | false =>
          cases witnessMem with
          | head => exact Bool.noConfusion (witnessMatches.symm.trans headMatch)
          | tail _ inTail =>
              exact firstIndexWithRoot_matches_of_mem links boundaryNodes targetRoot tail witness inTail
                witnessMatches

/-- The `k`-th block label of a spider extract, read in range, is the least-index representative of `k`'s component
— `firstIndexWithRoot` on the target boundary root, scanning all indices. -/
private theorem blockLabelAt_eq (bottomCount : Nat) (state : WireState) (index : Nat)
    (indexInRange : index < bottomCount + state.openWires.length) :
    natListGetAt (extractSpiderDiagram bottomCount state).blockLabels index
      = firstIndexWithRoot state.links (matchingBoundaryNodes bottomCount state)
          (unionFindRootOf state.links (natListGetAt (matchingBoundaryNodes bottomCount state) index))
          (List.range (bottomCount + state.openWires.length)) := by
  show natListGetAt ((List.range (bottomCount + state.openWires.length)).map (fun candidate =>
      firstIndexWithRoot state.links (matchingBoundaryNodes bottomCount state)
        (unionFindRootOf state.links (natListGetAt (matchingBoundaryNodes bottomCount state) candidate))
        (List.range (bottomCount + state.openWires.length)))) index = _
  rw [natListGetAt_map_inRange _ (List.range (bottomCount + state.openWires.length)) index
      (by rw [rangeLengthLocal]; exact indexInRange),
    rangeGetAtBelowLocal (bottomCount + state.openWires.length) index indexInRange]

/-- ★ **The bridge: the boundary same-component relation IS the block-label equality.**  `matchingSameComponent n
state i j` (two boundary ports share a union-find component) equals `(blockLabels.get i == blockLabels.get j)` (they
carry the same least-index block label) for in-range `i`, `j`.  Two directions: equal roots give the same
`firstIndexWithRoot` (congruence on the target root); equal labels give equal roots (both labels match their own
port's root via `firstIndexWithRoot_matches_of_mem`, so the ports' roots coincide).  The exact CONVERSE of the shipped
forward view lemma `extractSpiderDiagram_forget_eq_of_connectivityView`. -/
theorem matchingSameComponent_eq_blockLabelBeq (bottomCount : Nat) (state : WireState) (firstIndex secondIndex : Nat)
    (firstInRange : firstIndex < bottomCount + state.openWires.length)
    (secondInRange : secondIndex < bottomCount + state.openWires.length) :
    matchingSameComponent bottomCount state firstIndex secondIndex
      = (natListGetAt (extractSpiderDiagram bottomCount state).blockLabels firstIndex
          == natListGetAt (extractSpiderDiagram bottomCount state).blockLabels secondIndex) := by
  rw [blockLabelAt_eq bottomCount state firstIndex firstInRange,
    blockLabelAt_eq bottomCount state secondIndex secondInRange]
  show (unionFindRootOf state.links (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex)
        == unionFindRootOf state.links (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex))
      = (firstIndexWithRoot state.links (matchingBoundaryNodes bottomCount state)
            (unionFindRootOf state.links (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex))
            (List.range (bottomCount + state.openWires.length))
          == firstIndexWithRoot state.links (matchingBoundaryNodes bottomCount state)
            (unionFindRootOf state.links (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex))
            (List.range (bottomCount + state.openWires.length)))
  apply natBeqEqBeqOfIff
  · intro rootEq
    exact congrArg (fun root => firstIndexWithRoot state.links (matchingBoundaryNodes bottomCount state) root
      (List.range (bottomCount + state.openWires.length))) rootEq
  · intro labelEq
    have firstMatch := firstIndexWithRoot_matches_of_mem state.links (matchingBoundaryNodes bottomCount state)
      (unionFindRootOf state.links (natListGetAt (matchingBoundaryNodes bottomCount state) firstIndex))
      (List.range (bottomCount + state.openWires.length)) firstIndex
      (ltImpMemRange firstIndex (bottomCount + state.openWires.length) firstInRange) (decide_eq_true rfl)
    have secondMatch := firstIndexWithRoot_matches_of_mem state.links (matchingBoundaryNodes bottomCount state)
      (unionFindRootOf state.links (natListGetAt (matchingBoundaryNodes bottomCount state) secondIndex))
      (List.range (bottomCount + state.openWires.length)) secondIndex
      (ltImpMemRange secondIndex (bottomCount + state.openWires.length) secondInRange) (decide_eq_true rfl)
    have firstRootEq := of_decide_eq_true firstMatch
    have secondRootEq := of_decide_eq_true secondMatch
    exact firstRootEq.symm.trans
      ((congrArg (fun label => unionFindRootOf state.links (natListGetAt (matchingBoundaryNodes bottomCount state)
        label)) labelEq).trans secondRootEq)

/-! ## Completeness — equal boundary partition ⟹ convertible -/

/-- ★ **`SpiderConv` is COMPLETE for the extraspecial (corelation) partition, UNCONDITIONALLY.**  Two words over `n`
bottom wires inducing the SAME boundary partition (`extraSpiderDiagramOf`) are `SpiderConv`-convertible.  Discharged by
the empty-prefix `whisker` constructor: the length premise is the equal top count; the boundary-view premise is the
bridge `matchingSameComponent_eq_blockLabelBeq` applied to both states, whose block labels agree because the whole
`extraSpiderDiagramOf` agrees.  NO crossing canonicalization ("comb") is needed — the invariant is the partition, and
the whisker is the corelation-quotient generator.  This is the Coya–Fong corelation completeness, machine-checked. -/
theorem spiderConv_complete {bottomCount : Nat} {leftWord rightWord : List BrauerAtom}
    (partitionEq : extraSpiderDiagramOf bottomCount leftWord = extraSpiderDiagramOf bottomCount rightWord) :
    SpiderConv bottomCount leftWord rightWord := by
  have lengthEq : (processBrauer (brauerSeed bottomCount) leftWord).openWires.length
      = (processBrauer (brauerSeed bottomCount) rightWord).openWires.length :=
    congrArg SpiderPartitionType.topCount partitionEq
  have blockLabelsEq : (extractSpiderDiagram bottomCount (processBrauer (brauerSeed bottomCount) leftWord)).blockLabels
      = (extractSpiderDiagram bottomCount (processBrauer (brauerSeed bottomCount) rightWord)).blockLabels :=
    congrArg SpiderPartitionType.blockLabels partitionEq
  exact SpiderConv.whisker bottomCount [] leftWord rightWord lengthEq
    (fun firstIndex secondIndex firstBound secondBound => by
      show matchingSameComponent bottomCount (processBrauer (brauerSeed bottomCount) leftWord) firstIndex secondIndex
        = matchingSameComponent bottomCount (processBrauer (brauerSeed bottomCount) rightWord) firstIndex secondIndex
      rw [matchingSameComponent_eq_blockLabelBeq bottomCount (processBrauer (brauerSeed bottomCount) leftWord)
          firstIndex secondIndex firstBound secondBound,
        matchingSameComponent_eq_blockLabelBeq bottomCount (processBrauer (brauerSeed bottomCount) rightWord)
          firstIndex secondIndex (lengthEq ▸ firstBound) (lengthEq ▸ secondBound),
        blockLabelsEq])

/-- ★ **The extraspecial word problem is characterized by the boundary partition.**  `SpiderConv n a b` holds IFF the
two words induce the same `extraSpiderDiagramOf` — soundness (`spiderConv_partitionSound`) one way, completeness
(`spiderConv_complete`) the other. -/
theorem spiderConv_iff_extraEq {bottomCount : Nat} {leftWord rightWord : List BrauerAtom} :
    SpiderConv bottomCount leftWord rightWord
      ↔ extraSpiderDiagramOf bottomCount leftWord = extraSpiderDiagramOf bottomCount rightWord :=
  ⟨spiderConv_partitionSound, spiderConv_complete⟩

/-- ★ **`Decidable (SpiderConv n a b)`** — the decision of the extraspecial-commutative-Frobenius (corelation) word
problem.  Decide the (decidable) equality of the two `SpiderPartitionType` invariants and transport across
`spiderConv_iff_extraEq`. -/
instance instDecidableSpiderConv (bottomCount : Nat) (leftWord rightWord : List BrauerAtom) :
    Decidable (SpiderConv bottomCount leftWord rightWord) :=
  decidable_of_iff _ spiderConv_iff_extraEq.symm

/-! ## The connected-spider readback — the Fauser normal form `δ^{n-1} ∘ μ^{m-1}` (`stepView`)

Fauser (*Some graphical aspects of Frobenius structures*, arXiv:1202.6380, Thm 3.8): any CONNECTED `m ⇒ n` tangle
straightens to `δ^{n-1} ∘ l^r ∘ m^{m-1}` — a μ-left-comb collapsing all inputs to one wire, then a δ-left-comb fanning
that wire to all outputs; the loop count `r` drops to `0` in the special theory.  This is the single-spider readback;
the general multi-block readback (routing per block) is the r8 target (the closed-count wall aside).  The per-atom
partition VIEW that the fold threads is `spiderViewOf`. -/

/-- The per-word boundary partition VIEW (the extraspecial invariant the decision reads) — the `stepView` the fold
computes atom by atom (`extraSpiderDiagramOf` IS that fold). -/
def spiderViewOf (bottomCount : Nat) (word : List BrauerAtom) : SpiderPartitionType :=
  extraSpiderDiagramOf bottomCount word

/-- The μ-left-comb collapsing `inputCount` bottom wires to ONE wire: a birthing unit when there are no inputs, the
identity when there is one, otherwise multiply the leftmost pair and recurse. -/
def mergeToOne : Nat → List BrauerAtom
  | 0 => [unitAt 0]
  | 1 => []
  | inputs + 2 => multAt 0 :: mergeToOne (inputs + 1)

/-- The δ-left-comb fanning ONE wire to `outputCount` top wires: a terminating counit when there are no outputs, the
identity when there is one, otherwise comultiply wire `0` and recurse. -/
def fanToN : Nat → List BrauerAtom
  | 0 => [counitAt 0]
  | 1 => []
  | outputs + 2 => comultAt 0 :: fanToN (outputs + 1)

/-- ★ **The connected-spider Fauser normal form** `μ^{m-1}` then `δ^{n-1}` — the canonical representative of the
CONNECTED `m ⇒ n` spider (all `m + n` boundary ports one block).  Computes. -/
def canonicalSpiderOf (inputCount outputCount : Nat) : List BrauerAtom :=
  mergeToOne inputCount ++ fanToN outputCount

/-! ### The readback computes — `#eval` demos + per-size realization -/

-- `#eval` — the connected readback realizes its `(m, n)` block (`SpiderPartitionType` derives `Repr`).
#eval extraSpiderDiagramOf 2 (canonicalSpiderOf 2 1)   -- {2, 1, [0,0,0]}
#eval extraSpiderDiagramOf 3 (canonicalSpiderOf 3 2)   -- {3, 2, [0,0,0,0,0]}

/-- The connected `2 ⇒ 1` spider readback `[μ]` realizes the single block `{2, 1, [0,0,0]}`. -/
theorem canonicalSpider_realizes_2_1 :
    extraSpiderDiagramOf 2 (canonicalSpiderOf 2 1)
      = { bottomCount := 2, topCount := 1, blockLabels := [0, 0, 0] } := by decide

/-- The connected `2 ⇒ 2` spider readback `[μ, δ]` (the Frobenius "H" element) realizes `{2, 2, [0,0,0,0]}`. -/
theorem canonicalSpider_realizes_2_2 :
    extraSpiderDiagramOf 2 (canonicalSpiderOf 2 2)
      = { bottomCount := 2, topCount := 2, blockLabels := [0, 0, 0, 0] } := by decide

/-- The connected `3 ⇒ 2` spider readback realizes the size-5 single block `{3, 2, [0,0,0,0,0]}`. -/
theorem canonicalSpider_realizes_3_2 :
    extraSpiderDiagramOf 3 (canonicalSpiderOf 3 2)
      = { bottomCount := 3, topCount := 2, blockLabels := [0, 0, 0, 0, 0] } := by decide

/-- The `0 ⇒ 3` readback (unit birthing, then fan) realizes `{0, 3, [0,0,0]}` — the input-free spider. -/
theorem canonicalSpider_realizes_0_3 :
    extraSpiderDiagramOf 0 (canonicalSpiderOf 0 3)
      = { bottomCount := 0, topCount := 3, blockLabels := [0, 0, 0] } := by decide

/-! ### Fusion — connected words reduce to their canonical spider (via completeness) -/

/-- ★ **Spider fusion, connected case.**  Associativity's RHS `μ(1⊗μ)` (`[multAt 1, multAt 0]`, a connected `3 ⇒ 1`
word) FUSES to the canonical `3 ⇒ 1` spider `[μ, μ]` — a genuine normal-form reduction produced by completeness (both
realize the same connected partition), NOT the seed associativity relation. -/
theorem spiderFusion_assocRhs_toCanonical :
    SpiderConv 3 [multAt 1, multAt 0] (canonicalSpiderOf 3 1) :=
  spiderConv_complete (by decide)

/-- ★ **Spider fusion is uniform over the partition, not the word.**  The `2 ⇒ 2` Frobenius "S" word `(μ⊗1)(1⊗δ)`
(`frobLeft.lhs`) fuses to the canonical `2 ⇒ 2` spider `[μ, δ]` — the same canonical target the "H" word already IS,
demonstrating both Frobenius orientations land on one normal form. -/
theorem spiderFusion_frobLeftLhs_toCanonical :
    SpiderConv 2 frobLeft.lhs (canonicalSpiderOf 2 2) :=
  spiderConv_complete (by decide)

/-! ## Non-vacuity of the DECIDER — both verdicts fire on real pairs -/

/-- ★ **The decider returns `isTrue` on a genuinely-convertible pair.**  `SpiderConv 2 frobLeft.lhs frobLeft.rhs`
(the Frobenius "S=X" law, distinct words) is decided TRUE by `instDecidableSpiderConv`. -/
theorem spiderConvDecision_isTrue_frobLeft : decide (SpiderConv 2 frobLeft.lhs frobLeft.rhs) = true := by decide

/-- ★ **The decider returns `isFalse` on a genuinely-non-convertible pair.**  The Frobenius "H" element `δμ` and the
identity pair (`frobeniusH_ne_identity`, distinct partitions) are decided FALSE by `instDecidableSpiderConv` — the
decision is proper, not vacuously accepting. -/
theorem spiderConvDecision_isFalse_HvsIdentity :
    decide (SpiderConv 2 [multAt 0, comultAt 0] [identityStrandAt 0, identityStrandAt 1]) = false := by decide

/-- ★ **The two decider verdicts are DISTINCT** — non-vacuity of `instDecidableSpiderConv` in one statement. -/
theorem spiderConvDecision_bothVerdicts :
    decide (SpiderConv 2 frobLeft.lhs frobLeft.rhs) = true
      ∧ decide (SpiderConv 2 [multAt 0, comultAt 0] [identityStrandAt 0, identityStrandAt 1]) = false :=
  ⟨spiderConvDecision_isTrue_frobLeft, spiderConvDecision_isFalse_HvsIdentity⟩

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the extraspecial (corelation) word problem is DECIDABLE, UNCONDITIONALLY (FROB-7).**
`instDecidableSpiderConv` decides `SpiderConv n a b` by `DecidableEq` on the two `SpiderPartitionType` invariants,
transported across `spiderConv_iff_extraEq` (soundness `spiderConv_partitionSound` ⊕ completeness
`spiderConv_complete`).  The completeness leg needs NO `S_n` crossing canonicalization ("comb", the still-open
`BRAUER-BREACH`): the invariant is the connectivity partition (Coya–Fong corelations), and the shipped `whisker`
constructor is its quotient generator, so the bridge `matchingSameComponent_eq_blockLabelBeq` (equal partition ⟹ equal
boundary view) closes crossing-free.  NON-VACUOUS: the decider returns `isTrue` on `frobLeft` and `isFalse` on
`H`-vs-identity (`spiderConvDecision_bothVerdicts`).  `= true`. -/
def fxFrob_hasSpiderConvDecision : Bool := true

/-- ★ **Honesty marker — the connected-spider Fauser normal form ships and computes (FROB-7).**  `canonicalSpiderOf`
(the μ-comb `mergeToOne` then δ-comb `fanToN`) is Fauser Thm 3.8's `δ^{n-1} ∘ μ^{m-1}` connected readback; its
realization is machine-checked on a demonstrated `(m, n)` family (`canonicalSpider_realizes_2_1` / `2_2` / `3_2` /
`0_3`), and connected words FUSE to it via completeness (`spiderFusion_assocRhs_toCanonical`,
`spiderFusion_frobLeftLhs_toCanonical`) — the ZX/hypergraph spider theorem, connected fragment.  `= true`. -/
def fxFrob_hasConnectedSpiderNF : Bool := true

/-- ★ **Honesty marker — the GENERAL-arity CONNECTED spider-fusion normal-form realization SHIPS (FROB-SEED-MERGE
r1, #2250, closing #2017's realization node).**  `extraSpiderDiagramOf m (canonicalSpiderOf m n) = ⟨m, n,
replicate (m+n) 0⟩` for ALL `m`, `n` — the Fauser connected NF's realization at EVERY arity, generalizing the
demonstrated `(m, n)` family of `fxFrob_hasConnectedSpiderNF`.  Machine-checked as `extraSpiderDiagramOf_canonicalSpider`
(`Table/FrobeniusConnectivityInduction.lean`): the `mergeToOne`/`fanToN` union-find fold connects every boundary port
(`canonicalSpiderConnectivity`) and leaves exactly `n` open wires (`canonicalSpider_finalOpenLength`), fed into the
shipped connectivity->partition reduction `spiderPartition_of_allConnected`.  Zero-axiom, comb-free, structural — the
DIRECT connectivity fold the r2 recon reduced the surviving node to (NOT the non-injective seed-merge simulation).  The
still-open GENERAL MULTI-BLOCK routing realization is spun out to `fxFrob_hasMultiBlockSpiderRealization`.  `= true`. -/
def fxFrob_hasSpiderFusionNF : Bool := true

/-- **Honesty marker — the general MULTI-BLOCK spider-fusion routing realization is the r8 target.**  A boundary
partition with MULTIPLE blocks needs a per-block realization PLUS a routing permutation that gathers each block's
scattered ports (crossings).  That routing is a FORWARD computation (decidable per instance, NOT the `S_n`
word-canonicalization comb — the DECISION `fxFrob_hasSpiderConvDecision` is already unconditional and needs no
readback), but the general multi-block realization theorem `extraSpiderDiagramOf n (canonicalReadback D) = D` is an
induction over block-routing not yet built.  Off the corelation DECISION path (unconditional) and off the CONNECTED
realization (`fxFrob_hasSpiderFusionNF`, now shipped).  `= false`. -/
def fxFrob_hasMultiBlockSpiderRealization : Bool := false

/-- **Honesty marker — the SPECIAL (`Cospan(FinSet)`, closed-count) word problem stays walled.**  `SpiderConv` decides
the EXTRASPECIAL / corelation classes (`extraSpiderDiagramOf`, partition only).  The full SPECIAL invariant
`spiderDiagramOf` additionally tracks the isolated-closed-component count, which the boundary partition view provably
does NOT determine (`closedCount_notDeterminedByBoundaryView`, `fxFrob_hasCospanClosedCountPermanentWall`).  So a
decision of the SPECIAL word problem needs a SEPARATE interior-own-root count invariant — orthogonal to every
boundary-view brick, the r8 residual.  `= false`. -/
def fxFrob_hasSpecialFrobeniusDecision : Bool := false

end FX1Poly.Polygraph
