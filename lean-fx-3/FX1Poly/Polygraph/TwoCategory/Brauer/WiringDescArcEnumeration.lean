import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcExtractorRec
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescReadOffWiring

/-! # BRAUER-MIDDLE r13 — T-ENUM (the E1 enumeration half): the arc read-offs enumerate exactly `d`'s arcs

The R5 ledger decomposed the standing tag-correspondence long-pole into four sub-legs; the master flips
`fxBrauer_hasTagCorrDisjoint` / `fxBrauer_hasTagCorrExtraction` still demand the read-off WIRED to a specific
diagram `d = extractDiagram foldState` over the six-phase standard-form word, which needs **T-ENUM** (the arc
enumeration, its own round) and **T-CLOSE** (target closure).  This file ships the ENUMERATION half of T-ENUM,
zero-axiom, structural: that the `filterMap` read-offs `capArcFeetIndices` / `throughStrandBottoms` /
`throughStrandTops` / `cupArcTopIndices` list exactly the arc-class members, that each cap arc is listed once (by
its smaller foot) under the boundary-involution gate, and that the `cupArcTops` `− bottomCount` subtraction is
exact.  GENUINELY NEW, no FROB analog — the read-offs had NO enumeration lemma before this round (only
`decide`-checked literal instances).

## What this file ships (each zero-axiom, structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`)

The recon adjudicated T-ENUM into three separable pieces: **E1** enumeration-correctness (the `filterMap`s list
exactly `d`'s arcs, gated to a well-formed involution partner), **E2** conjugator-correctness (the
`permutationToCrossingWord` staircases realize the read-off orders — a separate selection-sort induction), and
**E3** fold-alignment (the six-phase fold with conjugators connects each enumerated arc).  This round is E1.

  * **`IsBoundaryInvolution`** — the well-formedness gate the recon found ABSENT (`DiagramType.partner` is a bare
    `List Nat` with no involution invariant, so the naive T-ENUM over arbitrary `d` is FALSE): a boundary partner
    that has the right length, maps in range, is self-inverse, and is fixed-point-free.  A `Prop` bundle; inhabited
    (`isBoundaryInvolution_swapPair`), so the gated lemmas are non-vacuous.

  * **the four enumeration-SOUNDNESS lemmas** (`capArcFeetIndices_mem_sound` / `throughStrandBottoms_mem_sound` /
    `throughStrandTops_mem_sound` / `cupArcTopIndices_mem_sound`) — every index the read-off emits genuinely
    satisfies its arc-class predicate (the "no spurious arc" direction).  Involution-FREE (pure `filterMap`-over-
    `List.range` inversion).  These supply the arc LIST the downstream T-CONNECT / T-CLOSE range over.

  * **`cupArcTop_sub_exact`** — the `cupArcTops` `− bottomCount` subtraction is EXACT: on a genuine cup top the
    subtracted partner recovers `bottomCount + (partner − bottomCount) = partner`.  The exact propext trap the recon
    named — discharged additively via `addSubCancelEnum` (`Nat.le.dest`), never `Nat.sub_add_cancel`.

  * **`capArcFeetIndices_arc_closes` + `capArcFeetIndices_excludes_larger_foot`** — under the involution gate each
    cap arc CLOSES (`partner (partner index) = index`) and is listed exactly ONCE (the larger foot `partner index`
    is NOT re-emitted, because it would need `partner index < partner (partner index) = index`, contradicting
    `index < partner index`).  The "each arc once" dedup content.  `cupArcTopIndices_excludes_larger_foot` is the
    ∗-dual on the cup side.

  * **`capFoot_not_throughBottom`** — a cap foot is never a through bottom (their `filterMap` predicates are
    mutually exclusive: `partner < bottomCount` vs `bottomCount ≤ partner`).  The partition skeleton, involution-free.

  * **E2 down-payment** (`descendingSwapPositions_self` / `_ofLe`, `permutationToCrossingWord_zero` / `_one`) — the
    structural base cases of the deferred conjugator-correctness induction: the descending-swap bubble is empty at
    or below its start, and the realizer is empty at width 0 / 1.  Scaffolding for the r14 E2 round.

## The honest residual (E2 + E3, named — this round does NOT close T-ENUM, let alone the masters)

The recon adjudicated the r6 "near-definitional" claim as HALF-RIGHT-AND-MISLEADING: the word is BUILT from the
read-offs, but T-ENUM has three separable pieces and crossing conjugation genuinely breaks the naive alignment.  So:

  * **E2 — conjugator-correctness** (`fxBrauer_hasArcConjugatorLeg = false`): the goal
    `permuteOfCrossingWord n (permutationToCrossingWord n order) = order` for the read-off orders is a
    `permutationRealizerFold` bubble-carry (selection-sort) induction, currently only `decide`-validated on four
    concrete widths (`permutationRealizer_transposition` / `_threeCycle` / `_reversal` / `_width4`).  Its own r14 round.

  * **E3 — fold-alignment** (folded into `fxBrauer_hasArcEnumerationConjugated = false`): the six-phase fold WITH
    the `bottomPerm` / `topPerm` conjugating staircases connects exactly each enumerated arc `(i, d.partner[i])` —
    full T-CONNECT.  The GLUE folds (`capThenCupFold_connects`) give it for CANONICAL positions; routing the actual
    boundary feet through the conjugators is the missing piece.

So `fxBrauer_hasArcEnumeration = true` (E1) but `fxBrauer_hasArcEnumerationConjugated = false` (E1 ∧ E2 ∧ E3), and
the masters `fxBrauer_hasTagCorrDisjoint` / `fxBrauer_hasTagCorrExtraction`, the roundtrip nodes, and the
completeness flags stay honestly `false`; #2013 does NOT close.  The E1 lemmas are the LIST the T-CLOSE assembly
(`extractDiagram_realizes_partner_ofConnectivity`, still named only in the R5 ledger) will range over once E2 ∧ E3
land, feeding `partnerIndexOf_readsPartner_reachable` (`Brauer/WiringDescBoundaryPartneredFold.lean`) per arc.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The propext-free arithmetic + membership kit (private, re-derived per the zero-dep discipline)

The `Nat.blt` / `Nat.ble` / `&&` deciders, `List.range` membership, and `filterMap` inversion Lean core supplies
route through `propext` / `Quot.sound`.  These private copies are the structural, full-enum-`Bool`-match
replacements the codebase re-derives per file (mirroring `WiringDescCombFold`'s `natLtOfBlt` kit,
`ArcPartitionCommute`'s `mem_range_imp_lt`, and `ExtractionMembership`'s `listMemFilterMapInverted`). -/

/-- Left projection of a true boolean conjunction — full-enum `Bool` match, `propext`-free. -/
private theorem boolAndLeftEnum : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → leftFlag = true
  | true, _, _ => rfl
  | false, _, conj => Bool.noConfusion conj

/-- Right projection of a true boolean conjunction. -/
private theorem boolAndRightEnum : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → rightFlag = true
  | true, _, conj => conj
  | false, _, conj => Bool.noConfusion conj

/-- `Nat.ble a b = true` from `a ≤ b` — structural on `a`, `propext`-free. -/
private theorem natBleOfLeEnum : (a b : Nat) → a ≤ b → Nat.ble a b = true
  | 0, _, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | a + 1, b + 1, h => natBleOfLeEnum a b (Nat.le_of_succ_le_succ h)

/-- `a ≤ b` from `Nat.ble a b = true` — structural on `a`, `propext`-free. -/
private theorem natLeOfBleEnum : (a b : Nat) → Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => Bool.noConfusion h
  | a + 1, b + 1, h => Nat.succ_le_succ (natLeOfBleEnum a b h)

/-- `a < b` from `Nat.blt a b = true` — `Nat.blt a b` is `Nat.ble (a+1) b`. -/
private theorem natLtOfBltEnum (a b : Nat) (h : Nat.blt a b = true) : a < b := natLeOfBleEnum (a + 1) b h

/-- `a ≤ b → a - b = 0` — structural, `propext`-free (Lean core's `Nat.sub_eq_zero_of_le` leaks `propext`). -/
private theorem natSubEqZeroOfLeEnum : (a b : Nat) → a ≤ b → a - b = 0
  | 0, b, _ => Nat.zero_sub b
  | a + 1, 0, h => absurd h (Nat.not_succ_le_zero a)
  | a + 1, b + 1, h => by
      rw [Nat.succ_sub_succ]
      exact natSubEqZeroOfLeEnum a b (Nat.le_of_succ_le_succ h)

/-- A bounded eliminator for `index < 2` — casing the two live indices, the rest refuted by a hand-built
`Nat.le` chain (no equation-compiler exhaustiveness magic, hence `propext`-free). -/
private theorem boundedTwoElim {motive : Nat → Prop} (h0 : motive 0) (h1 : motive 1) :
    (index : Nat) → index < 2 → motive index
  | 0, _ => h0
  | 1, _ => h1
  | _ + 2, h => absurd h (fun hc =>
      Nat.not_succ_le_zero _ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hc)))

/-- `n ≤ i → n + (i - n) = i` — structural, `propext`-free (the `Nat.le.dest` discharge, never `Nat.sub_add_cancel`). -/
private theorem addSubCancelEnum : (n i : Nat) → n ≤ i → n + (i - n) = i
  | 0, i, _ => by rw [Nat.zero_add, Nat.sub_zero]
  | n + 1, 0, h => absurd h (Nat.not_succ_le_zero n)
  | n + 1, i + 1, h => by
      rw [show (i + 1) - (n + 1) = i - n from Nat.succ_sub_succ i n, Nat.add_right_comm n 1 (i - n)]
      exact congrArg (· + 1) (addSubCancelEnum n i (Nat.le_of_succ_le_succ h))

/-- `List.range.loop count acc` lists `0 … count-1` in front of `acc` — a member is below `count` or in `acc`.
Structural on `count`, `propext`-free (Lean core's `List.mem_range` leaks `propext`). -/
private theorem memRangeLoopEnum {target : Nat} :
    (count : Nat) → (acc : List Nat) → target ∈ List.range.loop count acc → target < count ∨ target ∈ acc
  | 0, _, membership => Or.inr membership
  | count + 1, acc, membership => by
      cases memRangeLoopEnum count (count :: acc) membership with
      | inl isBelow => exact Or.inl (Nat.lt_succ_of_lt isBelow)
      | inr consMembership =>
          cases consMembership with
          | head => exact Or.inl (Nat.lt_succ_self _)
          | tail _ tailMembership => exact Or.inr tailMembership

/-- A member of `List.range count` is below `count` — `propext`-free `List.mem_range.mp`. -/
private theorem memRangeLtEnum {target count : Nat} (membership : target ∈ List.range count) : target < count := by
  cases memRangeLoopEnum count [] membership with
  | inl isBelow => exact isBelow
  | inr nilMembership => nomatch nilMembership

/-- Membership in a `filterMap` inverts to a source member with a `some` image — `propext`-free
(Lean core's `List.mem_filterMap` is an iff leaking `propext`). -/
private theorem memFilterMapInvertedEnum {sourceType targetType : Type}
    {transform : sourceType → Option targetType} {image : targetType} :
    {inputList : List sourceType} → image ∈ inputList.filterMap transform →
    ∃ preimage, preimage ∈ inputList ∧ transform preimage = some image
  | [], imageMem => nomatch imageMem
  | headElement :: remaining, imageMem => by
      cases headImage : transform headElement with
      | none =>
          have imageMemReduced : image ∈ List.filterMap transform remaining := by
            dsimp only [List.filterMap] at imageMem
            rw [headImage] at imageMem
            exact imageMem
          obtain ⟨preimage, preimageMem, preimageEq⟩ := memFilterMapInvertedEnum imageMemReduced
          exact ⟨preimage, List.Mem.tail headElement preimageMem, preimageEq⟩
      | some mappedHead =>
          have imageMemReduced : image ∈ mappedHead :: List.filterMap transform remaining := by
            dsimp only [List.filterMap] at imageMem
            rw [headImage] at imageMem
            exact imageMem
          cases imageMemReduced with
          | head => exact ⟨headElement, List.Mem.head remaining, headImage⟩
          | tail _ innerMembership =>
              obtain ⟨preimage, preimageMem, preimageEq⟩ := memFilterMapInvertedEnum innerMembership
              exact ⟨preimage, List.Mem.tail headElement preimageMem, preimageEq⟩

/-! ## The well-formed boundary involution gate (the recon-found ABSENT invariant) -/

/-- ★ **A well-formed boundary partner matching.**  `DiagramType.partner` carries NO involution invariant, so the
naive T-ENUM over arbitrary `d` is FALSE (the `capArcFeetIndices` dedup and the `cupArcTops` `− bottomCount`
subtraction both RELY on the partner being a fixed-point-free involution).  This gate names that invariant: over the
`total = bottomCount + topCount` boundary ports the partner has the right length, maps in range, is self-inverse
(`partner (partner index) = index`), and is fixed-point-free.  Every `d = extractDiagram foldState` satisfies it (by
the r12 totality + `partnerIndexOf_isInvolution`); that instantiation is the T-CLOSE wiring step, deferred. -/
structure IsBoundaryInvolution (total : Nat) (partner : List Nat) : Prop where
  /-- The partner list spans exactly the `total` boundary ports. -/
  hasBoundaryLength : partner.length = total
  /-- Every boundary port is matched to a boundary port. -/
  mapsInRange : ∀ index, index < total → natListGetAt partner index < total
  /-- The matching is an involution — following a partner edge twice returns to the start. -/
  isSelfInverse : ∀ index, index < total → natListGetAt partner (natListGetAt partner index) = index
  /-- No port is matched to itself. -/
  isFixedPointFree : ∀ index, index < total → natListGetAt partner index ≠ index

/-! ## E1 — the enumeration-soundness lemmas (involution-free) -/

/-- ★ **Cap-foot enumeration soundness.**  Every index `capArcFeetIndices` emits is a genuine bottom–bottom cap
smaller foot: in the bottom range, its partner is a bottom port, and it is the SMALLER of the two feet.  The "no
spurious cap arc" direction — a pure `filterMap`-over-`List.range` inversion, no involution needed. -/
theorem capArcFeetIndices_mem_sound (bottomCount : Nat) (partner : List Nat) (index : Nat)
    (member : index ∈ capArcFeetIndices bottomCount partner) :
    index < bottomCount ∧ natListGetAt partner index < bottomCount ∧ index < natListGetAt partner index := by
  unfold capArcFeetIndices at member
  obtain ⟨preimage, preimageMem, preimageEq⟩ := memFilterMapInvertedEnum member
  have preLt : preimage < bottomCount := memRangeLtEnum preimageMem
  cases hcond : (Nat.blt (natListGetAt partner preimage) bottomCount
      && Nat.blt preimage (natListGetAt partner preimage)) with
  | true =>
      rw [hcond] at preimageEq
      dsimp only at preimageEq
      have indexEq : preimage = index := Option.some.inj preimageEq
      subst indexEq
      exact ⟨preLt, natLtOfBltEnum _ _ (boolAndLeftEnum _ _ hcond),
        natLtOfBltEnum _ _ (boolAndRightEnum _ _ hcond)⟩
  | false =>
      rw [hcond] at preimageEq
      dsimp only at preimageEq
      injection preimageEq

/-- ★ **Through-bottom enumeration soundness.**  Every index `throughStrandBottoms` emits is a genuine through
bottom port: in the bottom range with a TOP partner (`bottomCount ≤ partner`).  Involution-free. -/
theorem throughStrandBottoms_mem_sound (bottomCount : Nat) (partner : List Nat) (index : Nat)
    (member : index ∈ throughStrandBottoms bottomCount partner) :
    index < bottomCount ∧ bottomCount ≤ natListGetAt partner index := by
  unfold throughStrandBottoms at member
  obtain ⟨preimage, preimageMem, preimageEq⟩ := memFilterMapInvertedEnum member
  have preLt : preimage < bottomCount := memRangeLtEnum preimageMem
  cases hcond : Nat.ble bottomCount (natListGetAt partner preimage) with
  | true =>
      rw [hcond] at preimageEq
      dsimp only at preimageEq
      have indexEq : preimage = index := Option.some.inj preimageEq
      subst indexEq
      exact ⟨preLt, natLeOfBleEnum _ _ hcond⟩
  | false =>
      rw [hcond] at preimageEq
      dsimp only at preimageEq
      injection preimageEq

/-- ★ **Through-top enumeration soundness.**  Every top index `throughStrandTops` emits is a genuine through top:
below `topCount` with a BOTTOM partner (`partner (bottomCount + topIndex) < bottomCount`).  Involution-free. -/
theorem throughStrandTops_mem_sound (bottomCount topCount : Nat) (partner : List Nat) (topIndex : Nat)
    (member : topIndex ∈ throughStrandTops bottomCount topCount partner) :
    topIndex < topCount ∧ natListGetAt partner (bottomCount + topIndex) < bottomCount := by
  unfold throughStrandTops at member
  obtain ⟨preimage, preimageMem, preimageEq⟩ := memFilterMapInvertedEnum member
  have preLt : preimage < topCount := memRangeLtEnum preimageMem
  cases hcond : Nat.blt (natListGetAt partner (bottomCount + preimage)) bottomCount with
  | true =>
      rw [hcond] at preimageEq
      dsimp only at preimageEq
      have indexEq : preimage = topIndex := Option.some.inj preimageEq
      subst indexEq
      exact ⟨preLt, natLtOfBltEnum _ _ hcond⟩
  | false =>
      rw [hcond] at preimageEq
      dsimp only at preimageEq
      injection preimageEq

/-- ★ **Cup-top enumeration soundness.**  Every top index `cupArcTopIndices` emits is a genuine top–top cup smaller
top foot: below `topCount`, its partner is a TOP port (`bottomCount ≤ partner`), and its port is the SMALLER of the
two (`bottomCount + topIndex < partner`).  Involution-free. -/
theorem cupArcTopIndices_mem_sound (bottomCount topCount : Nat) (partner : List Nat) (topIndex : Nat)
    (member : topIndex ∈ cupArcTopIndices bottomCount topCount partner) :
    topIndex < topCount
      ∧ bottomCount ≤ natListGetAt partner (bottomCount + topIndex)
      ∧ bottomCount + topIndex < natListGetAt partner (bottomCount + topIndex) := by
  unfold cupArcTopIndices at member
  obtain ⟨preimage, preimageMem, preimageEq⟩ := memFilterMapInvertedEnum member
  have preLt : preimage < topCount := memRangeLtEnum preimageMem
  cases hcond : (Nat.ble bottomCount (natListGetAt partner (bottomCount + preimage))
      && Nat.blt (bottomCount + preimage) (natListGetAt partner (bottomCount + preimage))) with
  | true =>
      rw [hcond] at preimageEq
      dsimp only at preimageEq
      have indexEq : preimage = topIndex := Option.some.inj preimageEq
      subst indexEq
      exact ⟨preLt, natLeOfBleEnum _ _ (boolAndLeftEnum _ _ hcond),
        natLtOfBltEnum _ _ (boolAndRightEnum _ _ hcond)⟩
  | false =>
      rw [hcond] at preimageEq
      dsimp only at preimageEq
      injection preimageEq

/-! ## E1 — the `cupArcTops` `− bottomCount` subtraction is exact (the named propext trap) -/

/-- ★ **The `cupArcTops` `− bottomCount` subtraction is EXACT.**  On a genuine cup top foot the subtracted partner
recovers the partner exactly: `bottomCount + (partner (bottomCount + topIndex) − bottomCount)
= partner (bottomCount + topIndex)`.  This is the `Nat.sub` the recon flagged as a propext trap — discharged
additively via `addSubCancelEnum` (`Nat.le.dest`), NEVER `Nat.sub_add_cancel`.  So `expandCupTopPairs`' top-index
`partner − bottomCount` genuinely names the partner top. -/
theorem cupArcTop_sub_exact (bottomCount topCount : Nat) (partner : List Nat) (topIndex : Nat)
    (member : topIndex ∈ cupArcTopIndices bottomCount topCount partner) :
    bottomCount + (natListGetAt partner (bottomCount + topIndex) - bottomCount)
      = natListGetAt partner (bottomCount + topIndex) :=
  addSubCancelEnum bottomCount (natListGetAt partner (bottomCount + topIndex))
    (cupArcTopIndices_mem_sound bottomCount topCount partner topIndex member).2.1

/-! ## E1 — the arc classes are mutually exclusive (the partition skeleton, involution-free) -/

/-- ★ **A cap foot is never a through bottom.**  The two `filterMap` predicates are mutually exclusive — a cap foot
has a BOTTOM partner (`partner < bottomCount`) while a through bottom has a TOP partner (`bottomCount ≤ partner`).
Involution-free; the bottom-boundary half of "the arc families partition the boundary". -/
theorem capFoot_not_throughBottom (bottomCount : Nat) (partner : List Nat) (index : Nat)
    (capMember : index ∈ capArcFeetIndices bottomCount partner)
    (throughMember : index ∈ throughStrandBottoms bottomCount partner) : False :=
  Nat.lt_irrefl (natListGetAt partner index)
    (Nat.lt_of_lt_of_le (capArcFeetIndices_mem_sound bottomCount partner index capMember).2.1
      (throughStrandBottoms_mem_sound bottomCount partner index throughMember).2)

/-! ## E1 — each cap arc closes and is listed exactly once (the involution-gated dedup) -/

/-- ★ **Each cap arc CLOSES under the involution gate.**  For a cap smaller foot `index`, following the partner edge
twice returns to `index`: `partner (partner index) = index`.  So `capArcFeet`'s pair `[index, partner index]` is a
genuine closed cap arc.  Uses only `isSelfInverse` (with `index < bottomCount ≤ total`). -/
theorem capArcFeetIndices_arc_closes (bottomCount total : Nat) (partner : List Nat)
    (bottomLe : bottomCount ≤ total) (wf : IsBoundaryInvolution total partner)
    (index : Nat) (member : index ∈ capArcFeetIndices bottomCount partner) :
    natListGetAt partner (natListGetAt partner index) = index :=
  wf.isSelfInverse index
    (Nat.lt_of_lt_of_le (capArcFeetIndices_mem_sound bottomCount partner index member).1 bottomLe)

/-- ★ **Each cap arc is listed exactly ONCE.**  The LARGER foot `partner index` of a cap arc is NOT emitted by
`capArcFeetIndices`: were it, cup soundness would give `partner index < partner (partner index) = index`, but the
smaller-foot condition already gives `index < partner index` — a contradiction.  Under the involution gate, so
`capArcFeetIndices` lists each bottom–bottom cap arc once (by its smaller foot). -/
theorem capArcFeetIndices_excludes_larger_foot (bottomCount total : Nat) (partner : List Nat)
    (bottomLe : bottomCount ≤ total) (wf : IsBoundaryInvolution total partner)
    (index : Nat) (memberIndex : index ∈ capArcFeetIndices bottomCount partner)
    (memberLarger : natListGetAt partner index ∈ capArcFeetIndices bottomCount partner) : False := by
  have smallSound := capArcFeetIndices_mem_sound bottomCount partner index memberIndex
  have largeSound := capArcFeetIndices_mem_sound bottomCount partner (natListGetAt partner index) memberLarger
  have closes : natListGetAt partner (natListGetAt partner index) = index :=
    capArcFeetIndices_arc_closes bottomCount total partner bottomLe wf index memberIndex
  have largerLtIndex : natListGetAt partner index < index := by
    have step := largeSound.2.2
    rw [closes] at step
    exact step
  exact Nat.lt_irrefl index (Nat.lt_trans smallSound.2.2 largerLtIndex)

/-- ★ **The ∗-dual cup dedup — each cup arc is listed exactly ONCE.**  The LARGER top foot of a cup arc (the top
index `partner (bottomCount + topIndex) − bottomCount`) is NOT re-emitted by `cupArcTopIndices`: its port
`partner (bottomCount + topIndex)` sends back to `bottomCount + topIndex` (involution), which is SMALLER than it, so
the smaller-top condition fails.  Under the involution gate, so `cupArcTopIndices` lists each top–top cup arc once. -/
theorem cupArcTopIndices_excludes_larger_foot (bottomCount topCount : Nat) (partner : List Nat)
    (wf : IsBoundaryInvolution (bottomCount + topCount) partner)
    (topIndex : Nat) (memberSmall : topIndex ∈ cupArcTopIndices bottomCount topCount partner)
    (memberLarge : natListGetAt partner (bottomCount + topIndex) - bottomCount
      ∈ cupArcTopIndices bottomCount topCount partner) : False := by
  have smallSound := cupArcTopIndices_mem_sound bottomCount topCount partner topIndex memberSmall
  have largePort : bottomCount + (natListGetAt partner (bottomCount + topIndex) - bottomCount)
      = natListGetAt partner (bottomCount + topIndex) :=
    cupArcTop_sub_exact bottomCount topCount partner topIndex memberSmall
  have largeSound := cupArcTopIndices_mem_sound bottomCount topCount partner
    (natListGetAt partner (bottomCount + topIndex) - bottomCount) memberLarge
  have smallPortLt : bottomCount + topIndex < bottomCount + topCount :=
    Nat.add_lt_add_left smallSound.1 bottomCount
  have closes : natListGetAt partner (natListGetAt partner (bottomCount + topIndex)) = bottomCount + topIndex :=
    wf.isSelfInverse (bottomCount + topIndex) smallPortLt
  have largerLt : natListGetAt partner (bottomCount + topIndex) < bottomCount + topIndex := by
    have step := largeSound.2.2
    rw [largePort, closes] at step
    exact step
  exact Nat.lt_irrefl (bottomCount + topIndex) (Nat.lt_trans smallSound.2.2 largerLt)

/-! ## E2 down-payment — the deferred conjugator induction's structural base cases -/

/-- The descending-swap bubble from an index to ITSELF is empty (`endIndex - endIndex = 0`). -/
theorem descendingSwapPositions_self (endIndex : Nat) : descendingSwapPositions endIndex endIndex = [] := by
  unfold descendingSwapPositions
  rw [Nat.sub_self]
  rfl

/-- The descending-swap bubble is empty whenever the end is at or below the start. -/
theorem descendingSwapPositions_ofLe (endIndex startIndex : Nat) (le : endIndex ≤ startIndex) :
    descendingSwapPositions endIndex startIndex = [] := by
  unfold descendingSwapPositions
  rw [natSubEqZeroOfLeEnum endIndex startIndex le]
  rfl

/-- The permutation realizer is empty at width 0 (nothing to place). -/
theorem permutationToCrossingWord_zero (perm : List Nat) : permutationToCrossingWord 0 perm = [] := rfl

/-- The permutation realizer is empty at width 1 (a single strand is already placed). -/
theorem permutationToCrossingWord_one (perm : List Nat) : permutationToCrossingWord 1 perm = [] := rfl

/-! ## Non-vacuity — the gate is inhabited and the soundness lemmas fire on the adversarial-B diagram -/

/-- ★ **The involution gate is INHABITED.**  The single-cap boundary partner `[1, 0]` over two ports has the right
length, maps in range, is self-inverse, and is fixed-point-free — so the gated dedup lemmas are non-vacuous. -/
theorem isBoundaryInvolution_swapPair : IsBoundaryInvolution 2 [1, 0] where
  hasBoundaryLength := rfl
  mapsInRange := boundedTwoElim (motive := fun index => natListGetAt [1, 0] index < 2)
    (by decide) (by decide)
  isSelfInverse := boundedTwoElim
    (motive := fun index => natListGetAt [1, 0] (natListGetAt [1, 0] index) = index) rfl rfl
  isFixedPointFree := boundedTwoElim (motive := fun index => natListGetAt [1, 0] index ≠ index)
    (by decide) (by decide)

/-- ★ **Non-vacuity — cap soundness fires on the adversarial-B cap arc.**  Boundary index `0` is a genuine cap
smaller foot of `adversarialBDiagram` (partner `[2, 4, 0, 5, 1, 3]`): in range, partner `2 < 3`, and `0 < 2`. -/
theorem capArcFeetIndices_mem_sound_adversarialB :
    (0 : Nat) < 3
      ∧ natListGetAt adversarialBDiagram.partner 0 < 3
      ∧ (0 : Nat) < natListGetAt adversarialBDiagram.partner 0 :=
  capArcFeetIndices_mem_sound 3 adversarialBDiagram.partner 0 (List.Mem.head [])

/-- ★ **Non-vacuity — cup soundness + sub-exactness fire on the adversarial-B cup arc.**  Top index `0` is a genuine
cup smaller top foot, and `bottomCount + (partner (bottomCount + 0) − bottomCount) = partner (bottomCount + 0)`
(the `− bottomCount` is exact: `3 + (5 − 3) = 5`). -/
theorem cupArcTop_sub_exact_adversarialB :
    3 + (natListGetAt adversarialBDiagram.partner (3 + 0) - 3)
      = natListGetAt adversarialBDiagram.partner (3 + 0) :=
  cupArcTop_sub_exact 3 3 adversarialBDiagram.partner 0 (List.Mem.head [])

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the T-ENUM ENUMERATION half (E1) is SHIPPED (r13).**  The four enumeration-soundness
lemmas (`capArcFeetIndices_mem_sound` / `throughStrandBottoms_mem_sound` / `throughStrandTops_mem_sound` /
`cupArcTopIndices_mem_sound`) prove the `filterMap` read-offs emit only genuine arc-class members; `cupArcTop_sub_exact`
proves the `cupArcTops` `− bottomCount` subtraction exact (the named propext trap); under the `IsBoundaryInvolution`
gate `capArcFeetIndices_arc_closes` + `capArcFeetIndices_excludes_larger_foot` (and the ∗-dual
`cupArcTopIndices_excludes_larger_foot`) prove each arc closes and is listed exactly once; `capFoot_not_throughBottom`
gives the partition skeleton.  Fires on the adversarial-B diagram (`capArcFeetIndices_mem_sound_adversarialB`,
`cupArcTop_sub_exact_adversarialB`).  GENUINELY NEW — the read-offs had NO enumeration lemma before this round.
`= true`. -/
def fxBrauer_hasArcEnumeration : Bool := true

/-- **Honesty WALL marker — the conjugator-correctness leg (E2) is NOT built (the r13 residual).**  The goal
`permuteOfCrossingWord n (permutationToCrossingWord n order) = order` for the read-off orders — that the
`permutationToCrossingWord` staircases genuinely realize the enumeration orders — is a `permutationRealizerFold`
bubble-carry (selection-sort) induction, currently only `decide`-validated on four concrete widths
(`permutationRealizer_transposition` / `_threeCycle` / `_reversal` / `_width4`).  Only the structural base cases are
shipped this round (`descendingSwapPositions_self` / `_ofLe`, `permutationToCrossingWord_zero` / `_one`).  Its own
r14 round; NOT near-definitional (the recon adjudicated the r6 "near-definitional" claim as misleading — crossing
conjugation genuinely breaks the naive alignment).  `= false`. -/
def fxBrauer_hasArcConjugatorLeg : Bool := false

/-- **Honesty WALL marker — the CONJUGATED enumeration (full T-ENUM = E1 ∧ E2 ∧ E3) is NOT assembled.**  E1 (this
round) supplies the arc LIST; but wiring it into `partnerIndexOf_readsPartner_reachable` to pin
`extractDiagram foldState = d` per arc needs E2 (conjugator-correctness, `fxBrauer_hasArcConjugatorLeg`) AND E3
(fold-alignment: the six-phase fold WITH the `bottomPerm` / `topPerm` staircases connects each enumerated arc
`(i, d.partner[i])` — full T-CONNECT, the GLUE folds give only the canonical positions).  Both unbuilt, so the
masters `fxBrauer_hasTagCorrDisjoint` / `fxBrauer_hasTagCorrExtraction`, the roundtrip nodes, and the completeness
flags stay honestly `false`; #2013 does NOT close.  `= false`. -/
def fxBrauer_hasArcEnumerationConjugated : Bool := false

/-- ★★★ **The BRAUER-MIDDLE r13 GRAND LEDGER — MACHINE-CHECKED.**  The r13 T-ENUM E1 marker
(`fxBrauer_hasArcEnumeration`) is `true`, on top of the shipped r11→r12 markers (the fold lift, the extraction
read-off, the partner-totality seed + fold, the wired firing); and EVERY remaining wall — the E2 conjugator leg, the
full conjugated-enumeration node, both tag-correspondence masters (`fxBrauer_hasTagCorrDisjoint`,
`fxBrauer_hasTagCorrExtraction`), the extractor-totality roundtrip nodes, and the master completeness flags — is
`false`.  A `rfl`-conjunction the kernel checks over the shipped markers: r13 shipped the arc-enumeration soundness
half of T-ENUM, but the conjugator-correctness (E2) and fold-alignment (E3) are unbuilt, so the two-source master
assembly is not wired, no master flip is fabricated, and #2013 does NOT close. -/
theorem fxBrauer_r13Ledger :
    (fxBrauer_hasBoundedBoundaryFoldLift = true
      ∧ fxBrauer_hasPartnerReadOff = true
      ∧ fxBrauer_hasBoundaryPartneredFold = true
      ∧ fxBrauer_hasReadOffWiredFiring = true
      ∧ fxBrauer_hasArcEnumeration = true)
    ∧ (fxBrauer_hasArcConjugatorLeg = false
      ∧ fxBrauer_hasArcEnumerationConjugated = false)
    ∧ (fxBrauer_hasTagCorrDisjoint = false
      ∧ fxBrauer_hasTagCorrExtraction = false)
    ∧ (fxBrauer_hasExt5CorrectedRoundtripProof = false
      ∧ fxBrauer_hasExt5TotalExtractorRoundtrip = false)
    ∧ (fxBrauer_hasBrauerV2FullCompleteness = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- ★★ **Honesty marker — BRAUER-MIDDLE r13 did NOT close #2013.**  The round shipped the ENUMERATION half (E1) of
T-ENUM — the four `filterMap` soundness lemmas, the `cupArcTops` `− bottomCount` exactness, the involution-gated cap
+ cup "each arc once" dedup, the partition skeleton, and the conjugator base cases — each zero-axiom and structural,
firing on the adversarial-B diagram.  But T-ENUM's conjugator-correctness (E2) and fold-alignment (E3) are named,
not built, so the read-off is not wired to a specific `d`, both tag-correspondence masters and the completeness
flags stay `false`, and #2013 does not close — every residual a ROUTE / totality gap, never a truth gap
(Lehrer–Zhang arXiv:1207.5889 Thm 2.6 guarantees the underlying completeness).  `= false`. -/
def fxBrauer_hasBrauerMiddleR13Complete : Bool := false

end FX1Poly.Polygraph
