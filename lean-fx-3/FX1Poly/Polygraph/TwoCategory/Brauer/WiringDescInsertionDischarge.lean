import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStaircaseCanonical

/-! # WP-BRAUER r13 — `InRangeInsertionStep` DISCHARGED: the insertion residual falls to the comb staircase

The honest in-range insertion residual `InRangeInsertionStep` (`Brauer/WiringDescInsertion.lean`) — for every
genuine (distinct-entry) permutation `perm` and in-range `position + 1 < perm.length`,
`canonicalCrossingWord perm ++ [position]` is `BrauerConvFree7`-convertible to
`canonicalCrossingWord (applyAdjacentSwap perm position)` — is INHABITED here, as a COROLLARY of the shipped
comb-staircase straightening `crossingWords_equalPerm_conv` (`Brauer/WiringDescStaircaseCanonical.lean`, the
BREACH r2 route).  The route: both sides are crossing words over generators strictly below `perm.length - 1`
(the range certificate) realizing the SAME through-strand permutation (the realization + equivariance kit), so
the staircase straightening converts them.  No insertion-route move (EXTEND / CANCEL / COMMUTE / BRAID carry) is
touched — the braid-ascent WALL analysis of r12 stands as the honest record of the insertion-internal route; the
Prop itself is now proven through the alternate door.

## The three bricks

  * **The range certificate** (`canonicalCrossingWord_mentionsOnlyBelow`): every letter of the canonical word is
    strictly below `perm.length - 1` — each recorded letter is a GENUINE leftmost descent of an intermediate
    same-length list (`leftmostDescent_blt_predLength`), threaded through the bubble fuel
    (`bubbleWordFueled_mentionsOnlyBelow`) and the reversal.
  * **The realization** (`canonicalCrossingWord_realizes_lehmerStandardize`): for a DISTINCT list,
    `permuteOfCrossingWord perm.length (canonicalCrossingWord perm) = lehmerStandardize perm` — the Lehmer
    standardization (each entry replaced by its rank `countEntriesBelow entry perm`).  NOTE the honest correction:
    the naive form `... = perm` is FALSE off the range-permutation domain (`perm = [5, 7]`: canonical word `[]`,
    realization `[0, 1] != [5, 7]` — `canonicalRealization_smoke_nonRangeAscending`), and `InRangeInsertionStep`
    quantifies over ALL distinct lists; the standardization is the invariant that survives.  Proof: fuel induction
    on `inversionCount` via the shipped staircase-snoc (`canonicalCrossingWord_snoc_leftmostDescent`), the Lehmer
    drop (`inversionCount_ofLeftmostDescentSwap_succ`), the snoc law (`permuteOfCrossingWord_snoc`), the swap
    involution — plus the identity base `lehmerStandardize_ofIdentityDistinct` (a strictly-ascending list
    standardizes to `List.range`).
  * **The equivariance** (`lehmerStandardize_applyAdjacentSwap`): the standardization commutes with every adjacent
    swap — ranks are multiset-determined (`countEntriesBelow_applyAdjacentSwap`), positions merely permute.

`canonicalInsertion_permEq` chains the three into the equal-permutation hypothesis;
`crossingWords_equalPerm_conv` finishes.  Corollaries: `braidAscentInsertionStep_holds` (the r9 leaf Prop
`BraidAscentInsertionStep` is inhabited — the sharpest named residual closes), and the r7 well-formed folds become
UNCONDITIONAL (`crossingOnly_straightens_unconditional`, `crossingWords_equalPerm_conv_wellFormed_unconditional`).

Raw Lean 4 + Init; structural recursion only (fuel = `inversionCount`); no `omega` / `simp` / `decide` /
`native_decide` / `WellFounded.fix`.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph

/-! ## Local propext-free structural helpers (private re-derivations; the shipped originals are `private`) -/

/-- Left projection of a true boolean conjunction — full-enum `Bool` match, `propext`-free. -/
private theorem boolAndTrueLeftLocal : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true →
    leftFlag = true
  | true, _, _ => rfl
  | false, _, conj => Bool.noConfusion conj

/-- Right projection of a true boolean conjunction. -/
private theorem boolAndTrueRightLocal : (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true →
    rightFlag = true
  | true, _, conj => conj
  | false, _, conj => Bool.noConfusion conj

/-- Left projection of a false boolean disjunction. -/
private theorem boolOrFalseLeftLocal : (leftFlag rightFlag : Bool) → (leftFlag || rightFlag) = false →
    leftFlag = false
  | false, _, _ => rfl
  | true, _, disj => Bool.noConfusion disj

/-- Reflect `not flag = true` to `flag = false` — full-enum `Bool`, `propext`-free. -/
private theorem eqFalseOfNotTrueLocal : (flag : Bool) → (not flag) = true → flag = false
  | false, _ => rfl
  | true, notTrue => Bool.noConfusion notTrue

/-- Collapse a two-branch `Bool` match whose scrutinee is known `false` — structural, no match-motive `propext`. -/
private theorem condFalseLocal {alpha : Type _} (thenValue elseValue : alpha) :
    (scrutinee : Bool) → scrutinee = false →
    (match scrutinee with | true => thenValue | false => elseValue) = elseValue
  | false, _ => rfl
  | true, scrutineeFalse => Bool.noConfusion scrutineeFalse

/-- Collapse a two-branch `Bool` match whose scrutinee is known `true` — mirror of `condFalseLocal`. -/
private theorem condTrueLocal {alpha : Type _} (thenValue elseValue : alpha) :
    (scrutinee : Bool) → scrutinee = true →
    (match scrutinee with | true => thenValue | false => elseValue) = thenValue
  | true, _ => rfl
  | false, scrutineeTrue => Bool.noConfusion scrutineeTrue

/-- `Nat.beq` is symmetric — structural on both `Nat`s. -/
private theorem natBeqSymmLocal : (leftValue rightValue : Nat) →
    Nat.beq leftValue rightValue = Nat.beq rightValue leftValue
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | _ + 1, 0 => rfl
  | leftValue + 1, rightValue + 1 => natBeqSymmLocal leftValue rightValue

/-- `Nat.ble (value + 1) value = false` — the strict-below-self round-trip, structural. -/
private theorem natBleSuccSelfFalseLocal : (value : Nat) → Nat.ble (value + 1) value = false
  | 0 => rfl
  | value + 1 => natBleSuccSelfFalseLocal value

/-- `Nat.blt value value = false` — nothing is strictly below itself. -/
private theorem natBltSelfFalseLocal (value : Nat) : Nat.blt value value = false :=
  natBleSuccSelfFalseLocal value

/-- `Nat.blt 0 (value + 1) = true` — zero is below every successor. -/
private theorem natBltZeroSuccLocal (value : Nat) : Nat.blt 0 (value + 1) = true := rfl

/-- `Nat.blt` antisymmetry — `right < left` rules out `left < right`.  Structural on both `Nat`s. -/
private theorem natBltAsymmLocal : (leftValue rightValue : Nat) →
    Nat.blt rightValue leftValue = true → Nat.blt leftValue rightValue = false
  | 0, 0, bltTrue => Bool.noConfusion bltTrue
  | 0, _ + 1, bltTrue => Bool.noConfusion bltTrue
  | _ + 1, 0, _ => rfl
  | leftValue + 1, rightValue + 1, bltTrue => natBltAsymmLocal leftValue rightValue bltTrue

/-- `Nat.blt larger smaller = false → Nat.ble smaller larger = true` — the antisymmetric complement. -/
private theorem bleOfNotBltSwapLocal : (smaller larger : Nat) → Nat.blt larger smaller = false →
    Nat.ble smaller larger = true
  | 0, _, _ => rfl
  | _ + 1, 0, bltFalse => Bool.noConfusion bltFalse
  | smaller + 1, larger + 1, bltFalse => bleOfNotBltSwapLocal smaller larger bltFalse

/-- A distinct `≤` pair is `<` — `Nat.ble` plus `Nat.beq = false` gives `Nat.blt`.  Structural. -/
private theorem bltOfBleNeqLocal : (smaller larger : Nat) → Nat.ble smaller larger = true →
    Nat.beq smaller larger = false → Nat.blt smaller larger = true
  | 0, 0, _, beqFalse => Bool.noConfusion beqFalse
  | 0, _ + 1, _, _ => rfl
  | _ + 1, 0, bleTrue, _ => Bool.noConfusion bleTrue
  | smaller + 1, larger + 1, bleTrue, beqFalse => bltOfBleNeqLocal smaller larger bleTrue beqFalse

/-- `Nat.ble` transitivity — structural on all three `Nat`s. -/
private theorem natBleTransLocal : (lower mid upper : Nat) →
    Nat.ble lower mid = true → Nat.ble mid upper = true → Nat.ble lower upper = true
  | 0, _, _, _, _ => rfl
  | _ + 1, 0, _, bleLowerMid, _ => Bool.noConfusion bleLowerMid
  | _ + 1, _ + 1, 0, _, bleMidUpper => Bool.noConfusion bleMidUpper
  | lower + 1, mid + 1, upper + 1, bleLowerMid, bleMidUpper =>
      natBleTransLocal lower mid upper bleLowerMid bleMidUpper

/-- Weaken a strict lower bound to a weak one — `Nat.ble (value + 1) bound → Nat.ble value bound`. -/
private theorem natBleOfBleSuccLeftLocal : (lower upper : Nat) →
    Nat.ble (lower + 1) upper = true → Nat.ble lower upper = true
  | 0, _, _ => rfl
  | _ + 1, 0, bleTrue => Bool.noConfusion bleTrue
  | lower + 1, upper + 1, bleTrue => natBleOfBleSuccLeftLocal lower upper bleTrue

/-- `Nat.blt` transitivity, via the two `ble` legs. -/
private theorem natBltTransLocal (low mid high : Nat)
    (lowBelowMid : Nat.blt low mid = true) (midBelowHigh : Nat.blt mid high = true) :
    Nat.blt low high = true :=
  natBleTransLocal (low + 1) mid high lowBelowMid (natBleOfBleSuccLeftLocal mid high midBelowHigh)

/-- Reflect a propositional `≤` to a true `Nat.ble` — structural. -/
private theorem bleOfLeLocal : (lower upper : Nat) → lower ≤ upper → Nat.ble lower upper = true
  | 0, _, _ => rfl
  | _ + 1, 0, succLeZero => absurd succLeZero (Nat.not_succ_le_zero _)
  | lower + 1, upper + 1, succLeSucc => bleOfLeLocal lower upper (Nat.le_of_succ_le_succ succLeSucc)

/-- `value ≤ 0 → value = 0` — structural. -/
private theorem natEqZeroOfLeZeroLocal : (value : Nat) → value ≤ 0 → value = 0
  | 0, _ => rfl
  | _ + 1, succLeZero => absurd succLeZero (Nat.not_succ_le_zero _)

/-- `value - 1 + 1 = value` when `1 ≤ value` — structural (positivity rules out `0`). -/
private theorem predSuccOfPosLocal : (value : Nat) → 1 ≤ value → value - 1 + 1 = value
  | 0, positive => absurd positive (Nat.not_succ_le_zero 0)
  | _ + 1, _ => rfl

/-- `1 + value = value + 1` — structural on `value`. -/
private theorem onePlusCommLocal : (value : Nat) → 1 + value = value + 1
  | 0 => rfl
  | value + 1 => congrArg Nat.succ (onePlusCommLocal value)

/-- Right-associate a snoc through a following append — structural, avoids Init's `List.append_assoc`. -/
private theorem appendSnocAssocLocal {alpha : Type _} :
    (frontList : List alpha) → (midElement : alpha) → (tailList : List alpha) →
    (frontList ++ [midElement]) ++ tailList = frontList ++ (midElement :: tailList)
  | [], _, _ => rfl
  | headElement :: restList, midElement, tailList =>
      congrArg (headElement :: ·) (appendSnocAssocLocal restList midElement tailList)

/-- `List.reverseAux list acc = List.reverse list ++ acc` — the accumulator floats out.  Structural. -/
private theorem reverseAuxAppendLocal {alpha : Type _} :
    (list : List alpha) → (accumulated : List alpha) →
    List.reverseAux list accumulated = List.reverse list ++ accumulated
  | [], _ => rfl
  | headElement :: tailList, accumulated => by
      show List.reverseAux tailList (headElement :: accumulated)
          = List.reverseAux tailList [headElement] ++ accumulated
      rw [reverseAuxAppendLocal tailList (headElement :: accumulated),
        reverseAuxAppendLocal tailList [headElement]]
      exact (appendSnocAssocLocal (List.reverse tailList) headElement accumulated).symm

/-- `List.reverse (head :: tail) = List.reverse tail ++ [head]` — the propext-free `reverse_cons`. -/
private theorem reverseConsLocal2 {alpha : Type _} (headElement : alpha) (tailList : List alpha) :
    List.reverse (headElement :: tailList) = List.reverse tailList ++ [headElement] := by
  show List.reverseAux tailList [headElement] = List.reverse tailList ++ [headElement]
  exact reverseAuxAppendLocal tailList [headElement]

/-- Reduce `countEntriesBelow` on a cons whose head IS below the value — the head contributes `1`. -/
private theorem countEntriesBelow_cons_below (value entryHead : Nat) (rest : List Nat)
    (headBelow : Nat.blt entryHead value = true) :
    countEntriesBelow value (entryHead :: rest) = 1 + countEntriesBelow value rest := by
  dsimp only [countEntriesBelow]; rw [headBelow]

/-- Reduce `countEntriesBelow` on a cons whose head is NOT below the value — the head contributes `0`. -/
private theorem countEntriesBelow_cons_notBelow (value entryHead : Nat) (rest : List Nat)
    (headNotBelow : Nat.blt entryHead value = false) :
    countEntriesBelow value (entryHead :: rest) = countEntriesBelow value rest := by
  dsimp only [countEntriesBelow]; rw [headNotBelow]; exact Nat.zero_add _

/-! ## Brick (b) — the range certificate: every canonical-word letter is strictly below `length - 1`

Each letter the bubble word records is the leftmost descent of a NON-IDENTITY intermediate list of the SAME
length, and a genuine adjacent descent lives at a position `< length - 1`.  Reversal preserves the certificate. -/

/-- ★ **A genuine leftmost descent is strictly below `length - 1`.**  A non-identity list has its leftmost descent
at a real adjacent junction, of which there are only `length - 1` (positions `0 .. length - 2`).  Structural on the
list, mirroring the `leftmostDescent` matcher. -/
theorem leftmostDescent_blt_predLength :
    (perm : List Nat) → isIdentityPerm perm = false →
    Nat.blt (leftmostDescent perm) (perm.length - 1) = true
  | [], nonIdentity => Bool.noConfusion nonIdentity
  | _ :: [], nonIdentity => Bool.noConfusion nonIdentity
  | first :: second :: rest, nonIdentity =>
      match hDescent : Nat.blt second first with
      | true => by
          have leftmostIsZero : leftmostDescent (first :: second :: rest) = 0 :=
            condTrueLocal 0 (leftmostDescent (second :: rest) + 1) (Nat.blt second first) hDescent
          rw [leftmostIsZero]
          show Nat.blt 0 (rest.length + 1) = true
          exact natBltZeroSuccLocal rest.length
      | false => by
          have identityReduces :
              isIdentityPerm (first :: second :: rest) = isIdentityPerm (second :: rest) :=
            condFalseLocal false (isIdentityPerm (second :: rest)) (Nat.blt second first) hDescent
          have tailNonIdentity : isIdentityPerm (second :: rest) = false :=
            identityReduces.symm.trans nonIdentity
          have leftmostIsSucc :
              leftmostDescent (first :: second :: rest) = leftmostDescent (second :: rest) + 1 :=
            condFalseLocal 0 (leftmostDescent (second :: rest) + 1) (Nat.blt second first) hDescent
          rw [leftmostIsSucc]
          show Nat.blt (leftmostDescent (second :: rest)) ((second :: rest).length - 1) = true
          exact leftmostDescent_blt_predLength (second :: rest) tailNonIdentity

/-- ★ **The bubble word mentions only positions strictly below `length - 1`.**  Fuel induction: each recorded
letter is `leftmostDescent` of a non-identity intermediate (`leftmostDescent_blt_predLength`), and the swap
preserves the length (`applyAdjacentSwap_length`), so the bound is stable down the recursion. -/
theorem bubbleWordFueled_mentionsOnlyBelow :
    (fuel : Nat) → (perm : List Nat) →
    mentionsOnlyBelow (perm.length - 1) (bubbleWordFueled fuel perm) = true
  | 0, _ => rfl
  | fuel + 1, perm => by
      match hId : isIdentityPerm perm with
      | true =>
          rw [bubbleWordFueled_identity (fuel + 1) perm hId]
          rfl
      | false =>
          have fueledStep : bubbleWordFueled (fuel + 1) perm
              = leftmostDescent perm
                :: bubbleWordFueled fuel (applyAdjacentSwap perm (leftmostDescent perm)) :=
            condFalseLocal []
              (leftmostDescent perm
                :: bubbleWordFueled fuel (applyAdjacentSwap perm (leftmostDescent perm)))
              (isIdentityPerm perm) hId
          rw [fueledStep]
          show (Nat.blt (leftmostDescent perm) (perm.length - 1)
                && mentionsOnlyBelow (perm.length - 1)
                    (bubbleWordFueled fuel (applyAdjacentSwap perm (leftmostDescent perm)))) = true
          have tailBound :=
            bubbleWordFueled_mentionsOnlyBelow fuel (applyAdjacentSwap perm (leftmostDescent perm))
          rw [applyAdjacentSwap_length perm (leftmostDescent perm)] at tailBound
          rw [leftmostDescent_blt_predLength perm hId, tailBound]
          rfl

/-- Concatenation preserves the `mentionsOnlyBelow` certificate — structural on the front word. -/
private theorem mentionsOnlyBelow_append_true (bound : Nat) :
    (frontWord backWord : List Nat) →
    mentionsOnlyBelow bound frontWord = true → mentionsOnlyBelow bound backWord = true →
    mentionsOnlyBelow bound (frontWord ++ backWord) = true
  | [], _, _, hBack => hBack
  | position :: rest, backWord, hFront, hBack => by
      show (Nat.blt position bound && mentionsOnlyBelow bound (rest ++ backWord)) = true
      rw [boolAndTrueLeftLocal _ _ hFront,
        mentionsOnlyBelow_append_true bound rest backWord (boolAndTrueRightLocal _ _ hFront) hBack]
      rfl

/-- Reversal preserves the `mentionsOnlyBelow` certificate — via the propext-free `reverse_cons` + append. -/
private theorem mentionsOnlyBelow_reverse_true (bound : Nat) :
    (word : List Nat) → mentionsOnlyBelow bound word = true →
    mentionsOnlyBelow bound word.reverse = true
  | [], _ => rfl
  | position :: rest, hWord => by
      rw [reverseConsLocal2 position rest]
      refine mentionsOnlyBelow_append_true bound rest.reverse [position]
        (mentionsOnlyBelow_reverse_true bound rest (boolAndTrueRightLocal _ _ hWord)) ?_
      show (Nat.blt position bound && true) = true
      rw [boolAndTrueLeftLocal _ _ hWord]
      rfl

/-- ★★ **The canonical crossing word mentions only positions strictly below `perm.length - 1`** — the exact
`mentionsOnlyBelow` certificate `crossingWords_equalPerm_conv` consumes at
`generatorCount := perm.length - 1`. -/
theorem canonicalCrossingWord_mentionsOnlyBelow (perm : List Nat) :
    mentionsOnlyBelow (perm.length - 1) (canonicalCrossingWord perm) = true := by
  show mentionsOnlyBelow (perm.length - 1) (bubbleWord perm).reverse = true
  exact mentionsOnlyBelow_reverse_true (perm.length - 1) (bubbleWord perm)
    (bubbleWordFueled_mentionsOnlyBelow (inversionCount perm) perm)

/-! ## The Lehmer standardization + swap equivariance

`lehmerStandardize perm` replaces every entry by its rank (`countEntriesBelow entry perm`).  For a distinct
list this is the order-isomorphic copy of `perm` on `{0 .. length-1}`; it is EXACTLY what
`permuteOfCrossingWord` realizes from the canonical word (the honest correction of the naive `= perm`, which is
FALSE off the range-permutation domain).  Ranks are multiset-determined, so the standardization commutes with
every adjacent swap — the equivariance the permutation-equality hypothesis needs. -/

/-- Rank every entry of `word` against the fixed `reference` multiset. -/
def lehmerRankAgainst (reference : List Nat) : List Nat → List Nat
  | [] => []
  | entry :: rest => countEntriesBelow entry reference :: lehmerRankAgainst reference rest

/-- ★ **The Lehmer standardization** — every entry replaced by its rank among the list's own entries. -/
def lehmerStandardize (perm : List Nat) : List Nat := lehmerRankAgainst perm perm

/-- Swapping the REFERENCE leaves every rank unchanged — ranks are multiset-determined
(`countEntriesBelow_applyAdjacentSwap`).  Structural on the ranked word. -/
private theorem lehmerRankAgainst_referenceSwap (perm : List Nat) (position : Nat) :
    (word : List Nat) →
    lehmerRankAgainst (applyAdjacentSwap perm position) word = lehmerRankAgainst perm word
  | [] => rfl
  | entry :: rest => by
      show countEntriesBelow entry (applyAdjacentSwap perm position)
            :: lehmerRankAgainst (applyAdjacentSwap perm position) rest
          = countEntriesBelow entry perm :: lehmerRankAgainst perm rest
      rw [countEntriesBelow_applyAdjacentSwap entry perm position,
        lehmerRankAgainst_referenceSwap perm position rest]

/-- Swapping the SUBJECT permutes the ranked positions — structural on the swap's own matcher. -/
private theorem lehmerRankAgainst_applyAdjacentSwap (reference : List Nat) :
    (word : List Nat) → (position : Nat) →
    lehmerRankAgainst reference (applyAdjacentSwap word position)
      = applyAdjacentSwap (lehmerRankAgainst reference word) position
  | [], _ => rfl
  | _ :: [], _ => rfl
  | _ :: _ :: _, 0 => rfl
  | first :: second :: rest, position + 1 => by
      show countEntriesBelow first reference
            :: lehmerRankAgainst reference (applyAdjacentSwap (second :: rest) position)
          = countEntriesBelow first reference
            :: applyAdjacentSwap (lehmerRankAgainst reference (second :: rest)) position
      exact congrArg (countEntriesBelow first reference :: ·)
        (lehmerRankAgainst_applyAdjacentSwap reference (second :: rest) position)

/-- ★★ **The standardization commutes with every adjacent swap** — swap the reference back
(`lehmerRankAgainst_referenceSwap`), then permute the subject (`lehmerRankAgainst_applyAdjacentSwap`).  No
distinctness or range hypothesis. -/
theorem lehmerStandardize_applyAdjacentSwap (perm : List Nat) (position : Nat) :
    lehmerStandardize (applyAdjacentSwap perm position)
      = applyAdjacentSwap (lehmerStandardize perm) position := by
  show lehmerRankAgainst (applyAdjacentSwap perm position) (applyAdjacentSwap perm position)
      = applyAdjacentSwap (lehmerRankAgainst perm perm) position
  rw [lehmerRankAgainst_referenceSwap perm position (applyAdjacentSwap perm position),
    lehmerRankAgainst_applyAdjacentSwap perm perm position]

/-! ## The identity base — a strictly-ascending list standardizes to `List.range` -/

/-- Is `low` strictly below EVERY entry of the list?  Structural `Nat.blt` all-scan. -/
private def isBelowAllEntries (low : Nat) : List Nat → Bool
  | [] => true
  | entry :: rest => Nat.blt low entry && isBelowAllEntries low rest

/-- Lower the strict bound of an all-scan along `Nat.blt`-transitivity. -/
private theorem isBelowAllEntries_ofBltHead : (low mid : Nat) → (entries : List Nat) →
    Nat.blt low mid = true → isBelowAllEntries mid entries = true →
    isBelowAllEntries low entries = true
  | _, _, [], _, _ => rfl
  | low, mid, entry :: rest, lowBelowMid, midBelowAll => by
      show (Nat.blt low entry && isBelowAllEntries low rest) = true
      rw [natBltTransLocal low mid entry lowBelowMid (boolAndTrueLeftLocal _ _ midBelowAll),
        isBelowAllEntries_ofBltHead low mid rest lowBelowMid (boolAndTrueRightLocal _ _ midBelowAll)]
      rfl

/-- An identity (no-adjacent-descent) cons has no descent at its junction. -/
private theorem noJunctionDescent_ofIdentityCons (head second : Nat) (rest : List Nat)
    (hId : isIdentityPerm (head :: second :: rest) = true) : Nat.blt second head = false := by
  match hBlt : Nat.blt second head with
  | false => rfl
  | true =>
      have reduce : isIdentityPerm (head :: second :: rest) = false :=
        condTrueLocal false (isIdentityPerm (second :: rest)) (Nat.blt second head) hBlt
      exact Bool.noConfusion (reduce.symm.trans hId)

/-- The tail of an identity cons is identity. -/
private theorem isIdentityPerm_tailLocal : (head : Nat) → (rest : List Nat) →
    isIdentityPerm (head :: rest) = true → isIdentityPerm rest = true
  | _, [], _ => rfl
  | head, second :: rest, hId => by
      have identityReduces : isIdentityPerm (head :: second :: rest) = isIdentityPerm (second :: rest) :=
        condFalseLocal false (isIdentityPerm (second :: rest)) (Nat.blt second head)
          (noJunctionDescent_ofIdentityCons head second rest hId)
      exact identityReduces.symm.trans hId

/-- ★ **Identity + distinct puts the head strictly below every later entry** — the weak adjacent ascent
(`isIdentityPerm`) sharpens to a strict one under global distinctness, then transitivity carries it down. -/
private theorem isBelowAllEntries_ofIdentityDistinct :
    (head : Nat) → (rest : List Nat) →
    isIdentityPerm (head :: rest) = true → isDistinctList (head :: rest) = true →
    isBelowAllEntries head rest = true
  | _, [], _, _ => rfl
  | head, second :: rest, hId, hDist => by
      have noDescent : Nat.blt second head = false :=
        noJunctionDescent_ofIdentityCons head second rest hId
      have headNotMem : memBool head (second :: rest) = false :=
        eqFalseOfNotTrueLocal _ (boolAndTrueLeftLocal _ _ hDist)
      have beqSecondHead : Nat.beq second head = false := boolOrFalseLeftLocal _ _ headNotMem
      have beqHeadSecond : Nat.beq head second = false :=
        (natBeqSymmLocal head second).trans beqSecondHead
      have headBelowSecond : Nat.blt head second = true :=
        bltOfBleNeqLocal head second (bleOfNotBltSwapLocal head second noDescent) beqHeadSecond
      have tailId : isIdentityPerm (second :: rest) = true :=
        isIdentityPerm_tailLocal head (second :: rest) hId
      have tailDist : isDistinctList (second :: rest) = true := boolAndTrueRightLocal _ _ hDist
      have secondBelowAll : isBelowAllEntries second rest = true :=
        isBelowAllEntries_ofIdentityDistinct second rest tailId tailDist
      show (Nat.blt head second && isBelowAllEntries head rest) = true
      rw [headBelowSecond,
        isBelowAllEntries_ofBltHead head second rest headBelowSecond secondBelowAll]
      rfl

/-- Nothing in a strictly-above list counts as below — the rank of a minimum is `0`. -/
private theorem countEntriesBelow_eq_zero_ofBelowAll :
    (low : Nat) → (entries : List Nat) → isBelowAllEntries low entries = true →
    countEntriesBelow low entries = 0
  | _, [], _ => rfl
  | low, entry :: rest, belowAll => by
      rw [countEntriesBelow_cons_notBelow low entry rest
          (natBltAsymmLocal entry low (boolAndTrueLeftLocal _ _ belowAll)),
        countEntriesBelow_eq_zero_ofBelowAll low rest (boolAndTrueRightLocal _ _ belowAll)]

/-- Pointwise `1 + ·` on a `Nat` list — the rank shift a strictly-below reference head induces. -/
private def onePlusEach : List Nat → List Nat
  | [] => []
  | value :: rest => (1 + value) :: onePlusEach rest

/-- `onePlusEach` distributes over append — structural. -/
private theorem onePlusEach_append : (frontList backList : List Nat) →
    onePlusEach (frontList ++ backList) = onePlusEach frontList ++ onePlusEach backList
  | [], _ => rfl
  | value :: rest, backList => congrArg ((1 + value) :: ·) (onePlusEach_append rest backList)

/-- Consing a strictly-below head onto the reference shifts every rank by one. -/
private theorem lehmerRankAgainst_consReference_shift (head : Nat) (referenceTail : List Nat) :
    (word : List Nat) → isBelowAllEntries head word = true →
    lehmerRankAgainst (head :: referenceTail) word = onePlusEach (lehmerRankAgainst referenceTail word)
  | [], _ => rfl
  | entry :: rest, belowAll => by
      show countEntriesBelow entry (head :: referenceTail)
            :: lehmerRankAgainst (head :: referenceTail) rest
          = (1 + countEntriesBelow entry referenceTail)
            :: onePlusEach (lehmerRankAgainst referenceTail rest)
      rw [countEntriesBelow_cons_below entry head referenceTail (boolAndTrueLeftLocal _ _ belowAll),
        lehmerRankAgainst_consReference_shift head referenceTail rest
          (boolAndTrueRightLocal _ _ belowAll)]

/-- `List.range.loop count accumulated = List.range.loop count [] ++ accumulated` — the accumulator floats out. -/
private theorem rangeLoopAppendLocal : (count : Nat) → (accumulated : List Nat) →
    List.range.loop count accumulated = List.range.loop count [] ++ accumulated
  | 0, _ => rfl
  | count + 1, accumulated => by
      show List.range.loop count (count :: accumulated) = List.range.loop count [count] ++ accumulated
      rw [rangeLoopAppendLocal count (count :: accumulated), rangeLoopAppendLocal count [count]]
      exact (appendSnocAssocLocal (List.range.loop count []) count accumulated).symm

/-- `List.range (count + 1) = List.range count ++ [count]` — the snoc decomposition. -/
private theorem rangeSnocLocal (count : Nat) :
    List.range (count + 1) = List.range count ++ [count] := by
  show List.range.loop count [count] = List.range.loop count [] ++ [count]
  exact rangeLoopAppendLocal count [count]

/-- `List.range (count + 1) = 0 :: onePlusEach (List.range count)` — the head decomposition. -/
private theorem rangeConsLocal : (count : Nat) →
    List.range (count + 1) = 0 :: onePlusEach (List.range count)
  | 0 => rfl
  | count + 1 => by
      calc List.range (count + 1 + 1)
          = List.range (count + 1) ++ [count + 1] := rangeSnocLocal (count + 1)
        _ = (0 :: onePlusEach (List.range count)) ++ [count + 1] := by rw [rangeConsLocal count]
        _ = 0 :: (onePlusEach (List.range count) ++ [count + 1]) := rfl
        _ = 0 :: (onePlusEach (List.range count) ++ [1 + count]) := by rw [onePlusCommLocal count]
        _ = 0 :: (onePlusEach (List.range count) ++ onePlusEach [count]) := rfl
        _ = 0 :: onePlusEach (List.range count ++ [count]) := by
              rw [onePlusEach_append (List.range count) [count]]
        _ = 0 :: onePlusEach (List.range (count + 1)) := by rw [rangeSnocLocal count]

/-- ★ **The identity base — a strictly-ascending (identity + distinct) list standardizes to `List.range`.**
The head has rank `0` (it is the strict minimum) and every tail rank shifts by exactly one (the reference gains
one strictly-below entry), so the ranks read `0, 1, 2, …` — `List.range length`. -/
theorem lehmerStandardize_ofIdentityDistinct :
    (perm : List Nat) → isIdentityPerm perm = true → isDistinctList perm = true →
    lehmerStandardize perm = List.range perm.length
  | [], _, _ => rfl
  | head :: rest, hId, hDist => by
      have belowAll : isBelowAllEntries head rest = true :=
        isBelowAllEntries_ofIdentityDistinct head rest hId hDist
      have tailStd : lehmerRankAgainst rest rest = List.range rest.length :=
        lehmerStandardize_ofIdentityDistinct rest (isIdentityPerm_tailLocal head rest hId)
          (boolAndTrueRightLocal _ _ hDist)
      show countEntriesBelow head (head :: rest) :: lehmerRankAgainst (head :: rest) rest
          = List.range (rest.length + 1)
      have headRankZero : countEntriesBelow head (head :: rest) = 0 := by
        rw [countEntriesBelow_cons_notBelow head head rest (natBltSelfFalseLocal head)]
        exact countEntriesBelow_eq_zero_ofBelowAll head rest belowAll
      rw [headRankZero, lehmerRankAgainst_consReference_shift head rest rest belowAll, tailStd,
        rangeConsLocal rest.length]

/-! ## Brick (a) — the realization: the canonical word realizes the Lehmer standardization

Fuel induction on `inversionCount`: at the identity the canonical word is empty and the realization is
`List.range length = lehmerStandardize perm` (the base above); at a descent the staircase-snoc peels the last
letter, `permuteOfCrossingWord_snoc` applies it, the IH fires at the once-bubbled permutation (Lehmer measure
drops by one), and the swap-equivariance + involution close the ring. -/

/-- The identity case of the realization, shared by the fuel base and the fuel step. -/
private theorem canonicalCrossingWord_realizes_identityCase (perm : List Nat)
    (hId : isIdentityPerm perm = true) (hDist : isDistinctList perm = true) :
    permuteOfCrossingWord perm.length (canonicalCrossingWord perm) = lehmerStandardize perm := by
  have canonicalNil : canonicalCrossingWord perm = [] := by
    show (bubbleWord perm).reverse = []
    exact congrArg List.reverse (bubbleWordFueled_identity (inversionCount perm) perm hId)
  rw [canonicalNil]
  show List.range perm.length = lehmerStandardize perm
  exact (lehmerStandardize_ofIdentityDistinct perm hId hDist).symm

/-- The fueled realization — structural on the fuel (`inversionCount perm` at the top level). -/
theorem canonicalCrossingWord_realizesFueled :
    (fuel : Nat) → (perm : List Nat) → inversionCount perm ≤ fuel → isDistinctList perm = true →
    permuteOfCrossingWord perm.length (canonicalCrossingWord perm) = lehmerStandardize perm
  | 0, perm, invLe, hDist =>
      canonicalCrossingWord_realizes_identityCase perm
        (isIdentityPerm_ofInversionCountZero perm
          (natEqZeroOfLeZeroLocal (inversionCount perm) invLe))
        hDist
  | fuel + 1, perm, invLe, hDist => by
      match hId : isIdentityPerm perm with
      | true => exact canonicalCrossingWord_realizes_identityCase perm hId hDist
      | false =>
          rw [canonicalCrossingWord_snoc_leftmostDescent perm hId,
            permuteOfCrossingWord_snoc perm.length
              (canonicalCrossingWord (applyAdjacentSwap perm (leftmostDescent perm)))
              (leftmostDescent perm)]
          have invDrop := inversionCount_ofLeftmostDescentSwap_succ perm hId
          have succLe : inversionCount (applyAdjacentSwap perm (leftmostDescent perm)) + 1
              ≤ fuel + 1 := by
            rw [invDrop]; exact invLe
          have swapRealizes := canonicalCrossingWord_realizesFueled fuel
            (applyAdjacentSwap perm (leftmostDescent perm)) (Nat.le_of_succ_le_succ succLe)
            (isDistinctList_applyAdjacentSwap perm (leftmostDescent perm) hDist)
          rw [applyAdjacentSwap_length perm (leftmostDescent perm)] at swapRealizes
          rw [swapRealizes, lehmerStandardize_applyAdjacentSwap perm (leftmostDescent perm),
            applyAdjacentSwap_involutive (lehmerStandardize perm) (leftmostDescent perm)]

/-- ★★ **The realization** — for a DISTINCT list, the canonical crossing word realizes the Lehmer
standardization: `permuteOfCrossingWord perm.length (canonicalCrossingWord perm) = lehmerStandardize perm`.
(The naive `= perm` form is FALSE off the range-permutation domain —
`canonicalRealization_smoke_nonRangeAscending`; on genuine range-permutations the two coincide —
`canonicalRealization_smoke_residualLeaf`.) -/
theorem canonicalCrossingWord_realizes_lehmerStandardize (perm : List Nat)
    (hDist : isDistinctList perm = true) :
    permuteOfCrossingWord perm.length (canonicalCrossingWord perm) = lehmerStandardize perm :=
  canonicalCrossingWord_realizesFueled (inversionCount perm) perm (Nat.le_refl _) hDist

/-! ## The permutation-equality brick + THE DISCHARGE -/

/-- ★★ **The two insertion-step sides realize the SAME permutation** — snoc the last letter
(`permuteOfCrossingWord_snoc`), realize both sides (`canonicalCrossingWord_realizes_lehmerStandardize`), and
commute the standardization past the swap (`lehmerStandardize_applyAdjacentSwap`).  No in-range hypothesis
needed — the equivariance holds for out-of-range no-op swaps too. -/
theorem canonicalInsertion_permEq (perm : List Nat) (position : Nat)
    (hDist : isDistinctList perm = true) :
    permuteOfCrossingWord perm.length (canonicalCrossingWord perm ++ [position])
      = permuteOfCrossingWord perm.length
          (canonicalCrossingWord (applyAdjacentSwap perm position)) := by
  rw [permuteOfCrossingWord_snoc perm.length (canonicalCrossingWord perm) position,
    canonicalCrossingWord_realizes_lehmerStandardize perm hDist]
  have swapRealizes := canonicalCrossingWord_realizes_lehmerStandardize
    (applyAdjacentSwap perm position) (isDistinctList_applyAdjacentSwap perm position hDist)
  rw [applyAdjacentSwap_length perm position] at swapRealizes
  rw [swapRealizes, lehmerStandardize_applyAdjacentSwap perm position]

/-- ★★★ **`InRangeInsertionStep` HOLDS** — the honest in-range insertion residual
(`Brauer/WiringDescInsertion.lean`) is inhabited: for every distinct-entry `perm` and
`position + 1 < perm.length`, inserting `s_position` at the tail of the canonical word is
`BrauerConvFree7`-convertible to the canonical word of the swapped permutation.  PROOF: both words carry the
`mentionsOnlyBelow (perm.length - 1)` certificate (`canonicalCrossingWord_mentionsOnlyBelow` + the in-range
inserted letter) and realize the same permutation (`canonicalInsertion_permEq`), so the shipped comb-staircase
straightening `crossingWords_equalPerm_conv` (BREACH r2) converts them.  The r12 braid-ascent WALL analysis of
the insertion-internal route stands as history; the Prop falls through the alternate door. -/
theorem inRangeInsertionStep_holds : InRangeInsertionStep :=
  fun perm position hDist inRange => by
    have lengthPos : 1 ≤ perm.length :=
      Nat.le_trans (Nat.succ_le_succ (Nat.zero_le position)) (Nat.le_of_lt inRange)
    have positionBlt : Nat.blt position (perm.length - 1) = true := by
      have succSuccLe : position + 1 + 1 ≤ (perm.length - 1) + 1 := by
        rw [predSuccOfPosLocal perm.length lengthPos]
        exact inRange
      exact bleOfLeLocal (position + 1) (perm.length - 1) (Nat.le_of_succ_le_succ succSuccLe)
    have insertedRange : mentionsOnlyBelow (perm.length - 1) [position] = true := by
      show (Nat.blt position (perm.length - 1) && true) = true
      rw [positionBlt]
      rfl
    have leftRange : mentionsOnlyBelow (perm.length - 1)
        (canonicalCrossingWord perm ++ [position]) = true :=
      mentionsOnlyBelow_append_true (perm.length - 1) (canonicalCrossingWord perm) [position]
        (canonicalCrossingWord_mentionsOnlyBelow perm) insertedRange
    have rightRange : mentionsOnlyBelow (perm.length - 1)
        (canonicalCrossingWord (applyAdjacentSwap perm position)) = true := by
      have base := canonicalCrossingWord_mentionsOnlyBelow (applyAdjacentSwap perm position)
      rw [applyAdjacentSwap_length perm position] at base
      exact base
    have permEqShifted : permuteOfCrossingWord ((perm.length - 1) + 1)
          (canonicalCrossingWord perm ++ [position])
        = permuteOfCrossingWord ((perm.length - 1) + 1)
            (canonicalCrossingWord (applyAdjacentSwap perm position)) := by
      rw [predSuccOfPosLocal perm.length lengthPos]
      exact canonicalInsertion_permEq perm position hDist
    exact crossingWords_equalPerm_conv (perm.length - 1)
      (canonicalCrossingWord perm ++ [position])
      (canonicalCrossingWord (applyAdjacentSwap perm position))
      leftRange rightRange permEqShifted

/-! ## Corollaries — the named residual leaf closes; the r7 folds become unconditional -/

/-- ★★ **The braid-ascent leaf `BraidAscentInsertionStep` HOLDS** — the r9 residual Prop
(`Brauer/WiringDescInsertion.lean`), the sharpest named leg of the insertion route, is a direct instance of the
discharged `InRangeInsertionStep` at `position := leftmostDescent perm + 1` (its extra non-reflex / ascent
side-conditions are simply unused).  Inhabited via the comb-staircase door, NOT via an insertion-internal carry
fold — the r12 wall record about the shipped-move set is untouched. -/
theorem braidAscentInsertionStep_holds : BraidAscentInsertionStep :=
  fun perm distinct _nonIdentity inRange _nonReflex _ascent =>
    inRangeInsertionStep_holds perm (leftmostDescent perm + 1) distinct inRange

/-- ★★ **The r7 well-formed straightening fold, UNCONDITIONAL** — every well-formed crossing word
`BrauerConvFree7`-reduces to the canonical word of its permutation, with the insertion-step hypothesis of
`crossingOnly_straightens_wellFormed` discharged by `inRangeInsertionStep_holds`. -/
theorem crossingOnly_straightens_unconditional (bottomCount : Nat) (word : List Nat)
    (wfWord : wellFormedCrossingWord bottomCount word = true) :
    BrauerConvFree7 (crossingWord word)
      (crossingWord (canonicalCrossingWord (permuteOfCrossingWord bottomCount word))) :=
  crossingOnly_straightens_wellFormed bottomCount inRangeInsertionStep_holds word wfWord

/-- ★★ **The r7 well-formed word problem, UNCONDITIONAL** — two well-formed crossing words with equal realized
permutation are convertible, the insertion route now closing end-to-end (independent confirmation of the comb
route's `crossingWords_equalPerm_conv`, through the r7/r9 fold interface). -/
theorem crossingWords_equalPerm_conv_wellFormed_unconditional (bottomCount : Nat)
    (wordLeft wordRight : List Nat)
    (wfLeft : wellFormedCrossingWord bottomCount wordLeft = true)
    (wfRight : wellFormedCrossingWord bottomCount wordRight = true)
    (permEq : permuteOfCrossingWord bottomCount wordLeft
      = permuteOfCrossingWord bottomCount wordRight) :
    BrauerConvFree7 (crossingWord wordLeft) (crossingWord wordRight) :=
  crossingWords_equalPerm_conv_wellFormed bottomCount inRangeInsertionStep_holds
    wordLeft wordRight wfLeft wfRight permEq

/-! ## Non-vacuity smokes — kernel-`rfl` where the statement is a closed computation -/

/-- Non-vacuity — on the genuine range-permutation `[1, 3, 0, 2]` (the r9 residual-leaf permutation) the
canonical word realizes the permutation ITSELF (standardization is the identity there).  Kernel `rfl`. -/
theorem canonicalRealization_smoke_residualLeaf :
    permuteOfCrossingWord 4 (canonicalCrossingWord [1, 3, 0, 2]) = [1, 3, 0, 2]
      ∧ lehmerStandardize [1, 3, 0, 2] = [1, 3, 0, 2] :=
  ⟨rfl, rfl⟩

/-- Non-vacuity — the honest correction is REAL: on the ascending non-range distinct list `[5, 7]` the naive
realization target `perm` FAILS (`[0, 1] != [5, 7]`) while the standardization target is exact; likewise on the
descending `[7, 5]`.  Kernel `rfl`. -/
theorem canonicalRealization_smoke_nonRangeAscending :
    permuteOfCrossingWord 2 (canonicalCrossingWord [5, 7]) = [0, 1]
      ∧ lehmerStandardize [5, 7] = [0, 1]
      ∧ permuteOfCrossingWord 2 (canonicalCrossingWord [7, 5]) = [1, 0]
      ∧ lehmerStandardize [7, 5] = [1, 0] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- ★ Non-vacuity — the discharged step FIRES on the r8/r9 stuck configuration: `perm = [1, 3, 0, 2]`,
`position = 2 = leftmostDescent + 1` (the braid-ascent leaf's own instance;
`braidAscentResidual_conclusion_isStuckExample` pins these words to `[2,0,1,2]` / `[0,1,2,1]`). -/
theorem inRangeInsertionStep_smoke_residualLeaf :
    BrauerConvFree7 (crossingWord (canonicalCrossingWord [1, 3, 0, 2] ++ [2]))
      (crossingWord (canonicalCrossingWord (applyAdjacentSwap [1, 3, 0, 2] 2))) :=
  inRangeInsertionStep_holds [1, 3, 0, 2] 2 rfl (Nat.le_refl 4)

/-- ★ Non-vacuity — the same firing read at the literal stuck words: `[2, 0, 1, 2] ~ [0, 1, 2, 1]` (the exact
r8 hand-witnessed jam pair), now produced BY the discharged insertion step (the two word forms are
kernel-definitionally the canonical-word forms of the previous smoke). -/
theorem inRangeInsertionStep_smoke_stuckPair :
    BrauerConvFree7 (crossingWord [2, 0, 1, 2]) (crossingWord [0, 1, 2, 1]) :=
  inRangeInsertionStep_smoke_residualLeaf

/-- Non-vacuity — the braid-mode instance on three strands: `perm = [2, 0, 1]`, `position = 1` gives the
canonical braid pair `[1, 0, 1] ~ [0, 1, 0]` through the discharged step (matches
`crossingInsertionStep_braid_smoke`). -/
theorem inRangeInsertionStep_smoke_braidPair :
    BrauerConvFree7 (crossingWord [1, 0, 1]) (crossingWord [0, 1, 0]) :=
  inRangeInsertionStep_holds [2, 0, 1] 1 rfl (Nat.le_refl 3)

/-- Non-vacuity — the range certificate is genuinely consumed: the canonical word of the 4-strand residual-leaf
permutation mentions only generators `< 3`.  Kernel `rfl`. -/
theorem canonicalCrossingWord_mentionsOnlyBelow_smoke :
    mentionsOnlyBelow 3 (canonicalCrossingWord [1, 3, 0, 2]) = true :=
  rfl

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — WP-BRAUER r13: `InRangeInsertionStep` is DISCHARGED (the insertion residual closes
as a comb-staircase corollary).**  `inRangeInsertionStep_holds` inhabits the honest r7 residual Prop
`InRangeInsertionStep` verbatim, via range certificate (`canonicalCrossingWord_mentionsOnlyBelow`) + Lehmer
realization (`canonicalCrossingWord_realizes_lehmerStandardize`, the honest correction of the naive `= perm`
which is FALSE off range-permutations) + swap equivariance (`lehmerStandardize_applyAdjacentSwap`) + the shipped
`crossingWords_equalPerm_conv`.  Consequently: (1) `braidAscentInsertionStep_holds` inhabits the r9 leaf Prop
`BraidAscentInsertionStep` — the statement guarded by `fxBrauer_hasBraidAscentResidual = false`
(`Brauer/WiringDescInsertion.lean`) is discharged; (2) the statement guarded by
`fxBrauer_hasCrossingInsertionStepGeneralResidual = false` (same file — "the sole remaining leg of
`InRangeInsertionStep`") is discharged; (3) the insertion-induction statement of
`fxBrauer_hasCrossingStraighteningInsertionResidual = false` (`Brauer/WiringDescStraightening.lean`) is
discharged in its committed honest in-range reformulation (the unrestricted `∀ (perm) (position)` reading was
machine-REFUTED at r6 and stays false — that is a permanent refutation, not an open leg); and (4) the r7/r9
conditional folds become unconditional (`crossingOnly_straightens_unconditional`,
`crossingWords_equalPerm_conv_wellFormed_unconditional`).  HONEST SCOPE: the discharge routes through the comb
staircase (BREACH r2), NOT through an insertion-internal braid-carry fold — the r12 wall record
(`fxBrauer_hasBraidAscentLeafWalled`, "no monovariant descends on the shipped move set") is a statement about
that move set and is untouched.  Non-vacuous: `inRangeInsertionStep_smoke_{residualLeaf, stuckPair, braidPair}`
fire the discharged step on the exact r8/r9 stuck configuration and the braid pair.  `= true`. -/
def fxBrauer_hasInRangeInsertionStepDischarged : Bool := true

end FX1Poly.Polygraph
