import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScanSplit

/-! # MatchingPartnerScanLocalize — where a partner scan LANDS (the two classification duals)

The classification half of the valley-append split reads `isSurvivorTop (matchingOf bc V) (bc+p)` as a
single `Nat.blt (partner[bc+p]) bc` and must decide it against `natListGetAt finalOpen p < bc`.  Both
directions reduce to WHERE `findPartnerScan` lands relative to the fresh floor `bc`:

  * a below-floor survivor (`v < bc`) is matched to a BOTTOM (`partner < bc`) — the scan lands on a
    front (bottom) candidate that PASSES, so the result is a genuine list member below the floor;
  * a cup leg (`v ≥ bc`) is matched to another TOP (`partner ≥ bc`) — every front candidate misses, the
    scan drops to the top segment whose every candidate (and the exclude sentinel) sits at or above the
    floor, so the result is at or above the floor.

Both directions are governed by two elementary structural facts about `findPartnerScan`, DUAL to the
shipped `findPartnerScan_append_ofFrontFails` / `_ofFoundInFront` first-hit discipline:

  * `findPartnerScan_result_mem_or_eq_exclude` — the scan returns either a genuine list member or the
    exclude sentinel (never anything else);
  * `findPartnerScan_result_passes_of_exists` — if some candidate passes the whole test, the returned
    index itself PASSES the test and IS a list member (the first hit is a real hit).

From these two: `findPartnerScan_result_ge_of_all_ge` (top-segment localization, the cup-leg direction)
is immediate, and the below-floor direction closes via the shipped front-hit append lemma.

Raw Lean 4 + Init; structural recursion on the candidate list, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Where the scan lands: a genuine member or the exclude sentinel -/

/-- ★ **A partner scan returns a genuine candidate or the exclude sentinel.**  Structural on the
candidate list: a passing head is returned (and is the list head); a failing head is skipped and the
tail's result is a tail member (or the sentinel).  The scan never fabricates an index outside its inputs
— the localization backbone for both classification directions. -/
theorem findPartnerScan_result_mem_or_eq_exclude (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootHere excludeIndex : Nat) :
    (candidates : List Nat) →
    findPartnerScan links boundaryNodes rootHere excludeIndex candidates ∈ candidates
      ∨ findPartnerScan links boundaryNodes rootHere excludeIndex candidates = excludeIndex
  | [] => Or.inr rfl
  | candidate :: rest => by
      cases headTest : (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere) with
      | true =>
          have resultEq : findPartnerScan links boundaryNodes rootHere excludeIndex (candidate :: rest)
              = candidate := by
            rw [findPartnerScan_cons links boundaryNodes rootHere excludeIndex candidate rest, headTest]
            exact if_pos rfl
          exact Or.inl (by rw [resultEq]; exact List.Mem.head rest)
      | false =>
          have skip : findPartnerScan links boundaryNodes rootHere excludeIndex (candidate :: rest)
              = findPartnerScan links boundaryNodes rootHere excludeIndex rest :=
            findPartnerScan_cons_ofTestFails links boundaryNodes rootHere excludeIndex candidate rest headTest
          rcases findPartnerScan_result_mem_or_eq_exclude links boundaryNodes rootHere excludeIndex rest with
            memRest | eqExcl
          · exact Or.inl (skip ▸ List.Mem.tail candidate memRest)
          · exact Or.inr (skip.trans eqExcl)

/-! ## The first hit is a real hit -/

/-- ★ **If any candidate passes, the returned index passes and is a member.**  The first-hit discipline
made explicit: given a witness candidate whose exclude-and-root whole test holds, the scan's result both
PASSES that same whole test and IS a genuine list member.  Structural on the list: a passing head is the
answer; a failing head is skipped and the witness necessarily survives into the tail (it cannot be the
failing head, since it passes).  Powers the below-floor (survivor) direction: a below-floor survivor's own
bottom index passes, so the scan lands on a passing — hence below-floor — bottom candidate. -/
theorem findPartnerScan_result_passes_of_exists (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootHere excludeIndex : Nat) :
    (candidates : List Nat) →
    (∃ witness, witness ∈ candidates ∧
      (witness != excludeIndex
        && unionFindRootOf links (natListGetAt boundaryNodes witness) == rootHere) = true) →
    (findPartnerScan links boundaryNodes rootHere excludeIndex candidates != excludeIndex
        && unionFindRootOf links
            (natListGetAt boundaryNodes
              (findPartnerScan links boundaryNodes rootHere excludeIndex candidates)) == rootHere) = true
      ∧ findPartnerScan links boundaryNodes rootHere excludeIndex candidates ∈ candidates
  | [], ⟨_, witnessMem, _⟩ => nomatch witnessMem
  | candidate :: rest, ⟨witness, witnessMem, witnessPasses⟩ => by
      cases headTest : (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere) with
      | true =>
          have resultEq : findPartnerScan links boundaryNodes rootHere excludeIndex (candidate :: rest)
              = candidate := by
            rw [findPartnerScan_cons links boundaryNodes rootHere excludeIndex candidate rest, headTest]
            exact if_pos rfl
          exact ⟨by rw [resultEq]; exact headTest, by rw [resultEq]; exact List.Mem.head rest⟩
      | false =>
          have skip : findPartnerScan links boundaryNodes rootHere excludeIndex (candidate :: rest)
              = findPartnerScan links boundaryNodes rootHere excludeIndex rest :=
            findPartnerScan_cons_ofTestFails links boundaryNodes rootHere excludeIndex candidate rest headTest
          have witnessInRest : witness ∈ rest := by
            cases witnessMem with
            | head => rw [headTest] at witnessPasses; exact Bool.noConfusion witnessPasses
            | tail _ memTail => exact memTail
          obtain ⟨restPasses, restMem⟩ :=
            findPartnerScan_result_passes_of_exists links boundaryNodes rootHere excludeIndex rest
              ⟨witness, witnessInRest, witnessPasses⟩
          exact ⟨skip ▸ restPasses, skip ▸ List.Mem.tail candidate restMem⟩

/-! ## The cup-leg direction: the scan lands at or above the floor -/

/-- ★ **A partner scan over candidates all at or above a floor (with an at-or-above exclude) lands at or
above the floor.**  Immediate from `findPartnerScan_result_mem_or_eq_exclude`: the result is a member (≥
floor by hypothesis) or the exclude sentinel (≥ floor by hypothesis).  This is the cup-leg classification
direction — once a cup leg's whole bottom-front misses (`findPartnerScan_range_frontSegmentMisses` drops
the scan to the top segment), every remaining candidate and the exclude are `≥ bc`, so the partner is a
TOP port. -/
theorem findPartnerScan_result_ge_of_all_ge (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootHere excludeIndex floor : Nat) (candidates : List Nat)
    (excludeGe : floor ≤ excludeIndex) (allGe : ∀ candidate ∈ candidates, floor ≤ candidate) :
    floor ≤ findPartnerScan links boundaryNodes rootHere excludeIndex candidates := by
  rcases findPartnerScan_result_mem_or_eq_exclude links boundaryNodes rootHere excludeIndex candidates with
    resultMem | resultExcl
  · exact allGe _ resultMem
  · rw [resultExcl]; exact excludeGe

/-! ## Honesty marker -/

/-- **Honesty marker — the two partner-scan LOCALIZATION duals of the classification half are SHIPPED.**
Landed here, all zero-axiom:

  * `findPartnerScan_result_mem_or_eq_exclude` — a partner scan returns a genuine candidate or the
    exclude sentinel, never a fabricated index.
  * `findPartnerScan_result_passes_of_exists` — if any candidate passes the whole exclude-and-root test,
    the returned index itself passes and is a list member (the first hit is a real hit).
  * `findPartnerScan_result_ge_of_all_ge` — a scan over candidates all `≥ floor` (with an `≥ floor`
    exclude) lands `≥ floor`: the cup-leg (top-segment) classification direction.

These are the DUALS of the shipped `findPartnerScan_append_ofFrontFails` / `_ofFoundInFront` first-hit
discipline, supplying exactly the scan-landing facts N3a (below-floor: the front hit lands `< bc`) and N3b
(cup leg: the top-segment scan lands `≥ bc`) the classification lemma routes through.  What this marker
does NOT itself close: the union-find floor facts (a bottom root stays `< bc`; a cup-leg root stays `≥
bc`) that DISCHARGE the two directions' hypotheses (the passing bottom witness / the whole-front miss) —
those are the union-find half proper.  No gate flag is flipped.  `= true`. -/
def fxMode_hasPartnerScanLocalize : Bool := true

end FX1Poly.Polygraph
