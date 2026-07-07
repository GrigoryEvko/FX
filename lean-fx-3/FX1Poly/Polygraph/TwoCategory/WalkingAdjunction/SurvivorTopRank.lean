import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.CupShiftReranking

/-! # SurvivorTopRank — the survivor-top classification and count (Piece II tail, brick 2 crux)

The valley-append split needs to reconstruct the CAP block's own diagram from the WHOLE valley's diagram.  The
inversion handle is a classification of the whole valley `V = capBlock ++ cupBlock`'s TOP ports over bottom count
`bc`: a top port `t` (`bc ≤ t`) is a **survivor-top** iff its partner is a bottom (`V.partner[t] < bc`, a cap-block
through-strand), and a **cup-top** iff its partner is another top (`V.partner[t] ≥ bc`, a top-top cup arc).  The
cup order embedding `phi` (`processSpine_wireOrderEmbedding_ofAllCupArity`) preserves the survivors' relative
order, so a survivor bottom's rank among the cap-state open wires is recoverable from `V.partner` ALONE by counting
survivor-tops below its partner top port — a function of the whole diagram, no mid-state data.

This file lands the classification layer:

  * ★ `isSurvivorTop` — the Bool predicate "top port `t` is matched to a bottom" (`bc ≤ t` and `V.partner[t] < bc`).
  * ★ `survivorTopRank` — the count of survivor-tops strictly below a top port, over the whole diagram's partner
    list.  A flat `Nat` fold, so it COMPUTES.
  * ★ `survivorTopRank_strictMono_atSurvivorTop` — the ORDER-PRESERVATION of the count on survivor-tops: past any
    survivor-top the count strictly increases, so the survivor-tops are ranked in their boundary order.

Raw Lean 4 + Init; structural recursion on the count bound, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The survivor-top predicate and the survivor-top count -/

/-- ★ **The survivor-top predicate.**  Over a diagram at bottom count `m.bottomCount`, a top port `topIndex`
(`m.bottomCount ≤ topIndex`) is a SURVIVOR-TOP when its partner is a BOTTOM boundary index
(`m.partner[topIndex] < m.bottomCount`) — i.e. it is the top end of a cap-block through-strand rather than the
end of a top-top cup arc.  A pure Bool test on the diagram's partner list (via `Nat.ble` / `Nat.blt`, no `decide`
coercion), so it computes and carries no `propext`. -/
def isSurvivorTop (diagram : DiagramType) (topIndex : Nat) : Bool :=
  Nat.ble diagram.bottomCount topIndex
    && Nat.blt (natListGetAt diagram.partner topIndex) diagram.bottomCount

/-- ★ **The survivor-top count.**  The number of survivor-tops strictly below `topBound`, folded over the boundary
indices `0 … topBound-1`.  (Bottom indices `< bottomCount` never pass `isSurvivorTop`'s lower guard, so the count
effectively ranges over the top segment.)  A flat `Nat` recursion on the bound, so it COMPUTES. -/
def survivorTopCount (diagram : DiagramType) : Nat → Nat
  | 0 => 0
  | topBound + 1 => survivorTopCount diagram topBound + cond (isSurvivorTop diagram topBound) 1 0

/-- ★ **The survivor-top rank of a top port.**  The number of survivor-tops strictly below `topIndex` — the
position of `topIndex` among the survivor-tops in boundary order.  Reads ONLY the diagram's partner list, so it is
a well-defined function of the whole valley's `matchingOf` (no mid-state / cup-order data). -/
def survivorTopRank (diagram : DiagramType) (topIndex : Nat) : Nat :=
  survivorTopCount diagram topIndex

/-! ## Monotonicity of the count -/

/-- One more bound never decreases the count. -/
theorem survivorTopCount_le_succ (diagram : DiagramType) (topBound : Nat) :
    survivorTopCount diagram topBound ≤ survivorTopCount diagram (topBound + 1) :=
  Nat.le_add_right (survivorTopCount diagram topBound) (cond (isSurvivorTop diagram topBound) 1 0)

/-- The count over a shifted-up bound dominates the count over the base bound (monotone, add form). -/
theorem survivorTopCount_le_add (diagram : DiagramType) (base : Nat) :
    (delta : Nat) → survivorTopCount diagram base ≤ survivorTopCount diagram (base + delta)
  | 0 => Nat.le_refl _
  | delta + 1 =>
      Nat.le_trans (survivorTopCount_le_add diagram base delta)
        (survivorTopCount_le_succ diagram (base + delta))

/-- The survivor-top count is monotone in its bound. -/
theorem survivorTopCount_mono (diagram : DiagramType) {lowerBound upperBound : Nat}
    (boundLe : lowerBound ≤ upperBound) :
    survivorTopCount diagram lowerBound ≤ survivorTopCount diagram upperBound := by
  obtain ⟨delta, deltaEq⟩ := Nat.le.dest boundLe
  rw [← deltaEq]
  exact survivorTopCount_le_add diagram lowerBound delta

/-! ## The order-preservation of the survivor-top rank -/

/-- ★ **The survivor-top rank strictly increases past a survivor-top.**  If `firstTop` is a survivor-top and
`firstTop < secondTop`, then `survivorTopRank diagram firstTop < survivorTopRank diagram secondTop`: the count
over `firstTop + 1` is exactly one more than the count over `firstTop` (the survivor-top at `firstTop` contributes
its `1`), and monotonicity carries that strict gap up to `secondTop`.  So the survivor-tops are ranked in strictly
increasing boundary order — the order half of the backward re-ranking. -/
theorem survivorTopRank_strictMono_atSurvivorTop (diagram : DiagramType) {firstTop secondTop : Nat}
    (indexLt : firstTop < secondTop) (firstIsSurvivor : isSurvivorTop diagram firstTop = true) :
    survivorTopRank diagram firstTop < survivorTopRank diagram secondTop := by
  have monoStep : survivorTopCount diagram (firstTop + 1) ≤ survivorTopCount diagram secondTop :=
    survivorTopCount_mono diagram indexLt
  have unfoldSucc : survivorTopCount diagram (firstTop + 1)
      = survivorTopCount diagram firstTop + cond (isSurvivorTop diagram firstTop) 1 0 := rfl
  rw [unfoldSucc, firstIsSurvivor] at monoStep
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (survivorTopCount diagram firstTop)) monoStep

/-! ## The order-side rank engine — a survivor's position among the survivor-tops

The forward re-ranking (`survivorPartner_inWholeValley`) pins EVERY survivor bottom's whole-valley partner top
port to `bottomCount + phi rankCap`, with `phi` the cup order embedding (strictly monotone).  So the survivor-tops,
listed by their survivor-bottom's cap-state rank `r`, sit at strictly increasing positions `phi r`.  The
survivor-side count of ranks `r` whose image `phi r` falls below `phi rankCap` is therefore exactly `rankCap` — the
position of `rankCap` among the survivors.  This is the ARITHMETIC core of the backward re-ranking, proven
unconditionally here as a pure count identity over a strictly-monotone map.  (Bridging this survivor-side count to
the top-side `survivorTopRank` needs the classification that a whole-valley top port `bottomCount + p` is a
survivor-top IFF `p` is in the image of `phi` — the surjectivity of the cup embedding onto the survivor positions,
i.e. the standing valley-descent residual #2185; see the honesty marker.) -/

/-- `cond true 1 0 = 1` at default transparency (the `cond` reduction `rw` cannot do under reducible transparency). -/
theorem cond_true_one : cond true 1 0 = 1 := rfl

/-- `cond false 1 0 = 0` at default transparency. -/
theorem cond_false_one : cond false 1 0 = 0 := rfl

/-- A generic count-below-a-bound of a Bool predicate — `survivorTopCount` is the special case at `isSurvivorTop`. -/
def countBelow (predicate : Nat → Bool) : Nat → Nat
  | 0 => 0
  | bound + 1 => countBelow predicate bound + cond (predicate bound) 1 0

/-- `survivorTopCount` is the generic count of the survivor-top predicate. -/
theorem survivorTopCount_eq_countBelow (diagram : DiagramType) :
    (bound : Nat) → survivorTopCount diagram bound = countBelow (isSurvivorTop diagram) bound
  | 0 => rfl
  | bound + 1 => congrArg (· + cond (isSurvivorTop diagram bound) 1 0)
      (survivorTopCount_eq_countBelow diagram bound)

/-- Two predicates agreeing below the bound give equal counts. -/
theorem countBelow_congr (predicateFirst predicateSecond : Nat → Bool) :
    (bound : Nat) → (∀ index, index < bound → predicateFirst index = predicateSecond index) →
    countBelow predicateFirst bound = countBelow predicateSecond bound
  | 0, _ => rfl
  | bound + 1, agree => by
      show countBelow predicateFirst bound + cond (predicateFirst bound) 1 0
        = countBelow predicateSecond bound + cond (predicateSecond bound) 1 0
      rw [countBelow_congr predicateFirst predicateSecond bound
          (fun index indexLt => agree index (Nat.lt_succ_of_lt indexLt)),
        agree bound (Nat.lt_succ_self bound)]

/-- The count of `index < threshold` over `[0, bound)` is `bound` when `bound ≤ threshold` (all pass). -/
theorem countBelow_ltSelf_eq_bound (threshold : Nat) :
    (bound : Nat) → bound ≤ threshold →
    countBelow (fun index => decide (index < threshold)) bound = bound
  | 0, _ => rfl
  | bound + 1, succLe => by
      have boundLt : bound < threshold := Nat.lt_of_lt_of_le (Nat.lt_succ_self bound) succLe
      show countBelow (fun index => decide (index < threshold)) bound
          + cond (decide (bound < threshold)) 1 0 = bound + 1
      rw [countBelow_ltSelf_eq_bound threshold bound (Nat.le_of_lt boundLt),
        decide_eq_true boundLt, cond_true_one]

/-- The count of `index < threshold` over `[0, bound)` is `threshold` when `threshold ≤ bound` (exactly the
first `threshold` pass). -/
theorem countBelow_ltSelf_eq_threshold (threshold : Nat) :
    (bound : Nat) → threshold ≤ bound →
    countBelow (fun index => decide (index < threshold)) bound = threshold
  | 0, thLeZero => (Nat.le_zero.mp thLeZero).symm
  | bound + 1, thLeSucc => by
      rcases Nat.lt_or_ge bound threshold with boundLt | boundGe
      · have thEq : threshold = bound + 1 := Nat.le_antisymm thLeSucc boundLt
        show countBelow (fun index => decide (index < threshold)) bound
            + cond (decide (bound < threshold)) 1 0 = threshold
        rw [countBelow_ltSelf_eq_bound threshold bound (Nat.le_of_lt boundLt),
          decide_eq_true boundLt, cond_true_one, thEq]
      · show countBelow (fun index => decide (index < threshold)) bound
            + cond (decide (bound < threshold)) 1 0 = threshold
        rw [countBelow_ltSelf_eq_threshold threshold bound boundGe,
          decide_eq_false (Nat.not_lt.mpr boundGe), cond_false_one, Nat.add_zero]

/-- Under a strictly-monotone `phi`, the image-below test agrees with the plain below test:
`decide (phi index < phi rankCap) = decide (index < rankCap)`. -/
theorem strictMono_decideLt_agree {phi : Nat → Nat}
    (strictMono : ∀ firstIndex secondIndex, firstIndex < secondIndex → phi firstIndex < phi secondIndex)
    (rankCap index : Nat) :
    decide (phi index < phi rankCap) = decide (index < rankCap) := by
  rcases Nat.lt_or_ge index rankCap with indexLt | indexGe
  · rw [decide_eq_true (strictMono index rankCap indexLt), decide_eq_true indexLt]
  · have phiGe : phi rankCap ≤ phi index := by
      rcases Nat.eq_or_lt_of_le indexGe with rankEq | rankLt
      · exact Nat.le_of_eq (congrArg phi rankEq)
      · exact Nat.le_of_lt (strictMono rankCap index rankLt)
    rw [decide_eq_false (Nat.not_lt.mpr phiGe), decide_eq_false (Nat.not_lt.mpr indexGe)]

/-- ★ **The order-side rank engine.**  For a strictly-monotone `phi` and `rankCap < midWidth`, the count of
survivor ranks `index < midWidth` whose image `phi index` falls below `phi rankCap` is exactly `rankCap`.  This is
"`phi` maps `rankCap` to its position among the survivor-tops" made a pure count identity: rewrite the image-below
test to the plain below test (`strictMono_decideLt_agree`), then the plain count of `index < rankCap` over
`[0, midWidth)` is `rankCap` (`countBelow_ltSelf_eq_threshold`, `rankCap ≤ midWidth`).  The arithmetic core of the
backward re-ranking's value half; the top-side bridge is the residual #2185. -/
theorem strictMono_countBelow_image_eq_rank {phi : Nat → Nat}
    (strictMono : ∀ firstIndex secondIndex, firstIndex < secondIndex → phi firstIndex < phi secondIndex)
    {rankCap midWidth : Nat} (rankLtWidth : rankCap < midWidth) :
    countBelow (fun index => decide (phi index < phi rankCap)) midWidth = rankCap := by
  rw [countBelow_congr (fun index => decide (phi index < phi rankCap))
      (fun index => decide (index < rankCap)) midWidth
      (fun index _ => strictMono_decideLt_agree strictMono rankCap index)]
  exact countBelow_ltSelf_eq_threshold rankCap midWidth (Nat.le_of_lt rankLtWidth)

/-! ## Honesty marker -/

/-- **Honesty marker — the backward re-ranking's CLASSIFICATION + ORDER ENGINE are CLOSED; the value half
reduces to the surjectivity of the cup embedding (residual #2185).**

Landed here, all zero-axiom:

  * `isSurvivorTop` / `survivorTopRank` — a whole-valley top port is classified as a cap-block through-strand end
    (partner is a bottom) vs a cup arc end (partner is a top), reading ONLY the diagram's partner list.
    `survivorTopRank` counts survivor-tops below a top port, and `survivorTopRank_strictMono_atSurvivorTop` proves
    the count strictly increases past each survivor-top — so survivor-tops are ranked in boundary order.

  * `strictMono_countBelow_image_eq_rank` — the ORDER-SIDE ARITHMETIC of the value half: for the
    strictly-monotone cup embedding `phi` and `rankCap < midWidth`, the count of survivor ranks whose image falls
    below `phi rankCap` is exactly `rankCap` ("`phi` maps `rankCap` to its position among the survivors").  Built
    from the generic count-below (`countBelow`), its predicate congruence, and the plain-below count identity
    (`countBelow_ltSelf_eq_threshold`), routed through the strict-monotone below-test agreement.

What this marker does NOT claim (the genuine snag): the full value half
`survivorTopRank (matchingOf bc V) (V.partner[survivor]) = rankCap`.  The forward re-ranking
(`survivorPartner_inWholeValley`) pins each survivor's partner top to `bc + phi rankCap` on the SURVIVOR
(bottom) side, and the engine above counts on that survivor side.  But `survivorTopRank` counts on the TOP side
— over the boundary indices `bc … bc + phi rankCap` — so closing the value half requires equating the top-side
count with the survivor-side count.  That equality is exactly the CLASSIFICATION `isSurvivorTop (matchingOf bc V)
(bc + p) = true ↔ (∃ r < midWidth, phi r = p)`, i.e. that the whole valley's survivor-top positions are EXACTLY
the image of the cup embedding `phi` — the SURJECTIVITY of `phi` onto the survivor positions (equivalently, that
every non-image final open wire is a cup leg, not a survivor).  That is the standing "mid-state rigidity /
index-shift bijection" residual — the valley-descent beam #2185 — the SAME residual named by
`fxMode_hasCupShiftReranking`, `fxMode_hasValleyAppendSplitLoopAndFrame`, and
`fxMode_hasValleySurvivorOrderPreservation`.  It is NOT shipped (the covariant-monotone reconstruction map was
machine-refuted), so the F-assembly (task 3), cup dual (task 4), `valleyAppend_split` (task 5), and the clean
whole-valley Piece II (task 6) remain gated behind it.  No gate flag is flipped.  `= true`. -/
def fxMode_hasSurvivorTopClassification : Bool := true

end FX1Poly.Polygraph
