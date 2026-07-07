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

/-! ## Honesty marker -/

/-- **Honesty marker — the survivor-top classification + count is CLOSED (brick 2, order half).**  `isSurvivorTop`
classifies a whole-valley top port as a cap-block through-strand end (partner is a bottom) vs a cup arc end
(partner is a top), reading only the diagram's partner list.  `survivorTopRank` counts survivor-tops below a top
port, and `survivorTopRank_strictMono_atSurvivorTop` proves the count strictly increases past each survivor-top —
so survivor-tops are ranked in boundary order.  This is the classification layer of the backward re-ranking; the
VALUE half (that this rank of a survivor's partner top equals its cap-state open-wire rank `rankCap`) is the next
brick, built on the shipped forward re-ranking `survivorPartner_inWholeValley`.  No gate flag is flipped.
`= true`. -/
def fxMode_hasSurvivorTopClassification : Bool := true

end FX1Poly.Polygraph
