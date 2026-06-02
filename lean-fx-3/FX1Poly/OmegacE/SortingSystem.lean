import FX1Poly.OmegacE.TranspositionSystem

/-! # FX1Poly/OmegacE/SortingSystem
    — the braid/symmetric system: the sorting / symmetric-group convergent presentation (SN-120 opener, #623)

The third concrete decided system — the "graduation".  Where SN-118 (transposition) was a single rule and
SN-119 (absorption) was a fixed two-rule set, SN-120 is a guarded rule FAMILY: parameterized by a priority
`slotValue : OmegacECell → Nat`, the rule `[a,b] → [b,a]` fires for EVERY pair with `slotValue b < slotValue a`
(an adjacent descending pair).  This is bubble sort = the symmetric-group word problem (two words are
convertible iff they are permutations sorting to the same `slotValue`-ascending normal form).

* `sortingSwapRule a b` — the adjacent-swap generator `[a,b] → [b,a]`.
* `sortingSystem slotValue` — membership is an EXISTENTIAL with a strict-order guard
  `∃ a b, slotValue b < slotValue a ∧ rule = sortingSwapRule a b` — the genuinely-new structure (a guarded
  family) vs the absorption system's two-element disjunction.
* `sortingSwapRule_fires` — non-vacuity (given a descending pair).
* `sortingSystem_isLengthPreserving` + the three length invariants — length is a convertibility invariant, so
  the word problem is bounded search over the finite same-length (permutation) class.

## Honest scope / deferred

This ships the SYSTEM + length invariants + non-vacuity.  The subsequent SN-120 atoms:

  1. TERMINATION via the INVERSION COUNT over `slotValue` (the number of out-of-order pairs), which strictly
     decreases by one per swap — the bubble-sort measure (generalizes SN-118's `aBeforeBInversions` to count
     ALL out-of-order pairs; may consume the SN-115/116/117 RPO / Dershowitz-Manna / LPO orderings).
  2. LOCAL CONFLUENCE with the genuine braid critical pair `[a,b,c]` (`slotValue a > b > c`): the two one-step
     reducts `[b,a,c]` / `[a,c,b]` join to the sorted `[c,b,a]` via MULTI-step sequences (a real `RewritesMany`).
  3. BOUNDED-SEARCH DECIDABILITY: a guarded `WordReducer` (scan for the leftmost descending adjacency) +
     `decidableConvertibleModulo_ofConvergent`.

## Zero-axiom verification

`fires` is the guarded `fire` (`⟨a, b, descending, rfl⟩` membership); `isLengthPreserving` destructures the
existential then `rfl`; the invariants instantiate the shipped preservation lemmas.  Verified `#print axioms`-clean
in scratch.  Per-decl gated in `FX1PolyAudit/AuditOmegacE.lean`.
-/

namespace FX1Poly.OmegacE

/-- The adjacent-swap rule `[a,b] → [b,a]` (one generator of the sorting / symmetric-group presentation). -/
def sortingSwapRule {dimension : Nat} (biggerCell smallerCell : OmegacECell dimension) :
    OmegacERewriteRule dimension where
  leftHandSide := { cells := [biggerCell, smallerCell] }
  rightHandSide := { cells := [smallerCell, biggerCell] }

/-- The **sorting system** parameterized by a priority `slotValue`: a guarded rule FAMILY.  An adjacent
descending pair `[a,b]` with `slotValue b < slotValue a` swaps to `[b,a]` (bubble sort toward ascending order).
Membership is an EXISTENTIAL with a strict-order guard — the genuinely-new structure vs the two-element
disjunction of the absorption system. -/
def sortingSystem {dimension : Nat} (slotValue : OmegacECell dimension → Nat) :
    OmegacERewriteRule dimension → Prop :=
  fun rule => ∃ biggerCell smallerCell,
    slotValue smallerCell < slotValue biggerCell ∧ rule = sortingSwapRule biggerCell smallerCell

/-- **Non-vacuity**: whenever `slotValue b < slotValue a`, the system genuinely rewrites `[a,b] → [b,a]`
(`fire` of the guarded family member). -/
theorem sortingSwapRule_fires {dimension : Nat} (slotValue : OmegacECell dimension → Nat)
    (biggerCell smallerCell : OmegacECell dimension)
    (descending : slotValue smallerCell < slotValue biggerCell) :
    OmegacEWord.RewritesOneStep (sortingSystem slotValue)
      { cells := [biggerCell, smallerCell] } { cells := [smallerCell, biggerCell] } :=
  OmegacEWord.RewritesOneStep.fire (sortingSwapRule biggerCell smallerCell)
    ⟨biggerCell, smallerCell, descending, rfl⟩

/-- **The sorting system is length-preserving**: every swap rule has `|[a,b]| = 2 = |[b,a]|`.  Destructure
the existential membership, subst the rule, `rfl`. -/
theorem sortingSystem_isLengthPreserving {dimension : Nat} (slotValue : OmegacECell dimension → Nat) :
    IsLengthPreservingSystem (sortingSystem slotValue) := by
  intro rule isInSystem
  obtain ⟨biggerCell, smallerCell, _descending, hrule⟩ := isInSystem
  subst hrule
  rfl

theorem sortingSystem_rewritesOneStep_length_preserved {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat)
    {sourceWord targetWord : OmegacEWord dimension}
    (step : OmegacEWord.RewritesOneStep (sortingSystem slotValue) sourceWord targetWord) :
    sourceWord.length = targetWord.length :=
  step.length_preserved (sortingSystem_isLengthPreserving slotValue)

theorem sortingSystem_rewritesMany_length_preserved {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat)
    {sourceWord targetWord : OmegacEWord dimension}
    (many : OmegacEWord.RewritesMany (sortingSystem slotValue) sourceWord targetWord) :
    sourceWord.length = targetWord.length :=
  many.length_preserved (sortingSystem_isLengthPreserving slotValue)

theorem sortingSystem_convertibleModulo_length_preserved {dimension : Nat}
    (slotValue : OmegacECell dimension → Nat)
    {sourceWord targetWord : OmegacEWord dimension}
    (conv : OmegacEWord.ConvertibleModulo (sortingSystem slotValue) sourceWord targetWord) :
    sourceWord.length = targetWord.length :=
  conv.length_preserved (sortingSystem_isLengthPreserving slotValue)

end FX1Poly.OmegacE
