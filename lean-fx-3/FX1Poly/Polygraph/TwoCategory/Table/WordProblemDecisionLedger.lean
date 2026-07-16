/-! # Polygraph/TwoCategory/Table/WordProblemDecisionLedger — the grand word-problem DECISION ledger

★ **The decided-9 walkers' WORD-PROBLEM DECISION status, machine-checked (WP-LEDGER #2048, core round).**

This is the DECISION-lane counterpart to `Polygraph/Omega/SquierFamilyCensus`.  The census grounds which
walkers have a coherent PRESENTATION (shipped / op-dual / walled); it names the nine "decided" walkers but
never grounds the actual word-problem DECISION in the decision witnesses — "decided-9" is a claim carried by
the census's NAME, not by its content.  This ledger carries the decision itself: for each rung, WHICH decider
decides its word problem, at WHAT strength, and — crucially — which rung has NO decider at all.

## The honest correction the census hides

The census reads "decided-9".  At the DECISION level it is **decided-8**: the walking cyclic-3
`<s | s.s.s => id>` has NO shipped word-problem decider anywhere in the tree — only the Omega coherent
presentation (`cyclicThreeWalkerCoherentPresentation`) and the homology `CyclicThreeChainComplex`
(`H1 = ZZ/3`).  Its 1-cell word problem is decidable in principle (it is `Z/3`, the parity/mod-3 analogue of
the shipped involution decider `decideInvolutionOneCellConv`), but no decider is shipped.  Recorded as
`decisionNotShipped` below, and flagged by `fxWpLedger_cyclicThreeDecisionUnshipped`.

## The key distinction the census blurs: presentation-walled vs decision-decided

The walking adjunction has NO coherent Squier PRESENTATION (non-convergent Schanuel-Street zig-zag,
`fxOmega4_walkingAdjunctionCoherentPresentationWalledR2 = true`) yet its word problem IS totally decided —
by boundary-arc MATCHING (Joyal-Street), not rewriting (`decideSaturatedTwoCellConv_ofSeed`).
Presentation-walled and decision-decided are ORTHOGONAL; this ledger reads the decision axis.

## The per-rung decision witnesses (decl NAMES cited, per the anchor-rot discipline — never file:line)

  | Walker                          | Decision status              | Witness decl |
  |---------------------------------|------------------------------|--------------|
  | walking involution              | oneCellDecided (dim-1 Z/2)   | `instDecidableInvolutionOneCellConv` |
  | walking monad                   | fullTwoCellDecided           | `monadSaturatedTwoCellDecision` |
  | walking cyclic-3                | decisionNotShipped           | — (presentation + homology only) |
  | idempotent semigroup (= monad)  | fullTwoCellDecided           | `decideSaturatedConvOverIdempotentNative` |
  | walking comonad                 | fullTwoCellDecided           | `decideSaturatedConvOverComonadNative` |
  | idempotent comonad              | fullTwoCellDecided           | `decideSaturatedConvOverIdempotentComonadNative` |
  | walking KZ                      | fullTwoCellDecided (+ order) | `decideKZEq` / `decideKZLETotal` |
  | walking co-KZ                   | orderDecidedOnly (directed)  | `decideCoKZLETotal` |
  | walking adjunction              | fullTwoCellDecided (matching)| `decideSaturatedTwoCellConv_ofSeed` |

→ **8 of 9** carry a shipped total decider; SIX are full saturated-2-cell deciders, one is a 1-cell decider
(involution), one a directed-order decider only (co-KZ).  The lone gap is cyclic-3.

## NOT the capstone close (honest)

This is the DECISION-ledger CORE: the rung taxonomy, the kernel-checked per-rung status map, the coverage
counts, and the honest markers.  It does NOT yet (1) GROUND the eight deciders in a held witness bundle — that
is the immediate follow-on (`WordProblemDecisionWitnessBundle`), the non-rotting upgrade that replaces these
decl-name citations with actual typechecked terms; (2) ship the cyclic-3 decider; (3) tabulate the
beyond-decided-9 rungs (equivalence, Frobenius monad, strong monad, bunched bimonoid, Brauer, ...) with their
walls; (4) attach the cost tags (WP-CEIL-COST #2046).  `fxWpLedger_grandLedgerClosed = false`.

Raw Lean 4 + Init; a machine-checked census (an enum, a total status map, `rfl` counts, `List.Mem`
exhaustiveness, `Bool` markers), every declaration axiom-free.  Per-declaration `#assert_no_axioms` gated in
the audit twin. -/

namespace FX1Poly.Polygraph.Table

/-! ## The decided-walker enumeration (mirrors `Omega.SquierFamilyWalker`, decision-axis) -/

/-- The **decided-9 walkers** indexed on the DECISION axis — the same nine the Omega census names, here the
index for the per-rung word-problem decision status (`wordProblemDecisionStatus`). -/
inductive WordProblemDecidedWalker
  /-- The walking involution `<s | s.s => id>` — decided at dimension 1 (the monoid `Z/2`). -/
  | walkingInvolution
  /-- The walking monad `<t | eta, mu>` — full saturated-2-cell decision (Delta-plus monotone map). -/
  | walkingMonad
  /-- The walking cyclic-3 `<s | s.s.s => id>` — NO shipped decider (presentation + homology only). -/
  | walkingCyclicThree
  /-- The idempotent semigroup `<e | e.e => e>` (= the idempotent monad over `monadModeSignature`). -/
  | idempotentSemigroup
  /-- The walking comonad = op(monad). -/
  | walkingComonad
  /-- The idempotent comonad = op(idempotent semigroup). -/
  | idempotentComonad
  /-- The walking KZ doctrine = monad (abelianized) + a decided directed order. -/
  | walkingKZ
  /-- The walking co-KZ doctrine = comonad (the directed KZ order reversed). -/
  | walkingCoKZ
  /-- The walking adjunction — presentation-walled, decision-decided by matching. -/
  | walkingAdjunction

/-- The complete enumeration of the decided-9 walkers — NINE, listed. -/
def allWordProblemDecidedWalkers : List WordProblemDecidedWalker :=
  [.walkingInvolution, .walkingMonad, .walkingCyclicThree, .idempotentSemigroup,
    .walkingComonad, .idempotentComonad, .walkingKZ, .walkingCoKZ, .walkingAdjunction]

/-- ★ **The decided-walker count is exactly NINE** — kernel-checked (`rfl`). -/
theorem wordProblemDecidedWalkerCountIsNine : allWordProblemDecidedWalkers.length = 9 := rfl

/-- ★ **The decided-9 enumeration is EXHAUSTIVE** — every walker appears (full case split, `List.Mem` ctors,
propext-free). -/
theorem allWordProblemDecidedWalkersExhaustive :
    ∀ walker : WordProblemDecidedWalker, walker ∈ allWordProblemDecidedWalkers
  | .walkingInvolution => List.Mem.head _
  | .walkingMonad => List.Mem.tail _ (List.Mem.head _)
  | .walkingCyclicThree => List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | .idempotentSemigroup =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  | .walkingComonad =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  | .idempotentComonad =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _)))))
  | .walkingKZ =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  | .walkingCoKZ =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  | .walkingAdjunction =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))

/-! ## The word-problem decision status of each walker -/

/-- The **word-problem decision status** of a decided walker on the DECISION axis. -/
inductive WordProblemDecisionStatus
  /-- A total saturated-2-cell decider is shipped (decides every parallel 2-cell pair). -/
  | fullTwoCellDecided
  /-- A total 1-cell (dimension-1) decider is shipped, but no 2-cell decision (the walker's content is dim 1). -/
  | oneCellDecided
  /-- A total directed-order decider is shipped, but only for the preorder (no symmetric saturated conv). -/
  | orderDecidedOnly
  /-- No word-problem decider is shipped — a coherent presentation exists but no decision witness. -/
  | decisionNotShipped

/-- The decision-status map: six full-2-cell deciders, one 1-cell (involution), one order-only (co-KZ), one
unshipped (cyclic-3).  KZ is `fullTwoCellDecided` (its 2-cell equality decides via `decideKZEq`) and
additionally ships a directed-order decider `decideKZLETotal`. -/
def wordProblemDecisionStatus : WordProblemDecidedWalker → WordProblemDecisionStatus
  | .walkingInvolution => .oneCellDecided
  | .walkingMonad => .fullTwoCellDecided
  | .walkingCyclicThree => .decisionNotShipped
  | .idempotentSemigroup => .fullTwoCellDecided
  | .walkingComonad => .fullTwoCellDecided
  | .idempotentComonad => .fullTwoCellDecided
  | .walkingKZ => .fullTwoCellDecided
  | .walkingCoKZ => .orderDecidedOnly
  | .walkingAdjunction => .fullTwoCellDecided

/-- Whether a walker has a SHIPPED word-problem decider (any strength) — false only for cyclic-3.  Full
enumeration (no wildcard arm) so the match stays propext-free. -/
def hasShippedWordProblemDecider : WordProblemDecidedWalker → Bool
  | .walkingInvolution => true
  | .walkingMonad => true
  | .walkingCyclicThree => false
  | .idempotentSemigroup => true
  | .walkingComonad => true
  | .idempotentComonad => true
  | .walkingKZ => true
  | .walkingCoKZ => true
  | .walkingAdjunction => true

/-- The eight walkers with a SHIPPED word-problem decider (all but cyclic-3), enumerated. -/
def allWordProblemDecidedWalkersWithShippedDecider : List WordProblemDecidedWalker :=
  [.walkingInvolution, .walkingMonad, .idempotentSemigroup,
    .walkingComonad, .idempotentComonad, .walkingKZ, .walkingCoKZ, .walkingAdjunction]

/-- ★ **The shipped-decider count is exactly EIGHT** — kernel-checked (`rfl`).  Cyclic-3 is the lone gap. -/
theorem wordProblemShippedDeciderCountIsEight :
    allWordProblemDecidedWalkersWithShippedDecider.length = 8 := rfl

/-- The six walkers with a FULL saturated-2-cell decider, enumerated. -/
def allWordProblemFullTwoCellDecidedWalkers : List WordProblemDecidedWalker :=
  [.walkingMonad, .idempotentSemigroup, .walkingComonad, .idempotentComonad,
    .walkingKZ, .walkingAdjunction]

/-- ★ **The full-2-cell-decider count is exactly SIX** — kernel-checked (`rfl`). -/
theorem wordProblemFullTwoCellDeciderCountIsSix :
    allWordProblemFullTwoCellDecidedWalkers.length = 6 := rfl

/-- ★ **Cyclic-3 is the UNIQUE unshipped rung** — `hasShippedWordProblemDecider` is false at cyclic-3 and
true everywhere else (full case split, `rfl` per arm). -/
theorem cyclicThreeIsUniqueUnshippedDecision :
    ∀ walker : WordProblemDecidedWalker,
      hasShippedWordProblemDecider walker = false ↔ walker = .walkingCyclicThree
  | .walkingInvolution => ⟨fun h => Bool.noConfusion h, fun h => WordProblemDecidedWalker.noConfusion h⟩
  | .walkingMonad => ⟨fun h => Bool.noConfusion h, fun h => WordProblemDecidedWalker.noConfusion h⟩
  | .walkingCyclicThree => ⟨fun _ => rfl, fun _ => rfl⟩
  | .idempotentSemigroup => ⟨fun h => Bool.noConfusion h, fun h => WordProblemDecidedWalker.noConfusion h⟩
  | .walkingComonad => ⟨fun h => Bool.noConfusion h, fun h => WordProblemDecidedWalker.noConfusion h⟩
  | .idempotentComonad => ⟨fun h => Bool.noConfusion h, fun h => WordProblemDecidedWalker.noConfusion h⟩
  | .walkingKZ => ⟨fun h => Bool.noConfusion h, fun h => WordProblemDecidedWalker.noConfusion h⟩
  | .walkingCoKZ => ⟨fun h => Bool.noConfusion h, fun h => WordProblemDecidedWalker.noConfusion h⟩
  | .walkingAdjunction => ⟨fun h => Bool.noConfusion h, fun h => WordProblemDecidedWalker.noConfusion h⟩

/-! ## The census markers -/

/-- ★ **EIGHT OF NINE decided rungs carry a shipped decider (recorded).**  `= true` records the DECISION-axis
coverage: eight of the decided-9 walkers have a shipped total word-problem decider
(`wordProblemShippedDeciderCountIsEight`), six of them full saturated-2-cell deciders
(`wordProblemFullTwoCellDeciderCountIsSix`).  The census's "decided-9" is decided-8 on the decision axis. -/
def fxWpLedger_decisionCoverageEightOfNine : Bool := true

/-- ★ **GAP — the walking cyclic-3 word problem has NO shipped decider.**  `= true` records the honest gap the
census hides: cyclic-3 has only the Omega coherent presentation (`cyclicThreeWalkerCoherentPresentation`) and
the homology (`CyclicThreeChainComplex`, `H1 = ZZ/3`) — NO `Decidable`, no normalizer, no `_iff_` decider.
Its 1-cell word problem is decidable in principle (`Z/3`, the mod-3 analogue of the shipped involution parity
decider) but unshipped.  `cyclicThreeIsUniqueUnshippedDecision` proves it is the sole gap. -/
def fxWpLedger_cyclicThreeDecisionUnshipped : Bool := true

/-- ★★ **The walking adjunction is presentation-WALLED yet decision-DECIDED.**  `= true` records the axis
distinction the census blurs: the adjunction has no convergent Squier presentation
(`fxOmega4_walkingAdjunctionCoherentPresentationWalledR2 = true`, Schanuel-Street zig-zag) but its word problem
is totally decided by boundary-arc MATCHING (`decideSaturatedTwoCellConv_ofSeed`), not rewriting.
Presentation-walled and decision-decided are orthogonal; this ledger reads the decision axis. -/
def fxWpLedger_adjunctionPresentationWalledDecisionDecided : Bool := true

/-- ★ **The uniform decision machinery covers FOUR of the six full-2-cell deciders.**  `= true` records that
monad / idempotent / comonad / idempotent-comonad all inhabit the ONE interface
`DecidableSaturatedConvForRel`, with comonad / idempotent-comonad obtained from monad / idempotent by the ONE
op-transport combinator `decideSaturatedConvUnderOp` (no new normalizer).  The adjunction (matching) and KZ
(directed order) use their own interfaces — no single decider reaches all nine. -/
def fxWpLedger_uniformInterfaceCoversFourOfSix : Bool := true

/-- ★ **THE GRAND WORD-PROBLEM LEDGER IS NOT CLOSED (honest, core round).**  `= false` records that this is the
DECISION-ledger CORE, not the capstone (#2048) close.  Still owed: (1) the held witness bundle grounding the
eight deciders (`WordProblemDecisionWitnessBundle`, the non-rotting upgrade); (2) the cyclic-3 decider; (3) the
beyond-decided-9 rungs (equivalence / Frobenius monad / strong monad / bunched bimonoid / Brauer ...) with
their walls; (4) the WP-CEIL-COST #2046 cost tags.  Set `true` only when every rung is decided-or-walled with a
held witness and a cost tag. -/
def fxWpLedger_grandLedgerClosed : Bool := false

end FX1Poly.Polygraph.Table
