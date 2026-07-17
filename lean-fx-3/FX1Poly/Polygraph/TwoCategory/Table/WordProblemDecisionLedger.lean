/-! # Polygraph/TwoCategory/Table/WordProblemDecisionLedger — the grand word-problem DECISION ledger

★ **The decided-16 walkers' WORD-PROBLEM DECISION status, machine-checked (WP-LEDGER #2048, core round).**

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
  | walking cyclic-3                | oneCellDecided (dim-1 Z/3)   | `decideCyclicThreeOneCellConv` |
  | idempotent semigroup (= monad)  | fullTwoCellDecided           | `decideSaturatedConvOverIdempotentNative` |
  | walking comonad                 | fullTwoCellDecided           | `decideSaturatedConvOverComonadNative` |
  | idempotent comonad              | fullTwoCellDecided           | `decideSaturatedConvOverIdempotentComonadNative` |
  | walking KZ                      | fullTwoCellDecided (+ order) | `decideKZEq` / `decideKZLETotal` |
  | walking co-KZ                   | orderDecidedOnly (directed)  | `decideCoKZLETotal` |
  | walking adjunction              | fullTwoCellDecided (matching)| `decideSaturatedTwoCellConv_ofSeed` |
  | walking monoid operad           | treePastingDecided           | `decideOperadTreeConv` |
  | walking traced (3-axiom frag)   | fragmentDecided              | `decideTracedDiagramConv` |
  | walking double (unit-free grid) | guardedFragmentDecided       | `decideDoubleTileConv` |
  | positive braid monoid `B_3^+`   | oneCellDecided (dim-1, inf.) | `decideBraidThreeConv` |
  | walking commutative monoid      | treePastingDecided (= ℕ)     | `decideCommMonoidTreeConv` |
  | walking bounded semilattice     | treePastingDecided (= {⊥,⊤}) | `decideSemilatticeTreeConv` |
  | walking abelian group           | treePastingDecided (= ℤ)     | `decideAbelianGroupTreeConv` |

→ **16 of 16** carry a shipped total decider; SIX are full saturated-2-cell deciders, THREE are dimension-1
deciders (involution Z/2, cyclic-3 Z/3, and `B_3^+` — the first INFINITE dim-1 rung, left-greedy Garside NF),
one a directed-order decider only (co-KZ), FOUR are tree-pasting deciders (the operad's right-comb NF, plus
the three single-generator algebra seeds — the commutative monoid whose word problem collapses to `(ℕ, +, 0)`
by leaf count, the bounded semilattice whose idempotency collapses it to the two-element lattice `{⊥, ⊤}`
by slot presence, and the walking abelian group whose formal inverse completes that count to the integers `ℤ`
by winding number), one a FRAGMENT decider (the traced 3-axiom relation as shipped, smart-constructor NF — the
full JSV set walled in the walker's own `fxTraced_hasFullJsvTraceAxiomsDecided`), and one a GUARDED-fragment
decider (the double-cat unit-free grid, `(width, height)` invariant under well-formedness hypotheses — the
unit-bearing extension walled in `fxDouble_hasUnitBearingGridDecided`).  The former lone gap (cyclic-3) closed,
the operad joined via WP-OPERAD brick 2, the wave-5 trio (traced / double / braid) joined via WP-TRACED brick
2, WP-DOUBLE brick 2, and WP-BRAID-3, the two single-generator monoid seeds joined as decided-15, and the
walking abelian group (= walking ℤ, winding-number NF) joined as decided-16.

## NOT the capstone close (honest)

This is the DECISION-ledger CORE: the rung taxonomy, the kernel-checked per-rung status map, the coverage
counts, and the honest markers.  The witness bundle (`WordProblemDecisionWitnessBundle`) HOLDS all sixteen
deciders as grounded aliases, and the cost tags landed (`WordProblemCostLedger`, WP-CEIL-COST #2046).  Still
owed for the capstone (#2048): the beyond-decided-16 rungs (equivalence — resolved refute-and-relocate,
Frobenius monad, strong monad, bunched bimonoid, Brauer, cohesion-quadruple, ...) tabulated with their walls
in ONE machine-checked enumeration.  `fxWpLedger_grandLedgerClosed = false`.

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
  /-- The walking monoid operad `<m:2, e:0 | assoc, unitL, unitR>` — tree-pasting carrier (`OperadTree`, not
  `ModalityPath`), decided by the right-comb normal form (`decideOperadTreeConv`, WP-OPERAD brick 2). -/
  | walkingOperad
  /-- The walking traced structure, 3-AXIOM FRAGMENT (vanishing-I + yanking + left tightening) — wire-diagram
  carrier (`TracedDiagram`), decided by the smart-constructor normal form (`decideTracedDiagramConv`,
  WP-TRACED brick 2); the full JSV axiom set is the walker's own named wall. -/
  | walkingTraced
  /-- The walking-square double category, UNIT-FREE well-formed fragment — tile carrier (`DoubleTile`),
  decided by the `(width, height)` grid invariant under well-formedness hypotheses (`decideDoubleTileConv`,
  WP-DOUBLE brick 2); the unit-bearing extension is the walker's own named wall. -/
  | walkingDouble
  /-- The positive braid monoid `B_3^+ = <s1, s2 | s1.s2.s1 = s2.s1.s2>` — the first INFINITE dim-1 rung,
  decided by the left-greedy Garside normal form (`decideBraidThreeConv`, WP-BRAID-3). -/
  | walkingBraidPositive
  /-- The walking commutative monoid `<m:2, e:0 | assoc, unitL, unitR, comm>` — tree carrier
  (`CommMonoidTree`); ONE generating slot ⟹ word problem = `(ℕ, +, 0)` (leaf count), decided completely by
  `decideCommMonoidTreeConv` (`WalkingCommutativeMonoid/CommutativeMonoidSeed.lean`). -/
  | walkingCommutativeMonoid
  /-- The walking bounded semilattice `<m:2, e:0 | assoc, unitL, unitR, comm, idem>` — tree carrier
  (`SemilatticeTree`); ONE generating slot ⟹ idempotency collapses the count to the two-element lattice
  `{⊥, ⊤}`, decided completely by `decideSemilatticeTreeConv` (`WalkingSemilattice/SemilatticeSeed.lean`). -/
  | walkingBoundedSemilattice
  /-- The walking abelian group `<m:2, e:0, i:1 | assoc, unitL, unitR, comm, invL, invR>` — tree carrier
  (`AbelianGroupTree`); ONE generating slot ⟹ adjoining a formal inverse completes the commutative monoid's
  count to the integers `ℤ`, so the word problem is winding-number equality (a difference pair `ℕ²/~`, no
  signed type), decided completely by `decideAbelianGroupTreeConv`
  (`WalkingAbelianGroup/AbelianGroupSeed.lean`). -/
  | walkingAbelianGroup

/-- The complete enumeration of the decided-16 walkers — SIXTEEN, listed. -/
def allWordProblemDecidedWalkers : List WordProblemDecidedWalker :=
  [.walkingInvolution, .walkingMonad, .walkingCyclicThree, .idempotentSemigroup,
    .walkingComonad, .idempotentComonad, .walkingKZ, .walkingCoKZ, .walkingAdjunction,
    .walkingOperad, .walkingTraced, .walkingDouble, .walkingBraidPositive,
    .walkingCommutativeMonoid, .walkingBoundedSemilattice, .walkingAbelianGroup]

/-- ★ **The decided-walker count is exactly SIXTEEN** — kernel-checked (`rfl`). -/
theorem wordProblemDecidedWalkerCountIsSixteen : allWordProblemDecidedWalkers.length = 16 := rfl

/-- ★ **The decided-16 enumeration is EXHAUSTIVE** — every walker appears (full case split, `List.Mem` ctors,
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
  | .walkingOperad =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))))))))
  | .walkingTraced =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
  | .walkingDouble =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
  | .walkingBraidPositive =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.head _))))))))))))
  | .walkingCommutativeMonoid =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.head _)))))))))))))
  | .walkingBoundedSemilattice =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))
  | .walkingAbelianGroup =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))

/-! ## The word-problem decision status of each walker -/

/-- The **word-problem decision status** of a decided walker on the DECISION axis. -/
inductive WordProblemDecisionStatus
  /-- A total saturated-2-cell decider is shipped (decides every parallel 2-cell pair). -/
  | fullTwoCellDecided
  /-- A total 1-cell (dimension-1) decider is shipped, but no 2-cell decision (the walker's content is dim 1). -/
  | oneCellDecided
  /-- A total directed-order decider is shipped, but only for the preorder (no symmetric saturated conv). -/
  | orderDecidedOnly
  /-- A total TREE-PASTING decider is shipped — the walker's carrier is operadic trees (grafting
  composition), not `ModalityPath` words; the decision is a tree normal form (right-comb). -/
  | treePastingDecided
  /-- A total decider is shipped for the walker's SHIPPED axiom FRAGMENT — the relation as-is is fully
  decided, but it is a named strict subset of the classical axiom set (the extension is the walker's own
  wall flag, e.g. the traced full-JSV rows). -/
  | fragmentDecided
  /-- A total decider is shipped on a WELL-FORMEDNESS-GUARDED fragment — the decider carries wf hypotheses
  (e.g. the double-cat unit-free grid: `decideDoubleTileConv` takes `IsUnitFreeGrid` witnesses); the
  unguarded extension is the walker's own wall flag. -/
  | guardedFragmentDecided
  /-- No word-problem decider is shipped — a coherent presentation exists but no decision witness. -/
  | decisionNotShipped

/-- The decision-status map: six full-2-cell deciders, THREE 1-cell deciders (involution Z/2, cyclic-3 Z/3,
the infinite `B_3^+` by Garside NF), one order-only (co-KZ), FOUR tree-pasting (operad + the three
single-generator seeds: commutative monoid, bounded semilattice, abelian group), one fragment (traced
3-axiom), one guarded-fragment (double unit-free grid).  KZ is `fullTwoCellDecided` (its 2-cell equality
decides via `decideKZEq`) and additionally ships a directed-order decider `decideKZLETotal`. -/
def wordProblemDecisionStatus : WordProblemDecidedWalker → WordProblemDecisionStatus
  | .walkingInvolution => .oneCellDecided
  | .walkingMonad => .fullTwoCellDecided
  | .walkingCyclicThree => .oneCellDecided
  | .idempotentSemigroup => .fullTwoCellDecided
  | .walkingComonad => .fullTwoCellDecided
  | .idempotentComonad => .fullTwoCellDecided
  | .walkingKZ => .fullTwoCellDecided
  | .walkingCoKZ => .orderDecidedOnly
  | .walkingAdjunction => .fullTwoCellDecided
  | .walkingOperad => .treePastingDecided
  | .walkingTraced => .fragmentDecided
  | .walkingDouble => .guardedFragmentDecided
  | .walkingBraidPositive => .oneCellDecided
  | .walkingCommutativeMonoid => .treePastingDecided
  | .walkingBoundedSemilattice => .treePastingDecided
  | .walkingAbelianGroup => .treePastingDecided

/-- Whether a walker has a SHIPPED word-problem decider (any strength) — true at all sixteen (cyclic-3's
former gap closed; the operad, traced fragment, unit-free double grid, `B_3^+` Garside, and the three
single-generator algebra seeds all joined).  Full enumeration (no wildcard arm) so the match stays
propext-free. -/
def hasShippedWordProblemDecider : WordProblemDecidedWalker → Bool
  | .walkingInvolution => true
  | .walkingMonad => true
  | .walkingCyclicThree => true
  | .idempotentSemigroup => true
  | .walkingComonad => true
  | .idempotentComonad => true
  | .walkingKZ => true
  | .walkingCoKZ => true
  | .walkingAdjunction => true
  | .walkingOperad => true
  | .walkingTraced => true
  | .walkingDouble => true
  | .walkingBraidPositive => true
  | .walkingCommutativeMonoid => true
  | .walkingBoundedSemilattice => true
  | .walkingAbelianGroup => true

/-- All SIXTEEN decided walkers carry a SHIPPED word-problem decider. -/
def allWordProblemDecidedWalkersWithShippedDecider : List WordProblemDecidedWalker :=
  [.walkingInvolution, .walkingMonad, .walkingCyclicThree, .idempotentSemigroup,
    .walkingComonad, .idempotentComonad, .walkingKZ, .walkingCoKZ, .walkingAdjunction,
    .walkingOperad, .walkingTraced, .walkingDouble, .walkingBraidPositive,
    .walkingCommutativeMonoid, .walkingBoundedSemilattice, .walkingAbelianGroup]

/-- ★ **The shipped-decider count is exactly SIXTEEN** — kernel-checked (`rfl`).  Cyclic-3's former gap
closed by `decideCyclicThreeOneCellConv` (decided-8 → 9); the operad's right-comb decision joined (9 → 10);
the wave-5 trio joined — traced 3-axiom fragment (`decideTracedDiagramConv`), unit-free double grid
(`decideDoubleTileConv`), `B_3^+` Garside (`decideBraidThreeConv`) — decided-10 → decided-13; the two
single-generator monoid rungs joined — commutative monoid (`decideCommMonoidTreeConv`, = ℕ) and
bounded semilattice (`decideSemilatticeTreeConv`, = `{⊥,⊤}`) — decided-13 → decided-15; the walking abelian
group joined — (`decideAbelianGroupTreeConv`, = ℤ winding number) — decided-15 → decided-16. -/
theorem wordProblemShippedDeciderCountIsSixteen :
    allWordProblemDecidedWalkersWithShippedDecider.length = 16 := rfl

/-- The six walkers with a FULL saturated-2-cell decider, enumerated. -/
def allWordProblemFullTwoCellDecidedWalkers : List WordProblemDecidedWalker :=
  [.walkingMonad, .idempotentSemigroup, .walkingComonad, .idempotentComonad,
    .walkingKZ, .walkingAdjunction]

/-- ★ **The full-2-cell-decider count is exactly SIX** — kernel-checked (`rfl`). -/
theorem wordProblemFullTwoCellDeciderCountIsSix :
    allWordProblemFullTwoCellDecidedWalkers.length = 6 := rfl

/-- ★ **ALL SIXTEEN decided walkers carry a shipped decider** — `hasShippedWordProblemDecider` is true at
every walker (full case split, `rfl` per arm). -/
theorem allWordProblemDecidedWalkersHaveShippedDecider :
    ∀ walker : WordProblemDecidedWalker, hasShippedWordProblemDecider walker = true
  | .walkingInvolution => rfl
  | .walkingMonad => rfl
  | .walkingCyclicThree => rfl
  | .idempotentSemigroup => rfl
  | .walkingComonad => rfl
  | .idempotentComonad => rfl
  | .walkingKZ => rfl
  | .walkingCoKZ => rfl
  | .walkingAdjunction => rfl
  | .walkingOperad => rfl
  | .walkingTraced => rfl
  | .walkingDouble => rfl
  | .walkingBraidPositive => rfl
  | .walkingCommutativeMonoid => rfl
  | .walkingBoundedSemilattice => rfl
  | .walkingAbelianGroup => rfl

/-! ## The census markers -/

/-- ★ **SIXTEEN OF SIXTEEN decided rungs carry a shipped decider (recorded).**  `= true` records that the
DECISION axis covers ALL sixteen walkers (`wordProblemShippedDeciderCountIsSixteen`), six of them full
saturated-2-cell deciders (`wordProblemFullTwoCellDeciderCountIsSix`), after cyclic-3's ℤ/3 decider landed
(decided-8 → 9), the operad's right-comb decision joined (9 → 10), the wave-5 trio — traced fragment,
unit-free double grid, `B_3^+` Garside — joined (10 → 13), the two single-generator monoid
rungs — commutative monoid (= ℕ) and bounded semilattice (= `{⊥,⊤}`) — joined (13 → 15), and the walking
abelian group (= ℤ winding number) joined (15 → 16,
`allWordProblemDecidedWalkersHaveShippedDecider`). -/
def fxWpLedger_decisionCoverageSixteenOfSixteen : Bool := true

/-- ★ **The traced 3-axiom fragment joined the decided census (recorded).**  `= true` records that
`decideTracedDiagramConv` (WP-TRACED brick 2, `WalkingTraced/TracedDiagramDecision.lean`) totally decides
the SHIPPED traced fragment (vanishing-I + yanking + left tightening + congruence) via the smart-constructor
normal form `tracedNF` — the fragment is an orthogonal strictly-size-reducing system, so the seed's
"needs the Int-construction" prose was stale FOR IT.  The full JSV axiom set (sliding etc.) stays walled in
the walker's own `fxTraced_hasFullJsvTraceAxiomsDecided = false`; this rung enters as `fragmentDecided`,
honestly scoped. -/
def fxWpLedger_tracedFragmentDecisionShipped : Bool := true

/-- ★ **The unit-free double-cat grid joined the decided census (recorded).**  `= true` records that
`decideDoubleTileConv` (WP-DOUBLE brick 2, `WalkingDouble/DoubleTileGridNF.lean`) decides the walking-square
tile word problem on the UNIT-FREE well-formed fragment via the `(tileWidth, tileHeight)` invariant — the
decider carries `IsUnitFreeGrid` hypotheses (hence `guardedFragmentDecided`), completeness rides the
interchange-star grid merge `hMerge`.  The unit-bearing extension stays walled in the walker's own
`fxDouble_hasUnitBearingGridDecided = false`. -/
def fxWpLedger_unitFreeDoubleGridDecisionShipped : Bool := true

/-- ★ **The positive braid monoid `B_3^+` joined the decided census (recorded).**  `= true` records that
`decideBraidThreeConv` (WP-BRAID-3, `WalkingBraid/BraidThreeGarsideDecision.lean`) totally decides the FULL
`B_3^+` word problem on arbitrary words via the left-greedy Garside normal form (`braidNormalizeWord` over
`BraidGarsideCanon`; completeness through the greedy-agreement crux `braidPrependAtom_braidAgreement`) — the
FIRST decided rung whose carrier monoid is INFINITE (`s1^k` all distinct), entering as `oneCellDecided`
alongside the finite `Z/2` / `Z/3` residue rungs.  The braid GROUP (negative Δ-powers) is a future rung. -/
def fxWpLedger_braidPositiveGarsideDecisionShipped : Bool := true

/-- ★ **The walking monoid operad joined the decided census (recorded).**  `= true` records that
`decideOperadTreeConv` (WP-OPERAD brick 2, `WalkingOperad/OperadTreeDecision.lean`) totally decides the
operad tree-pasting word problem via the right-comb normal form (`operadNF = reify ∘ arityOf`; soundness
`operadNF_congr_of_conv`; completeness `conv_toReify` via the `reify_mulOp_append` grafting crux;
characterization `operadConv_iff_nf_eq`), zero-axiom — the FIRST decided rung whose carrier is operadic
trees rather than `ModalityPath` words.  The prior decided-9 is upgraded to decided-10. -/
def fxWpLedger_operadDecisionShipped : Bool := true

/-- ★ **CLOSED — the walking cyclic-3 word problem now HAS a shipped decider.**  `= true` records that the
former honest gap is closed: `decideCyclicThreeOneCellConv` (in `WalkingCyclicThree/CyclicThreeDecision.lean`)
totally decides the cyclic-3 one-cell word problem via a genuine ℤ/3 residue (`cyclicThreeResidueOf =
natMod3 ∘ length`; soundness `cyclicThreeResidueOf_congr_of_conv`; completeness
`cyclicThreeOneCellConv_of_residue_eq`; the cyclic content `shiftResidueTripleIsIdentity`), zero-axiom.  The
prior "decided-8" is upgraded to decided-9. -/
def fxWpLedger_cyclicThreeDecisionShipped : Bool := true

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

/-- ★ **THE GRAND WORD-PROBLEM LEDGER IS NOT CLOSED (honest).**  `= false` records that the decided-16 core
is complete (all sixteen deciders shipped + held in `WordProblemDecisionWitnessBundle`) and the WP-CEIL-COST
#2046 cost tags landed (`WordProblemCostLedger`, all `.cited`, `fxWpCost_allTagsProved = false`).

THE ENUMERATION CLAUSE IS NOW DELIVERED: the beyond-decided-16 rungs (equivalence, Frobenius monad, strong
monad, bunched bimonoid, distributive law, Brauer, cohesion-quadruple, adjoint-triple string, 2-group,
endomorphism) AND the fragment-extension walls (traced full-JSV, double unit-bearing, braid group) are
tabulated with their walls in ONE machine-checked enumeration — `WordProblemBeyondCensusWalls.lean`
(thirteen rungs, total disposition map, live-flag `rfl` pins per rung,
`fxWpBeyond_beyondCensusWallsTabulated = true`).

THE REMAINING FLIP BILL (verbatim: "a held witness and a cost tag" per rung): (1) witness aliases + cost
tags for the THREE beyond-census DECIDED rungs (the adjoint-triple string decision; the Brauer indexed-scope
normal form; the braid GROUP `decideBraidThreeGroupConv`, WP-BRAID-4) in the witness bundle + cost ledger;
(2) a per-wall adjudication of what "held witness" means
for a walled rung (the pin theorems hold the wall FLAGS — whether that satisfies the demand is an
orchestrator decision to record, not to assume); (3) `fxWpCost_allTagsProved` remains false (COST-7).
Set `true` only when every rung is decided-or-walled with a held witness and a cost tag; any flip must
update `fxWpBeyond_tabulationLandedGrandStillOpen` in the SAME commit (it rfl-pins this marker). -/
def fxWpLedger_grandLedgerClosed : Bool := false

end FX1Poly.Polygraph.Table
