import FX1Poly.Polygraph.Omega.ZXPhaseFree.CombRowFold

/-! # Polygraph/Omega/ZXPhaseFree/CombTrueArmFold — THE SHARED-COPY-PREFIX CARRIER
and its general fusion: the true-arm content the single-row fold's wall named

The prior round (`CombRowFold`, the `zxq*` atoms) proved the FALSE-arm prefix-shift
identity (`zxqCombPrefixShift`, general — an unset prefix wire whiskers the whole
comb by one identity strand) and the `[false, true]` traversal, then walled the
general single-row fold (`zxqHasGeneralCombFold := false`) on the exact remaining
obstruction: the TRUE-arm correlated Z-copy prefix.  A set bit forks one carrier
value that is shared across every later set position, so the general fold's target
at the set positions is a copy-CHAIN of the SAME free root — not a spectator `|0>`
and not a plain whiskered smaller state.

This round builds the true-arm content bottom-up, general in the number of forks:

* THE SHARED-COPY-PREFIX CARRIER (`zxhChainFrom`): the copy chain that fans one
  shared Z root to `forkCount + 1` correlated free bits — one full-width Z fork per
  bit, the `k`-th layer a `zSpider (startWidth + k) (startWidth + k + 1)` adding
  exactly one leg.  This is the "one Z-fork per set bit fanning a single free root"
  the wall named.

* THE GENERAL CHAIN FUSION (`zxhChainFromFuse`, PROVED, general in `startWidth`
  and `forkCount`): the copy chain collapses to a SINGLE Z spider
  `zSpider startWidth (startWidth + forkCount + 1)` — a fold of the committed
  parallel fusion `zxwParallelFusionZ`, one fusion per fork, closed by induction on
  the fork count.  This generalizes the r18 span pin `zxmCopyStateFusedSpanPin`
  (the `n = 2` case only) to a real `ZxwConv` for ALL fork counts.  It is the
  algebraic backbone of the true arm: the correlated copy chain a run of set bits
  produces IS one spider.

* THE FIRES (`zxh*Fire`, `zxh*SpanPin`): length-2, length-3, length-4 copy chains
  fuse (fresh `ZxwConv` fires the prior rounds never pinned), plus `zxpSpanEqB`
  kernel pins for fresh single-row targets — `[true, true, true]` (a length-3 copy
  chain), `[true, false, true]` reconfirmed against the chain form, and a
  discriminating FALSE span control.

* THE GENERAL FOLD stays walled (`zxhHasGeneralSingleRowFold := false`) with two
  genuinely different burned attacks recorded precisely: the algebraic chain fusion
  is now general, but wiring the FED source into the chain at each set bit still
  needs the moving-position feed-collapse bookkeeping that r18/r19/r20 named.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`,
no `Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive
scrutinees.  Fresh markers are this file's `zxh*`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — a clean arithmetic shifter (no AC simp set) -/

/-- `startWidth + 1 + forkCount = startWidth + forkCount + 1` — the successor slides
right across an addition.  Proved by structural induction on `forkCount`, no Nat AC
lemmas (those leak propext as a set). -/
theorem zxhSuccSlideRight : (startWidth : Nat) -> (forkCount : Nat) ->
    startWidth + 1 + forkCount = startWidth + forkCount + 1
  | _startWidth, 0 => rfl
  | startWidth, forkPred + 1 =>
      congrArg (fun value => value + 1) (zxhSuccSlideRight startWidth forkPred)

/-! ## Stage 1 — THE SHARED-COPY-PREFIX CARRIER: the copy chain fanning one root -/

/-- THE COPY CHAIN: starting from `startWidth` already-correlated strands, add
`forkCount` more correlated legs one at a time — the `k`-th layer is a full-width
`zSpider (startWidth + k) (startWidth + k + 1)` fanning the shared root by exactly
one leg.  With `startWidth = 0` and one root creation this is the correlated
free-bit copy state a run of set bits produces. -/
def zxhChainFrom (startWidth : Nat) : Nat -> List (List ZxpCell)
  | 0 => []
  | forkCount + 1 =>
      [ZxpCell.zSpider startWidth (startWidth + 1)]
        :: zxhChainFrom (startWidth + 1) forkCount

/-- Well-formedness of a one-cell Z-spider layer at its own domain arity. -/
theorem zxhSpiderLayerWF (domArity codArity : Nat) :
    ZxpLayersWF domArity [[ZxpCell.zSpider domArity codArity]] :=
  ZxpLayersWF.cons (Nat.add_zero domArity) (ZxpLayersWF.nil _)

/-! ## Stage 2 — THE GENERAL CHAIN FUSION: the copy chain IS one Z spider -/

/-- THE GENERAL CHAIN FUSION: a copy chain of `forkCount + 1` full-width Z forks
(the shared root fanned to `forkCount + 1` correlated bits) collapses to the single
Z spider `zSpider startWidth (startWidth + forkCount + 1)`.  Structural induction on
`forkCount`: the base is the lone spider; the step lifts the induction hypothesis
below the leading fork and fires ONE committed parallel fusion
(`zxwParallelFusionZ`).  General in the start width and the fork count — the
algebraic backbone of the true arm's correlated copy prefix. -/
theorem zxhChainFromFuse : (startWidth : Nat) -> (forkCount : Nat) ->
    ZxwConv
      { sourceArity := startWidth, layers := zxhChainFrom startWidth (forkCount + 1) }
      { sourceArity := startWidth
        layers := [[ZxpCell.zSpider startWidth (startWidth + forkCount + 1)]] }
  | startWidth, 0 => by
      refine ZxwConv.refl _ ?_
      exact zxhSpiderLayerWF startWidth (startWidth + 1)
  | startWidth, forkPred + 1 => by
      -- lift the induction hypothesis below the leading fork
      have hLift := zxwLiftConv startWidth
        [[ZxpCell.zSpider startWidth (startWidth + 1)]] []
        (zxhChainFromFuse (startWidth + 1) forkPred)
        (zxhSpiderLayerWF startWidth (startWidth + 1)) rfl (ZxpLayersWF.nil _)
      simp only [zxpCatLayers, zxpCatLayersNilRight] at hLift
      -- fire one parallel fusion on the exposed two-spider column
      have hFuse := zxwParallelFusionZ startWidth
        (startWidth + 1 + forkPred + 1) startWidth
      -- reconcile the shared-leg / output-leg arithmetic and chain
      have hArith : startWidth + 1 + forkPred + 1 = startWidth + (forkPred + 1) + 1 :=
        congrArg (fun value => value + 1) (zxhSuccSlideRight startWidth forkPred)
      exact hArith ▸ ZxwConv.trans hLift hFuse

/-! ## Stage 3 — the free-bit copy state and its fusion -/

/-- THE FREE-BIT COPY STATE: create one shared Z root, then fan it to
`freeBitsPred + 1` correlated free bits — the canonical correlated output a run of
`freeBitsPred + 1` set bits produces. -/
def zxhFreeCopyState (freeBitsPred : Nat) : ZxpDiagram :=
  { sourceArity := 0, layers := zxhChainFrom 0 (freeBitsPred + 1) }

/-- THE FREE-BIT COPY STATE FUSES: the correlated copy state collapses to the single
Z spider `zSpider 0 (freeBitsPred + 1)` — the fused two-output-and-up copy state.
The `startWidth = 0` instance of the general chain fusion. -/
theorem zxhFreeCopyStateFuses (freeBitsPred : Nat) :
    ZxwConv (zxhFreeCopyState freeBitsPred)
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 (freeBitsPred + 1)]] } := by
  have hFuse := zxhChainFromFuse 0 freeBitsPred
  have hArith : (0 : Nat) + freeBitsPred + 1 = freeBitsPred + 1 :=
    congrArg (fun value => value + 1) (Nat.zero_add freeBitsPred)
  show ZxwConv (zxhFreeCopyState freeBitsPred)
    { sourceArity := 0, layers := [[ZxpCell.zSpider 0 (freeBitsPred + 1)]] }
  exact hArith ▸ hFuse

/-! ## Stage 4 — THE CHAIN-FUSE FIRES: fresh correlated-copy chains collapse -/

/-- Explicit pin: the length-3 copy chain `zxhChainFrom 0 3` is the three-fork
full-width staircase `[[Z01], [Z12], [Z23]]` (each layer fans the shared root by
one leg). -/
theorem zxhLengthThreeChainLayers :
    zxhChainFrom 0 3 =
      [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 2], [ZxpCell.zSpider 2 3]] := rfl

/-- FIRE (fresh): the length-3 copy chain collapses to the single Z spider
`[[Z03]]` — three correlated free bits from one shared root, `ZxwConv`, the
`n = 3` case the prior rounds only ever pinned semantically. -/
theorem zxhLengthThreeChainFuseFire :
    ZxwConv { sourceArity := 0, layers := zxhChainFrom 0 3 }
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 3]] } :=
  zxhChainFromFuse 0 2

/-- FIRE (fresh): the length-4 copy chain collapses to `[[Z04]]` — four correlated
free bits from one shared root. -/
theorem zxhLengthFourChainFuseFire :
    ZxwConv { sourceArity := 0, layers := zxhChainFrom 0 4 }
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 4]] } :=
  zxhChainFromFuse 0 3

/-- FIRE (fresh, general start): a chain that starts from `2` already-correlated
strands and adds three forks collapses to `[[Z2 5]]` — the start-width-general
instance the induction needs. -/
theorem zxhStartTwoChainFuseFire :
    ZxwConv { sourceArity := 2, layers := zxhChainFrom 2 3 }
      { sourceArity := 2, layers := [[ZxpCell.zSpider 2 5]] } :=
  zxhChainFromFuse 2 2

/-- FIRE (fresh): the three-free-bit copy state fuses to `[[Z03]]`. -/
theorem zxhFreeCopyThreeFuseFire :
    ZxwConv (zxhFreeCopyState 2)
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 3]] } :=
  zxhFreeCopyStateFuses 2

/-! ## Stage 4b — THE COMMITTED TWO-BIT TRAVERSAL RE-DERIVED THROUGH THE CHAIN:
the general chain fusion recovers the r18 fused result as one instance -/

/-- THE TWO-BIT COMB, VIA THE CHAIN: the committed `[true, true]` traversal
(`zxmCombTraversalTwoBit`) lands on `zxhFreeCopyState 1` on the nose — the
full-width copy chain coincides with the leg-fork chain at width two — and the
general chain fusion (`zxhFreeCopyStateFuses`) then collapses it to `[[Z02]]`.
This re-derives the committed `zxmCombTraversalTwoBitFused` THROUGH the general
chain machinery, an end-to-end true-arm fire: two created states feed-collapse to a
correlated copy chain, which fuses to one spider. -/
theorem zxhTwoBitTraversalViaChain :
    ZxwConv (zxqFoldSource [true, true])
      { sourceArity := 0, layers := [[ZxpCell.zSpider 0 2]] } :=
  ZxwConv.trans zxmCombTraversalTwoBit (zxhFreeCopyStateFuses 1)

/-! ## Stage 5 — THE SPAN FIRES: fresh single-row targets on the correlated chain -/

/-- Kernel span pin: the three-free-bit copy state lands in the SAME span class as
`[[Z03]]`.  Note `zxpSpanEqB` is COARSE on output-leg count (it also holds against
`[[Z0k]]` for other `k`), so this pins the correlated-Z-copy span-class, NOT the
exact leg count; the exact three-leg identity is the `ZxwConv` fire
`zxhFreeCopyThreeFuseFire`. -/
theorem zxhFreeCopyThreeSpanPin :
    zxpSpanEqB (zxpDiagramDenote (zxhFreeCopyState 2))
      (zxpDiagramDenote { sourceArity := 0, layers := [[ZxpCell.zSpider 0 3]] }) = true :=
  rfl

/-- FIRE (fresh): three set bits `[true, true, true]` feed-collapse to a length-3
correlated copy chain, landing in the SAME span class as `[[Z03]]` — the genuine
`n = 3` true-arm target: three set positions sharing ONE free root.  As above,
`zxpSpanEqB` is coarse on leg count, so this pins the correlated-Z-copy class; the
exact three-leg `ZxwConv` identity is `zxhLengthThreeChainFuseFire`. -/
theorem zxhTrueTrueTrueSpanPin :
    zxpSpanEqB (zxpDiagramDenote (zxqFoldSource [true, true, true]))
      (zxpDiagramDenote { sourceArity := 0, layers := [[ZxpCell.zSpider 0 3]] }) = true :=
  rfl

/-- FIRE (fresh): three set bits collapse to the three-free-bit copy chain state
(`zxhFreeCopyState 2`) — the correlated-copy chain form, span-equal to the feed. -/
theorem zxhTrueTrueTrueChainSpanPin :
    zxpSpanEqB (zxpDiagramDenote (zxqFoldSource [true, true, true]))
      (zxpDiagramDenote (zxhFreeCopyState 2)) = true :=
  rfl

/-- FIRE (discriminating FALSE control): three set bits do NOT collapse to three
INDEPENDENT free bits `[[Z01, Z01, Z01]]` — the three set positions share ONE
correlated root, they are not three unrelated free bits.  The span separates. -/
theorem zxhTrueTrueTrueNotIndependentSpanPin :
    zxpSpanEqB (zxpDiagramDenote (zxqFoldSource [true, true, true]))
      (zxpDiagramDenote
        { sourceArity := 0
          layers := [[ZxpCell.zSpider 0 1, ZxpCell.zSpider 0 1, ZxpCell.zSpider 0 1]] })
      = false :=
  rfl

/-- FIRE (discriminating FALSE control): three set bits are not three `|0>` states
`[[X01, X01, X01]]` either — the correlated free root is not the zero state. -/
theorem zxhTrueTrueTrueNotZeroSpanPin :
    zxpSpanEqB (zxpDiagramDenote (zxqFoldSource [true, true, true]))
      (zxpDiagramDenote
        { sourceArity := 0
          layers := [[ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1]] })
      = false :=
  rfl

/-! ## Stage 6 — the honest marker ledger -/

/-- CONTENT MARKER (TRUE): the SHARED-COPY-PREFIX CARRIER and its general fusion are
LANDED (`zxhChainFrom`, `zxhChainFromFuse`, general in `startWidth` and `forkCount`)
— the correlated copy chain a run of set bits produces (one Z fork per bit fanning a
single shared root) collapses to ONE Z spider, as a real `ZxwConv` for ALL fork
counts, a fold of the committed `zxwParallelFusionZ`.  This generalizes the r18
`n = 2` span pin `zxmCopyStateFusedSpanPin` to the general true-arm algebra. -/
def zxhHasSharedCopyChainFusion : Bool := true

/-- CONTENT MARKER (TRUE): the two-bit traversal is RE-DERIVED THROUGH THE CHAIN
(`zxhTwoBitTraversalViaChain`) — the committed `[true, true]` feed-collapse lands on
the length-2 copy chain (`zxhFreeCopyState 1`, the full-width chain coinciding with
the leg-fork chain at width two) and the general chain fusion collapses it to
`[[Z02]]`, recovering `zxmCombTraversalTwoBitFused` through the general machinery. -/
def zxhHasTwoBitViaChain : Bool := true

/-- CONTENT MARKER (TRUE): the fresh chain-fuse and single-row span fires are LIVE
(`zxhLengthThreeChainFuseFire`, `zxhLengthFourChainFuseFire`,
`zxhStartTwoChainFuseFire`, `zxhFreeCopyThreeFuseFire`; `zxhTrueTrueTrueSpanPin`,
`zxhTrueTrueTrueChainSpanPin`, plus two discriminating FALSE controls) — the
length-3 and length-4 correlated copy chains collapse, three set bits pin to the
shared length-3 copy, and the FALSE controls separate the correlated root from three
independent free bits and from three `|0>` states. -/
def zxhHasChainAndSpanFires : Bool := true

/-- OWNER MARKER (FALSE): the GENERAL single-row fold did NOT land — a created
`|0>` block fed into an arbitrary comb `zxnXorRowLayers rowBits` is not converted to
its free-bit normal form for general `rowBits`.  The committed owner-false flags
`zxqHasGeneralCombFold`, `zxuHasGeneralIdentityAbsorb`,
`zxmHasGeneralCombTraversal`, `zxiHasFeedingCombRouter`, `zxjHasIdentityAbsorb`,
`zxkIdentityAbsorbIsProven` stay byte-intact false.

The r20 wall isolated the obstruction to the true arm's correlated Z-copy prefix.
This round supplies the ALGEBRAIC backbone of that prefix in full generality: the
correlated copy chain IS one spider (`zxhChainFromFuse`).  What remains unbuilt is
the WIRING of the fed source into that chain across the whole comb.  Two genuinely
different attacks burned:

* (A) THE CHAIN-DRIVEN FOLD.  With `zxhChainFromFuse` in hand, the plan is a
  structural recursion over `rowBits` carrying a shared-copy accumulator: at a
  `true` bit, extend the chain by one fork; at a `false` bit, whisker via
  `zxqCombPrefixShift`; at the base, fuse.  BURN: extending the chain at set bit
  `j_k` requires the fed state to be feed-collapsed (`zxuFeedColumnCollapse`) at the
  MOVING strand index `k` (the count of already-processed set bits) AND the shared
  carrier copy to be ROUTED (`zxuStateWalk`) from its current column to strand `k`,
  a route whose length grows with the inter-set-bit gap.  The chain fusion is
  position-free, but the FEED that builds each chain layer fires at a per-set-bit
  moving left-pad — the exact moving-position bookkeeping r18/r19/r20 named — so the
  chain accumulator does not by itself thread the feed through the comb.

* (B) THE FUSED-TARGET INDUCTION.  Alternatively target the fused spider
  `[[Z0 setCount]]` directly and feed-collapse each set bit into the growing spider
  via `zxwMidForkFuseZ`.  BURN: `zxwMidForkFuseZ` grows a spider by a fork on a leg
  at a FIXED position, but the comb presents each set bit's fork at the carrier's
  current strand, which the intervening unset-bit crossings SHIFT — so the fork to
  be fused sits at a moving position, and reconciling it with the fixed-position
  fusion needs the same `zxuStateWalk` route as (A).  Both attacks reduce to the
  identical unbuilt piece: routing the shared carrier and the fed state to the
  moving set-bit column, the feed-collapse fold this file's chain algebra does not
  supply. -/
def zxhHasGeneralSingleRowFold : Bool := false

end FX1Poly.Polygraph.Omega.ZXPhaseFree
