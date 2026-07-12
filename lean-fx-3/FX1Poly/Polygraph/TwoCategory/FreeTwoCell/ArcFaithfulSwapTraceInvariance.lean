import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingSwapDispatcher

/-! # MODE-COMMUTE r14 (I2 + I4) — the FAITHFUL swap TRACE-EQUIVALENCE and its fold-invariance (extract-level)

The r13 dispatcher `arcFaithfulSwapExtractRestCommute` (`ArcCrossingSwapDispatcher`) proves the SINGLE two-step
exchange move: for any pair of faithful-step arities `(lowKind, highKind)`, the low-first and high-first two-step
runs (offset per Delpeuch–Vicary) land equal `rest`-spine extracts, under a uniform admissible seed
(freshness, forest-rootedness, `0 < nextFresh`, the bottom-boundary bound) and the combo's disjoint-window bound.
This file closes that generator up into the reflexive-symmetric-transitive TRACE CONGRUENCE and proves the
extract is invariant along it.

## The construction (I2)

  * `FaithfulSwapTraceEquiv bottomCount` — the equivalence closure of the dispatcher's own two-step swap on
    `ArcWireState`.  Its ★ generating constructor `ofSwap` PACKAGES the dispatcher's five admissibility hypotheses
    as FIELDS (freshness, forest, `0 < nextFresh`, `bottomCount ≤ nextFresh`, the window), so the closure is
    genuinely inhabited only at admissible swaps and the fold-invariance below never re-derives them mid-chain.
    `refl` / `symm` / `trans` close it into an equivalence relation.

  * ★ `extractArc_eq_of_faithfulSwapTraceEquiv` — **the trace-invariance.**  For any `signature`, boundary indices
    and continuation `rest`, states related by `FaithfulSwapTraceEquiv` have EQUAL `extractArc`-after-`rest`.  By
    STRUCTURAL induction on the equivalence derivation: the `ofSwap` arm IS the dispatcher (verbatim), `refl` is
    `rfl`, `symm` / `trans` are `Eq.symm` / `Eq.trans`.  This is the printed **universal property of the trace
    (free partially commutative) monad** (Cartier–Foata / Mazurkiewicz; Diekert–Rozenberg, *The Book of Traces*):
    a semantics sending independent adjacent generators to commuting operators factors uniquely through the trace
    congruence, so equal traces ⇒ equal image.  The nine disjoint-window commutes are the commuting-image
    hypothesis; the fold is the induced evaluation morphism.  The Godement/interchange reading is Mimram, *Towards
    3-Dimensional Rewriting Theory* (LMCS 2014), eq. (1.8)–(1.9): pastings equal iff exchange-equivalent.

## The honest keystone bill (I4)

`fxMode_hasArcFaithfulTraceInvariance := true` is a NEW marker on the LITERAL delivery above — the swap-trace
congruence's extract-invariance, at the dispatcher's STATE + KIND granularity.  It is NOT the faithful analogue of
the general-signature `:545` keystone `ArcGodementSamePartitionFresh`: that needs a faithful
`ArcGodementSwapRenameable` — the `∃ sigma, ArcRenameRel …` Mazurkiewicz support/locality witness between the two
general-signature `runArcCellFaithful` run orders — the SAME open combinatorial core that keeps the shipped cup/cap
keystone false.  I1's `natListSwapTwoAt_map` is the crossing's renaming brick for that route, but assembling the
faithful renaming simulation is OUT OF SCOPE (an honest wall).  So the permanent originals stay false:
`fxMode_hasArcPeelGeneralSignature` (the arity ceiling) and `fxMode_hasArcGodementSamePartitionFreshProof` (the
`:545` / #2043 / WP-AMALG residual) are re-pinned `false` by `rfl`; a faithful-engine keystone is a NEW marker, the
originals stay false PERMANENTLY.

Raw Lean 4 + Init; STRUCTURAL induction on the equivalence derivation, no `omega` / `simp`-AC / `WellFounded.fix`.
The inductive has no wildcard match; `symm` / `trans` route through `Eq.symm` / `Eq.trans` (propext-free).
Per-declaration `#assert_no_axioms` AND independent `#print axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The faithful swap trace congruence -/

/-- The reflexive-symmetric-transitive closure of the dispatcher's two-step swap on `ArcWireState`.  The
generating `ofSwap` constructor packages the dispatcher's five admissibility hypotheses as fields, so the closure
is inhabited exactly at admissible swaps.  Signature-free — it relates arc STATES, so a single congruence serves
every signature at the fold-invariance below. -/
inductive FaithfulSwapTraceEquiv (bottomCount : Nat) : ArcWireState → ArcWireState → Prop where
  /-- The generator: one admissible two-step exchange move relates its low-first and high-first runs. -/
  | ofSwap (state : ArcWireState) (lowKind highKind : ArcSwapKind) (gap positionLow : Nat)
      (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
      (nextFreshPos : 0 < state.nextFresh) (boundaryBelowFresh : bottomCount ≤ state.nextFresh)
      (window : swapWindowFits lowKind highKind gap positionLow state.openWires.length) :
      FaithfulSwapTraceEquiv bottomCount
        (redexTwoStep lowKind highKind state gap positionLow)
        (reductTwoStep lowKind highKind state gap positionLow)
  /-- Reflexivity. -/
  | refl (state : ArcWireState) : FaithfulSwapTraceEquiv bottomCount state state
  /-- Symmetry. -/
  | symm {stateLeft stateRight : ArcWireState} :
      FaithfulSwapTraceEquiv bottomCount stateLeft stateRight →
      FaithfulSwapTraceEquiv bottomCount stateRight stateLeft
  /-- Transitivity. -/
  | trans {stateLeft stateMid stateRight : ArcWireState} :
      FaithfulSwapTraceEquiv bottomCount stateLeft stateMid →
      FaithfulSwapTraceEquiv bottomCount stateMid stateRight →
      FaithfulSwapTraceEquiv bottomCount stateLeft stateRight

/-! ## The trace-invariance: `extractArc` is constant along the congruence -/

/-- ★ **THE FAITHFUL SWAP TRACE-INVARIANCE.**  States related by `FaithfulSwapTraceEquiv` have EQUAL
`extractArc`-after-`rest`, for any `signature`, boundary indices and continuation `rest`.  Structural induction on
the equivalence derivation: the `ofSwap` arm fires the r13 dispatcher `arcFaithfulSwapExtractRestCommute` verbatim
(its packaged fields ARE the dispatcher's five hypotheses); `refl` is `rfl`; `symm` / `trans` are `Eq.symm` /
`Eq.trans`.  This is the induced evaluation morphism of the trace monoid's universal property — equal traces ⇒
equal image. -/
theorem extractArc_eq_of_faithfulSwapTraceEquiv {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) {stateLeft stateRight : ArcWireState}
    (equiv : FaithfulSwapTraceEquiv bottomCount stateLeft stateRight)
    (rest : List (SpineAtom signature sourceMode targetMode)) :
    extractArc bottomCount (processArcSpine stateLeft rest)
      = extractArc bottomCount (processArcSpine stateRight rest) := by
  induction equiv with
  | ofSwap state lowKind highKind gap positionLow fresh forest nextFreshPos boundaryBelowFresh window =>
      exact arcFaithfulSwapExtractRestCommute bottomCount state lowKind highKind gap positionLow
        fresh forest nextFreshPos boundaryBelowFresh window rest
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ leftHypothesis rightHypothesis => exact leftHypothesis.trans rightHypothesis

/-! ## Non-vacuity — the congruence is inhabited on a MIXED crossing-involving swap, and the invariance fires -/

/-- ★ **The congruence is non-vacuously inhabited by a MIXED crossing generator.**  On the width-6 fresh initial
seed the (cup LOW, cross HIGH) two-step exchange move (`gap = 2`, `positionLow = 1`, window `2 + 1 + 2 ≤ 6`) is an
admissible `ofSwap` — a genuine crossing-involving arm, machine-confirmed equal on both run orders by the r14
truth-probe.  Built from `arcStateFresh_initial` / `isUnionFindForest_nil` / the concrete bounds, not a hand
fixture. -/
theorem faithfulSwapTraceEquiv_mixedSeed_confirms :
    FaithfulSwapTraceEquiv 6
      (redexTwoStep ArcSwapKind.cup ArcSwapKind.cross (ArcWireState.mk (List.range 6) [] 6 0 [] []) 2 1)
      (reductTwoStep ArcSwapKind.cup ArcSwapKind.cross (ArcWireState.mk (List.range 6) [] 6 0 [] []) 2 1) :=
  FaithfulSwapTraceEquiv.ofSwap (ArcWireState.mk (List.range 6) [] 6 0 [] [])
    ArcSwapKind.cup ArcSwapKind.cross 2 1
    (arcStateFresh_initial 6) isUnionFindForest_nil (by decide) (Nat.le_refl 6)
    (by show (2 : Nat) + 1 + 2 ≤ (List.range 6).length; decide)

/-- ★ **The trace-invariance fires on the mixed seed (parameterized over the continuation `rest`).**  Feeding
`faithfulSwapTraceEquiv_mixedSeed_confirms` into `extractArc_eq_of_faithfulSwapTraceEquiv`: the two run orders of
the (cup, cross) exchange yield EQUAL extract-after-`rest` for every `signature` and `rest`.  A real instance of
the trace-invariance on a crossing-involving arm. -/
theorem extractArc_eq_of_faithfulSwapTraceEquiv_mixedSeed_confirms {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (rest : List (SpineAtom signature sourceMode targetMode)) :
    extractArc 6 (processArcSpine
        (redexTwoStep ArcSwapKind.cup ArcSwapKind.cross (ArcWireState.mk (List.range 6) [] 6 0 [] []) 2 1) rest)
      = extractArc 6 (processArcSpine
          (reductTwoStep ArcSwapKind.cup ArcSwapKind.cross (ArcWireState.mk (List.range 6) [] 6 0 [] []) 2 1) rest) :=
  extractArc_eq_of_faithfulSwapTraceEquiv 6 faithfulSwapTraceEquiv_mixedSeed_confirms rest

/-! ## Honesty marker (I4) + the permanent keystone pins -/

/-- **Honesty marker (I4) — the FAITHFUL swap TRACE-INVARIANCE is delivered.**  `FaithfulSwapTraceEquiv` is the
reflexive-symmetric-transitive closure of the r13 dispatcher's admissible two-step exchange move, and
`extractArc_eq_of_faithfulSwapTraceEquiv` proves the extract-after-`rest` is INVARIANT along it, by structural
induction on the equivalence derivation firing `arcFaithfulSwapExtractRestCommute` verbatim in the `ofSwap` arm.
This is the induced evaluation morphism of the trace (free partially commutative) monoid's universal property
(Cartier–Foata / Mazurkiewicz; the interchange/Godement reading is Mimram 2014 eq. 1.8–1.9).  Non-vacuous on a
MIXED crossing-involving arm (`faithfulSwapTraceEquiv_mixedSeed_confirms` /
`extractArc_eq_of_faithfulSwapTraceEquiv_mixedSeed_confirms`).  This is a NEW marker on the literal delivery — it
does NOT flip the general-signature `:545` keystone (see the pins).  The shipped step / extract engines and the
dispatcher are never edited.  `= true`. -/
def fxMode_hasArcFaithfulTraceInvariance : Bool := true

/-- **Honesty pin — the r13 dispatcher stays `true`** (the `ofSwap` arm's sole provider).  `rfl`. -/
theorem arcFaithfulTraceInvariance_dispatcher_stays_true :
    fxMode_hasArcFaithfulSwapDispatcher = true := rfl

/-- **Honesty pin — the general-signature peel stays the open keystone.**  The trace-invariance lives at the
dispatcher's STATE + KIND granularity; it does NOT build the general-signature faithful peel.
`fxMode_hasArcPeelGeneralSignature` stays `false`.  `rfl`. -/
theorem arcFaithfulTraceInvariance_generalSignature_stays_false :
    fxMode_hasArcPeelGeneralSignature = false := rfl

/-- **Honesty pin — the `:545` / #2043 / WP-AMALG fresh-partition keystone stays false PERMANENTLY.**  The
faithful analogue of `ArcGodementSamePartitionFresh` needs a faithful `ArcGodementSwapRenameable` (the
Mazurkiewicz renaming simulation between the two general-signature run orders) — the SAME open combinatorial core
that keeps the shipped keystone false; the trace-invariance does not advance it.
`fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.  `rfl`. -/
theorem arcFaithfulTraceInvariance_samePartitionFreshProof_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
