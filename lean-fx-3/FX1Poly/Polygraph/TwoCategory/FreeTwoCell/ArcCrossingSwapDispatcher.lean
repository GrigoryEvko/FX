import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingHeteroBlockCommute
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapCorePackage

/-! # MODE-COMMUTE r13 — the NINE-PAIR faithful swap DISPATCHER (assembled)

`ArcSwapCorePackage` (WalkingAdjunction) delivered the FOUR cup/cap × cup/cap two-step swap cores as peel-ready
packages (`arcSwapCorePackage_cupCup` / `_cupCap` / `_capCup` / `_capCap`) plus the `rest`-spine consumer
`extractArc_eq_rest_of_swapCorePackage`.  `ArcCrossingDisjointBlockCommute` (r10) delivered the homogeneous
crossing × crossing disjoint commute (`stepCrossArc_disjointCommute`) and `ArcCrossingHeteroBlockCommute` (r12)
the FOUR heterogeneous crossing × cup/cap state commutes (`stepCrossArc_stepCupArc_heteroCommute` and siblings).
Between them the three provider families cover ALL NINE arity pairs of the faithful step's three arms
(`stepCupArc` = `0⇒2`, `stepCapArc` = `2⇒0`, `stepCrossArc` = `2⇒2`), but under THREE different interfaces.  This
file ASSEMBLES them into ONE dispatcher over a single kind-indexed entry point.

## The offset convention (grounded in Delpeuch–Vicary)

The low/high two-step spelling is the printed **exchange move** of Delpeuch & Vicary, *Normalization for planar
string diagrams* (LMCS 18(1:10) 2022), Def. 13–14: passing a generator of net wire-change `Δ = O − I` past an
adjacent disjoint-window generator shifts the passed window by `Δ`.  Cup has `Δ = +2`, cap `Δ = −2`, crossing
`Δ = 0`.  The `redexHighPosition` / `reductHighPosition` functions below encode exactly this — the high window sits
at `gap + 2 + positionLow` except where the low op is a cap (`gap + positionLow`), the `−2` shift.  In the
polygraph frame this is the interchange / Godement law for disjoint 2-cells (Mimram, *Towards 3-Dimensional
Rewriting Theory*, LMCS, eqns 1.8–1.9); the `rest`-threaded corollary is the single-adjacent-independent-swap
generator of the Mazurkiewicz trace congruence (Earnshaw, *String Diagrammatic Trace Theory*, MFCS 2023, Lem
4.11 / Def 4.2).  The per-combo `swapWindowFits` hypothesis is Def. 13 admissibility (disjoint windows), and the
whole-extract equality is Lemma 15 (the exchange preserves the diagram).

## What is assembled

  * `ArcSwapKind` — the three faithful-step arities (`cup` / `cap` / `cross`).
  * `redexTwoStep` / `reductTwoStep` — the low-first / high-first two-step run at kind `(lowKind, highKind)`,
    with the high window offset by `redexHighPosition` / `reductHighPosition` (the `Δ` shift above).
  * `swapWindowFits` — the per-combo disjoint-window admissibility bound (nine arms, full enumeration).
  * The FIVE cross-involving `rest`-corollaries (`extractArc_eq_rest_of_cupCrossSwap` and siblings) — the missing
    `ofSwap` providers that put the five crossing combos into the SAME `extractArc _ (processArcSpine _ rest) = …`
    shape the four cup/cap combos already have via `extractArc_eq_rest_of_swapCorePackage`.  Each is one
    `congrArg` off the r10 / r12 state equality.
  * ★ `arcFaithfulSwapExtractRestCommute` — THE DISPATCHER: casing on the two kinds, all NINE arity pairs land
    equal `rest`-spine extracts under ONE uniform seed (state freshness, forest, `0 < nextFresh`, boundary bound)
    and the combo's window bound.  The cup/cap arms route through the sigma-renaming packages; the five
    crossing arms route through the `congrArg` corollaries (redex = reduct literally, no package, no sigma).

## What this file does NOT do (the permanent pins stay false)

It does NOT flip the general-signature keystone `fxMode_hasArcPeelGeneralSignature` (the arity ceiling): the
dispatcher lives at the STATE + KIND level, it does not build a general-signature `stepArcAtomFaithful` peel.  It
does NOT touch the #2043 / WP-AMALG fresh-partition residual `fxMode_hasArcGodementSamePartitionFreshProof`
(orthogonal — the Mazurkiewicz renaming witness).  The shipped `stepArcAtom` / `stepCupArc` / `stepCapArc` /
`stepCrossArc` / `extractArc` and every provider theorem are never edited.  This certificate is strictly ADDITIVE.

Raw Lean 4 + Init; structural `cases`, no `omega` / `simp`-AC / `WellFounded.fix`.  The kind matches are full
enumerations (no wildcard arm — a wildcard leaks `propext`).  Per-declaration `#assert_no_axioms` AND an
independent `#print axioms` are gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The three faithful-step arities and the kind-indexed two-step runs -/

/-- The three arities of the faithful step: a cup (`0⇒2`), a cap (`2⇒0`), or a crossing (`2⇒2`). -/
inductive ArcSwapKind where
  | cup
  | cap
  | cross

/-- Fire one faithful step of the given arity at `position` — the dispatch over the three step functions. -/
def stepArcOfKind (kind : ArcSwapKind) (state : ArcWireState) (position : Nat) : ArcWireState :=
  match kind with
  | ArcSwapKind.cup => stepCupArc state position
  | ArcSwapKind.cap => stepCapArc state position
  | ArcSwapKind.cross => stepCrossArc state position

/-- The high window's position in the LOW-FIRST run: `gap + 2 + positionLow`, except a low cap shifts it DOWN by
its removed pair to `gap + positionLow` (the Delpeuch–Vicary `Δ = O − I` offset; cap has `Δ = −2`). -/
def redexHighPosition (lowKind : ArcSwapKind) (gap positionLow : Nat) : Nat :=
  match lowKind with
  | ArcSwapKind.cup => gap + 2 + positionLow
  | ArcSwapKind.cap => gap + positionLow
  | ArcSwapKind.cross => gap + 2 + positionLow

/-- The high window's position in the HIGH-FIRST run: `gap + positionLow` for a low cup (the cup's `+2` has not
yet fired), `gap + 2 + positionLow` for a low cap or crossing. -/
def reductHighPosition (lowKind : ArcSwapKind) (gap positionLow : Nat) : Nat :=
  match lowKind with
  | ArcSwapKind.cup => gap + positionLow
  | ArcSwapKind.cap => gap + 2 + positionLow
  | ArcSwapKind.cross => gap + 2 + positionLow

/-- The LOW-FIRST two-step run: fire the low op at `positionLow`, then the high op at the redex high window. -/
def redexTwoStep (lowKind highKind : ArcSwapKind) (state : ArcWireState) (gap positionLow : Nat) : ArcWireState :=
  stepArcOfKind highKind (stepArcOfKind lowKind state positionLow) (redexHighPosition lowKind gap positionLow)

/-- The HIGH-FIRST two-step run: fire the high op at the reduct high window, then the low op at `positionLow`. -/
def reductTwoStep (lowKind highKind : ArcSwapKind) (state : ArcWireState) (gap positionLow : Nat) : ArcWireState :=
  stepArcOfKind lowKind (stepArcOfKind highKind state (reductHighPosition lowKind gap positionLow)) positionLow

/-- The per-combo disjoint-window admissibility bound (Delpeuch–Vicary Def. 13).  Nine arms, full enumeration of
the kind pairs — each is the exact window hypothesis the corresponding provider consumes. -/
def swapWindowFits : ArcSwapKind → ArcSwapKind → Nat → Nat → Nat → Prop
  | ArcSwapKind.cup, ArcSwapKind.cup, gap, positionLow, scanLength => gap + positionLow ≤ scanLength
  | ArcSwapKind.cup, ArcSwapKind.cap, gap, positionLow, scanLength => gap + positionLow + 2 ≤ scanLength
  | ArcSwapKind.cup, ArcSwapKind.cross, gap, positionLow, scanLength => gap + positionLow + 2 ≤ scanLength
  | ArcSwapKind.cap, ArcSwapKind.cup, gap, positionLow, scanLength => gap + positionLow + 2 ≤ scanLength
  | ArcSwapKind.cap, ArcSwapKind.cap, _gap, positionLow, scanLength => positionLow + 2 ≤ scanLength
  | ArcSwapKind.cap, ArcSwapKind.cross, gap, positionLow, scanLength => gap + 2 + positionLow + 1 < scanLength
  | ArcSwapKind.cross, ArcSwapKind.cup, _gap, positionLow, scanLength => positionLow + 2 ≤ scanLength
  | ArcSwapKind.cross, ArcSwapKind.cap, _gap, positionLow, scanLength => positionLow + 1 < scanLength
  | ArcSwapKind.cross, ArcSwapKind.cross, gap, positionLow, scanLength => gap + 2 + positionLow + 1 < scanLength

/-! ## The crossing-window arithmetic bridge and the five cross-involving `rest`-corollaries -/

/-- The r10 pivot→gap bridge: the low crossing window sits disjointly below the shifted high window
(`positionLow + 2 ≤ gap + 2 + positionLow`), so `stepCrossArc_disjointCommute` instantiates at pivots
`positionLow` and `gap + 2 + positionLow`.  One `Nat` inequality; no `omega`. -/
private theorem lowShiftDisjoint (positionLow gap : Nat) : positionLow + 2 ≤ gap + 2 + positionLow := by
  rw [Nat.add_right_comm gap 2 positionLow]
  exact Nat.add_le_add_right (Nat.le_add_left positionLow gap) 2

/-- ★ **cup LOW / cross HIGH — `rest`-corollary.**  The r12 `stepCrossArc_stepCupArc_heteroCommute` state
equality carried through a common `rest` by `congrArg`. -/
theorem extractArc_eq_rest_of_cupCrossSwap {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (state : ArcWireState) (positionLow gap : Nat)
    (window : gap + positionLow + 2 ≤ state.openWires.length)
    (rest : List (SpineAtom signature sourceMode targetMode)) :
    extractArc bottomCount (processArcSpine
        (stepCrossArc (stepCupArc state positionLow) (gap + 2 + positionLow)) rest)
      = extractArc bottomCount (processArcSpine
        (stepCupArc (stepCrossArc state (gap + positionLow)) positionLow) rest) :=
  congrArg (fun scanState => extractArc bottomCount (processArcSpine scanState rest))
    (stepCrossArc_stepCupArc_heteroCommute state positionLow gap window)

/-- ★ **cross LOW / cup HIGH — `rest`-corollary** (no shift; a crossing preserves width). -/
theorem extractArc_eq_rest_of_crossCupSwap {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (state : ArcWireState) (positionLow gap : Nat)
    (window : positionLow + 2 ≤ state.openWires.length)
    (rest : List (SpineAtom signature sourceMode targetMode)) :
    extractArc bottomCount (processArcSpine
        (stepCupArc (stepCrossArc state positionLow) (gap + 2 + positionLow)) rest)
      = extractArc bottomCount (processArcSpine
        (stepCrossArc (stepCupArc state (gap + 2 + positionLow)) positionLow) rest) :=
  congrArg (fun scanState => extractArc bottomCount (processArcSpine scanState rest))
    (stepCupArc_stepCrossArc_heteroCommute state positionLow gap window)

/-- ★ **cap LOW / cross HIGH — `rest`-corollary** (the `−2` offset). -/
theorem extractArc_eq_rest_of_capCrossSwap {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (state : ArcWireState) (positionLow gap : Nat)
    (window : gap + 2 + positionLow + 1 < state.openWires.length)
    (rest : List (SpineAtom signature sourceMode targetMode)) :
    extractArc bottomCount (processArcSpine
        (stepCrossArc (stepCapArc state positionLow) (gap + positionLow)) rest)
      = extractArc bottomCount (processArcSpine
        (stepCapArc (stepCrossArc state (gap + 2 + positionLow)) positionLow) rest) :=
  congrArg (fun scanState => extractArc bottomCount (processArcSpine scanState rest))
    (stepCrossArc_stepCapArc_heteroCommute state positionLow gap window)

/-- ★ **cross LOW / cap HIGH — `rest`-corollary** (no shift). -/
theorem extractArc_eq_rest_of_crossCapSwap {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (state : ArcWireState) (positionLow gap : Nat)
    (window : positionLow + 1 < state.openWires.length)
    (rest : List (SpineAtom signature sourceMode targetMode)) :
    extractArc bottomCount (processArcSpine
        (stepCapArc (stepCrossArc state positionLow) (gap + 2 + positionLow)) rest)
      = extractArc bottomCount (processArcSpine
        (stepCrossArc (stepCapArc state (gap + 2 + positionLow)) positionLow) rest) :=
  congrArg (fun scanState => extractArc bottomCount (processArcSpine scanState rest))
    (stepCapArc_stepCrossArc_heteroCommute state positionLow gap window)

/-- ★ **cross LOW / cross HIGH — `rest`-corollary.**  The r10 homogeneous disjoint commute instantiated at pivots
`positionLow` and `gap + 2 + positionLow` (disjoint by `lowShiftDisjoint`), carried through `rest`. -/
theorem extractArc_eq_rest_of_crossCrossSwap {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (state : ArcWireState) (positionLow gap : Nat)
    (window : gap + 2 + positionLow + 1 < state.openWires.length)
    (rest : List (SpineAtom signature sourceMode targetMode)) :
    extractArc bottomCount (processArcSpine
        (stepCrossArc (stepCrossArc state positionLow) (gap + 2 + positionLow)) rest)
      = extractArc bottomCount (processArcSpine
        (stepCrossArc (stepCrossArc state (gap + 2 + positionLow)) positionLow) rest) :=
  congrArg (fun scanState => extractArc bottomCount (processArcSpine scanState rest))
    (stepCrossArc_disjointCommute state positionLow (gap + 2 + positionLow)
      (lowShiftDisjoint positionLow gap) window)

/-! ## THE DISPATCHER — all nine arity pairs, one entry point -/

/-- ★ **THE NINE-PAIR FAITHFUL SWAP DISPATCHER.**  For EVERY pair of faithful-step arities `(lowKind, highKind)`,
the low-first two-step run and the high-first two-step run (offset per Delpeuch–Vicary) land equal `rest`-spine
extracts, under one uniform seed (freshness, forest, `0 < nextFresh`, the boundary bound) and the combo's
disjoint-window bound `swapWindowFits`.  Casing on the two kinds routes each of the four cup/cap arms through the
sigma-renaming package + `extractArc_eq_rest_of_swapCorePackage`, and each of the five crossing arms through its
`congrArg` `rest`-corollary (where redex = reduct literally — no package, no event renaming). -/
theorem arcFaithfulSwapExtractRestCommute {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount : Nat) (state : ArcWireState)
    (lowKind highKind : ArcSwapKind) (gap positionLow : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nextFreshPos : 0 < state.nextFresh) (boundaryBelowFresh : bottomCount ≤ state.nextFresh)
    (window : swapWindowFits lowKind highKind gap positionLow state.openWires.length)
    (rest : List (SpineAtom signature sourceMode targetMode)) :
    extractArc bottomCount (processArcSpine (redexTwoStep lowKind highKind state gap positionLow) rest)
      = extractArc bottomCount (processArcSpine (reductTwoStep lowKind highKind state gap positionLow) rest) := by
  cases lowKind with
  | cup =>
    cases highKind with
    | cup =>
      dsimp only [redexTwoStep, reductTwoStep, stepArcOfKind, redexHighPosition, reductHighPosition]
      exact extractArc_eq_rest_of_swapCorePackage bottomCount _ _
        (arcSwapCorePackage_cupCup state fresh forest nextFreshPos bottomCount boundaryBelowFresh
          gap positionLow window) rest
    | cap =>
      dsimp only [redexTwoStep, reductTwoStep, stepArcOfKind, redexHighPosition, reductHighPosition]
      exact extractArc_eq_rest_of_swapCorePackage bottomCount _ _
        (arcSwapCorePackage_cupCap state fresh forest nextFreshPos bottomCount boundaryBelowFresh
          gap positionLow window) rest
    | cross =>
      dsimp only [redexTwoStep, reductTwoStep, stepArcOfKind, redexHighPosition, reductHighPosition]
      exact extractArc_eq_rest_of_cupCrossSwap bottomCount state positionLow gap window rest
  | cap =>
    cases highKind with
    | cup =>
      dsimp only [redexTwoStep, reductTwoStep, stepArcOfKind, redexHighPosition, reductHighPosition]
      exact extractArc_eq_rest_of_swapCorePackage bottomCount _ _
        (arcSwapCorePackage_capCup state fresh forest nextFreshPos bottomCount boundaryBelowFresh
          gap positionLow window) rest
    | cap =>
      dsimp only [redexTwoStep, reductTwoStep, stepArcOfKind, redexHighPosition, reductHighPosition]
      exact extractArc_eq_rest_of_swapCorePackage bottomCount _ _
        (arcSwapCorePackage_capCap state fresh forest nextFreshPos bottomCount boundaryBelowFresh
          gap positionLow window) rest
    | cross =>
      dsimp only [redexTwoStep, reductTwoStep, stepArcOfKind, redexHighPosition, reductHighPosition]
      exact extractArc_eq_rest_of_capCrossSwap bottomCount state positionLow gap window rest
  | cross =>
    cases highKind with
    | cup =>
      dsimp only [redexTwoStep, reductTwoStep, stepArcOfKind, redexHighPosition, reductHighPosition]
      exact extractArc_eq_rest_of_crossCupSwap bottomCount state positionLow gap window rest
    | cap =>
      dsimp only [redexTwoStep, reductTwoStep, stepArcOfKind, redexHighPosition, reductHighPosition]
      exact extractArc_eq_rest_of_crossCapSwap bottomCount state positionLow gap window rest
    | cross =>
      dsimp only [redexTwoStep, reductTwoStep, stepArcOfKind, redexHighPosition, reductHighPosition]
      exact extractArc_eq_rest_of_crossCrossSwap bottomCount state positionLow gap window rest

/-! ## Non-vacuity — the dispatcher fires at the reachable initial seed -/

/-- ★ **Non-vacuous (cup/cap route): the dispatcher fires for the cup × cup combo at every fresh initial seed.**
The initial state `mk (range bottomCount) [] bottomCount 0 [] []` witnesses freshness (`arcStateFresh_initial`),
forest (`isUnionFindForest_nil`), and — for `0 < bottomCount` — the `nextFresh` and boundary bounds
simultaneously, so the sigma-renaming package route is genuinely reachable. -/
theorem arcFaithfulSwapDispatcher_cupCupSeed_confirms {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount gap positionLow : Nat) (nextFreshPos : 0 < bottomCount)
    (window : gap + positionLow ≤ (List.range bottomCount).length)
    (rest : List (SpineAtom signature sourceMode targetMode)) :
    extractArc bottomCount (processArcSpine (redexTwoStep ArcSwapKind.cup ArcSwapKind.cup
        (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) gap positionLow) rest)
      = extractArc bottomCount (processArcSpine (reductTwoStep ArcSwapKind.cup ArcSwapKind.cup
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) gap positionLow) rest) :=
  arcFaithfulSwapExtractRestCommute bottomCount
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
    ArcSwapKind.cup ArcSwapKind.cup gap positionLow
    (arcStateFresh_initial bottomCount) isUnionFindForest_nil nextFreshPos (Nat.le_refl bottomCount)
    window rest

/-- ★ **Non-vacuous (crossing route): the dispatcher fires for the cross × cross combo at every fresh initial
seed with an in-range disjoint window.**  The `congrArg` route (redex = reduct literally) is reachable. -/
theorem arcFaithfulSwapDispatcher_crossCrossSeed_confirms {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (bottomCount gap positionLow : Nat) (nextFreshPos : 0 < bottomCount)
    (window : gap + 2 + positionLow + 1 < (List.range bottomCount).length)
    (rest : List (SpineAtom signature sourceMode targetMode)) :
    extractArc bottomCount (processArcSpine (redexTwoStep ArcSwapKind.cross ArcSwapKind.cross
        (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) gap positionLow) rest)
      = extractArc bottomCount (processArcSpine (reductTwoStep ArcSwapKind.cross ArcSwapKind.cross
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) gap positionLow) rest) :=
  arcFaithfulSwapExtractRestCommute bottomCount
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
    ArcSwapKind.cross ArcSwapKind.cross gap positionLow
    (arcStateFresh_initial bottomCount) isUnionFindForest_nil nextFreshPos (Nat.le_refl bottomCount)
    window rest

/-! ## Honesty marker + pins -/

/-- **Honesty marker — the NINE-PAIR faithful swap dispatcher is ASSEMBLED.**  `arcFaithfulSwapExtractRestCommute`
routes ALL NINE arity pairs of the faithful step's three arms (cup / cap / cross) to equal `rest`-spine extracts:
the four cup/cap combos through the sigma-renaming `ArcSwapCorePackage` + `extractArc_eq_rest_of_swapCorePackage`,
the five crossing combos through the five `congrArg` `rest`-corollaries off the r10 / r12 state equalities
(redex = reduct literally).  The low/high offset is the Delpeuch–Vicary exchange move (`Δ`-shift), the per-combo
`swapWindowFits` bound is its disjoint-window admissibility, and the whole-extract equality is its
diagram-preservation.  Non-vacuous at the reachable initial seed on both routes
(`arcFaithfulSwapDispatcher_cupCupSeed_confirms` / `_crossCrossSeed_confirms`).  What this marker does NOT claim:
a general-signature `stepArcAtomFaithful` peel (the arity ceiling stays open) and the fresh-partition keystone
(orthogonal).  The shipped step / extract engines and every provider theorem are never edited.  `= true`. -/
def fxMode_hasArcFaithfulSwapDispatcher : Bool := true

/-- **Honesty pin — the general-signature peel stays the open keystone.**  The dispatcher lives at the STATE +
KIND level; it does not build a general-signature faithful peel.  `fxMode_hasArcPeelGeneralSignature` stays
`false`.  `rfl`. -/
theorem arcFaithfulSwapDispatcher_generalSignature_stays_false :
    fxMode_hasArcPeelGeneralSignature = false := rfl

/-- **Honesty pin — the #2043 / WP-AMALG fresh-partition keystone is untouched** (the Mazurkiewicz renaming
witness, orthogonal to the crossing/offset content).  `fxMode_hasArcGodementSamePartitionFreshProof` stays
`false`.  `rfl`. -/
theorem arcFaithfulSwapDispatcher_samePartitionFreshProof_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

/-- **Honesty pin — the r12 heterogeneous crossing × cup/cap commutes stay `true`** (the five crossing arms'
providers).  `rfl`. -/
theorem arcFaithfulSwapDispatcher_heteroBlockCommute_stays_true :
    fxMode_hasArcCrossingHeteroBlockCommute = true := rfl

/-- **Honesty pin — the r10 crossing × crossing disjoint commute stays `true`** (the cross × cross arm's
provider).  `rfl`. -/
theorem arcFaithfulSwapDispatcher_disjointBlockCommute_stays_true :
    fxMode_hasArcCrossingDisjointBlockCommute = true := rfl

/-- **Honesty pin — the four cup/cap swap-core packages stay `true`** (the four cup/cap arms' providers).
`rfl`. -/
theorem arcFaithfulSwapDispatcher_swapCorePackage_stays_true :
    fxMode_hasArcSwapCorePackage = true := rfl

end FX1Poly.Polygraph
