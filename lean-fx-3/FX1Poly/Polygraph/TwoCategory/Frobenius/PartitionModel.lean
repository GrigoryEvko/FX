import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDesc

/-! # WP-FROB r1 (FROB-2) — the special-commutative-Frobenius spider PARTITION engine

The ADJPOLY dichotomy (`#2212`) splits adjunction polygraphs into an ACYCLIC family (loop-free — the Fong–Cong
engine) and a CYCLIC family (Frobenius / ambijunction — circles close).  The Frobenius spider is the canonical
cyclic instance; this file builds its decision substrate.

## The mathematics, pinned

The PROP for **special commutative Frobenius monoids** is `Cospan(FinSet)` (Lack, *Composing PROPs*, TAC 13 (2004);
Rosebrugh–Sabadini–Walters): a hom `m ⇒ n` is a **cospan** of finite sets, whose invariant is a **partition of the
`m + n` boundary ports** together with a **count of the closed / isolated components** (cospan-middle elements hit by
nothing).  The **extraspecial** quotient (Coya–Fong, *Corelations are the prop for extraspecial commutative Frobenius
monoids*, arXiv:1601.02307) adds the **bone / extra law** `ε ∘ η = id` and passes to **corelations** — the partition
ALONE, the closed-component counter discarded.

The one variance the literature corrects in the r1 brief: the **special law** `μ ∘ δ = id` kills only *multiplicity*
(parallel edges / the μ-after-δ bubble), it does **NOT** kill the isolated-component counter.  Coya–Fong §3.1:
"the special law shows that having multiple connections between points is irrelevant, and the extra law shows that
'extra' components not connected to the domain or codomain are irrelevant."  So the closed-component counter stays
**LIVE** for the special (Cospan) walker; it is dropped only for the extraspecial (corelation) walker.  This file
realizes exactly that: the FULL `SpiderDiagramType` (partition + closed count) is the special invariant, and
`forgetSpiderClosed` projects to the partition-only extraspecial invariant.

## The engine, reused from Brauer verbatim

The spider engine IS Brauer's `stepWiring` / `processBrauer` fold (`Brauer/WiringDesc.lean`) — no new step machinery.
Matchings pair ports (every Brauer class has size exactly 2); spiders MERGE classes of arbitrary size (mult / comult
have 3 ports, unit / counit have 1), but the union-find fold handles that natively: a generator's `WiringDesc` arc
list simply unions all of its merging ports into one class.  On a same-component arc Brauer's fold takes the loop
branch (leaving `links` UNCHANGED, `loops + 1`) whereas an always-union fold is a no-op on the same root (also
leaving `links` unchanged) — so the final union-find `links` is **bit-identical** either way; only Brauer's `loops`
field differs.  We therefore **ignore `state.loops`** and recompute the closed-component count freshly from `links`
at the end (`extractSpiderDiagram`): a component with NO boundary node is an isolated closed component (the
Cospan-apex count), a same-class merge (the special μ-after-δ bubble) leaves a component still touching boundary and
is NOT counted.  This is precisely why `loops` must be dropped: keeping it would wrongly identify the special bubble
with an isolated circle.

## The delta vs Brauer, as a partition

Brauer's `DiagramType.partner` is a degree-2 PARTNER matching — it cannot express a size-1 block (unit / counit) or a
size-≥3 block (mult / comult).  So the spider carrier is a genuine **set partition** stored as least-index block
labels (`SpiderDiagramType.blockLabels`): `blockLabels.get k` is the smallest boundary index in `k`'s union-find
class.  This is a canonical normal form for partitions of arbitrary block size, so `SpiderDiagramType` derives
`DecidableEq` and diagram equality is `rfl` / `decide`.

## Honest ledger — the non-special (2Cob) variant is OUT OF SCOPE r1

The PROP for PLAIN commutative Frobenius algebras is `2Cob` (Abrams 1996): its invariant is partition **plus a genus
per connected block**.  The special law is exactly what collapses the genus, dropping `2Cob` to `Cospan(FinSet)`.  The
genus-per-block refinement is deliberately NOT built here (`fxFrob_has2CobGenus = false`); it is ledgered as future
work, no code.

Raw Lean 4 + Init; reuses the shipped `WiringDesc` / `WireState` / union-find primitives verbatim.  Structural
recursion (fuel = list length in the union-find), no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The spider carrier — a boundary partition + a closed-component count -/

/-- ★ The **topological type of a special-commutative-Frobenius spider diagram**: the boundary port counts split
into bottom (source) and top (target), the boundary **partition** as canonical least-index block labels
(`blockLabels.get k` is the smallest boundary index sharing `k`'s union-find class), and the count of **closed /
isolated components** (Cospan apex elements touching no boundary).  A flat datum of `Nat` / `List Nat`, so its
equality is decidable and COMPUTES.  This is the FULL special (`Cospan(FinSet)`) invariant. -/
structure SpiderDiagramType where
  /-- The number of bottom-boundary ports (the source word's length). -/
  bottomCount : Nat
  /-- The number of top-boundary ports (the target word's length). -/
  topCount : Nat
  /-- The canonical partition of the `bottomCount + topCount` boundary ports, as least-index block labels. -/
  blockLabels : List Nat
  /-- The number of closed / isolated components (Cospan-apex elements touching no boundary). -/
  closedComponents : Nat
deriving DecidableEq

/-- ★ The **extraspecial (corelation) invariant** — the boundary partition ALONE, the closed-component counter
discarded (the bone / extra law `ε ∘ η = id`).  The partition-only projection of `SpiderDiagramType`. -/
structure SpiderPartitionType where
  /-- The number of bottom-boundary ports. -/
  bottomCount : Nat
  /-- The number of top-boundary ports. -/
  topCount : Nat
  /-- The canonical boundary partition as least-index block labels. -/
  blockLabels : List Nat
deriving DecidableEq

/-- Project the full special diagram type down to the extraspecial partition-only invariant (forget the
closed-component count — the bone law). -/
def forgetSpiderClosed (diagram : SpiderDiagramType) : SpiderPartitionType :=
  { bottomCount := diagram.bottomCount, topCount := diagram.topCount, blockLabels := diagram.blockLabels }

/-! ## The per-generator spider wirings

Each generator's `WiringDesc` (Brauer's datum) merges all of its ports into one class.  Endpoint tags:
`0 … inputCount-1` are the consumed input ports, `inputCount …` the produced output ports.  Every `internalLoops`
is `0` — a circle is an emergent composite (unit-then-counit), never a single generator's bubble. -/

/-- The **multiplication** `μ : 2 ⇒ 1` — inputs `0`, `1` and output `0` all merge into one class. -/
def multWiring : WiringDesc := { inputCount := 2, outputCount := 1, arcs := [(0, 2), (1, 2)], internalLoops := 0 }

/-- The **comultiplication** `δ : 1 ⇒ 2` — input `0` and outputs `0`, `1` all merge into one class. -/
def comultWiring : WiringDesc := { inputCount := 1, outputCount := 2, arcs := [(0, 1), (0, 2)], internalLoops := 0 }

/-- The **unit** `η : 0 ⇒ 1` — produces one fresh boundary port, no arcs (a singleton class until something merges
it). -/
def unitWiring : WiringDesc := { inputCount := 0, outputCount := 1, arcs := [], internalLoops := 0 }

/-- The **counit** `ε : 1 ⇒ 0` — consumes one port, no arcs (its class becomes an isolated closed component exactly
when it touches no boundary — the bone circle). -/
def counitWiring : WiringDesc := { inputCount := 1, outputCount := 0, arcs := [], internalLoops := 0 }

/-- A multiplication atom at `position`. -/
def multAt (position : Nat) : BrauerAtom := { position := position, wiring := multWiring }

/-- A comultiplication atom at `position`. -/
def comultAt (position : Nat) : BrauerAtom := { position := position, wiring := comultWiring }

/-- A unit atom at `position`. -/
def unitAt (position : Nat) : BrauerAtom := { position := position, wiring := unitWiring }

/-- A counit atom at `position`. -/
def counitAt (position : Nat) : BrauerAtom := { position := position, wiring := counitWiring }

/-! ## Extracting the boundary partition + closed-component count -/

/-- Scan candidate boundary indices for the FIRST whose node shares `targetRoot`'s component — scanning
`0, 1, 2, …` upward yields the least-index representative of the block (the candidate itself always matches its own
root, so a non-empty in-range scan always finds one). -/
def firstIndexWithRoot (links : List (Nat × Nat)) (boundaryNodes : List Nat) (targetRoot : Nat) :
    List Nat → Nat
  | [] => 0
  | candidate :: rest =>
      if unionFindRootOf links (natListGetAt boundaryNodes candidate) == targetRoot then candidate
      else firstIndexWithRoot links boundaryNodes targetRoot rest

/-- Whether any node in the list has union-find root equal to `targetRoot` — the "component touches boundary"
predicate, applied to the boundary-node list. -/
def natListRootEqAny (links : List (Nat × Nat)) (targetRoot : Nat) : List Nat → Bool
  | [] => false
  | node :: rest =>
      if unionFindRootOf links node == targetRoot then true
      else natListRootEqAny links targetRoot rest

/-- Count the union-find components (own-roots) over the given node list that touch NO boundary node — the closed /
isolated component count.  Structural on the node list; call it on `List.range state.nextFresh` so a unit-then-counit
wire that never entered `links` is still seen (its root is itself). -/
def closedComponentCount (links : List (Nat × Nat)) (boundaryNodes : List Nat) : List Nat → Nat
  | [] => 0
  | node :: rest =>
      let isOwnRoot := unionFindRootOf links node == node
      let touchesBoundary := natListRootEqAny links node boundaryNodes
      (if isOwnRoot && not touchesBoundary then 1 else 0)
        + closedComponentCount links boundaryNodes rest

/-- ★ Read the final wire state into a `SpiderDiagramType`: the remaining open wires ARE the top ports (in order),
the bottom ports were node ids `0 … bottomCount-1`, the partition pairs boundary indices by shared component (as
least-index block labels), and the closed-component count scans ALL allocated nodes for own-roots that touch no
boundary.  Reads only `links` / `openWires` / `nextFresh` — `state.loops` is deliberately ignored (see the header:
Brauer's `loops` would wrongly count the special μ-after-δ bubble). -/
def extractSpiderDiagram (bottomCount : Nat) (state : WireState) : SpiderDiagramType :=
  let topWires := state.openWires
  let topCount := topWires.length
  let boundaryNodes := List.range bottomCount ++ topWires
  let total := bottomCount + topCount
  let indices := List.range total
  { bottomCount := bottomCount,
    topCount := topCount,
    blockLabels := indices.map (fun index =>
      firstIndexWithRoot state.links boundaryNodes
        (unionFindRootOf state.links (natListGetAt boundaryNodes index)) indices),
    closedComponents := closedComponentCount state.links boundaryNodes (List.range state.nextFresh) }

/-- ★ The **spider diagram** of a generator word over `bottomCount` bottom wires: run the Brauer wiring engine from
the seed, then read off the boundary partition + closed-component count.  Computes (the smokes are `rfl`). -/
def spiderDiagramOf (bottomCount : Nat) (atoms : List BrauerAtom) : SpiderDiagramType :=
  extractSpiderDiagram bottomCount (processBrauer (brauerSeed bottomCount) atoms)

/-- The **extraspecial (corelation) reading** of a generator word — the partition-only invariant (bone law: the
closed-component count discarded). -/
def extraSpiderDiagramOf (bottomCount : Nat) (atoms : List BrauerAtom) : SpiderPartitionType :=
  forgetSpiderClosed (spiderDiagramOf bottomCount atoms)

/-! ## Engine smokes — the partition engine sees arbitrary-size blocks -/

/-- A multiplication over two strands merges everything into ONE block — `blockLabels = [0, 0, 0]` (b0, b1, t0 all
one class), a size-3 block a degree-2 Brauer matching cannot express. -/
theorem mult_spiderDiagram :
    spiderDiagramOf 2 [multAt 0]
      = { bottomCount := 2, topCount := 1, blockLabels := [0, 0, 0], closedComponents := 0 } := rfl

/-- Contrast: two identity strands stay in SEPARATE blocks — `blockLabels = [0, 1, 0, 1]` (b0↔t0, b1↔t1), distinct
from the merged multiplication. -/
theorem identityPair_spiderDiagram :
    spiderDiagramOf 2 [identityStrandAt 0, identityStrandAt 1]
      = { bottomCount := 2, topCount := 2, blockLabels := [0, 1, 0, 1], closedComponents := 0 } := rfl

/-- The multiplication and the identity pair are DISTINCT spider diagrams (different block structure AND top count) —
non-vacuity of the partition invariant. -/
theorem mult_ne_identityPair :
    spiderDiagramOf 2 [multAt 0] ≠ spiderDiagramOf 2 [identityStrandAt 0, identityStrandAt 1] := by decide

/-- ★ **The closed-component counter FIRES.**  A unit then a counit with no other arc (`η` then `ε`, the bone
circle) produces one isolated component — `closedComponents = 1` — over the empty boundary, whereas the empty word
has `closedComponents = 0`.  This is the Cospan-apex count the special invariant keeps live. -/
theorem bone_closedComponents_one :
    (spiderDiagramOf 0 [unitAt 0, counitAt 0]).closedComponents = 1
      ∧ (spiderDiagramOf 0 ([] : List BrauerAtom)).closedComponents = 0 :=
  ⟨rfl, rfl⟩

/-- ★ **The special μ-after-δ bubble is NOT a closed component.**  `δ` then `μ` on one strand re-merges two ports
already in the same class; the component still touches boundary, so `closedComponents = 0` — distinguishing the
special bubble (uncounted) from the bone circle (counted).  The Brauer reading of the SAME word counts the bubble as
a loop (`loops = 1`), exhibiting the exact engine delta. -/
theorem specialBubble_uncounted :
    (spiderDiagramOf 1 [comultAt 0, multAt 0]).closedComponents = 0
      ∧ (brauerDiagramOf 1 [comultAt 0, multAt 0]).loops = 1 :=
  ⟨rfl, rfl⟩

/-- The crossing over two strands permutes the boundary partition into the transposition matching
`blockLabels = [0, 1, 1, 0]` (b0↔t1, b1↔t0) — the symmetry generator, reused from Brauer, reading through the spider
partition engine. -/
theorem crossing_spiderDiagram :
    spiderDiagramOf 2 [crossingAt 0]
      = { bottomCount := 2, topCount := 2, blockLabels := [0, 1, 1, 0], closedComponents := 0 } := rfl

/-! ## Honesty markers -/

/-- **Honesty marker — the spider WIRING engine is SHIPPED and computing.**  The four generators `μ` / `δ` / `η` /
`ε` ship as `WiringDesc` rows (`multWiring` / `comultWiring` / `unitWiring` / `counitWiring`) driving Brauer's
`stepWiring` / `processBrauer` fold verbatim; the union-find merges arbitrary-size classes natively
(`mult_spiderDiagram` reads the size-3 block `[0,0,0]` no degree-2 matching can express).  `= true`. -/
def fxFrob_hasSpiderWiringEngine : Bool := true

/-- **Honesty marker — the PARTITION MODEL is SHIPPED with a decidable canonical carrier.**  `SpiderDiagramType`
(boundary partition as least-index block labels + closed-component count) and its partition-only projection
`SpiderPartitionType` both derive `DecidableEq`; `extractSpiderDiagram` reads a wire state into the full special
(`Cospan(FinSet)`) invariant, `forgetSpiderClosed` / `extraSpiderDiagramOf` project to the extraspecial
(corelation) invariant.  `= true`. -/
def fxFrob_hasPartitionModel : Bool := true

/-- **Honesty marker — the closed-component invariant is SHIPPED EXACTLY as the literature fixes it.**  The special
law kills MULTIPLICITY only, so the closed-component counter stays LIVE: the μ-after-δ bubble is uncounted
(`specialBubble_uncounted`, still boundary-connected), the unit-then-counit circle is counted
(`bone_closedComponents_one`), and the Brauer `loops` reading of the bubble (`= 1`) exhibits why `loops` must be
dropped.  `= true`. -/
def fxFrob_hasPartitionInvariant : Bool := true

/-- **Honesty marker — the non-special `2Cob` (genus-per-block) variant is OUT OF SCOPE r1.**  Plain commutative
Frobenius algebras present `2Cob`, whose invariant refines the partition with a genus per connected block; the
special law collapses the genus, dropping to `Cospan(FinSet)`.  The genus refinement is ledgered as future work, no
code.  `= false`. -/
def fxFrob_has2CobGenus : Bool := false

end FX1Poly.Polygraph
