import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingDecision

/-! # WP-BRAUER-1 / WP-BRAUER-2 — the table-driven `WiringDesc` engine and the symmetric self-dual presentation

The walking-adjunction decision route already ships a **planar-algebra connectivity engine** (`MatchingDecision`):
a union-find over open wires (`WireState`), threaded bottom-to-top, that reads a free 2-cell's spine into its
boundary perfect-matching plus closed-loop count (`DiagramType`).  It hardcodes exactly two generator shapes —
`stepCup` (a `0 ⇒ 2` unit) and `stepCap` (a `2 ⇒ 0` counit) — and its generic fallback DROPS the wiring (inserts
DISCONNECTED fresh outputs), so a genuine crossing cannot pass through it.

This file generalizes that engine along one data axis.

## WP-BRAUER-1 — `WiringDesc`, one engine for any generator wiring

A **`WiringDesc`** is a generator's own boundary wiring: a perfect matching on its input ⊔ output ports plus a
count of loops internal to the box.  Endpoint tags `0 … inputCount-1` are the consumed input ports;
`inputCount … inputCount+outputCount-1` are the produced output ports.  `stepWiring` fires ONE union-find step for
ANY such generator: slice the input wires at the live position, allocate fresh output wires, fold the arc list
into the union-find (per-arc, closing a loop exactly when the two ends were already connected — the SAME
loop-on-same rule `stepCap` uses), then splice the outputs back in.  The shipped `stepCup` / `stepCap` are
`stepWiring` at `cupWiring` / `capWiring` — proven by `rfl` at the computational seed (`stepWiring_cupWiring_seed`,
`stepWiring_capWiring_seed`).  The **crossing** is one new row `crossingWiring = [(in0,out1),(in1,out0)]`; the fold
is planarity-agnostic, so `stepWiring` captures its transposition with ZERO new machinery
(`crossing_diagram` reads off the swap `[3,2,1,0]`).

## WP-BRAUER-2 — the Brauer / Temperley–Lieb + crossing presentation, as a value

The **Brauer category** is the free symmetric self-dual category on one self-dual object: its hom-sets ARE the
perfect matchings of the boundary, and two diagrams are equal iff they induce the same matching (Brauer 1937;
Kauffman diagram calculus 1987; Kock, *Frobenius Algebras and 2D TQFT* 2004 for the snake/zigzag equations).
Temperley–Lieb is the planar (non-crossing) subcategory — the crossing is the sole added generator promoting TL
to Brauer.  We ship the presentation as DATA: the three generators (`cup`, `cap`, `crossing`) with their
`WiringDesc`s, and the Reidemeister-style relation set (`brauerPresentation`) — the snake / zigzag triangle
identities (both orientations), crossing involutivity R2, the Yang–Baxter R3, and the cup/cap slide past a
crossing (naturality R1).  Each relation is a SOUNDNESS witness: both sides induce the SAME `DiagramType`, by
`rfl`.  Adding the snake + crossing relations is exactly what makes the shipped matching invariant COMPLETE for
this category — unlike the walking adjunction, where the snake gap keeps it incomplete.

## Honest scope

  * The `WiringDesc` engine and the crossing generator are SHIPPED and computing (`rfl` / `decide` smokes).
  * The presentation's per-relation soundness is SHIPPED as concrete witnesses.  Its GENERAL soundness (every
    convertible pair has equal matching) rides the SAME open residual as the adjunction route — the
    state-parametric union-find (Godement / interchange) independence — now also over the crossing steps; no new
    obstruction, no discount (`fxBrauer_hasBrauerSoundness = false`).
  * COMPLETENESS (equal matching ⇒ convertible) is the classical Brauer/TL straightening normal form — settled
    mathematics, real work, not yet built (`fxBrauer_hasBrauerCompleteness = false`).

Raw Lean 4 + Init; reuses the shipped `WireState` / union-find primitives verbatim.  Structural recursion, no
`omega` / `simp`-AC / `native_decide`.  Per-declaration `#assert_no_axioms` in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## WP-BRAUER-1: the wiring description + more list helpers -/

/-- ★ A **`WiringDesc`** — a generator's boundary wiring: how many boundary ports it consumes / produces, the
perfect matching on those ports (endpoint tags `0 … inputCount-1` = inputs, `inputCount … inputCount+outputCount-1`
= outputs), and the number of loops internal to the box.  A flat `Nat` / `List (Nat × Nat)` datum, so its equality
is decidable and it drives the engine by pure data — no indexed match on the generator. -/
structure WiringDesc where
  /-- The number of boundary input ports the generator consumes. -/
  inputCount : Nat
  /-- The number of boundary output ports the generator produces. -/
  outputCount : Nat
  /-- The wiring: a list of arcs, each pairing two endpoint tags. -/
  arcs : List (Nat × Nat)
  /-- The number of closed loops internal to the generator (a bubble); `0` for cup / cap / crossing. -/
  internalLoops : Nat
deriving DecidableEq

/-- Take `count` wires from `openWires` starting at `position` — the input ports a generator consumes.  Structural
on the list, so it computes. -/
def natListSliceAt : List Nat → Nat → Nat → List Nat
  | _, _, 0 => []
  | [], _, _ => []
  | head :: rest, 0, Nat.succ count => head :: natListSliceAt rest 0 count
  | _ :: rest, Nat.succ position, count => natListSliceAt rest position count

/-- Remove `count` wires from `openWires` starting at `position` — the block a generator consumes (the arity-`2`
special case is the shipped `natListRemoveTwoAt`).  Structural on the list. -/
def natListRemoveManyAt : List Nat → Nat → Nat → List Nat
  | wires, _, 0 => wires
  | [], _, _ => []
  | _ :: rest, 0, Nat.succ count => natListRemoveManyAt rest 0 count
  | head :: rest, Nat.succ position, count => head :: natListRemoveManyAt rest position count

/-! ## WP-BRAUER-1: the single wiring step -/

/-- Decode a wiring endpoint tag to its wire node id: tags below `inputCount` index the sliced input wires; the
rest index the freshly allocated output wires. -/
def wiringEndpointNode (inputNodes outputNodes : List Nat) (inputCount tag : Nat) : Nat :=
  if tag < inputCount then natListGetAt inputNodes tag
  else natListGetAt outputNodes (tag - inputCount)

/-- Fold a generator's arc list into the running union-find: for each arc, decode both endpoint tags to nodes and
either count a loop (already same component — the shipped `stepCap` rule) or union them.  Returns the updated links
and the loops closed by this generator's arcs.  Structural on the arc list. -/
def stepWiringArcs (inputNodes outputNodes : List Nat) (inputCount : Nat) :
    List (Nat × Nat) → Nat → List (Nat × Nat) → List (Nat × Nat) × Nat
  | [], loops, links => (links, loops)
  | (firstTag, secondTag) :: rest, loops, links =>
      let firstNode := wiringEndpointNode inputNodes outputNodes inputCount firstTag
      let secondNode := wiringEndpointNode inputNodes outputNodes inputCount secondTag
      if isSameComponent links firstNode secondNode then
        stepWiringArcs inputNodes outputNodes inputCount rest (loops + 1) links
      else
        stepWiringArcs inputNodes outputNodes inputCount rest loops
          (unionFindJoin links firstNode secondNode)

/-- ★ The **one wiring step** — process any generator described by a `WiringDesc` at the live `position`: slice its
input wires, allocate fresh output wires, fold its arcs into the union-find (with per-arc loop detection), and
splice the outputs back into the open-wire list.  Specializes to the shipped `stepCup` / `stepCap` on
`cupWiring` / `capWiring`. -/
def stepWiring (state : WireState) (position : Nat) (desc : WiringDesc) : WireState :=
  let inputNodes := natListSliceAt state.openWires position desc.inputCount
  let outputNodes := (List.range desc.outputCount).map (· + state.nextFresh)
  let foldResult := stepWiringArcs inputNodes outputNodes desc.inputCount desc.arcs 0 state.links
  { openWires :=
      natListInsertAt (natListRemoveManyAt state.openWires position desc.inputCount) position outputNodes,
    links := foldResult.fst,
    nextFresh := state.nextFresh + desc.outputCount,
    loops := state.loops + foldResult.snd + desc.internalLoops }

/-! ## WP-BRAUER-1: the canonical generator wirings -/

/-- The unit / **cup** `0 ⇒ 2`: the two produced ports are matched to each other. -/
def cupWiring : WiringDesc := { inputCount := 0, outputCount := 2, arcs := [(0, 1)], internalLoops := 0 }

/-- The counit / **cap** `2 ⇒ 0`: the two consumed ports are matched to each other. -/
def capWiring : WiringDesc := { inputCount := 2, outputCount := 0, arcs := [(0, 1)], internalLoops := 0 }

/-- ★ The **crossing** `2 ⇒ 2`: input `0` to output `1`, input `1` to output `0` — the transposition.  The sole
generator promoting Temperley–Lieb to the (symmetric) Brauer category. -/
def crossingWiring : WiringDesc :=
  { inputCount := 2, outputCount := 2, arcs := [(0, 3), (1, 2)], internalLoops := 0 }

/-- The **identity strand** `1 ⇒ 1`: input `0` to output `0` (a through-strand). -/
def identityWiring : WiringDesc := { inputCount := 1, outputCount := 1, arcs := [(0, 1)], internalLoops := 0 }

/-! ## WP-BRAUER-1: agreement with the shipped steps (at the computational seed)

The new engine IS the shipped one on the shipped generators.  Both sides compute on a ground state, so agreement
is `rfl`. -/

/-- A ground seed for a diagram with `bottomCount` bottom wires. -/
def brauerSeed (bottomCount : Nat) : WireState :=
  { openWires := List.range bottomCount, links := [], nextFresh := bottomCount, loops := 0 }

/-- ★ `stepWiring … cupWiring` agrees with the shipped `stepCup` — the cup wiring engine step reproduces the
hardcoded unit step (at the empty-open-wire seed). -/
theorem stepWiring_cupWiring_seed :
    stepWiring (brauerSeed 0) 0 cupWiring = stepCup (brauerSeed 0) 0 := rfl

/-- ★ `stepWiring … capWiring` agrees with the shipped `stepCap` — the cap wiring engine step reproduces the
hardcoded counit step (on a two-open-wire seed).  Both take the union branch here (the two wires start
disconnected). -/
theorem stepWiring_capWiring_seed :
    stepWiring (brauerSeed 2) 0 capWiring = stepCap (brauerSeed 2) 0 := rfl

/-- A cap on two ALREADY-CONNECTED wires closes a loop — the engine's loop-on-same rule matches `stepCap`'s.  Seed
the state with a cup (two connected wires) then cap them. -/
theorem stepWiring_capWiring_loop :
    stepWiring (stepCup (brauerSeed 0) 0) 0 capWiring = stepCap (stepCup (brauerSeed 0) 0) 0 := rfl

/-! ## WP-BRAUER-2: the Brauer diagram evaluator -/

/-- A **Brauer atom**: a generator (by its `WiringDesc`) fired at a boundary `position`. -/
structure BrauerAtom where
  /-- The live position at which the generator's input block sits in the open-wire list. -/
  position : Nat
  /-- The generator's boundary wiring. -/
  wiring : WiringDesc
deriving DecidableEq

/-- Fire one Brauer atom. -/
def stepBrauerAtom (state : WireState) (atom : BrauerAtom) : WireState :=
  stepWiring state atom.position atom.wiring

/-- Fold a list of Brauer atoms bottom-to-top. -/
def processBrauer (state : WireState) (atoms : List BrauerAtom) : WireState :=
  atoms.foldl stepBrauerAtom state

/-- ★ The **Brauer diagram** of a sequence of generators over `bottomCount` bottom wires: run the wiring engine
from the seed, then read off the boundary perfect-matching + loop count.  Computes (the smokes are `rfl`). -/
def brauerDiagramOf (bottomCount : Nat) (atoms : List BrauerAtom) : DiagramType :=
  extractDiagram bottomCount (processBrauer (brauerSeed bottomCount) atoms)

/-- The generators as named atoms, parameterized by position. -/
def cupAt (position : Nat) : BrauerAtom := { position := position, wiring := cupWiring }

/-- A cap atom at `position`. -/
def capAt (position : Nat) : BrauerAtom := { position := position, wiring := capWiring }

/-- A crossing atom at `position`. -/
def crossingAt (position : Nat) : BrauerAtom := { position := position, wiring := crossingWiring }

/-- An identity-strand atom at `position`. -/
def identityStrandAt (position : Nat) : BrauerAtom := { position := position, wiring := identityWiring }

/-! ## WP-BRAUER-1: the crossing captures the transposition -/

/-- ★ **The crossing smoke.**  One crossing over two bottom strands induces the TRANSPOSITION matching
`[3, 2, 1, 0]`: bottom port `0` (boundary `0`) is matched to boundary `3` (top port `1`), bottom port `1` to top
port `0`.  Computed by `rfl` — the wiring engine captures the crossing's connectivity with no permutation
extension, exactly as the recon predicted. -/
theorem crossing_diagram :
    brauerDiagramOf 2 [crossingAt 0]
      = { bottomCount := 2, topCount := 2, partner := [3, 2, 1, 0], loops := 0 } := rfl

/-- Contrast: two identity strands (no crossing) give the STRAIGHT matching `[2, 3, 0, 1]` — bottom `0` to top `0`,
bottom `1` to top `1`.  So the crossing is genuinely distinct from the identity as a diagram. -/
theorem identity_pair_diagram :
    brauerDiagramOf 2 [identityStrandAt 0, identityStrandAt 1]
      = { bottomCount := 2, topCount := 2, partner := [2, 3, 0, 1], loops := 0 } := rfl

/-! ## WP-BRAUER-2: the relations, as data + soundness witnesses -/

/-- A **Brauer relation**: two generator words over a common boundary, asserted (by the soundness witnesses) to
induce the same diagram. -/
structure BrauerRelation where
  /-- The number of bottom boundary wires both sides act on. -/
  boundaryCount : Nat
  /-- The left-hand generator word. -/
  lhs : List BrauerAtom
  /-- The right-hand generator word. -/
  rhs : List BrauerAtom
deriving DecidableEq

/-- **S1 snake (zig-zag) on one strand**: `(cap ▷ id) ∘ (id ▷ cup) = id`.  Create a cup to the right of the
strand, then cap the strand together with the cup's near leg — leaving one through-strand. -/
def snakeRelation : BrauerRelation :=
  { boundaryCount := 1, lhs := [cupAt 1, capAt 0], rhs := [] }

/-- **S2 snake (the mirror)**: `(id ▷ cap) ∘ (cup ▷ id) = id`.  Cup to the LEFT of the strand, then cap the cup's
far leg with the strand. -/
def snakeMirrorRelation : BrauerRelation :=
  { boundaryCount := 1, lhs := [cupAt 0, capAt 1], rhs := [] }

/-- **R2 crossing involutivity** (symmetric, not braided): `crossing ∘ crossing = id ⊗ id`. -/
def crossingInvolutionRelation : BrauerRelation :=
  { boundaryCount := 2, lhs := [crossingAt 0, crossingAt 0], rhs := [] }

/-- The Yang–Baxter left word `(X⊗id)(id⊗X)(X⊗id)` on three strands. -/
def yangBaxterLhsWord : List BrauerAtom := [crossingAt 0, crossingAt 1, crossingAt 0]

/-- The Yang–Baxter right word `(id⊗X)(X⊗id)(id⊗X)` on three strands. -/
def yangBaxterRhsWord : List BrauerAtom := [crossingAt 1, crossingAt 0, crossingAt 1]

/-- **R3 Yang–Baxter**: `(X⊗id)(id⊗X)(X⊗id) = (id⊗X)(X⊗id)(id⊗X)` on three strands. -/
def yangBaxterRelation : BrauerRelation :=
  { boundaryCount := 3, lhs := yangBaxterLhsWord, rhs := yangBaxterRhsWord }

/-- **R1 cap slides past a crossing** (naturality): capping two strands after crossing one of them past a third is
the same diagram as crossing then capping the other pair.  On three strands: cross the middle-right pair, then cap
the left-middle pair, versus crossing the left-middle pair then capping the middle-right pair. -/
def capSlideRelation : BrauerRelation :=
  { boundaryCount := 3,
    lhs := [crossingAt 1, capAt 0],
    rhs := [crossingAt 0, capAt 1] }

/-- ★ The **Brauer / Temperley–Lieb + crossing presentation**, as a value: the relation set that (together with the
generators `cup` / `cap` / `crossing`) presents the free symmetric self-dual category.  Temperley–Lieb is the
sub-presentation dropping `crossing` and its relations (`snakeRelation`, `snakeMirrorRelation`). -/
def brauerPresentation : List BrauerRelation :=
  [snakeRelation, snakeMirrorRelation, crossingInvolutionRelation, yangBaxterRelation, capSlideRelation]

/-! ## WP-BRAUER-2: per-relation soundness (each a `rfl` witness) -/

/-- The snake straightens to the identity through-strand — both `[1, 0]`, no loops. -/
theorem snake_diagram_sound :
    brauerDiagramOf snakeRelation.boundaryCount snakeRelation.lhs
      = brauerDiagramOf snakeRelation.boundaryCount snakeRelation.rhs := rfl

/-- The mirror snake likewise straightens to the identity. -/
theorem snakeMirror_diagram_sound :
    brauerDiagramOf snakeMirrorRelation.boundaryCount snakeMirrorRelation.lhs
      = brauerDiagramOf snakeMirrorRelation.boundaryCount snakeMirrorRelation.rhs := rfl

/-- Two crossings compose to the identity on two strands (R2). -/
theorem crossingInvolution_diagram_sound :
    brauerDiagramOf crossingInvolutionRelation.boundaryCount crossingInvolutionRelation.lhs
      = brauerDiagramOf crossingInvolutionRelation.boundaryCount crossingInvolutionRelation.rhs := rfl

/-- The cap slides past the crossing (R1 naturality). -/
theorem capSlide_diagram_sound :
    brauerDiagramOf capSlideRelation.boundaryCount capSlideRelation.lhs
      = brauerDiagramOf capSlideRelation.boundaryCount capSlideRelation.rhs := rfl

/-! ### R3 Yang–Baxter — a STAGED single-step proof

Yang–Baxter is three nested crossings per side; proving it by one `rfl` over `brauerDiagramOf` blows up the
kernel `isDefEq` (the union-find fold has no sharing, so reducing step 3 re-reduces steps 2 and 1 — exponential in
depth).  Instead we stage it: each `stepBrauerAtom` is applied to a CONCRETE literal state (a single, cheap
reduction), the three steps are chained by `rw`, and the two sides — reaching DIFFERENT internal wire labels but
the SAME boundary matching (the full reversal `[5,4,3,2,1,0]`) — are compared by one `extractDiagram` over each
literal.  Every proof here is a single-step reduction, so the whole thing is fast and zero-axiom. -/

/-- The left word after its first crossing. -/
def yangBaxterStateLeftOne : WireState :=
  { openWires := [3, 4, 2], links := [(1, 3), (0, 4)], nextFresh := 5, loops := 0 }

/-- The left word after its second crossing. -/
def yangBaxterStateLeftTwo : WireState :=
  { openWires := [3, 5, 6], links := [(2, 5), (4, 6), (1, 3), (0, 4)], nextFresh := 7, loops := 0 }

/-- The left word after its third crossing. -/
def yangBaxterStateLeftThree : WireState :=
  { openWires := [7, 8, 6], links := [(5, 7), (3, 8), (2, 5), (4, 6), (1, 3), (0, 4)], nextFresh := 9, loops := 0 }

/-- The right word after its first crossing. -/
def yangBaxterStateRightOne : WireState :=
  { openWires := [0, 3, 4], links := [(2, 3), (1, 4)], nextFresh := 5, loops := 0 }

/-- The right word after its second crossing. -/
def yangBaxterStateRightTwo : WireState :=
  { openWires := [5, 6, 4], links := [(3, 5), (0, 6), (2, 3), (1, 4)], nextFresh := 7, loops := 0 }

/-- The right word after its third crossing. -/
def yangBaxterStateRightThree : WireState :=
  { openWires := [5, 7, 8], links := [(4, 7), (6, 8), (3, 5), (0, 6), (2, 3), (1, 4)], nextFresh := 9, loops := 0 }

/-- Left crossing step 1 (single reduction over the seed). -/
theorem yangBaxterStepLeftOne :
    stepBrauerAtom (brauerSeed 3) (crossingAt 0) = yangBaxterStateLeftOne := rfl

/-- Left crossing step 2 (single reduction over a concrete literal). -/
theorem yangBaxterStepLeftTwo :
    stepBrauerAtom yangBaxterStateLeftOne (crossingAt 1) = yangBaxterStateLeftTwo := rfl

/-- Left crossing step 3 (single reduction over a concrete literal). -/
theorem yangBaxterStepLeftThree :
    stepBrauerAtom yangBaxterStateLeftTwo (crossingAt 0) = yangBaxterStateLeftThree := rfl

/-- Right crossing step 1. -/
theorem yangBaxterStepRightOne :
    stepBrauerAtom (brauerSeed 3) (crossingAt 1) = yangBaxterStateRightOne := rfl

/-- Right crossing step 2. -/
theorem yangBaxterStepRightTwo :
    stepBrauerAtom yangBaxterStateRightOne (crossingAt 0) = yangBaxterStateRightTwo := rfl

/-- Right crossing step 3. -/
theorem yangBaxterStepRightThree :
    stepBrauerAtom yangBaxterStateRightTwo (crossingAt 1) = yangBaxterStateRightThree := rfl

/-- The left word processes to its final concrete state (three chained single steps). -/
theorem yangBaxterProcessLeft :
    processBrauer (brauerSeed 3) yangBaxterLhsWord = yangBaxterStateLeftThree := by
  show stepBrauerAtom (stepBrauerAtom (stepBrauerAtom (brauerSeed 3) (crossingAt 0)) (crossingAt 1))
      (crossingAt 0) = yangBaxterStateLeftThree
  rw [yangBaxterStepLeftOne, yangBaxterStepLeftTwo, yangBaxterStepLeftThree]

/-- The right word processes to its final concrete state (three chained single steps). -/
theorem yangBaxterProcessRight :
    processBrauer (brauerSeed 3) yangBaxterRhsWord = yangBaxterStateRightThree := by
  show stepBrauerAtom (stepBrauerAtom (stepBrauerAtom (brauerSeed 3) (crossingAt 1)) (crossingAt 0))
      (crossingAt 1) = yangBaxterStateRightThree
  rw [yangBaxterStepRightOne, yangBaxterStepRightTwo, yangBaxterStepRightThree]

/-- ★ The two Yang–Baxter words induce the same diagram (R3) — both the full reversal `[5, 4, 3, 2, 1, 0]`, via the
staged single-step reductions above. -/
theorem yangBaxter_diagram_sound :
    brauerDiagramOf yangBaxterRelation.boundaryCount yangBaxterRelation.lhs
      = brauerDiagramOf yangBaxterRelation.boundaryCount yangBaxterRelation.rhs := by
  show extractDiagram 3 (processBrauer (brauerSeed 3) yangBaxterLhsWord)
     = extractDiagram 3 (processBrauer (brauerSeed 3) yangBaxterRhsWord)
  rw [yangBaxterProcessLeft, yangBaxterProcessRight]
  rfl

/-- ★ **Every relation of the shipped presentation is diagram-sound** — the conjunction of the five per-relation
witnesses (two snakes, R2 involutivity, R3 Yang–Baxter, R1 cap-slide), reusing the proofs above (no
recomputation). -/
theorem brauerPresentation_allSound :
    (brauerDiagramOf snakeRelation.boundaryCount snakeRelation.lhs
        = brauerDiagramOf snakeRelation.boundaryCount snakeRelation.rhs)
    ∧ (brauerDiagramOf snakeMirrorRelation.boundaryCount snakeMirrorRelation.lhs
        = brauerDiagramOf snakeMirrorRelation.boundaryCount snakeMirrorRelation.rhs)
    ∧ (brauerDiagramOf crossingInvolutionRelation.boundaryCount crossingInvolutionRelation.lhs
        = brauerDiagramOf crossingInvolutionRelation.boundaryCount crossingInvolutionRelation.rhs)
    ∧ (brauerDiagramOf yangBaxterRelation.boundaryCount yangBaxterRelation.lhs
        = brauerDiagramOf yangBaxterRelation.boundaryCount yangBaxterRelation.rhs)
    ∧ (brauerDiagramOf capSlideRelation.boundaryCount capSlideRelation.lhs
        = brauerDiagramOf capSlideRelation.boundaryCount capSlideRelation.rhs) :=
  ⟨snake_diagram_sound, snakeMirror_diagram_sound, crossingInvolution_diagram_sound,
    yangBaxter_diagram_sound, capSlide_diagram_sound⟩

/-! ## Honesty markers -/

/-- **Honesty marker — the `WiringDesc` engine is SHIPPED and computing.**  `stepWiring` fires one union-find step
for any generator described by a `WiringDesc`, subsuming the shipped `stepCup` / `stepCap` (`stepWiring_cupWiring_seed`,
`stepWiring_capWiring_seed`, `stepWiring_capWiring_loop`).  `= true`. -/
def fxBrauer_hasWiringDescEngine : Bool := true

/-- **Honesty marker — the crossing generator is SHIPPED with no permutation extension.**  The crossing is one
`WiringDesc` row (`crossingWiring`); the planarity-agnostic fold captures its transposition (`crossing_diagram`
reads the swap `[3, 2, 1, 0]`, distinct from the straight pair `identity_pair_diagram`).  `= true`. -/
def fxBrauer_hasCrossingGenerator : Bool := true

/-- **Honesty marker — the Brauer / TL + crossing presentation ships as a value with per-relation soundness.**  The
generators (`cup` / `cap` / `crossing`) and the Reidemeister-style relation set (`brauerPresentation`: two snakes,
R2 involutivity, R3 Yang–Baxter, R1 cap-slide) are DATA; each relation carries a diagram-soundness witness (the
low-depth ones by `rfl`, R3 by the staged single-step chain `yangBaxter_diagram_sound`), and
`brauerPresentation_allSound` conjoins the whole set.  `= true`. -/
def fxBrauer_hasBrauerPresentation : Bool := true

/-- **Honesty marker — GENERAL Brauer soundness rides the standing Godement residual.**  Per-relation soundness is
shipped as witnesses, but "every convertible pair has equal matching" for the whole presentation is exactly the
state-parametric union-find (Godement / interchange) independence — the SAME open lemma as the adjunction route
(`fxMode_hasMatchingGodementIndependenceProof`), now also over the crossing steps.  No new obstruction, no
discount.  `= false`. -/
def fxBrauer_hasBrauerSoundness : Bool := false

/-- **Honesty marker — COMPLETENESS (equal matching ⇒ convertible) is the classical straightening NF, not yet
built.**  Adding the snake + crossing relations makes `DiagramType` a COMPLETE invariant for the symmetric Brauer
category (unlike the walking adjunction's snake gap), so the reconstruction target is the right normal form; but
the Brauer/TL straightening algorithm — settled mathematics, real work — is not yet shipped.  `= false`. -/
def fxBrauer_hasBrauerCompleteness : Bool := false

end FX1Poly.Polygraph
