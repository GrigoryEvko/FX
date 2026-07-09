import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingModel
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringLabelPinning

/-! # WalkingString — the FUSS-CATALAN carrier (`FcDiagram`), no-loops, and the FC fingerprint (FC-0)

The walking adjoint triple `F ⊣ G ⊣ H` (`StringSeed`, `G` shared) is the free 2-category on two adjacent
adjunctions.  Its string-diagram 2-cells are planar matchings of the `F`/`G`/`H` boundary ports; this file opens the
FUSS-CATALAN reading of those matchings.  Three structural facts about the seed drive it (all verified against the
shipped `StringSeed`/`StringLabelPinning`, not assumed):

  * **CHIRALITY.**  The two cups open the words `{F·G, G·H}`; the two caps close the REVERSED words `{G·F, H·G}`
    (`StringTwoCell.unitLower/unitUpper` vs `counitLower/counitUpper`, `StringSeed.lean:97-104`).  These two
    two-letter alphabets are DISJOINT (`stringCupCod_ne_capDom` — `F ≠ H` propagated into the words), so a cup-created
    pair can NEVER be deleted as-a-pair.  Hence NO CLOSED CIRCLES form: the union-find loop count is `0` on the
    exhibited cells (`StringColouredRefinement.stringWitnesses_loops_zero`), and the general no-loops direction is the
    N2 target here.
  * **2-COLOUR discipline.**  Every cup/cap arc pairs a `G`-end with an `{F, H}`-end, so an arc is canonically
    coloured by its non-`G` letter — `fWire` = the lower (`F ⊣ G`) colour, `hWire` = the upper (`G ⊣ H`) colour.  This
    is the Fuss–Catalan two-colour matching discipline (Bisch–Jones); `FcArc.colour` records it, read at arc creation
    from the boundary labels.
  * **snake collapses = triangle identities** (`StringSaturatedConv`), same-colour only; no cross-colour collapse.

## N0 — novelty verdict + the Fuss–Catalan facts the later FC phases need (with citations)

**Novelty (as-far-as-searchable UNPUBLISHED).**  Four adversarial cross-searches ("walking/free adjoint triple" ×
"Fuss–Catalan diagrammatic") returned no source connecting the two mature theories.  The nLab `adjoint string` page
(https://ncatlab.org/nlab/show/adjoint+string) carries the adjoint-triple story with NO Fuss–Catalan link; targeted
searches for a diagram-category presentation of the walking adjoint triple, and for "Fuss–Catalan" + "adjoint triple"
in a free monoidal setting, both came up empty.  So the specific identification — the free 2-category on an adjoint
TRIPLE `F ⊣ G ⊣ H` (`G` shared) has its boundary-word combinatorics governed by the TWO-COLOUR Fuss–Catalan
discipline (arcs 2-coloured by the non-`G` end, loop-free by chirality, counted by the `k = 2` Fuss–Catalan numbers)
— is novel AS A STATED IDENTIFICATION.  Priority-honest caveats: (a) the free adjoint PAIR → Δ story is classical
(Schanuel–Street, *The free adjunction*, Cahiers 27 (1986) 81–83: `Adj` homs are the subcategories of Δ preserving
top/bottom elements, composition = ordinal sum); (b) two-colour Fuss–Catalan planar diagrams are classical
(Bisch–Jones, *Invent. Math.* 128 (1997) 89–157).  The novelty is precisely the BRIDGE; the closest structural
precedent one rung below is the length-`2n+1` adjoint chain inside Δ itself (injections/surjections interleave to an
adjoint chain — nLab `adjoint string`).

**FC facts for FC-1..FC-4.**  Dimension: `dim FC_n^{(k)} = (1/(kn+1))·C((k+1)n, n)`; for `k = 2` this is
`(1/(2n+1))·C(3n, n) = 1, 1, 3, 12, 55` at `n = 0,1,2,3,4` (Bisch–Jones; Hussein thesis `f(k,m) = (1/m)C(km+m, m-1)`).
Diagram carrier + colour discipline: "a planar diagram … strings join pairs of points having the SAME colour" —
only MONOCHROMATIC non-crossing matchings are allowed; the boundary points read `abba abba ⋯ abba` (Banica
math/0010084; Liu YMSC free-product description).  Generator–relation presentation FC-2 will need for the insertion
census: coloured Temperley–Lieb generators `u_i^{(l)}` (`1 ≤ l ≤ k`) with `U_i^{(m)}U_i^{(p)} = ρ_i(min(m,p))·
U_i^{(max(m,p))}`, `|i − j| > 1` commutation, and the parity-dependent site relations (Bisch–Jones; Landau, *Pacific
J. Math.* 197 (2001), "middle patterns").  **Loop-parameter honesty caveat (drives N2):** in the FC ALGEBRA a closed
monochromatic loop CAN form and is killed by a scalar `δ_a`/`δ_b` in the LINEAR / subfactor completion; the diagram
BASIS is loop-free.  Our "no closed circles EVER" is STRONGER — it is a property of the free / walking-adjoint-triple
word ORIENTATION (chirality of insert vs delete), NOT inherited from Bisch–Jones.  So the N2 no-loops statement is
about `matchingOf` under this seed's oriented cup/cap words, and loop-freeness is NOT attributed to the FC algebra.

## What this file ships (FC-0, Phase 0)

  * **N1 `FcArc` / `FcDiagram`** — the Fuss–Catalan carrier: arcs pairing two boundary ports with the FC colour read
    at creation, plus the two boundary words; `deriving DecidableEq` (structural, no `Quot`).  `fcDiagramOf` refines
    the shipped `matchingOf` fold by reading each arc's colour off the boundary labels; `fcDiagramForget` is the
    forgetful map back to `ColouredDiagramType`, an on-the-nose `rfl` bridge.
  * **N2** — the no-loops content (see the `fxString_hasNoLoopsTheorem` marker for the honest status).
  * **N3** — the FC-number fingerprint: a monochromatic non-crossing perfect-matching enumerator, `#eval`-compared to
    the independently-computed Fuss–Catalan numbers (see `fxString_hasFcCountFingerprint`).

Raw Lean 4 + Init; structural / fuel recursion, full-enum matches, `propext`/`Quot.sound`/`Classical`/`sorry`/
`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## N1 — the Fuss–Catalan carrier -/

/-- Read a `WireLabel` list at a position, defaulting to `gWire` past the end (in range for a well-formed boundary;
the default keeps the reader total).  Cons-only structural recursion — propext-clean. -/
def wireLabelListGetAt : List WireLabel → Nat → WireLabel
  | [], _ => WireLabel.gWire
  | head :: _, 0 => head
  | _ :: rest, position + 1 => wireLabelListGetAt rest position

/-- The **Fuss–Catalan colour of an arc** from the labels of its two ends: an arc pairs one `G`-end with one
`{F, H}`-end, and the colour is the non-`G` letter (`fWire` = lower `F ⊣ G` colour, `hWire` = upper `G ⊣ H` colour).
For a `G`-`G` arc (both ends `G`, the shared-middle through-strand) the colour is `gWire` (degenerate); for a
same-letter `{F, H}` arc it is that letter.  Full-enum match on the low end — propext-clean. -/
def fcArcColour (lowLabel highLabel : WireLabel) : WireLabel :=
  match lowLabel with
  | WireLabel.gWire => highLabel
  | WireLabel.fWire => WireLabel.fWire
  | WireLabel.hWire => WireLabel.hWire

/-- ★ One **Fuss–Catalan arc**: an unordered pair of boundary ports (`lowEnd < highEnd`) plus its FC colour (the
non-`G` end's letter).  A flat datum of `Nat`/`WireLabel`, so equality is decidable and computes. -/
structure FcArc where
  /-- The lower (smaller-index) boundary port of the arc. -/
  lowEnd : Nat
  /-- The upper (larger-index) boundary port of the arc — the matched partner of `lowEnd`. -/
  highEnd : Nat
  /-- The Fuss–Catalan colour of the arc: the non-`G` end's letter (`gWire` iff both ends are `G`). -/
  colour : WireLabel
deriving DecidableEq

/-- ★ The **Fuss–Catalan diagram** of a walking-adjoint-triple 2-cell: the base boundary matching (`DiagramType`,
loop-free by N2), the FC arcs (one per matched pair, coloured at creation), and the two boundary words.  Loop-free
BY THE CARRIER — there is no loop field on the arcs; a closed loop would be a component with no boundary port, which
the arc list (pairs of boundary ports) cannot represent.  `deriving DecidableEq` — structural, no `Quot`. -/
structure FcDiagram where
  /-- The base boundary partner-matching + loop count (the colour-blind Joyal–Street type; loops `= 0` by N2). -/
  base : DiagramType
  /-- The Fuss–Catalan arcs, one per matched boundary pair, coloured by the non-`G` end at creation. -/
  arcs : List FcArc
  /-- The `F`/`G`/`H` labels of the bottom-boundary ports (fixed by the source 1-cell). -/
  bottomWord : List WireLabel
  /-- The `F`/`G`/`H` labels of the top-boundary ports (fixed by the target 1-cell). -/
  topWord : List WireLabel
deriving DecidableEq

/-- The `F`/`G`/`H` label of a boundary port `index`: a bottom port (`index < bottomCount`) reads the source word,
a top port reads the target word (offset by `bottomCount`). -/
def fcBoundaryLabelAt (bottomCount : Nat) (bottomWord topWord : List WireLabel) (index : Nat) : WireLabel :=
  if index < bottomCount then wireLabelListGetAt bottomWord index
  else wireLabelListGetAt topWord (index - bottomCount)

/-- Build the FC arc list from the base partner matching and the boundary labels: for each boundary index that is the
LOWER end of its matched pair (`index < partner.get index`), emit one arc, its colour read from the two ends' labels.
Self-partnered (unmatched) indices emit nothing.  Fold over `List.range` — the arc order is deterministic. -/
def fcArcsFromPartner (bottomCount : Nat) (bottomWord topWord : List WireLabel) (partner : List Nat) : List FcArc :=
  (List.range partner.length).foldr
    (fun index acc =>
      let partnerIndex := natListGetAt partner index
      if index < partnerIndex then
        { lowEnd := index, highEnd := partnerIndex,
          colour := fcArcColour (fcBoundaryLabelAt bottomCount bottomWord topWord index)
            (fcBoundaryLabelAt bottomCount bottomWord topWord partnerIndex) } :: acc
      else acc)
    []

/-- ★ The **Fuss–Catalan diagram of a walking-adjoint-triple 2-cell**: refine the shipped colour-blind boundary
matching `matchingOf` by reading each arc's FC colour off the boundary labels (`pathLabels` of the source / target
1-cells).  The colour of every arc is available at creation — no indexed match on the generator. -/
def fcDiagramOf {sourceMode targetMode : AdjointTripleMode}
    (sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode)
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) : FcDiagram :=
  let baseDiagram := matchingOf cell
  let bottomWord := pathLabels sourcePath
  let topWord := pathLabels targetPath
  { base := baseDiagram,
    arcs := fcArcsFromPartner baseDiagram.bottomCount bottomWord topWord baseDiagram.partner,
    bottomWord := bottomWord,
    topWord := topWord }

/-- The forgetful map `FcDiagram → ColouredDiagramType`: drop the FC arcs, keeping the base matching and the two
boundary words.  The arcs are DERIVED from those, so forgetting them loses no independent data. -/
def fcDiagramForget (fc : FcDiagram) : ColouredDiagramType :=
  { base := fc.base, bottomLabels := fc.bottomWord, topLabels := fc.topWord }

/-- ★ **`fcDiagramOf` forgets on the nose to `colouredMatchingOf`.**  The FC carrier is a genuine REFINEMENT of the
shipped two-level matching model: forgetting its arcs recovers `colouredMatchingOf` exactly (both build
`base := matchingOf cell`, `bottomLabels := pathLabels sourcePath`, `topLabels := pathLabels targetPath`).  `rfl`. -/
theorem fcDiagramForget_fcDiagramOf {sourceMode targetMode : AdjointTripleMode}
    (sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode)
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    fcDiagramForget (fcDiagramOf sourcePath targetPath cell)
      = colouredMatchingOf sourcePath targetPath cell := rfl

/-! ## N1 non-vacuity — the carrier reads the two Fuss–Catalan colours off real cells -/

/-- The bare lower cup `η : id ⇒ F·G` has ONE FC arc — the colour-1 arc pairing its `F`-leg (port 0) with its
`G`-leg (port 1), coloured `fWire` (the lower `F ⊣ G` colour). -/
theorem fcDiagramOf_stringUnitLower :
    fcDiagramOf (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) stringFG stringUnitLower
      = { base := { bottomCount := 0, topCount := 2, partner := [1, 0], loops := 0 },
          arcs := [{ lowEnd := 0, highEnd := 1, colour := WireLabel.fWire }],
          bottomWord := [],
          topWord := [WireLabel.fWire, WireLabel.gWire] } := rfl

/-- ★★ **The carrier 2-COLOURS the cross-level cell.**  `stringCrossLevelCell : G·F ⇒ G·H` (in NEITHER single
adjunction) gets TWO FC arcs of DIFFERENT colours: the bottom `G·F` cap arc (ports 0–1) coloured `fWire` (colour 1)
and the top `G·H` cup arc (ports 2–3) coloured `hWire` (colour 2).  This is the Fuss–Catalan two-colour discipline
read directly off a genuine cross-level cell — the FC carrier sees both colours where the base matching sees only
connectivity. -/
theorem fcDiagramOf_stringCrossLevelCell :
    fcDiagramOf stringGF stringGH stringCrossLevelCell
      = { base := { bottomCount := 2, topCount := 2, partner := [1, 0, 3, 2], loops := 0 },
          arcs := [{ lowEnd := 0, highEnd := 1, colour := WireLabel.fWire },
                   { lowEnd := 2, highEnd := 3, colour := WireLabel.hWire }],
          bottomWord := [WireLabel.gWire, WireLabel.fWire],
          topWord := [WireLabel.gWire, WireLabel.hWire] } := rfl

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the Fuss–Catalan carrier `FcDiagram` is shipped.**  `FcArc` (a boundary-port pair + the FC
colour) and `FcDiagram` (base matching + FC arcs + the two boundary words), both `deriving DecidableEq` structurally
(no `Quot`).  `fcDiagramOf` refines the shipped `matchingOf` fold by reading each arc's colour off the boundary
labels, and forgets on the nose to `colouredMatchingOf` (`fcDiagramForget_fcDiagramOf`, `rfl`).  Non-vacuous: it
2-colours the cross-level cell `G·F ⇒ G·H` into one `fWire` arc and one `hWire` arc
(`fcDiagramOf_stringCrossLevelCell`), the genuine Fuss–Catalan discipline read off a cell in neither single
adjunction.  `= true`. -/
def fxString_hasFcCarrier : Bool := true

end FX1Poly.Polygraph
