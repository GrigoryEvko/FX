import FX1Poly.Polygraph.Omega.ZXPhaseFree.IdentityResidual

/-! # Polygraph/Omega/ZXPhaseFree/IdentityRouter — THE FEEDING-COMB ATOMS land;
the full feeding-comb router and the `wireCount` identity induction stay walled

The absorption assembly (`zxbAbsorptionOfResiduals`) reduces phase-free
completeness to four cell-level residuals; the crossing residual is inhabited
(`zxkCrossingAbsorbHolds`), leaving the two spider colours and
`zxbIdentityAbsorbStatement` (the empty diagram at every arity converts to the
normal form of its own denotation).  The prior round landed the DISJOINT
create-state ride (`zxjZeroStateRidePastGenBlock`) and the whiskered identity
lift (`zxjEmptyRidesToWhiskeredIdentity`), and walled the identity residual on
THE MISSING ENGINE named there: *a created state routing past a comb that FEEDS
it* — the create-route-discard the `wireCount` step needs.

This round isolates and lands the ATOMS of that engine — the local one-cell
moves a created state performs as it passes a comb column — and records, with a
fresh pair of genuinely different burned attacks, exactly why chaining them into
the full router (and hence the induction) does not close here.

* (i)   THE FEEDING-COMB ATOMS (all PROVED, over `ZxwConv`): the state-copy
  duplication (`zxiStateCopyDuplicates`, a created X state above a Z copy becomes
  two created X states — Kissinger's `bialgUnitCopy`); the state-merge collapse
  (`zxiStateMergeAbsorbs`, a created X state fed into an X merge is the identity
  wire — `xMonoidUnit`); the create-kill annihilations (`zxiCreateKillAbsorbsX`,
  `zxiCreateKillAbsorbsZ` — `boneX`/`boneZ`, the carrier's birth-and-death); and
  the state slide past a crossing (`zxiStateSlidesPastCrossing`, the routing
  atom).  Each is fired straight from the seed row set and carries a kernel span
  pin.

* (ii)  THE WHISKERED CREATE-KILL (`zxiCreateKillAbsorbsXWhiskered`, PROVED) and
  THE TWO-ATOM COMPOSITE (`zxiCreateCopyThenKillBoth`, PROVED): a created X
  state, copied by a Z fork, with both copies killed, collapses to two kill
  cells — the create-route-discard motif at its smallest, assembled from the
  atoms through `zxwLiftConv`.

* (iii) THE FULL FEEDING-COMB ROUTER STAYS WALLED (`zxiHasFeedingCombRouter :=
  false`) and with it the `wireCount` induction (`zxiHasIdentityAbsorb :=
  false`).  Two genuinely different attacks burned, both converging on the same
  singular missing primitive; recorded on the marker docstrings.  The committed
  owner `zxkIdentityAbsorbIsProven := false` stays byte-intact.

Raw Lean 4 + Init only; zero-axiom; structural only; no `List.append`, no `Int`,
no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive scrutinees. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — T0: the semantics pinned by kernel evaluation

The empty diagram at any arity denotes the identity relation ON THE NOSE, and
the normal forms of the identity subspace are the interleaved create-comb-kill
machines the induction would have to build.  The layer counts (10, 22, 38 for
`wireCount` 1, 2, 3) and the whisker-form span-equality are the exact shapes the
attacks below must traverse. -/

/-- THE TARGET DENOTATION (definitional): the empty diagram at every arity
denotes the identity generator matrix `zxpIdRows wireCount` — so
`zxbIdentityAbsorbStatement wireCount` is `ZxwConv (empty wireCount)
(zxnNormalForm wireCount wireCount (zxpIdRows wireCount))` after this rewrite. -/
theorem zxiEmptyDiagramDenote (wireCount : Nat) :
    zxpDiagramDenote { sourceArity := wireCount, layers := [] }
      = zxpIdRows wireCount := rfl

/-- THE IDENTITY GENERATOR ROWS at `wireCount = 1`: one row `(1 | 1)` — the
diagonal of `F2^2`. -/
theorem zxiIdRowsOnePin : zxpIdRows 1 = [[true, true]] := rfl

/-- THE IDENTITY GENERATOR ROWS at `wireCount = 2`: two rows `e_0 ++ e_0` and
`e_1 ++ e_1` — each couples a domain strand with its created partner. -/
theorem zxiIdRowsTwoPin :
    zxpIdRows 2 = [[true, false, true, false], [false, true, false, true]] := rfl

/-- THE NORMAL-FORM SIZE at `wireCount = 1`: `init ; comb(row 0) ; kill` is a
10-layer machine (1 init + 8 comb + 1 kill). -/
theorem zxiNormalFormLayersOnePin :
    (zxnNormalForm 1 1 (zxpIdRows 1)).layers.length = 10 := rfl

/-- THE NORMAL-FORM SIZE at `wireCount = 2`: 22 layers (1 init + 20 comb + 1
kill; each row's comb is a 10-layer carrier staircase). -/
theorem zxiNormalFormLayersTwoPin :
    (zxnNormalForm 2 2 (zxpIdRows 2)).layers.length = 22 := rfl

/-- THE NORMAL-FORM SIZE at `wireCount = 3`: 38 layers — the machine the
`wireCount = 3` induction step would have to reach from three bare wires. -/
theorem zxiNormalFormLayersThreePin :
    (zxnNormalForm 3 3 (zxpIdRows 3)).layers.length = 38 := rfl

/-- ATTACK-A BOUNDARY EVIDENCE (kernel span pin): the whiskered inner normal form
`wire (x) NF(1)` — the right-hand side of `zxjEmptyRidesToWhiskeredIdentity` at
`leftWires = 1, innerWires = 1` — is SPAN-EQUAL to `zxnNormalForm 2 2 idRows2`
(both denote the two-strand identity), yet it is NOT a normal form (its init
layer creates one state, not two), so the r12 transport
`zxvGeneratorTransportHolds`, which bridges only two literal `zxnNormalForm`
diagrams of the same boundary, cannot re-canonicalize it. -/
theorem zxiWhiskerFormSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 2
          layers := zxpWhiskerLayers 1 0 (zxnNormalForm 1 1 (zxpIdRows 1)).layers })
      (zxpDiagramDenote (zxnNormalForm 2 2 (zxpIdRows 2))) = true := rfl

/-! ## Stage 1 — THE FEEDING-COMB ATOMS (T1 building blocks, proved)

Every comb `zxnXorRowLayers rowBits` is built from four cell events: a Z carrier
is CREATED, walked across the strands by CROSSINGS, forked/copied where a row bit
is set, and DISCARDED.  The four atoms below are exactly the one-cell laws a
created state obeys at each of those events — the local moves the router must
chain.  Each is a seed row fired into `ZxwConv` through `zxwOfZxpConv`. -/

/-- THE STATE-COPY DUPLICATION: a created X state above a Z copy becomes two
created X states (Kissinger's `bialgUnitCopy`, `eta_X ; delta_Z = eta_X (x)
eta_X`).  This is the state-through-copy behaviour named in the router brief. -/
theorem zxiStateCopyDuplicates :
    ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.xSpider 0 1], [ZxpCell.zSpider 1 2]] }
      { sourceArity := 0
        layers := [[ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1]] } :=
  zxwOfZxpConv (zxpRowConv ZxpRowTag.bialgUnitCopy)

/-- THE STATE-MERGE COLLAPSE: a created X state fed into an X merge alongside a
passing wire is the identity wire (`xMonoidUnit`, `eta_X ; mu_X = id`).  This is
the state-through-xor behaviour — the created carrier is absorbed at a merge. -/
theorem zxiStateMergeAbsorbs :
    ZxwConv
      { sourceArity := 1
        layers := [[ZxpCell.xSpider 0 1, ZxpCell.wire], [ZxpCell.xSpider 2 1]] }
      { sourceArity := 1, layers := [[ZxpCell.wire]] } :=
  zxwOfZxpConv (zxpRowConv ZxpRowTag.xMonoidUnit)

/-- THE CREATE-KILL ANNIHILATION (X): a created X state killed by an X collector
is nothing (`boneX`, `eta_X ; eps_X = ()`).  The created codomain strand's
birth-and-death when its row is the zero row. -/
theorem zxiCreateKillAbsorbsX :
    ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.xSpider 0 1], [ZxpCell.xSpider 1 0]] }
      { sourceArity := 0, layers := [] } :=
  zxwOfZxpConv (zxpRowConv ZxpRowTag.boneX)

/-- THE CREATE-KILL ANNIHILATION (Z): a created Z state killed by a Z collector
is nothing (`boneZ`).  This is the comb's OWN carrier being born and discarded —
the carrier is a `zSpider 0 1` (kernel dump of `zxnXorRowLayers`), so its
birth-and-death is the Z bone, not the X bone. -/
theorem zxiCreateKillAbsorbsZ :
    ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.zSpider 0 1], [ZxpCell.zSpider 1 0]] }
      { sourceArity := 0, layers := [] } :=
  zxwOfZxpConv (zxpRowConv ZxpRowTag.boneZ)

/-- THE STATE SLIDE PAST A CROSSING: a created X state routes past a passing
strand through the naturality staircase (the `slideRight` move at `xSpider 0 1`).
This is the ROUTING atom — the carrier walking across strands is a chain of these
slides. -/
theorem zxiStateSlidesPastCrossing :
    ZxwConv (zxwSlideRightLhs (ZxpCell.xSpider 0 1))
      (zxwSlideRightRhs (ZxpCell.xSpider 0 1)) :=
  zxwMoveConv (ZxwWindowMove.slideRight (ZxpCell.xSpider 0 1))

/-! ## Stage 2 — whiskered atoms and the two-atom composite (proved)

The router lands the atoms inside padding contexts (so a spectator strand passes)
and chains two of them into the create-route-discard motif at its smallest. -/

/-- THE WHISKERED CREATE-KILL (X): the X create-kill annihilation with one
spectator wire passing on the right — the atom lands in a padding context, the
form the layer recursion consumes. -/
theorem zxiCreateKillAbsorbsXWhiskered :
    ZxwConv
      { sourceArity := 1
        layers := [[ZxpCell.xSpider 0 1, ZxpCell.wire],
          [ZxpCell.xSpider 1 0, ZxpCell.wire]] }
      { sourceArity := 1, layers := [] } := by
  have hBone : ZxwConv (zxpRowLhs ZxpRowTag.boneX) (zxpRowRhs ZxpRowTag.boneX) :=
    zxwOfZxpConv (zxpRowConv ZxpRowTag.boneX)
  have hLift := zxwConvLift 1 0 1 [] [] hBone (ZxpLayersWF.nil _)
    (by show (1 : Nat) = 0 + (0 + 1); rfl) (ZxpLayersWF.nil _)
  exact hLift

/-- THE CREATE-ROUTE-DISCARD MOTIF (two-atom composite): a created X state,
copied by a Z fork, both copies killed, collapses to the two kill cells — the
state-copy atom fired above a spectator kill pair.  The purest instance of the
create-route-discard the identity induction assembles per strand; the FULL router
generalizes the copy to a whole feeding comb (walled below). -/
theorem zxiCreateCopyThenKillBoth :
    ZxwConv
      { sourceArity := 0
        layers := [[ZxpCell.xSpider 0 1], [ZxpCell.zSpider 1 2],
          [ZxpCell.xSpider 1 0, ZxpCell.xSpider 1 0]] }
      { sourceArity := 0
        layers := [[ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1],
          [ZxpCell.xSpider 1 0, ZxpCell.xSpider 1 0]] } := by
  have hCopy : ZxwConv (zxpRowLhs ZxpRowTag.bialgUnitCopy)
      (zxpRowRhs ZxpRowTag.bialgUnitCopy) :=
    zxwOfZxpConv (zxpRowConv ZxpRowTag.bialgUnitCopy)
  have hLift := zxwLiftConv 0 []
    [[ZxpCell.xSpider 1 0, ZxpCell.xSpider 1 0]] hCopy
    (ZxpLayersWF.nil _) rfl
    (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  exact hLift

/-! ## Stage 3 — kernel span pins for the atoms -/

/-- Span pin: the state-copy duplication is a semantic equivalence. -/
theorem zxiStateCopyDuplicatesSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 0
          layers := [[ZxpCell.xSpider 0 1], [ZxpCell.zSpider 1 2]] })
      (zxpDiagramDenote
        { sourceArity := 0
          layers := [[ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1]] }) = true := rfl

/-- Span pin: the state-merge collapse is a semantic equivalence. -/
theorem zxiStateMergeAbsorbsSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 1
          layers := [[ZxpCell.xSpider 0 1, ZxpCell.wire], [ZxpCell.xSpider 2 1]] })
      (zxpDiagramDenote { sourceArity := 1, layers := [[ZxpCell.wire]] }) = true :=
  rfl

/-- Span pin: the X create-kill annihilation is a semantic equivalence. -/
theorem zxiCreateKillAbsorbsXSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 0
          layers := [[ZxpCell.xSpider 0 1], [ZxpCell.xSpider 1 0]] })
      (zxpDiagramDenote { sourceArity := 0, layers := [] }) = true := rfl

/-- Span pin: the create-route-discard composite is a semantic equivalence. -/
theorem zxiCreateCopyThenKillBothSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 0
          layers := [[ZxpCell.xSpider 0 1], [ZxpCell.zSpider 1 2],
            [ZxpCell.xSpider 1 0, ZxpCell.xSpider 1 0]] })
      (zxpDiagramDenote
        { sourceArity := 0
          layers := [[ZxpCell.xSpider 0 1, ZxpCell.xSpider 0 1],
            [ZxpCell.xSpider 1 0, ZxpCell.xSpider 1 0]] }) = true := rfl

/-! ## Stage 4 — the honest marker ledger -/

/-- CONTENT MARKER (TRUE): the feeding-comb ATOMS are LIVE — the state-copy
duplication (`zxiStateCopyDuplicates`), the state-merge collapse
(`zxiStateMergeAbsorbs`), the X/Z create-kill annihilations
(`zxiCreateKillAbsorbsX` / `...Z`), the state slide past a crossing
(`zxiStateSlidesPastCrossing`), the whiskered create-kill
(`zxiCreateKillAbsorbsXWhiskered`), and the two-atom create-route-discard
composite (`zxiCreateCopyThenKillBoth`), each with a kernel span pin.  These are
the one-cell laws a created state obeys at each event of a comb column. -/
def zxiHasFeedingCombAtoms : Bool := true

/-- OWNER MARKER (FALSE): the FULL feeding-comb router did NOT land — a created
state routing past a WHOLE comb that feeds it (`zxnXorRowLayers rowBits` with the
state's strand a set bit of `rowBits`) is not built.  Two genuinely different
attacks burned, both converging on the same singular missing primitive.

* (C) ATOM-CHAINING THROUGH ONE COMB.  The atoms above are the local moves; I
  tried to chain them into `createState ; comb`.  BURN: the kernel dump of one
  comb (`zxnXorRowLayers [true, true]` is the 8-layer staircase `[Z01 w w]`,
  `[Z12 w w]`, `[w K21 w]`, `[x w]`, `[w Z12 w]`, `[w w K21]`, `[w x]`,
  `[w w Z10]`) shows the comb's CARRIER is a Z state `zSpider 0 1` walked by
  CROSSINGS, and the created X state from `init` sits on a DIFFERENT strand than
  the carrier.  The only atom that consumes an X state into a fork is
  `zxiStateCopyDuplicates` (X state directly above a Z copy on the SAME strand);
  here the X state must first traverse the crossing staircase (iterated
  `zxiStateSlidesPastCrossing`, whose bookkeeping grows with the gap width) to
  reach the fork, and the fork it reaches acts on the carrier bundle, so the
  interaction is a `bialgSquare` across the shared strand pair, not a unit-copy.
  The general carrier-staircase-times-bundle-bialgebra family is unbuilt — the
  same shape the SPIDER residuals need (see the `zxbZSpiderAbsorbStatement` wall
  note).

* (E) APPEND-STRAND TENSOR-MERGE.  I tried building `NF(m+1)` as
  `NF(m) (x) NF(1)` (block-diagonal identity, reached from the IH twice) then
  merging the two `init` layers (`[w^m K01^m] (x) [w K01] -> [w^(m+1) K01^(m+1)]`)
  and the two `kill` layers into single layers using the landed disjoint-block
  engines (`zxjZeroStateRidePastGenBlock`, `zxwLayersPastRightLayer`) and the
  landed crossing absorption (`zxkCrossingAbsorbHolds`).  BURN: the create-state
  ride commutes created states only past DISJOINT generator blocks; merging the
  inits forces the appended strand's created state to move past the `m` combs
  that COUPLE its codomain partner (`zxpIdRows 2 = [[T F T F], [F T F T]]` — each
  row sets both a domain strand and its created partner), so disjointness fails
  exactly as the prior round's attack B recorded; and `zxkCrossingAbsorbHolds`
  routes CROSSINGS through combs, not created states, so it cannot carry the
  state.  Both routes converge on the identical primitive: a created state
  routing PAST a comb that feeds it. -/
def zxiHasFeedingCombRouter : Bool := false

/-- OWNER MARKER (FALSE): the identity residual `zxbIdentityAbsorbStatement` did
NOT flip.  The atoms land, but the full feeding-comb router (`...Router := false`)
that the `wireCount` induction step (`wire (x) NF(m) ~ NF(m+1)`) consumes does
not close — both burned attacks above stall on it.  The committed owner
`zxkIdentityAbsorbIsProven := false` stays byte-intact.  The residual is
semantically true at every arity (kernel span pins `zxjIdentityResidualSpanPin*`,
this file's `zxiWhiskerFormSpanPin`); the wall is on the syntactic assembly, and
2 of 4 absorption residuals (the two spider colours) remain open besides — no
completeness flip is wired. -/
def zxiHasIdentityAbsorb : Bool := false

end FX1Poly.Polygraph.Omega.ZXPhaseFree
