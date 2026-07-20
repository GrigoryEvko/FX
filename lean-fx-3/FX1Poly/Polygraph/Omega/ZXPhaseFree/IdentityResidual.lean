import FX1Poly.Polygraph.Omega.ZXPhaseFree.AbsorptionInduction

/-! # Polygraph/Omega/ZXPhaseFree/IdentityResidual — THE CREATE-STATE RIDE
lands; the identity residual stays walled with a machine-checked gap

The absorption assembly (`zxbAbsorptionOfResiduals`) reduces phase-free
completeness to four named cell-level residuals; the crossing residual is now
inhabited repo-wide (`zxkCrossingAbsorbHolds`), leaving the two spider colours
and `zxbIdentityAbsorbStatement` (the empty diagram at every arity converts to
the normal form of its own denotation).  This round isolates the create-state
ride the identity induction was said to need and lands it as a reusable engine,
then records — with kernel evidence — exactly why the `wireCount` induction that
would consume it does not close.

* (i)  THE CREATE-STATE RIDE (`zxjZeroStateRidePastGenBlock`, PROVED): a block of
  created zero states on the right strands rides past a whole generator block on
  disjoint left strands — a direct instance of the committed disjoint-block
  engine `zxwLayersPastRightLayer` with the moving block chosen to be
  `zxnZeroStateCells`.  Because a created state has no input strands, the ride is
  automatic; the head layer of the left side is literally `zxnInitLayer`.  Fired
  at a literal instance with a kernel span pin.

* (ii) THE WHISKERED IDENTITY LIFT (`zxjEmptyRidesToWhiskeredIdentity`, PROVED
  CONDITIONAL): given the identity residual at `innerWires`, the empty diagram at
  `leftWires + innerWires` converts to the LEFT-WHISKERED normal form of the
  inner identity.  This is the horizontal half of the `wireCount` induction — the
  half that goes through — and it names precisely the residual that does not
  (the whiskered normal form is NOT itself `zxnNormalForm (leftWires+innerWires)
  (leftWires+innerWires) G` for any `G`, so the r12 transport cannot re-canonicalize it).

* (iii) THE IDENTITY RESIDUAL STAYS WALLED (`zxjHasIdentityAbsorb := false`), with
  two genuinely different burned attacks recorded on the marker docstring and a
  fresh soundness pin at `wireCount = 3`.  The committed owner
  `zxkIdentityAbsorbIsProven := false` stays byte-intact.

Raw Lean 4 + Init only; zero-axiom; structural only; no `List.append`, no `Int`,
no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive scrutinees. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 1 — THE CREATE-STATE RIDE (T1, proved) -/

/-- THE CREATE-STATE RIDE (over `ZxeConv`): a block of `freshCount` created zero
states on the right strands rides past a whole generator block on `strandWidth`
disjoint left strands.  The left side runs the generator block first (each of its
layers whiskered by `freshCount` right wires) below the `zxnInitLayer` that both
passes the domain and creates the fresh states; the right side runs the block
first, then creates the states.  A direct instance of `zxwLayersPastRightLayer`
with the moving block chosen to be `zxnZeroStateCells freshCount` — a created
state has no input strands, so disjointness from the block is automatic. -/
theorem zxjZeroStateRidePastGenBlock (freshCount strandWidth : Nat)
    (generatorRows : List (List Bool))
    (hAllRows : ZxpAllWidth strandWidth generatorRows) :
    ZxeConv
      { sourceArity := strandWidth
        layers := zxnInitLayer strandWidth freshCount
          :: zxpWhiskerLayers 0 freshCount
              (zxnGeneratorBlockLayers generatorRows) }
      { sourceArity := strandWidth
        layers := zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
          [zxnInitLayer strandWidth freshCount] } := by
  have hRide := zxwLayersPastRightLayer (zxnZeroStateCells freshCount)
    (zxnGeneratorBlockLayers generatorRows) strandWidth
    (zxnGeneratorBlockLayersWF generatorRows strandWidth hAllRows)
  rw [zxnZeroStateCellsDomArity, zxnZeroStateCellsCodArity,
    zxpWhiskerLayersZero (zxnGeneratorBlockLayers generatorRows),
    zxnGeneratorBlockLayersCodArity generatorRows strandWidth hAllRows,
    Nat.add_zero] at hRide
  exact hRide

/-- THE CREATE-STATE RIDE (over `ZxwConv`): the same ride embedded into the
wiring-extended congruence — the reusable form the induction consumes. -/
theorem zxjZeroStateRidePastGenBlockConv (freshCount strandWidth : Nat)
    (generatorRows : List (List Bool))
    (hAllRows : ZxpAllWidth strandWidth generatorRows) :
    ZxwConv
      { sourceArity := strandWidth
        layers := zxnInitLayer strandWidth freshCount
          :: zxpWhiskerLayers 0 freshCount
              (zxnGeneratorBlockLayers generatorRows) }
      { sourceArity := strandWidth
        layers := zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
          [zxnInitLayer strandWidth freshCount] } :=
  zxwOfZxeConv
    (zxjZeroStateRidePastGenBlock freshCount strandWidth generatorRows hAllRows)

/-! ## Stage 2 — THE WHISKERED IDENTITY LIFT (T2 horizontal half, conditional) -/

/-- THE WHISKERED IDENTITY LIFT: given the identity residual at `innerWires`, the
empty diagram at `leftWires + innerWires` converts to the left-whiskered normal
form of the inner identity.  A specialization of the pad-lifting congruence
`zxwConvLift` with `beforeLayers`/`afterLayers` empty, `rightWires = 0`.  This is
the half of the `wireCount` induction that goes through; the surviving residual
is that the right-hand side is a WHISKERED normal form, not a normal form of the
outer boundary, so no committed transport re-canonicalizes it (see the wall
marker below). -/
theorem zxjEmptyRidesToWhiskeredIdentity (leftWires innerWires : Nat)
    (hInner : ZxwConv { sourceArity := innerWires, layers := [] }
      (zxnNormalForm innerWires innerWires
        (zxpDiagramDenote { sourceArity := innerWires, layers := [] }))) :
    ZxwConv { sourceArity := leftWires + innerWires, layers := [] }
      { sourceArity := leftWires + innerWires
        layers := zxpWhiskerLayers leftWires 0
          (zxnNormalForm innerWires innerWires
            (zxpDiagramDenote { sourceArity := innerWires, layers := [] })).layers } := by
  have hLift := zxwConvLift (leftWires + innerWires) leftWires 0 [] [] hInner
    (ZxpLayersWF.nil _)
    (by show leftWires + innerWires = leftWires + (innerWires + 0)
        rw [Nat.add_zero])
    (ZxpLayersWF.nil _)
  dsimp only [zxpPadDiagram] at hLift
  rw [zxpCatLayersNilRight (zxpWhiskerLayers leftWires 0
    (zxnNormalForm innerWires innerWires
      (zxpDiagramDenote { sourceArity := innerWires, layers := [] })).layers)] at hLift
  exact hLift

/-! ## Stage 3 — fires and kernel span pins -/

/-- FIRE: the create-state ride at a literal instance — one fresh state rides
past the one-generator block `[[true]]` on one strand. -/
theorem zxjZeroStateRideFire :
    ZxwConv
      { sourceArity := 1
        layers := zxnInitLayer 1 1
          :: zxpWhiskerLayers 0 1 (zxnGeneratorBlockLayers [[true]]) }
      { sourceArity := 1
        layers := zxpCatLayers (zxnGeneratorBlockLayers [[true]])
          [zxnInitLayer 1 1] } :=
  zxjZeroStateRidePastGenBlockConv 1 1 [[true]]
    (ZxpAllWidth.cons rfl ZxpAllWidth.nil)

/-- Kernel span pin for the create-state ride fire: both sides denote the same
span (the ride is a semantic equivalence). -/
theorem zxjZeroStateRideFireSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 1
          layers := zxnInitLayer 1 1
            :: zxpWhiskerLayers 0 1 (zxnGeneratorBlockLayers [[true]]) })
      (zxpDiagramDenote
        { sourceArity := 1
          layers := zxpCatLayers (zxnGeneratorBlockLayers [[true]])
            [zxnInitLayer 1 1] }) = true := rfl

/-- Soundness pin for the identity residual at `wireCount = 1`: the empty one-wire
diagram and the normal form of its own identity denotation denote the same span. -/
theorem zxjIdentityResidualSpanPinOne :
    zxpSpanEqB (zxpDiagramDenote { sourceArity := 1, layers := [] })
      (zxpDiagramDenote (zxnNormalForm 1 1
        (zxpDiagramDenote { sourceArity := 1, layers := [] }))) = true := rfl

/-- Soundness pin for the identity residual at `wireCount = 2`. -/
theorem zxjIdentityResidualSpanPinTwo :
    zxpSpanEqB (zxpDiagramDenote { sourceArity := 2, layers := [] })
      (zxpDiagramDenote (zxnNormalForm 2 2
        (zxpDiagramDenote { sourceArity := 2, layers := [] }))) = true := rfl

/-- Soundness pin for the identity residual at `wireCount = 3` (fresh): the empty
three-wire diagram and the normal form of the interleaved three-strand identity
generator denote the same span — the certificate a landed induction step would
consume at the `n = 3` boundary. -/
theorem zxjIdentityResidualSpanPinThree :
    zxpSpanEqB (zxpDiagramDenote { sourceArity := 3, layers := [] })
      (zxpDiagramDenote (zxnNormalForm 3 3
        (zxpDiagramDenote { sourceArity := 3, layers := [] }))) = true := rfl

/-! ## Stage 4 — the honest marker ledger -/

/-- CONTENT MARKER (TRUE): the create-state ride is LIVE — a block of created zero
states rides past a whole generator block on disjoint strands
(`zxjZeroStateRidePastGenBlock` / `...Conv`), and the horizontal half of the
`wireCount` identity induction is proved conditional
(`zxjEmptyRidesToWhiskeredIdentity`).  Both are reusable engines with a literal
fire and a kernel span pin. -/
def zxjHasCreateStateRide : Bool := true

/-- OWNER MARKER (FALSE): the identity residual `zxbIdentityAbsorbStatement` did
NOT flip this round.  The create-state ride lands, but the `wireCount` induction
that would consume it does not close.  The committed owner
`zxkIdentityAbsorbIsProven := false` stays byte-intact.

Two genuinely different attacks burned:

* (A) WHISKER THE INDUCTION HYPOTHESIS (via `zxwConvLift`).
  `zxjEmptyRidesToWhiskeredIdentity` lifts the identity residual at `innerWires`
  to `ZxwConv (empty (leftWires + innerWires)) (whisker(leftWires,0)(NF ...))` —
  the empty outer diagram reaches the LEFT-WHISKERED inner normal form.  But the
  right-hand side is NOT a normal form of the outer boundary: kernel `#eval` of
  `whisker(1,0)(NF 1 1 idRows1)` shows its init layer is `[I I x01]`
  (= `zxnInitLayer 2 1`, one created state, cod arity 1), whereas
  `zxnNormalForm 2 2 idRows2` has init `[I I x01 x01]` (`zxnInitLayer 2 2`, two
  created states, cod arity 2).  So `whisker(1,0)(NF m)` is `wire ⊗ NF m`, not
  `zxnNormalForm (leftWires+m) (leftWires+m) G` for any `G`; the r12 transport
  `zxvGeneratorTransportHolds` only bridges two normal forms of the SAME boundary,
  so it cannot re-canonicalize the whiskered form.  The surviving step is
  `wire ⊗ NF m ~ NF (m+1)` — the one-strand create-route-discard insertion plus
  the re-interleaving of the outer init/kill — which is unbuilt.

* (B) THE DISJOINT CREATE-STATE RIDE INTO THE INDUCTION.
  `zxjZeroStateRidePastGenBlock` commutes created states past a generator block
  ONLY on disjoint strands.  But `zxpIdRows (m+1)` couples EVERY strand: row `i`
  is `e_i ++ e_i` (kernel `#eval` at `n = 2` = `[[true,false,true,false],
  [false,true,false,true]]`), so the added strand's created state is fed by its
  own comb `e_0 ++ e_0` (coupling domain strand `0` with codomain strand `m+1`)
  and is never disjoint from that comb.  The ride the induction actually needs is
  a created state routing PAST a comb that FEEDS it — a crossing-style
  column-routing engine, a separate arc, unbuilt here.

Fresh soundness pin `zxjIdentityResidualSpanPinThree` certifies the residual is
semantically true at `wireCount = 3`; the wall is on the syntactic assembly. -/
def zxjHasIdentityAbsorb : Bool := false

end FX1Poly.Polygraph.Omega.ZXPhaseFree
