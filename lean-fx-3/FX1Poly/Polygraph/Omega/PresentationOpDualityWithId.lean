import FX1Poly.Polygraph.Omega.MonadCoherentPresentation
import FX1Poly.Polygraph.Omega.IdempotentSemigroupDemonstrator

/-! # Polygraph/Omega/PresentationOpDualityWithId — the op-dual transport for the Omega-lane Squier
presentations (WP-SQUIER r3, the #2082 op-dual round)

★ **The op involution on the `OmegaComputad` / `CellExpr` presentation carrier, and the GENERIC transport
that ships the two genuine op-dual walkers (the walking comonad, the idempotent comonad) from their shipped
duals.**  Where the Table lane already ships the whole op-involution over its `RawTwoCellExpr` /
`SaturatedConvOver` substrate (`Table/PresentationOpDuality.lean`), the FOUR shipped coherent presentations
of the WP-SQUIER family live on the DISJOINT Omega lane (`OmegaComputad` / `CellExpr` /
`SaturatedConvOverWithId`), which had NO `op` involution.  This file builds it, mirroring the Table-lane
machine but adapted to the unified `CellExpr` (where the boundaries of a generator are CELLS, not a separate
`ModalityPath`).

## The op is COOP (reverse cells + flip vcomp order + SWAP whisker kinds)

The Table lane's carrier keeps 1-cells in a separate `ModalityPath`, so its `opCell` reverses only the
2-cells and leaves the paths fixed.  The Omega `CellExpr.gen label source target` carries its source / target
`dim`-cells INSIDE the carrier, so `op` must recurse into them.  The unique structural reversal that makes the
boundary-commutation lemma `boundarySource (op c) = op (boundaryTarget c)` hold at EVERY dimension is the
COOP-style involution:

  * `op (gen label source target) = gen label (op target) (op source)` — swap the boundary pair, recurse;
  * `op (id cell) = id (op cell)`;
  * `op (vcomp left right) = vcomp (op right) (op left)` — the vertical composite ORDER-FLIPS
    (contravariance of reversal);
  * `op (whiskerLeft w inner) = whiskerRight (op inner) (op w)` and
    `op (whiskerRight inner w) = whiskerLeft (op w) (op inner)` — the two whiskerings SWAP KIND.

The whisker-kind swap is exactly what aligns the whisker boundary `vcomp w (boundarySource inner)` (a left
whisker's source) with `vcomp (boundaryTarget (op inner)) (op w)` (a right whisker's target) after the
vcomp order-flip — the order-flip on `vcomp` and the kind-swap on whiskerings cancel to give boundary
commutation on the nose (`opBoundaryCommutes_all`).  On the shipped computads the 1-cell generators
(`s` / `t` / `e`, source = target = the single object) and their symmetric words (`t.t`, `e.e`) are op-FIXED,
so the comonad's rule is exactly the monad's `mu : t.t => t` read backwards as `delta : t => t.t`.

## What ships (B1 the transport, B2 the two genuine op-duals)

  * **`opCellExpr`** + **`opCellExpr_involutive`** — the cell involution (structural, propext-clean;
    constant `genLabel` on every shipped computad, so no `Nat`-match leak).
  * **`opBoundaryCommutes_all`** / **`opCellExpr_boundarySource`** / **`opCellExpr_boundaryTarget`** — the
    boundary-commutation lemma (`op` swaps source and target boundaries), by plain structural induction.
  * **`opStrictAxiomStable`** — op of each of the EIGHT `StrictAxiomRel` rows is a `SaturatedConvOverWithId`
    over the strict laws: `vcompUnitLeft <-> vcompUnitRight`, `vcompAssoc -> symm` of the reversed assoc,
    the whisker-unit / whisker-functorial laws swap left / right, and the **Godement interchange is op-stable
    ON THE NOSE** (the Omega `StrictAxiomRel.interchange` is already the symmetric cast-free middle-four, so
    op of it is the interchange row at the swapped-op'd arguments — no Godement-commute derivation needed,
    cleaner than the Table lane).
  * **`opCellRelOver`** + **`opConvWithId`** — the GENERIC transport of a whole `SaturatedConvOverWithId`
    derivation through `op` (via the universal property `recInto` into the op'd absorbing congruence, the two
    `vcompCongr` / whisker congruences swapping), and **`opCellRelOverStrictAxiom_derivable`** confirming the
    op'd strict part coincides with the actual strict laws (so the comonad shares the strict omega laws with
    the monad).
  * **`opCriticalPairResolved`** — the generic per-pair PEAK<->VALLEY swap: an op'd resolution's peak join is
    the original valley join transported, its valley the original peak.
  * **`comonadWalkerCoherentPresentation`** (= op(monad), 5 pairs) and
    **`idempotentComonadWalkerCoherentPresentation`** (= op(idempotent semigroup), 1 pair) — the two GENUINE
    op-dual coherent presentations, each with its least-congruence universal property fired.

## The honest scope (presentation transport, NOT convergence transport)

The r3 transport is about the PRESENTATION DATA, never about convergence.  An op-ed convergent system need
not be convergent — the reversed rules `id => ss`, `e => e.e`, `id => t`, `t => t.t` are all
NON-TERMINATING (identities grow).  But the shipped datum at every walker is the FRAGMENT scope: critical-pair
rows, generating 3-cells, peak / valley joins over `SaturatedConvOverWithId`, the per-pair resolution, the
least-congruence UP.  Every one of these is a `SaturatedConvOverWithId` derivation — `symm` is a constructor,
the strict laws are op-stable rows, the critical rows transport by the involutive row bridge — so `op`
reverses each derivation mechanically and the joins transport with ZERO termination / convergence input.
This is exactly the H2-WALKERS precedent (`Homology/PresentationOpDualityHomology.lean`, NAMED here, not
imported): there the homology transported through op-duality while convergence did not need to; here the
coherent-presentation DATA transports while convergence does not need to.  The honest claim r3 ships is *"the
op-dual walkers have Omega-lane coherent presentations at the joinable-modulo-strict fragment scope,
transported generically,"* NOT *"the op-dual rewriting systems are convergent."*

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit
twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The op involution on cells (COOP: reverse cells, flip vcomp, swap whisker kinds) -/

/-- ★ **`op` on a free cell** — the cell involution the Omega lane lacked.  Boundaries of a generator swap
(a `source => target` generator becomes a `target => source` one, both boundaries recursively op'd); the
vertical composite ORDER-FLIPS; the two whiskerings SWAP KIND (a left whisker becomes a right whisker of the
op'd factors, and conversely); identities and modes are payload-preserved.  Structural recursion, constant
return-constructor per case — propext-clean (mirrors `cellSize` / `toSkeleton`). -/
def opCellExpr {computad : OmegaComputad} :
    {dim : Nat} → CellExpr computad dim → CellExpr computad dim
  | _, .ofMode mode => CellExpr.ofMode mode
  | _, .gen label source target => CellExpr.gen label (opCellExpr target) (opCellExpr source)
  | _, .id cell => CellExpr.id (opCellExpr cell)
  | _, .vcomp left right => CellExpr.vcomp (opCellExpr right) (opCellExpr left)
  | _, .whiskerLeft whiskeringCell inner =>
      CellExpr.whiskerRight (opCellExpr inner) (opCellExpr whiskeringCell)
  | _, .whiskerRight inner whiskeringCell =>
      CellExpr.whiskerLeft (opCellExpr whiskeringCell) (opCellExpr inner)

/-- ★ **`op` is an involution on free cells** — `op (op cell) = cell`, by structural induction (the two
`vcomp` order-flips cancel, the two whisker-kind swaps cancel, generators / identities / modes are fixed). -/
theorem opCellExpr_involutive {computad : OmegaComputad} {dim : Nat}
    (cell : CellExpr computad dim) : opCellExpr (opCellExpr cell) = cell := by
  induction cell with
  | ofMode _ => rfl
  | gen label source target ihSource ihTarget =>
      dsimp only [opCellExpr]; rw [ihSource, ihTarget]
  | id inner ih => dsimp only [opCellExpr]; rw [ih]
  | vcomp left right ihLeft ihRight => dsimp only [opCellExpr]; rw [ihLeft, ihRight]
  | whiskerLeft whiskeringCell inner ihWhisker ihInner =>
      dsimp only [opCellExpr]; rw [ihWhisker, ihInner]
  | whiskerRight inner whiskeringCell ihInner ihWhisker =>
      dsimp only [opCellExpr]; rw [ihInner, ihWhisker]

/-! ## The boundary-commutation lemma (`op` swaps source and target boundaries) -/

/-- The boundary-commutation STATEMENT, guarded by dimension (`True` at dimension 0 where there is no
boundary; the two swap equations at a successor dimension).  A `Nat`-recursive `Prop` matched inside the
proof, mirroring `GlobularLegs` in `Carrier.lean` — propext-clean. -/
def OpBoundaryCommutes {computad : OmegaComputad} :
    {dim : Nat} → CellExpr computad dim → Prop
  | 0, _ => True
  | _ + 1, cell =>
      opCellExpr (boundarySource cell) = boundaryTarget (opCellExpr cell) ∧
      opCellExpr (boundaryTarget cell) = boundarySource (opCellExpr cell)

/-- ★ **`op` swaps source and target boundaries at every dimension** — by plain structural induction.  The
`gen` / `id` cases are `rfl`; the `vcomp` case rides the left / right sub-hypotheses across the order-flip;
the two whisker cases ride the inner hypothesis across the kind-swap-plus-order-flip cancellation. -/
theorem opBoundaryCommutes_all {computad : OmegaComputad} {dim : Nat}
    (cell : CellExpr computad dim) : OpBoundaryCommutes cell := by
  induction cell with
  | ofMode _ => exact True.intro
  | gen label source target _ _ => exact ⟨rfl, rfl⟩
  | id inner _ => exact ⟨rfl, rfl⟩
  | vcomp left right ihLeft ihRight => exact ⟨ihLeft.1, ihRight.2⟩
  | whiskerLeft whiskeringCell inner _ ihInner =>
      refine ⟨?_, ?_⟩
      · show CellExpr.vcomp (opCellExpr (boundarySource inner)) (opCellExpr whiskeringCell)
             = CellExpr.vcomp (boundaryTarget (opCellExpr inner)) (opCellExpr whiskeringCell)
        rw [ihInner.1]
      · show CellExpr.vcomp (opCellExpr (boundaryTarget inner)) (opCellExpr whiskeringCell)
             = CellExpr.vcomp (boundarySource (opCellExpr inner)) (opCellExpr whiskeringCell)
        rw [ihInner.2]
  | whiskerRight inner whiskeringCell ihInner _ =>
      refine ⟨?_, ?_⟩
      · show CellExpr.vcomp (opCellExpr whiskeringCell) (opCellExpr (boundarySource inner))
             = CellExpr.vcomp (opCellExpr whiskeringCell) (boundaryTarget (opCellExpr inner))
        rw [ihInner.1]
      · show CellExpr.vcomp (opCellExpr whiskeringCell) (opCellExpr (boundaryTarget inner))
             = CellExpr.vcomp (opCellExpr whiskeringCell) (boundarySource (opCellExpr inner))
        rw [ihInner.2]

/-- `op` of a source boundary is the target boundary of the op'd cell. -/
theorem opCellExpr_boundarySource {computad : OmegaComputad} {dim : Nat}
    (cell : CellExpr computad (dim + 1)) :
    opCellExpr (boundarySource cell) = boundaryTarget (opCellExpr cell) :=
  (opBoundaryCommutes_all cell).1

/-- `op` of a target boundary is the source boundary of the op'd cell. -/
theorem opCellExpr_boundaryTarget {computad : OmegaComputad} {dim : Nat}
    (cell : CellExpr computad (dim + 1)) :
    opCellExpr (boundaryTarget cell) = boundarySource (opCellExpr cell) :=
  (opBoundaryCommutes_all cell).2

/-! ## Op-stability of the strict omega laws (the genuine coherence, interchange on the nose) -/

/-- ★ **The strict omega laws are op-stable** — `op` of each of the EIGHT `StrictAxiomRel` rows is a
`SaturatedConvOverWithId` over the strict laws.  `vcompUnitLeft <-> vcompUnitRight`, `vcompAssoc -> symm` of
the assoc at reversed-op'd arguments, `whiskerLeftUnit <-> whiskerRightUnit`, `whiskerLeftFunctorial <->
whiskerRightFunctorial`, and — the genuine coherence — the **Godement interchange transports ON THE NOSE**:
`op` sends the interchange row to the interchange row at the swapped-op'd arguments (the Omega interchange is
already the symmetric cast-free middle-four, so no Godement-commute derivation is needed, unlike the Table
lane).  The boundary-mentioning rows (`vcompUnitLeft` / `vcompUnitRight` / `interchange`) ride the
boundary-commutation lemma. -/
theorem opStrictAxiomStable {computad : OmegaComputad} {dim : Nat}
    {cellA cellB : CellExpr computad dim} (row : StrictAxiomRel computad cellA cellB) :
    SaturatedConvOverWithId computad (StrictAxiomRel computad) (opCellExpr cellA) (opCellExpr cellB) := by
  cases row with
  | vcompAssoc cellX cellY cellZ =>
      exact SaturatedConvOverWithId.symm
        (SaturatedConvOverWithId.ofRelation
          (StrictAxiomRel.vcompAssoc (opCellExpr cellZ) (opCellExpr cellY) (opCellExpr cellX)))
  | vcompUnitLeft cellX =>
      dsimp only [opCellExpr]
      rw [opCellExpr_boundarySource cellX]
      exact SaturatedConvOverWithId.ofRelation (StrictAxiomRel.vcompUnitRight (opCellExpr cellX))
  | vcompUnitRight cellX =>
      dsimp only [opCellExpr]
      rw [opCellExpr_boundaryTarget cellX]
      exact SaturatedConvOverWithId.ofRelation (StrictAxiomRel.vcompUnitLeft (opCellExpr cellX))
  | whiskerLeftUnit whiskeringCell innerCell =>
      exact SaturatedConvOverWithId.ofRelation
        (StrictAxiomRel.whiskerRightUnit (opCellExpr innerCell) (opCellExpr whiskeringCell))
  | whiskerRightUnit innerCell whiskeringCell =>
      exact SaturatedConvOverWithId.ofRelation
        (StrictAxiomRel.whiskerLeftUnit (opCellExpr whiskeringCell) (opCellExpr innerCell))
  | whiskerLeftFunctorial whiskeringCell cellBeta cellGamma =>
      exact SaturatedConvOverWithId.ofRelation
        (StrictAxiomRel.whiskerRightFunctorial (opCellExpr cellGamma) (opCellExpr cellBeta)
          (opCellExpr whiskeringCell))
  | whiskerRightFunctorial cellAlpha cellBeta whiskeringCell =>
      exact SaturatedConvOverWithId.ofRelation
        (StrictAxiomRel.whiskerLeftFunctorial (opCellExpr whiskeringCell) (opCellExpr cellBeta)
          (opCellExpr cellAlpha))
  | interchange cellAlpha cellBeta =>
      dsimp only [opCellExpr]
      rw [opCellExpr_boundaryTarget cellAlpha, opCellExpr_boundarySource cellBeta,
        opCellExpr_boundarySource cellAlpha, opCellExpr_boundaryTarget cellBeta]
      exact SaturatedConvOverWithId.ofRelation
        (StrictAxiomRel.interchange (opCellExpr cellBeta) (opCellExpr cellAlpha))
  | whiskerAssocLeft whiskP whiskQ inner =>
      exact SaturatedConvOverWithId.ofRelation
        (StrictAxiomRel.whiskerAssocRight (opCellExpr inner) (opCellExpr whiskQ) (opCellExpr whiskP))
  | whiskerAssocRight inner whiskP whiskQ =>
      exact SaturatedConvOverWithId.ofRelation
        (StrictAxiomRel.whiskerAssocLeft (opCellExpr whiskQ) (opCellExpr whiskP) (opCellExpr inner))
  | whiskerLeftRightCommute whiskP inner whiskQ =>
      exact SaturatedConvOverWithId.symm
        (SaturatedConvOverWithId.ofRelation
          (StrictAxiomRel.whiskerLeftRightCommute (opCellExpr whiskQ) (opCellExpr inner)
            (opCellExpr whiskP)))

/-! ## The op'd relation and the generic convertibility transport -/

/-- **`op` on a law relation** — pull each argument back through `opCellExpr`.  The op-dual presentation's
law relation is `opCellRelOver` of its shipped dual's. -/
def opCellRelOver {computad : OmegaComputad} (baseRel : CellRelOver computad) : CellRelOver computad :=
  fun cellX cellY => baseRel (opCellExpr cellX) (opCellExpr cellY)

/-- The row bridge: a base row reflects EXACTLY into the `opCellRelOver` of its op'd cells, and back — by the
`op` involutivity on the two cells. -/
theorem opCellRelOver_involutive {computad : OmegaComputad} (baseRel : CellRelOver computad) {dim : Nat}
    (cellX cellY : CellExpr computad dim) :
    opCellRelOver baseRel (opCellExpr cellX) (opCellExpr cellY) ↔ baseRel cellX cellY := by
  unfold opCellRelOver
  rw [opCellExpr_involutive, opCellExpr_involutive]

/-- The forward congruence: the base saturated congruence maps into the `op`'d saturated conv (via the
universal property `recInto`).  The two `vcompCongr` arms SWAP, the two whisker congruences SWAP KIND (a left
whisker congruence becomes a right whisker congruence of the op'd factors), the whisker-1-cell congruences
SWAP KIND, `idCongr` maps, `ofRelation` rides the involutive row bridge, `refl` / `symm` / `trans` map. -/
def opDualityForwardCongruenceWithId {computad : OmegaComputad} (baseRel : CellRelOver computad) :
    IsSaturatedCongruenceWithId computad baseRel
      (fun cellX cellY => SaturatedConvOverWithId computad (opCellRelOver baseRel)
        (opCellExpr cellX) (opCellExpr cellY)) where
  ofRelation row := SaturatedConvOverWithId.ofRelation ((opCellRelOver_involutive baseRel _ _).mpr row)
  vcompCongrLeft {_ _ _ cellBeta} ih := SaturatedConvOverWithId.vcompCongrRight (opCellExpr cellBeta) ih
  vcompCongrRight {_ cellAlpha _ _} ih := SaturatedConvOverWithId.vcompCongrLeft (opCellExpr cellAlpha) ih
  whiskerLeftCongr {_ whiskeringCell _ _} ih :=
    SaturatedConvOverWithId.whiskerRightCongr (opCellExpr whiskeringCell) ih
  whiskerRightCongr {_ _ _ whiskeringCell} ih :=
    SaturatedConvOverWithId.whiskerLeftCongr (opCellExpr whiskeringCell) ih
  idCongr ih := SaturatedConvOverWithId.idCongr ih
  whiskerLeftWhiskerCongr {_ _ _ innerCell} ih :=
    SaturatedConvOverWithId.whiskerRightWhiskerCongr (opCellExpr innerCell) ih
  whiskerRightWhiskerCongr {_ innerCell _ _} ih :=
    SaturatedConvOverWithId.whiskerLeftWhiskerCongr (opCellExpr innerCell) ih
  refl cell := SaturatedConvOverWithId.refl (opCellExpr cell)
  symm ih := SaturatedConvOverWithId.symm ih
  trans ihLeft ihRight := SaturatedConvOverWithId.trans ihLeft ihRight

/-- ★ **The generic convertibility transport under `op`** — a whole `SaturatedConvOverWithId` derivation over
`baseRel` maps to a derivation over `opCellRelOver baseRel` on the op'd cells.  This is the machine every
op-dual walker instantiates: the shipped dual's derivations transport mechanically. -/
theorem opConvWithId {computad : OmegaComputad} {baseRel : CellRelOver computad} {dim : Nat}
    {cellA cellB : CellExpr computad dim}
    (conv : SaturatedConvOverWithId computad baseRel cellA cellB) :
    SaturatedConvOverWithId computad (opCellRelOver baseRel) (opCellExpr cellA) (opCellExpr cellB) :=
  SaturatedConvOverWithId.recInto (opDualityForwardCongruenceWithId baseRel) conv

/-- ★ **The op'd strict part coincides with the strict laws** — a row of `opCellRelOver (StrictAxiomRel)` is
`SaturatedConvOverWithId`-derivable over the actual `StrictAxiomRel` (via `opStrictAxiomStable` + `op`
involutivity).  So the op-dual walker SHARES the strict omega laws with its dual: the comonad's strict part
is the monad's, not a genuinely different relation. -/
theorem opCellRelOverStrictAxiom_derivable {computad : OmegaComputad} {dim : Nat}
    {cellX cellY : CellExpr computad dim}
    (row : opCellRelOver (StrictAxiomRel computad) cellX cellY) :
    SaturatedConvOverWithId computad (StrictAxiomRel computad) cellX cellY := by
  have transported := opStrictAxiomStable row
  rw [opCellExpr_involutive, opCellExpr_involutive] at transported
  exact transported

/-! ## The generic critical-pair resolution and its peak<->valley op-swap -/

/-- A **coherent resolution** of one critical pair over an arbitrary base relation — the shape the four
shipped walker resolutions (`MonadCriticalPairResolved`, `IdempotentSemigroupCriticalPairResolved`,
`InvolutionCoherentResolution`) all take: the two leg SOURCES convertible (peak), the two legs convertible
(the generating 3-cell), the two leg TARGETS convertible (valley). -/
structure CriticalPairResolvedOver (computad : OmegaComputad) (baseRel : CellRelOver computad) {d : Nat}
    (leftLeg rightLeg : CellExpr computad (d + 1)) : Prop where
  /-- The two leg SOURCES are convertible (the peak join). -/
  peakJoined : SaturatedConvOverWithId computad baseRel
    (boundarySource leftLeg) (boundarySource rightLeg)
  /-- The two legs are convertible (the generating 3-cell). -/
  legsConvertible : SaturatedConvOverWithId computad baseRel leftLeg rightLeg
  /-- The two leg TARGETS are convertible (the valley join). -/
  valleyJoined : SaturatedConvOverWithId computad baseRel
    (boundaryTarget leftLeg) (boundaryTarget rightLeg)

/-- ★ **The generic op-swap of a resolution (PEAK <-> VALLEY).**  Op of a coherent resolution is a coherent
resolution of the op'd legs over the op'd relation, with the peak and valley SWAPPED: the op'd peak join is
the original VALLEY join transported (the op'd legs' sources are the original targets, by boundary
commutation), and the op'd valley join is the original PEAK.  The whole per-pair resolution transports with
one generic lemma — the joins are NOT re-drawn per walker. -/
theorem opCriticalPairResolved {computad : OmegaComputad} {baseRel : CellRelOver computad} {d : Nat}
    {leftLeg rightLeg : CellExpr computad (d + 1)}
    (resolved : CriticalPairResolvedOver computad baseRel leftLeg rightLeg) :
    CriticalPairResolvedOver computad (opCellRelOver baseRel)
      (opCellExpr leftLeg) (opCellExpr rightLeg) where
  peakJoined := by
    have transported := opConvWithId resolved.valleyJoined
    rw [opCellExpr_boundaryTarget leftLeg, opCellExpr_boundaryTarget rightLeg] at transported
    exact transported
  legsConvertible := opConvWithId resolved.legsConvertible
  valleyJoined := by
    have transported := opConvWithId resolved.peakJoined
    rw [opCellExpr_boundarySource leftLeg, opCellExpr_boundarySource rightLeg] at transported
    exact transported

/-! ## B2 — the walking comonad = op(monad), five op-dual critical pairs -/

/-- A shipped monad resolution, re-read as a `CriticalPairResolvedOver` over the monad base relation (same
three fields). -/
def monadResolvedToOver {d : Nat} {leftLeg rightLeg : CellExpr monadOmegaComputad (d + 1)}
    (resolved : MonadCriticalPairResolved leftLeg rightLeg) :
    CriticalPairResolvedOver monadOmegaComputad monadOmegaBaseRel leftLeg rightLeg :=
  ⟨resolved.peakJoined, resolved.legsConvertible, resolved.valleyJoined⟩

/-- The op-dual of the `unitUnit` pair — the walking comonad's `counitCounit` critical pair, resolved
(peak <-> valley swapped from the monad's). -/
theorem comonadOmegaUnitUnitResolved :
    CriticalPairResolvedOver monadOmegaComputad (opCellRelOver monadOmegaBaseRel)
      (opCellExpr monadOmegaUnitUnitLeftLeg) (opCellExpr monadOmegaUnitUnitRightLeg) :=
  opCriticalPairResolved (monadResolvedToOver monadOmegaUnitUnitResolved)

/-- The op-dual of the `leftUnitAssoc` pair. -/
theorem comonadOmegaLeftUnitAssocResolved :
    CriticalPairResolvedOver monadOmegaComputad (opCellRelOver monadOmegaBaseRel)
      (opCellExpr monadOmegaLeftUnitAssocLeftLeg) (opCellExpr monadOmegaLeftUnitAssocRightLeg) :=
  opCriticalPairResolved (monadResolvedToOver monadOmegaLeftUnitAssocResolved)

/-- The op-dual of the `rightUnitAssoc` pair (the richest — both boundaries join modulo strict). -/
theorem comonadOmegaRightUnitAssocResolved :
    CriticalPairResolvedOver monadOmegaComputad (opCellRelOver monadOmegaBaseRel)
      (opCellExpr monadOmegaRightUnitAssocLeftLeg) (opCellExpr monadOmegaRightUnitAssocRightLeg) :=
  opCriticalPairResolved (monadResolvedToOver monadOmegaRightUnitAssocResolved)

/-- The op-dual of the `pentagon` pair (literally globular, transports to literally globular). -/
theorem comonadOmegaPentagonResolved :
    CriticalPairResolvedOver monadOmegaComputad (opCellRelOver monadOmegaBaseRel)
      (opCellExpr monadOmegaPentagonLeftLeg) (opCellExpr monadOmegaPentagonRightLeg) :=
  opCriticalPairResolved (monadResolvedToOver monadOmegaPentagonResolved)

/-- The op-dual of the `rootUnitAssoc` pair. -/
theorem comonadOmegaRootUnitAssocResolved :
    CriticalPairResolvedOver monadOmegaComputad (opCellRelOver monadOmegaBaseRel)
      (opCellExpr monadOmegaRootUnitAssocLeftLeg) (opCellExpr monadOmegaRootUnitAssocRightLeg) :=
  opCriticalPairResolved (monadResolvedToOver monadOmegaRootUnitAssocResolved)

/-- ★ **The walking-comonad coherent-presentation statement (honest scope).**  All FIVE op-dual critical
pairs are coherently resolved modulo the strict congruence, over `opCellRelOver monadOmegaBaseRel` (the
monad presentation read backwards). -/
def ComonadWalkerCoherentPresentationStatement : Prop :=
  CriticalPairResolvedOver monadOmegaComputad (opCellRelOver monadOmegaBaseRel)
    (opCellExpr monadOmegaUnitUnitLeftLeg) (opCellExpr monadOmegaUnitUnitRightLeg) ∧
  CriticalPairResolvedOver monadOmegaComputad (opCellRelOver monadOmegaBaseRel)
    (opCellExpr monadOmegaLeftUnitAssocLeftLeg) (opCellExpr monadOmegaLeftUnitAssocRightLeg) ∧
  CriticalPairResolvedOver monadOmegaComputad (opCellRelOver monadOmegaBaseRel)
    (opCellExpr monadOmegaRightUnitAssocLeftLeg) (opCellExpr monadOmegaRightUnitAssocRightLeg) ∧
  CriticalPairResolvedOver monadOmegaComputad (opCellRelOver monadOmegaBaseRel)
    (opCellExpr monadOmegaPentagonLeftLeg) (opCellExpr monadOmegaPentagonRightLeg) ∧
  CriticalPairResolvedOver monadOmegaComputad (opCellRelOver monadOmegaBaseRel)
    (opCellExpr monadOmegaRootUnitAssocLeftLeg) (opCellExpr monadOmegaRootUnitAssocRightLeg)

/-- ★★ **THE WALKING-COMONAD COHERENT PRESENTATION (= op(monad), five op-dual critical pairs).**  The walking
comonad `<t | counit : t => id, comult : t => t.t>` re-encoded as the op-dual of the walking monad presentation:
all FIVE Squier critical pairs transported through `opCriticalPairResolved`, each joinable-modulo-strict at
peak and valley (peak and valley swapped from the monad's).  The FIRST genuine op-dual walker shipped in the
Omega lane. -/
theorem comonadWalkerCoherentPresentation : ComonadWalkerCoherentPresentationStatement :=
  ⟨comonadOmegaUnitUnitResolved, comonadOmegaLeftUnitAssocResolved, comonadOmegaRightUnitAssocResolved,
    comonadOmegaPentagonResolved, comonadOmegaRootUnitAssocResolved⟩

/-- ★ **THE FIVE OP-DUAL 3-CELLS GENERATE THE IDENTIFICATION (least-congruence UP fired).**  For any relation
absorbing the op'd monad base relation, the two legs of every op'd monad row are identified — the comonad's
generating 3-cells (the op-transported monad 3-cells) fold through `recInto` to identify each critical pair in
EVERY model.  Uniform in the op'd row. -/
theorem comonadCriticalPairsIdentifiedInEveryModel {targetRel : CellRelOver monadOmegaComputad}
    (absorbs : IsSaturatedCongruenceWithId monadOmegaComputad (opCellRelOver monadOmegaBaseRel) targetRel)
    {d : Nat} {leftLeg rightLeg : CellExpr monadOmegaComputad d}
    (row : opCellRelOver monadOmegaBaseRel leftLeg rightLeg) : targetRel leftLeg rightLeg :=
  SaturatedConvOverWithId.recInto absorbs (SaturatedConvOverWithId.ofRelation row)

/-! ## B2 — the idempotent comonad = op(idempotent semigroup), one op-dual critical pair -/

/-- A shipped idempotent-semigroup resolution, re-read as a `CriticalPairResolvedOver` over the idempotent
base relation. -/
def idempotentResolvedToOver {d : Nat}
    {leftLeg rightLeg : CellExpr idempotentSemigroupOmegaComputad (d + 1)}
    (resolved : IdempotentSemigroupCriticalPairResolved leftLeg rightLeg) :
    CriticalPairResolvedOver idempotentSemigroupOmegaComputad idempotentSemigroupOmegaBaseRel
      leftLeg rightLeg :=
  ⟨resolved.peakJoined, resolved.legsConvertible, resolved.valleyJoined⟩

/-- ★ **THE TRUTH-PROBE — one shipped join transported.**  The idempotent semigroup's PEAK join
(`(ee)e ~ e(ee)`, a single associativity row) transported through `op` — the reversed chain type-checks as a
`SaturatedConvOverWithId` over `opCellRelOver idempotentSemigroupOmegaBaseRel` between the op'd peak sources.
Confirms the transport machine fires on a real shipped join before assembling the full op-dual resolution. -/
theorem idempotentComonadPeakJoinTransported :
    SaturatedConvOverWithId idempotentSemigroupOmegaComputad
      (opCellRelOver idempotentSemigroupOmegaBaseRel)
      (opCellExpr (boundarySource idempotentSemigroupOmegaEeeLeftLeg))
      (opCellExpr (boundarySource idempotentSemigroupOmegaEeeRightLeg)) :=
  opConvWithId idempotentSemigroupOmegaEeePeakJoin

/-- The op-dual of the idempotent semigroup's sole `eee` critical pair — the idempotent comonad's critical
pair, resolved (peak <-> valley swapped: the op'd peak is the original literal valley, the op'd valley the
original modulo-assoc peak). -/
theorem idempotentComonadOmegaEeeResolved :
    CriticalPairResolvedOver idempotentSemigroupOmegaComputad
      (opCellRelOver idempotentSemigroupOmegaBaseRel)
      (opCellExpr idempotentSemigroupOmegaEeeLeftLeg) (opCellExpr idempotentSemigroupOmegaEeeRightLeg) :=
  opCriticalPairResolved (idempotentResolvedToOver idempotentSemigroupOmegaEeeResolved)

/-- ★ **The idempotent-comonad coherent-presentation statement (honest scope).**  The sole op-dual critical
pair is coherently resolved — over `opCellRelOver idempotentSemigroupOmegaBaseRel`, half-globular with the
literal / modulo-strict boundaries swapped from the idempotent semigroup's. -/
def IdempotentComonadWalkerCoherentPresentationStatement : Prop :=
  CriticalPairResolvedOver idempotentSemigroupOmegaComputad
    (opCellRelOver idempotentSemigroupOmegaBaseRel)
    (opCellExpr idempotentSemigroupOmegaEeeLeftLeg) (opCellExpr idempotentSemigroupOmegaEeeRightLeg)

/-- ★★ **THE IDEMPOTENT-COMONAD COHERENT PRESENTATION (= op(idempotent semigroup), one op-dual critical
pair).**  The idempotent comonad `<e | e => e.e>` re-encoded as the op-dual of the idempotent-semigroup
presentation: its sole Squier critical pair transported through `opCriticalPairResolved`, joinable-
modulo-strict.  The SECOND genuine op-dual walker shipped in the Omega lane. -/
theorem idempotentComonadWalkerCoherentPresentation :
    IdempotentComonadWalkerCoherentPresentationStatement :=
  idempotentComonadOmegaEeeResolved

/-- ★ **THE OP-DUAL 3-CELL GENERATES THE IDENTIFICATION (least-congruence UP fired).**  For any relation
absorbing the op'd idempotent base relation, the two op'd legs are identified — the idempotent comonad's
generating 3-cell folds through `recInto` to identify the critical pair in EVERY model. -/
theorem idempotentComonadCriticalPairsIdentifiedInEveryModel
    {targetRel : CellRelOver idempotentSemigroupOmegaComputad}
    (absorbs : IsSaturatedCongruenceWithId idempotentSemigroupOmegaComputad
      (opCellRelOver idempotentSemigroupOmegaBaseRel) targetRel)
    {d : Nat} {leftLeg rightLeg : CellExpr idempotentSemigroupOmegaComputad d}
    (row : opCellRelOver idempotentSemigroupOmegaBaseRel leftLeg rightLeg) : targetRel leftLeg rightLeg :=
  SaturatedConvOverWithId.recInto absorbs (SaturatedConvOverWithId.ofRelation row)

/-! ## The honesty markers -/

/-- ★ **THE OMEGA-LANE `op` INVOLUTION SHIPS (B1).**  `= true` records that the `OmegaComputad` / `CellExpr`
presentation carrier now has its op involution (`opCellExpr`, structural involutivity `opCellExpr_involutive`,
boundary commutation `opBoundaryCommutes_all`), the strict-law op-stability (`opStrictAxiomStable`, interchange
on the nose), and the generic convertibility transport (`opConvWithId`) — all zero-axiom, STRUCTURAL.  This is
the machine the op-dual walkers instantiate. -/
def fxOmega4_omegaLaneHasOpInvolutionAndTransportR3 : Bool := true

/-- ★ **THE TWO GENUINE OP-DUAL WALKERS SHIP (B2).**  `= true` records that the walking comonad (= op(monad),
five pairs, `comonadWalkerCoherentPresentation`) and the idempotent comonad (= op(idempotent semigroup), one
pair, `idempotentComonadWalkerCoherentPresentation`) have Omega-lane coherent presentations, transported
generically through `opCriticalPairResolved` (the joins are NOT re-drawn per walker), each with its
least-congruence UP fired.  Two GENUINE op-transports (KZ / co-KZ ride the monad / comonad, being the same
presentation with the directed order forgotten — the census records the free-rider caveat). -/
def fxOmega4_squierFamilyTwoGenuineOpDualsShippedR3 : Bool := true

/-- ★ **HONEST SCOPE — PRESENTATION transport, NOT convergence transport.**  `= true` records that the r3
op-dual transport ships the coherent-presentation DATA (critical-pair rows, generating 3-cells, peak / valley
joins, per-pair resolutions, the least-congruence UP — every one a `SaturatedConvOverWithId` derivation
transported through `op`), NOT convergence: the reversed rules (`t => t.t`, `e => e.e`) are NON-TERMINATING,
so the op-dual rewriting systems are NOT convergent.  The transport takes ZERO termination / convergence
input — exactly the H2-WALKERS precedent (homology transported, convergence did not need to), NAMED here, not
imported. -/
def fxOmega4_squierOpDualPresentationNotConvergenceR3 : Bool := true

end FX1Poly.Polygraph.Omega
