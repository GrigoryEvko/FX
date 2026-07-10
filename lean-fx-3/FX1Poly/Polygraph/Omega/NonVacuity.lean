import FX1Poly.Polygraph.Omega.StrictAxioms

/-! # Polygraph/Omega/NonVacuity — the four OMEGA-1 r1 non-vacuity witnesses (B6)

Concrete inhabitants proving the r1 constructions are not vacuous, over a tiny demo computad (`Unit` modes, a
single generator label at every dimension).  Each check ships BOTH the memo's `#eval` and a machine-checked
`rfl` / `decide` theorem:

  1. a `CellExpr 3` inhabitant with `cellSize` positive;
  2. the boundaries of a concrete whisker cell computing to the expected lower cells (globularity non-vacuous);
  3. a `SaturatedConvOver 2` derivation firing a REAL interchange row through a REAL one-hole context
     constructor between two DISTINCT cells (congruence non-vacuous);
  4. structural `cellBeq` on distinct / equal `CellExpr 3` returning `false` / `true` (equality non-vacuous, no
     propext).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The demo computad and concrete cells -/

/-- A tiny computad — `Unit` modes, a single (`Unit`) generator label at every dimension.  Enough to inhabit
cells up to dimension 3 and exercise every constructor. -/
def demoComputad : OmegaComputad where
  modeCarrier := Unit
  genLabel := fun _ => Unit

/-- The trivial mode comparator for the demo (`Unit` modes are always equal). -/
def demoModeBeq : demoComputad.modeCarrier → demoComputad.modeCarrier → Bool := fun _ _ => true

/-- The trivial heterogeneous generator comparator for the demo (`Unit` labels are always equal). -/
def demoGenBeq : (dimA dimB : Nat) → demoComputad.genLabel dimA → demoComputad.genLabel dimB → Bool :=
  fun _ _ _ _ => true

/-- The 0-cell (an object). -/
def objectCell : CellExpr demoComputad 0 := CellExpr.ofMode ()

/-- A generating 1-cell. -/
def oneCellGen : CellExpr demoComputad 1 := CellExpr.gen (dim := 0) () objectCell objectCell

/-- The identity 1-cell on the object (structurally distinct from `oneCellGen`). -/
def oneCellId : CellExpr demoComputad 1 := CellExpr.id objectCell

/-- A generating 2-cell over `oneCellGen`. -/
def twoCellGen : CellExpr demoComputad 2 := CellExpr.gen (dim := 1) () oneCellGen oneCellGen

/-- A generating 2-cell over `oneCellId` (structurally distinct from `twoCellGen`). -/
def twoCellId : CellExpr demoComputad 2 := CellExpr.gen (dim := 1) () oneCellId oneCellId

/-- A concrete left-whisker cell — `oneCellGen` whiskered onto `twoCellGen`. -/
def whiskerCell : CellExpr demoComputad 2 := CellExpr.whiskerLeft oneCellGen twoCellGen

/-- A generating 3-cell over `twoCellGen` — witnesses `CellExpr 3` is inhabited (the world-first-(c) substrate
is non-empty). -/
def threeCellGen : CellExpr demoComputad 3 := CellExpr.gen (dim := 2) () twoCellGen twoCellGen

/-- A vertical-composite 3-cell — structurally distinct from `threeCellGen`, with `cellSize` 3. -/
def threeCellVcomp : CellExpr demoComputad 3 := CellExpr.vcomp threeCellGen threeCellGen

/-! ## Non-vacuity 1 — `CellExpr 3` inhabited with positive size -/

#eval cellSize threeCellVcomp

/-- `CellExpr 3` is inhabited and the composite 3-cell has size 3 (`1 + 1 + 1`) — positive. -/
theorem threeCellVcomp_size : cellSize threeCellVcomp = 3 := rfl

/-! ## Non-vacuity 2 — whisker boundaries compute to the expected lower cells -/

#eval cellSize (boundarySource whiskerCell)

/-- The source boundary of the whisker cell is the formal `vcomp` of the whiskering 1-cell with the whiskered
cell's source boundary — `boundarySource (oneCellGen <| twoCellGen) = oneCellGen . oneCellGen`. -/
theorem whiskerCell_boundarySource :
    boundarySource whiskerCell = CellExpr.vcomp oneCellGen oneCellGen := rfl

/-- The target boundary computes dually. -/
theorem whiskerCell_boundaryTarget :
    boundaryTarget whiskerCell = CellExpr.vcomp oneCellGen oneCellGen := rfl

/-! ## Non-vacuity 3 — a real interchange row fired through a real one-hole context -/

/-- ★ A **non-vacuous `SaturatedConvOver 2` derivation**: the Godement interchange row (a REAL
`StrictAxiomRel.interchange` between two DISTINCT `CellExpr 2`) fired through the REAL one-hole context
constructor `vcompCongrLeft`.  The generic OMEGA analogue of the shipped
`frobeniusSuffixCongruence_nonVacuous`. -/
def nonVacuousInterchangeConv :
    SaturatedConvOver demoComputad
      (unionCellRel demoComputad (StrictAxiomRel demoComputad) (emptyPresentation demoComputad))
      (CellExpr.vcomp
        (CellExpr.vcomp (CellExpr.whiskerRight twoCellGen (boundarySource twoCellId))
          (CellExpr.whiskerLeft (boundaryTarget twoCellGen) twoCellId))
        twoCellGen)
      (CellExpr.vcomp
        (CellExpr.vcomp (CellExpr.whiskerLeft (boundarySource twoCellGen) twoCellId)
          (CellExpr.whiskerRight twoCellGen (boundaryTarget twoCellId)))
        twoCellGen) :=
  SaturatedConvOver.vcompCongrLeft twoCellGen
    (SaturatedConvOver.ofRelation (Or.inl (StrictAxiomRel.interchange twoCellGen twoCellId)))

-- The two cells the interchange relates are genuinely DISTINCT (the left factor is a right-whisker on one
-- side, a left-whisker on the other) — so the congruence identifies non-equal cells.
#eval cellBeq demoModeBeq demoGenBeq
  (CellExpr.vcomp (CellExpr.whiskerRight twoCellGen (boundarySource twoCellId))
    (CellExpr.whiskerLeft (boundaryTarget twoCellGen) twoCellId))
  (CellExpr.vcomp (CellExpr.whiskerLeft (boundarySource twoCellGen) twoCellId)
    (CellExpr.whiskerRight twoCellGen (boundaryTarget twoCellId)))

/-- Machine-checked: the interchange's two sides are distinct under structural equality. -/
theorem interchange_sides_distinct :
    cellBeq demoModeBeq demoGenBeq
      (CellExpr.vcomp (CellExpr.whiskerRight twoCellGen (boundarySource twoCellId))
        (CellExpr.whiskerLeft (boundaryTarget twoCellGen) twoCellId))
      (CellExpr.vcomp (CellExpr.whiskerLeft (boundarySource twoCellGen) twoCellId)
        (CellExpr.whiskerRight twoCellGen (boundaryTarget twoCellId))) = false := rfl

/-! ## Non-vacuity 4 — structural equality returns false / true (no propext) -/

#eval cellBeq demoModeBeq demoGenBeq threeCellGen threeCellVcomp
#eval cellBeq demoModeBeq demoGenBeq threeCellVcomp threeCellVcomp

/-- Structural equality separates distinct `CellExpr 3` (a generator vs a composite). -/
theorem threeCell_distinct : cellBeq demoModeBeq demoGenBeq threeCellGen threeCellVcomp = false := rfl

/-- Structural equality accepts a `CellExpr 3` against itself. -/
theorem threeCell_reflexive : cellBeq demoModeBeq demoGenBeq threeCellVcomp threeCellVcomp = true := rfl

/-! ## Non-vacuity 5 — the well-formedness predicate is inhabited and discharges globularity (B3) -/

/-- The generating 1-cell is well-formed: its declared mode boundaries are trivially parallel. -/
theorem oneCellGen_isGlobular : IsGlobularCell oneCellGen := ⟨True.intro, True.intro, True.intro⟩

/-- The generating 2-cell is well-formed: its boundary 1-cells are globular and parallel to themselves. -/
theorem twoCellGen_isGlobular : IsGlobularCell twoCellGen :=
  ⟨oneCellGen_isGlobular, oneCellGen_isGlobular, rfl, rfl⟩

/-- The generating 3-cell is well-formed — `IsGlobularCell` is non-vacuous at dimension 3. -/
theorem threeCellGen_isGlobular : IsGlobularCell threeCellGen :=
  ⟨twoCellGen_isGlobular, twoCellGen_isGlobular, rfl, rfl⟩

/-- ★ Globularity discharges on the concrete well-formed 3-cell: its `GlobularLegs` (the `ss = ts`, `tt = st`
equations) are inhabited via `globularLegs_of_isGlobularCell` — the B3 theorem is non-vacuous. -/
theorem threeCellGen_globularLegs : GlobularLegs threeCellGen :=
  globularLegs_of_isGlobularCell threeCellGen threeCellGen_isGlobular

/-! ## Non-vacuity 6 — the derived `*_k` operations are concrete carrier terms (B4) -/

/-- The derived Godement composite `*_1` of two 3-cells — a real dim-3 carrier term (no new constructor). -/
def derivedGodementDimThree : CellExpr demoComputad 3 := godementComp threeCellGen threeCellGen

#eval cellSize derivedGodementDimThree

/-- The derived Godement `*_1` composite has size 5 (two whiskers + a vcomp over two size-1 generators). -/
theorem derivedGodementDimThree_size : cellSize derivedGodementDimThree = 5 := rfl

/-- The derived deep whisker `*_0` — a 3-cell whiskered by a 1-cell via id-promotion (the recon's
`whiskerLeft (id w) α`) — a real dim-3 carrier term. -/
def derivedWhiskerDimThree : CellExpr demoComputad 3 := whiskerByLowerId oneCellGen threeCellGen

#eval cellSize derivedWhiskerDimThree

/-- The derived deep whisker has size 2 (one whisker over a size-1 generator). -/
theorem derivedWhiskerDimThree_size : cellSize derivedWhiskerDimThree = 2 := rfl

end FX1Poly.Polygraph.Omega
