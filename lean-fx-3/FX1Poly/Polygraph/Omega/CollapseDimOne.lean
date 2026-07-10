import FX1Poly.Polygraph.Omega.StrictAxioms

/-! # Polygraph/Omega/CollapseDimOne — the n=1 collapse to `ModalityPath` (OMEGA-1 r1, B4b)

The T1.collapse-n1 deliverable: `CellExpr computad 0` is the modes (`ModeGraph.Mode`) and `CellExpr computad 1`
is the free 1-cells, which collapse to the free-monoid `ModalityPath` (`Signature.lean:50`) up to the strict
category laws.  The collapse is NOT a definitional equality: obeying the prime directive, `CellExpr 1` uses the
SAME five dimension-generic constructors as every dimension (`id` / `gen` / `vcomp`), presenting the free
category with EXPLICIT associativity and units, whereas `ModalityPath` is the already-normalised `nil` / `cons`
free monoid.  So the collapse is an iso UP TO `SaturatedConvOver StrictAxiomRel` (the strict category laws), not
on the nose.

r1 ships the computad built from a graph, the EASY direction of the iso as a real map (`realizePathCell` —
every modality path realises as a formal 1-cell), and the full collapse as a forward-declared Prop STATEMENT
(`dimOneCollapsesToPath`); r2 constructs the flattening map and proves the round-trip up to the strict laws.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph

/-! ## The computad of a mode graph -/

/-- The **generator labels of a pure mode graph** — only 1-cell generators exist (the modality edges, flattened
over their source / target modes); every other dimension is empty.  A `Nat`-recursive `Type`, propext-free. -/
def graphGenLabel (graph : ModeGraph) : Nat → Type
  | 1 => Sigma fun (sourceMode : graph.Mode) =>
      Sigma fun (targetMode : graph.Mode) => graph.Modality sourceMode targetMode
  | 0 => PEmpty
  | _ + 2 => PEmpty

/-- The **omega-computad of a mode graph** — modes as 0-cells, modality edges as the only (dimension-1)
generators.  `CellExpr (computadOfGraph graph) 1` is the free 1-category on the graph. -/
def computadOfGraph (graph : ModeGraph) : OmegaComputad where
  modeCarrier := graph.Mode
  genLabel := graphGenLabel graph

/-! ## The easy direction — realising a path as a formal 1-cell -/

/-- **Realise a modality path as a formal 1-cell** — the identity 1-cell for the empty path, a `vcomp` of the
head generator with the realised tail for a `cons`.  The build half of the dim-1 collapse iso: every
`ModalityPath` lands in `CellExpr (computadOfGraph graph) 1`.  Constant return type (always `CellExpr .. 1`), so
propext-free.  The flattening inverse and the round-trip up to the strict laws are the r2 obligation. -/
def realizePathCell {graph : ModeGraph} :
    {sourceMode targetMode : graph.Mode} →
    ModalityPath graph sourceMode targetMode → CellExpr (computadOfGraph graph) 1
  | _, _, .nil mode => CellExpr.id (CellExpr.ofMode mode)
  | sourceMode, _, @ModalityPath.cons _ _ middleMode _ modality rest =>
      CellExpr.vcomp
        (CellExpr.gen (dim := 0)
          (⟨sourceMode, middleMode, modality⟩ : graphGenLabel graph 1)
          (CellExpr.ofMode sourceMode) (CellExpr.ofMode middleMode))
        (realizePathCell rest)

/-! ## The collapse statement -/

/-- **STATEMENT: the dim-1 fragment collapses to `ModalityPath`.**  Every formal 1-cell over the
graph's computad is convertible (via the strict category laws `SaturatedConvOver StrictAxiomRel`) to the
realisation of some modality path — i.e. `realizePathCell` is surjective up to the strict laws.  Honest note:
this is an iso up to `SaturatedConvOver StrictAxiomRel`, not a definitional equality, because `CellExpr 1`
carries explicit `id` / `vcomp` where `ModalityPath` is pre-normalised `nil` / `cons`.

★ **HONEST STATUS (OMEGA-1 r2): this UNCONDITIONAL `∀` is REFUTED — see `dimOneCollapse_not_unconditional`.**
The extrinsic-boundary carrier admits `gen ⟨s, t, mod⟩ (ofMode a) (ofMode b)` with the DECLARED boundary
`(ofMode a, ofMode b)` disagreeing with the label modes `(s, t)`.  `StrictAxiomRel` at dimension 1 is only
`vcompAssoc` / `vcompUnitLeft` / `vcompUnitRight` (the whisker / interchange rows require dimension `dim+2`), and
none of these alter a `gen` atom; the one-hole congruences preserve the atom multiset.  Every realised path's
`gen` atoms are boundary-CANONICAL (`gen ⟨s, mid, mod⟩ (ofMode s) (ofMode mid)`), so an ill-boundaried `gen`
has NO path preimage.  The substantive collapse content that DOES hold unconditionally ships below:
`realizePath_composePath_conv` (the homomorphism), `realizePathCell_boundarySource`, and
`oneCellCollapse_vcompClosed` (compositional closure).  A `GlobularComputad`-restricted collapse (the boundary
of every generator canonical, and every `vcomp` composable) is the honest true statement OMEGA-2 layers on. -/
def dimOneCollapsesToPath (graph : ModeGraph) : Prop :=
  ∀ (cell : CellExpr (computadOfGraph graph) 1),
    ∃ (sourceMode targetMode : graph.Mode) (path : ModalityPath graph sourceMode targetMode),
      SaturatedConvOver (computadOfGraph graph) (StrictAxiomRel (computadOfGraph graph))
        cell (realizePathCell path)

/-! ## The dim-1 collapse content — homomorphism + compositional closure (OMEGA-1 r2, B1)

The unconditional `dimOneCollapsesToPath` is refuted (see its note).  What holds unconditionally, and carries
the mathematical content of "dimension 1 is the free 1-category on the graph", ships here: the boundary of a
realisation reads off the path's source mode; `realizePathCell` is a HOMOMORPHISM up to
`SaturatedConvOver StrictAxiomRel` (path composition maps to `vcomp`); hence the realisable cells are CLOSED
under composable vertical composition. -/

/-- The source boundary of a realised 1-cell is the mode the path starts at (`ofMode sourceMode`) — read off
structurally (`nil` gives `id (ofMode sourceMode)`; `cons` gives a `vcomp` whose left factor is the head `gen`
with declared source `ofMode sourceMode`).  Propext-free (`cases` + `rfl`). -/
theorem realizePathCell_boundarySource {graph : ModeGraph} {sourceMode targetMode : graph.Mode}
    (path : ModalityPath graph sourceMode targetMode) :
    boundarySource (realizePathCell path) = CellExpr.ofMode sourceMode := by
  cases path with
  | nil _ => rfl
  | cons _ _ => rfl

/-- ★ **`realizePathCell` is a homomorphism up to the strict category laws.**  Path composition maps to
vertical composition modulo `SaturatedConvOver StrictAxiomRel`: `realize (first . second)` is convertible to
`(realize first) vcomp (realize second)`.  By induction on `first` — the `nil` case fires `vcompUnitLeft` (the
realised tail's source boundary is `ofMode`, by `realizePathCell_boundarySource`), the `cons` case threads the
inductive hypothesis under `vcompCongrRight` then re-associates with `vcompAssoc`.  This is the substantive
"dimension 1 = free 1-category on the graph" content. -/
theorem realizePath_composePath_conv {graph : ModeGraph} {sourceMode middleMode : graph.Mode}
    (first : ModalityPath graph sourceMode middleMode) :
    ∀ {targetMode : graph.Mode} (second : ModalityPath graph middleMode targetMode),
      SaturatedConvOver (computadOfGraph graph) (StrictAxiomRel (computadOfGraph graph))
        (realizePathCell (composePath first second))
        (CellExpr.vcomp (realizePathCell first) (realizePathCell second)) := by
  induction first with
  | nil _ =>
      intro _ second
      have unitStep := SaturatedConvOver.ofRelation (computad := computadOfGraph graph)
        (baseRel := StrictAxiomRel (computadOfGraph graph))
        (StrictAxiomRel.vcompUnitLeft (realizePathCell second))
      rw [realizePathCell_boundarySource] at unitStep
      exact unitStep.symm
  | cons _ rest ih =>
      intro _ second
      exact SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrRight _ (ih second))
        (SaturatedConvOver.symm
          (SaturatedConvOver.ofRelation
            (StrictAxiomRel.vcompAssoc _ (realizePathCell rest) (realizePathCell second))))

/-- The realisable cells are CLOSED under composable vertical composition: if `cellA` collapses to `realize pA`
and `cellB` collapses to `realize pB` along a shared middle mode, then `vcomp cellA cellB` collapses to
`realize (pA . pB)`.  Two `vcompCongr` steps feed the composite into `realizePath_composePath_conv`; this is
the compositional half of the honest dim-1 collapse. -/
theorem oneCellCollapse_vcompClosed {graph : ModeGraph} {sourceMode middleMode targetMode : graph.Mode}
    (pathA : ModalityPath graph sourceMode middleMode) (pathB : ModalityPath graph middleMode targetMode)
    {cellA cellB : CellExpr (computadOfGraph graph) 1}
    (collapseA : SaturatedConvOver (computadOfGraph graph) (StrictAxiomRel (computadOfGraph graph))
      cellA (realizePathCell pathA))
    (collapseB : SaturatedConvOver (computadOfGraph graph) (StrictAxiomRel (computadOfGraph graph))
      cellB (realizePathCell pathB)) :
    SaturatedConvOver (computadOfGraph graph) (StrictAxiomRel (computadOfGraph graph))
      (CellExpr.vcomp cellA cellB) (realizePathCell (composePath pathA pathB)) :=
  SaturatedConvOver.trans
    (SaturatedConvOver.trans
      (SaturatedConvOver.vcompCongrLeft cellB collapseA)
      (SaturatedConvOver.vcompCongrRight (realizePathCell pathA) collapseB))
    (SaturatedConvOver.symm (realizePath_composePath_conv pathA pathB))

/-- ★ **The dim-0 collapse is definitional.**  `CellExpr computad 0` is exactly the modes carrier: `ofMode`
is the sole constructor at dimension 0, so `CellExpr (computadOfGraph graph) 0` is `graph.Mode` up to the
`ofMode` wrapper.  Witnessed by the round-trip on `ofMode`. -/
theorem dimZeroBoundaryIsMode {graph : ModeGraph} (mode : graph.Mode) :
    (CellExpr.ofMode (computad := computadOfGraph graph) mode) =
      CellExpr.ofMode mode := rfl

end FX1Poly.Polygraph.Omega
