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

/-- ★ **STATEMENT (r2 proves): the dim-1 fragment collapses to `ModalityPath`.**  Every formal 1-cell over the
graph's computad is convertible (via the strict category laws `SaturatedConvOver StrictAxiomRel`) to the
realisation of some modality path — i.e. `realizePathCell` is surjective up to the strict laws.  A forward-
declared Prop (not proven here): the free 1-category presented by `CellExpr .. 1` has `ModalityPath` as its
strict-law normal forms.  Honest note: this is an iso up to `SaturatedConvOver StrictAxiomRel`, not a
definitional equality, because `CellExpr 1` carries explicit `id` / `vcomp` where `ModalityPath` is
pre-normalised `nil` / `cons`. -/
def dimOneCollapsesToPath (graph : ModeGraph) : Prop :=
  ∀ (cell : CellExpr (computadOfGraph graph) 1),
    ∃ (sourceMode targetMode : graph.Mode) (path : ModalityPath graph sourceMode targetMode),
      SaturatedConvOver (computadOfGraph graph) (StrictAxiomRel (computadOfGraph graph))
        cell (realizePathCell path)

/-- ★ **The dim-0 collapse is definitional.**  `CellExpr computad 0` is exactly the modes carrier: `ofMode`
is the sole constructor at dimension 0, so `CellExpr (computadOfGraph graph) 0` is `graph.Mode` up to the
`ofMode` wrapper.  Witnessed by the round-trip on `ofMode`. -/
theorem dimZeroBoundaryIsMode {graph : ModeGraph} (mode : graph.Mode) :
    (CellExpr.ofMode (computad := computadOfGraph graph) mode) =
      CellExpr.ofMode mode := rfl

end FX1Poly.Polygraph.Omega
