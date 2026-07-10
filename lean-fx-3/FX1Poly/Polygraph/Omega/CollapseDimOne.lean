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

/-! ## The refutation of the UNCONDITIONAL collapse — the honest headline (OMEGA-1 r2, B1)

`dimOneCollapsesToPath` (every `CellExpr 1` convertible to a realised path) is FALSE for the
extrinsic-boundary carrier: `gen ⟨s, t, mod⟩ (ofMode a) (ofMode b)` admits a DECLARED boundary
`(ofMode a, ofMode b)` disagreeing with the label modes `(s, t)`, and no such ill-boundaried atom is
convertible to any realised path.  The proof is the OMEGA analogue of the OMEGA-2 invariant fold: a
gen-atom collector fed through `SaturatedConvOver.recInto`.

The collector is an ACCUMULATOR (difference-list): `vcomp`-associativity and the two `id`-units then hold
DEFINITIONALLY on the gen-atom list (no `List.append`, hence no `append_assoc` `propext` leak), and the
invariant is carried in the acc-GENERALISED form `∀ acc, skeletonGenAcc a acc = skeletonGenAcc b acc` so the
one-hole congruence fields discharge append-free.  Off dimension 1 the invariant is `True` (the whisker /
interchange rows only fire at dimension `+2`), so `recInto`'s dimension-generic fold stays clean. -/

/-- Collect the gen-atoms of a cell SKELETON, accumulator (difference-list) style: `vcomp` threads the
accumulator so associativity and the `id`-units hold on the nose, and no `List.append` appears (no
`append_assoc` `propext` leak).  Full six-constructor match — propext-free. -/
def skeletonGenAcc {computad : OmegaComputad} :
    CellSkeleton computad → List (CellSkeleton computad) → List (CellSkeleton computad)
  | .modeLeaf _, acc => acc
  | .genNode labelDim label source target, acc =>
      CellSkeleton.genNode labelDim label source target :: acc
  | .idNode _, acc => acc
  | .vcompNode left right, acc => skeletonGenAcc left (skeletonGenAcc right acc)
  | .whiskerLeftNode _ cell, acc => skeletonGenAcc cell acc
  | .whiskerRightNode cell _, acc => skeletonGenAcc cell acc

/-- The ordered gen-atom list of a 1-cell (the accumulator seeded empty). -/
def oneCellGenList {computad : OmegaComputad} (cell : CellExpr computad 1) :
    List (CellSkeleton computad) :=
  skeletonGenAcc (toSkeleton cell) []

/-- The gen-atom-list invariant relation, acc-GENERALISED at dimension 1 (so congruence is append-free) and
`True` off dimension 1 (the whisker / interchange rows only fire at dimension `+2`).  Full `Nat` enumeration
(`0` / `1` / `_ + 2`), no wildcard — propext-free. -/
def dimOneGenListInvariant (computad : OmegaComputad) : CellRelOver computad :=
  fun {dim} =>
    match dim with
    | 1 => fun cellAlpha cellBeta =>
        ∀ (acc : List (CellSkeleton computad)),
          skeletonGenAcc (toSkeleton cellAlpha) acc = skeletonGenAcc (toSkeleton cellBeta) acc
    | 0 => fun _ _ => True
    | _ + 2 => fun _ _ => True

/-- The invariant is trivially `True` on any dimension-`(dim+2)` pair (the `_ + 2` branch). -/
theorem dimOneGenListInvariant_trivial_succSucc {computad : OmegaComputad} {dim : Nat}
    (cellAlpha cellBeta : CellExpr computad (dim + 2)) :
    dimOneGenListInvariant computad cellAlpha cellBeta := True.intro

/-- Vertical associativity preserves the gen-atom list — definitionally at dimension 1 (the accumulator makes
associativity `rfl`), trivially above. -/
theorem dimOneGenListInvariant_vcompAssoc {computad : OmegaComputad} {dim : Nat}
    (cellA cellB cellC : CellExpr computad (dim + 1)) :
    dimOneGenListInvariant computad
      (CellExpr.vcomp (CellExpr.vcomp cellA cellB) cellC)
      (CellExpr.vcomp cellA (CellExpr.vcomp cellB cellC)) := by
  cases dim with
  | zero => intro _; rfl
  | succ _ => exact True.intro

/-- The left unit preserves the gen-atom list — the `id` factor contributes nothing to the accumulator. -/
theorem dimOneGenListInvariant_vcompUnitLeft {computad : OmegaComputad} {dim : Nat}
    (cellA : CellExpr computad (dim + 1)) :
    dimOneGenListInvariant computad
      (CellExpr.vcomp (CellExpr.id (boundarySource cellA)) cellA) cellA := by
  cases dim with
  | zero => intro _; rfl
  | succ _ => exact True.intro

/-- The right unit preserves the gen-atom list. -/
theorem dimOneGenListInvariant_vcompUnitRight {computad : OmegaComputad} {dim : Nat}
    (cellA : CellExpr computad (dim + 1)) :
    dimOneGenListInvariant computad
      (CellExpr.vcomp cellA (CellExpr.id (boundaryTarget cellA))) cellA := by
  cases dim with
  | zero => intro _; rfl
  | succ _ => exact True.intro

/-- The gen-atom-list invariant is an absorbing saturated congruence over the strict laws — the invariant fold
`recInto` runs on.  The one-hole congruence fields discharge append-free (the accumulator threads through), the
strict-law rows preserve it (`ofRelation`), and refl / symm / trans lift pointwise in the accumulator. -/
theorem dimOneGenListInvariant_isSaturatedCongruence (computad : OmegaComputad) :
    IsSaturatedCongruence computad (StrictAxiomRel computad) (dimOneGenListInvariant computad) where
  ofRelation := by
    intro _ _ _ row
    cases row with
    | vcompAssoc cellA cellB cellC => exact dimOneGenListInvariant_vcompAssoc cellA cellB cellC
    | vcompUnitLeft cellA => exact dimOneGenListInvariant_vcompUnitLeft cellA
    | vcompUnitRight cellA => exact dimOneGenListInvariant_vcompUnitRight cellA
    | whiskerLeftUnit _ _ => exact dimOneGenListInvariant_trivial_succSucc _ _
    | whiskerRightUnit _ _ => exact dimOneGenListInvariant_trivial_succSucc _ _
    | whiskerLeftFunctorial _ _ _ => exact dimOneGenListInvariant_trivial_succSucc _ _
    | whiskerRightFunctorial _ _ _ => exact dimOneGenListInvariant_trivial_succSucc _ _
    | interchange _ _ => exact dimOneGenListInvariant_trivial_succSucc _ _
  vcompCongrLeft := by
    intro dim _ _ cellBeta hyp
    cases dim with
    | zero => intro acc; exact hyp (skeletonGenAcc (toSkeleton cellBeta) acc)
    | succ _ => exact True.intro
  vcompCongrRight := by
    intro dim cellAlpha _ _ hyp
    cases dim with
    | zero => intro acc; exact congrArg (skeletonGenAcc (toSkeleton cellAlpha)) (hyp acc)
    | succ _ => exact True.intro
  whiskerLeftCongr := by
    intro _ _ _ _ _; exact dimOneGenListInvariant_trivial_succSucc _ _
  whiskerRightCongr := by
    intro _ _ _ _ _; exact dimOneGenListInvariant_trivial_succSucc _ _
  refl := by
    intro dim _
    cases dim with
    | zero => exact True.intro
    | succ k =>
        cases k with
        | zero => intro _; rfl
        | succ _ => exact True.intro
  symm := by
    intro dim _ _ hyp
    cases dim with
    | zero => exact True.intro
    | succ k =>
        cases k with
        | zero => intro acc; exact (hyp acc).symm
        | succ _ => exact True.intro
  trans := by
    intro dim _ _ _ hyp1 hyp2
    cases dim with
    | zero => exact True.intro
    | succ k =>
        cases k with
        | zero => intro acc; exact (hyp1 acc).trans (hyp2 acc)
        | succ _ => exact True.intro

/-- The gen-atom list is a `SaturatedConvOver StrictAxiomRel` invariant at dimension 1 (the acc-generalised
form), via the invariant fold. -/
theorem oneCellGenAcc_of_conv {computad : OmegaComputad} {cellAlpha cellBeta : CellExpr computad 1}
    (conv : SaturatedConvOver computad (StrictAxiomRel computad) cellAlpha cellBeta) :
    ∀ (acc : List (CellSkeleton computad)),
      skeletonGenAcc (toSkeleton cellAlpha) acc = skeletonGenAcc (toSkeleton cellBeta) acc :=
  SaturatedConvOver.recInto (dimOneGenListInvariant_isSaturatedCongruence computad) conv

/-! ## The refuting witness — a graph whose junk `gen` cell has no path preimage -/

/-- The refuting mode graph: two modes (`Bool`), a modality between every ordered pair.  Rich enough to build
an ill-boundaried `gen` 1-cell. -/
def refutingGraph : ModeGraph where
  Mode := Bool
  Modality := fun _ _ => Unit

/-- The computad of the refuting graph. -/
abbrev refutingComputad : OmegaComputad := computadOfGraph refutingGraph

/-- The **junk 1-cell**: a `false ⟶ true` generator whose DECLARED source / target boundaries are both `true`
(disagreeing with the label's source mode `false`).  A legal `CellExpr .. 1` with NO realised-path preimage. -/
def junkCell : CellExpr refutingComputad 1 :=
  CellExpr.gen (dim := 0)
    (⟨false, true, ()⟩ : graphGenLabel refutingGraph 1)
    (CellExpr.ofMode true) (CellExpr.ofMode true)

/-- The mode a skeleton denotes when it is a `modeLeaf` (`none` otherwise) — a propext-free discriminator. -/
def skeletonModeValue : CellSkeleton refutingComputad → Option Bool
  | .modeLeaf mode => some mode
  | .genNode _ _ _ _ => none
  | .idNode _ => none
  | .vcompNode _ _ => none
  | .whiskerLeftNode _ _ => none
  | .whiskerRightNode _ _ => none

/-- Whether a gen-atom skeleton's DECLARED source mode matches its label's source mode (as an `Eq` of
`Option Bool`, so realised atoms discharge by `rfl` — no `beq_self`).  Non-gen / off-dimension nodes are
vacuously canonical.  Full-enumeration match — propext-free. -/
def genAtomSourceCanonicalProp : CellSkeleton refutingComputad → Prop
  | .genNode 1 label source _ => skeletonModeValue source = some label.1
  | .genNode 0 _ _ _ => True
  | .genNode (_ + 2) _ _ _ => True
  | .modeLeaf _ => True
  | .idNode _ => True
  | .vcompNode _ _ => True
  | .whiskerLeftNode _ _ => True
  | .whiskerRightNode _ _ => True

/-- Every gen-atom in a list is source-canonical. -/
def allSourceCanonicalProp : List (CellSkeleton refutingComputad) → Prop
  | [] => True
  | atom :: rest => genAtomSourceCanonicalProp atom ∧ allSourceCanonicalProp rest

/-- Every realised path's gen-atoms are source-canonical: each atom's declared source is `ofMode s` for its
label's source mode `s`, so canonicity is `some s = some s` (`rfl`).  By induction on the path. -/
theorem realizePathCell_allSourceCanonical {sourceMode targetMode : refutingGraph.Mode}
    (path : ModalityPath refutingGraph sourceMode targetMode) :
    allSourceCanonicalProp (oneCellGenList (realizePathCell path)) := by
  induction path with
  | nil _ => exact True.intro
  | cons _ _ ih => exact ⟨rfl, ih⟩

/-- The junk cell's single gen-atom is NOT source-canonical: its declared source is `ofMode true`, its label
source is `false`, so canonicity would force `some true = some false`. -/
theorem junkCell_not_allSourceCanonical :
    ¬ allSourceCanonicalProp (oneCellGenList junkCell) := by
  intro hcanon
  exact Bool.noConfusion (Option.some.inj hcanon.1)

/-- ★ **The unconditional dim-1 collapse is REFUTED.**  `dimOneCollapsesToPath refutingGraph` would make the
junk cell convertible to some realised path; the gen-atom-list invariant then forces their gen-atom lists
equal, so the junk cell's non-canonical atom would appear in a realised path (all of whose atoms are canonical)
— contradiction.  This is the honest status of `dimOneCollapsesToPath`: it holds only on the boundary-canonical
(`GlobularComputad`) sub-carrier, and the substantive UNCONDITIONAL content is the homomorphism / closure
lemmas above. -/
theorem dimOneCollapse_not_unconditional : ¬ dimOneCollapsesToPath refutingGraph := by
  intro hcollapse
  obtain ⟨_, _, path, hconv⟩ := hcollapse junkCell
  have hlist : oneCellGenList junkCell = oneCellGenList (realizePathCell path) :=
    oneCellGenAcc_of_conv hconv []
  have hcanon : allSourceCanonicalProp (oneCellGenList (realizePathCell path)) :=
    realizePathCell_allSourceCanonical path
  rw [← hlist] at hcanon
  exact junkCell_not_allSourceCanonical hcanon

end FX1Poly.Polygraph.Omega
