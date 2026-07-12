import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidMatrixSemantics
import FX1Poly.Polygraph.Omega.StrictAxioms

/-! # Polygraph/Omega/WalkingBunchedBimonoidWhiskerOneCellCoherenceWall — the three whisker-vs-1-cell coherences:
matrix-sound, non-boundary-parallel (WP-PROP r18 adjudication); TWO of the three now LANDED (WP-PROP r19)

★★ **WP-PROP r19 SUPERSESSION.**  The r18 adjudication below walled ALL THREE coherences on the test
"non-boundary-parallel".  The r19 substrate round corrected that test — "non-boundary-parallel" is NOT
"chain-unsound".  The **associator** (both duals) and the **whisker left/right commute** ARE chain-sound and
are now genuine `StrictAxiomRel` rows (`StrictAxioms.whiskerAssocLeft` / `whiskerAssocRight` /
`whiskerLeftRightCommute`); the landing witnesses + the machine-checked identity-whisker-UNITOR STOP + the M4
cost table live in `WalkingBunchedBimonoidWhiskerCoherenceLanded`.  The five `...MatrixSound` and the
non-parallelism theorems below STAY VALID (matrix-soundness and the boundary-source disequalities are
unchanged facts).  The marker `fxBunchedBimonoid_whiskerOneCellCoherencesWalledNotLanded` is now scoped to the
SOLE residual, the identity-whisker unitor (still `= false` = "a walled whisker-coherence residual remains").

★ **THE r18 COHERENCE ADJUDICATION (superseded for assoc+commute) — machine-checked, honest, NON-silent.**  The
r17 CONV-fold wall
(`fxBunchedBimonoid_runCommuteConvGatedOnWhiskerAssociatorAndUnitors`) named three whisker-vs-1-cell coherences as
the residual gating the `recCombConv`-over-cells lift:

  (1) **whisker-1-cell ASSOCIATOR**  `whiskerLeft (vcomp P Q) X ~ whiskerLeft P (whiskerLeft Q X)`  (+ right dual
      `whiskerRight X (vcomp P Q) ~ whiskerRight (whiskerRight X P) Q`);
  (2) **whisker-by-identity-1-cell UNITORS**  `whiskerLeft (id c) X ~ X`  /  `whiskerRight X (id c) ~ X`;
  (3) **whisker-LEFT/RIGHT COMMUTE**  `whiskerRight (whiskerLeft P X) Q ~ whiskerLeft P (whiskerRight X Q)`.

## The adjudication (VERDICT: STRUCTURAL incompleteness — sound, but WALLED in this lane)

**These three ARE identities of the free strict 2-category** (the Cat-enrichment axioms; equivalently the
sesquicategory whisker-action laws `1.a = a`, `(xy).a = x.(y.a)`, `x.(a.y) = (x.a).y`, which survive even dropping
interchange).  A faithful presentation's congruence MUST contain them.  Machine-checked evidence, both directions:

  * **MATRIX-SOUND (they are TRUE strict-omega laws).**  Every instance below evaluates its two legs to the SAME
    `Mat(N)` map by `rfl` under `bunchedBimonoidEvalCell` (the free-bimonoid functor): `whiskerLeft`/`whiskerRight`
    are block direct sums with the whiskering 1-cell's identity block, and the two legs reassociate/absorb that
    block to the same matrix.  So the `Mat(N)` model validates them definitionally — they are legitimate rows.

  * **NON-BOUNDARY-PARALLEL (the design reason they are NOT in `StrictAxiomRel`).**  `StrictAxiomRel`'s invariant
    (stated on `interchange`: "Cast-free: both sides share the boundary"; and `Steiner/SoundnessFull`: "each row is
    boundary-parallel, `cases row <;> rfl` closes the poles uniformly") is that EVERY row is cast-free: its two
    sides have DEFINITIONALLY EQUAL `boundarySource`/`boundaryTarget`.  The three coherences VIOLATE that: their
    boundary sources differ by exactly the `vcompAssoc` / `vcompUnitLeft` laws that the OTHER rows govern.  E.g. the
    associator's poles are `boundarySource (whiskerLeft (vcomp P Q) X) = vcomp (vcomp P Q) (bs X)` vs
    `boundarySource (whiskerLeft P (whiskerLeft Q X)) = vcomp P (vcomp Q (bs X))` — pinned by `rfl` below, and their
    disequality is machine-checked (`bunchedBimonoidWhiskerOneCellAssocSourcesNotParallel`), against the
    boundary-PARALLEL `vcompAssoc` contrast (`bunchedBimonoidVcompAssocBoundaryParallel`, `rfl`).

## Why WALLED in the WP-PROP lane (NOT a unilateral row-addition here)

Landing these three as `StrictAxiomRel` rows is NOT a safe additive edit: because they are non-parallel they BREAK
the cast-free invariant, so `Steiner/SoundnessFull`'s `cases row <;> rfl` no longer closes (poles reassociate), and
the soundness master `Steiner/Soundness.lean`'s `cases row` needs genuinely new non-`rfl` arms (`linearize` equality
via reassociation).  The exhaustive `cases row` eliminators span `StrictAxioms.lean` + `Steiner/Soundness` +
`Steiner/SoundnessFull` + `Suspension` + `PresentationOpDualityWithId` + `CollapseDimOne` +
`FrobeniusMonadPresentation` + `EckmannHiltonWithId` — >=5 concurrent lanes.  Per the fix-pinned-bugs directive the
row-addition would require ALL those consumers updated in the SAME commit; under the six-lane `AuditAll` race that is
a coordinated `StrictAxioms.lean` SUBSTRATE-OWNER design decision (does `StrictAxiomRel` admit non-parallel rows, or
add a boundary-cast mechanism?), NOT a WP-PROP-lane change.  So: `StrictAxioms.lean` stays BYTE-INTACT; this file
records the three coherences + their machine-checked matrix-soundness + non-parallelism as the WP-PROP-owned
residual, and the marker `fxBunchedBimonoid_whiskerOneCellCoherencesWalledNotLanded := false` records that they are
NOT landed here.  The `recCombConv`-over-cells lift stays gated on the eventual coordinated substrate change.

Sources (web-literature synthesis, all fetched): nLab *strict 2-category* (whisker associativity/unit/compatibility
= the Cat-enrichment axioms); nLab *sesquicategory* (same laws survive dropping interchange); Mimram et al.
arXiv:1004.3135 (free-2-category 2-cells = formal composites modulo a congruence imposing associativity/absorption
for both compositions); mathlib4 `CategoryTheory.Monoidal.Free.Basic` (every structural coherence is a constructor of
the quotiented relation; omission ⇒ quotient too fine); Joyal–Street *Geometry of tensor calculus I* (the three
whiskerings are the same string diagram).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # W1 — MATRIX-SOUNDNESS: each coherence's two legs share the same `Mat(N)` map (`rfl`)
    # =========================================================================================

The whiskering cells `P = Q = bunchedBimonoidAdditiveGen` (width 1), the inner 2-cell `X = bunchedBimonoidAddSigmaGen`
(the `2x2` swap over `a.a`), the identity 1-cell `bunchedBimonoidIdOne = id *` (width 0). -/

/-- ★ **Associator (left) — matrix-sound.**  `whiskerLeft (a.a) X` and `whiskerLeft a (whiskerLeft a X)` evaluate to
the SAME `4x4` block map `directSum I_2 (swap)` — `rfl`. -/
theorem bunchedBimonoidWhiskerOneCellAssocLeftMatrixSound :
    bunchedBimonoidEvalCell
        (CellExpr.whiskerLeft (CellExpr.vcomp bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen)
          bunchedBimonoidAddSigmaGen)
      = bunchedBimonoidEvalCell
        (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
          (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)) := rfl

/-- ★ **Associator (right dual) — matrix-sound.**  `whiskerRight X (a.a)` and `whiskerRight (whiskerRight X a) a`
share the `4x4` block map `directSum (swap) I_2` — `rfl`. -/
theorem bunchedBimonoidWhiskerOneCellAssocRightMatrixSound :
    bunchedBimonoidEvalCell
        (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen
          (CellExpr.vcomp bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen))
      = bunchedBimonoidEvalCell
        (CellExpr.whiskerRight
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen)
          bunchedBimonoidAdditiveGen) := rfl

/-- ★ **Unitor (left) — matrix-sound.**  `whiskerLeft (id *) X ~ X`: the identity 1-cell has width 0, so its block
`directSum I_0 (swap)` is the swap itself — `rfl`. -/
theorem bunchedBimonoidWhiskerOneCellUnitorLeftMatrixSound :
    bunchedBimonoidEvalCell (CellExpr.whiskerLeft bunchedBimonoidIdOne bunchedBimonoidAddSigmaGen)
      = bunchedBimonoidEvalCell bunchedBimonoidAddSigmaGen := rfl

/-- ★ **Unitor (right dual) — matrix-sound.**  `whiskerRight X (id *) ~ X` — `rfl`. -/
theorem bunchedBimonoidWhiskerOneCellUnitorRightMatrixSound :
    bunchedBimonoidEvalCell (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidIdOne)
      = bunchedBimonoidEvalCell bunchedBimonoidAddSigmaGen := rfl

/-- ★ **Whisker left/right commute — matrix-sound.**  `whiskerRight (whiskerLeft a X) a` and
`whiskerLeft a (whiskerRight X a)` share the `4x4` block map `directSum I_1 (directSum (swap) I_1)` — `rfl`. -/
theorem bunchedBimonoidWhiskerOneCellCommuteMatrixSound :
    bunchedBimonoidEvalCell
        (CellExpr.whiskerRight (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
          bunchedBimonoidAdditiveGen)
      = bunchedBimonoidEvalCell
        (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
          (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen)) := rfl

/-! # =========================================================================================
    # W2 — NON-BOUNDARY-PARALLELISM: the design reason they are not `StrictAxiomRel` rows
    # =========================================================================================
-/

/-- The associator LHS's boundary source is `vcomp (vcomp a a) (bs X)` — `rfl`. -/
theorem bunchedBimonoidWhiskerOneCellAssocSourceLHS :
    boundarySource
        (CellExpr.whiskerLeft (CellExpr.vcomp bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen)
          bunchedBimonoidAddSigmaGen)
      = CellExpr.vcomp (CellExpr.vcomp bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen)
          (boundarySource bunchedBimonoidAddSigmaGen) := rfl

/-- The associator RHS's boundary source is `vcomp a (vcomp a (bs X))` — `rfl`.  Structurally DISTINCT from the LHS
source (the left factor is `a`, not `vcomp a a`): the two differ by exactly `vcompAssoc`. -/
theorem bunchedBimonoidWhiskerOneCellAssocSourceRHS :
    boundarySource
        (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
          (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen))
      = CellExpr.vcomp bunchedBimonoidAdditiveGen
          (CellExpr.vcomp bunchedBimonoidAdditiveGen (boundarySource bunchedBimonoidAddSigmaGen)) := rfl

/-- ★★ **The associator is NON-boundary-parallel** — its two legs have DIFFERENT boundary sources, so it cannot be a
cast-free `StrictAxiomRel` row.  The left factors clash (`vcomp a a` vs `a` = `gen`). -/
theorem bunchedBimonoidWhiskerOneCellAssocSourcesNotParallel :
    boundarySource
        (CellExpr.whiskerLeft (CellExpr.vcomp bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen)
          bunchedBimonoidAddSigmaGen)
      ≠ boundarySource
        (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
          (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)) := by
  intro hEq
  injection hEq with _ hLeft
  nomatch hLeft

/-- ★ **The identity-whisker unitor is NON-boundary-parallel** — `boundarySource (whiskerLeft (id *) X) = vcomp (id *)
(bs X)` differs from `boundarySource X = bs X` by exactly `vcompUnitLeft`. -/
theorem bunchedBimonoidWhiskerOneCellUnitorSourcesNotParallel :
    boundarySource (CellExpr.whiskerLeft bunchedBimonoidIdOne bunchedBimonoidAddSigmaGen)
      ≠ boundarySource bunchedBimonoidAddSigmaGen := by
  intro hEq
  injection hEq with _ hLeft
  nomatch hLeft

/-- Contrast — the EXISTING `vcompAssoc` row IS boundary-parallel: `boundarySource ((A.B).C) = boundarySource
(A.(B.C))` by `rfl`.  This is the cast-free invariant the three coherences violate. -/
theorem bunchedBimonoidVcompAssocBoundaryParallel :
    boundarySource
        (CellExpr.vcomp (CellExpr.vcomp bunchedBimonoidAddSigmaGen bunchedBimonoidAddSigmaGen)
          bunchedBimonoidAddSigmaGen)
      = boundarySource
        (CellExpr.vcomp bunchedBimonoidAddSigmaGen
          (CellExpr.vcomp bunchedBimonoidAddSigmaGen bunchedBimonoidAddSigmaGen)) := rfl

/-! # =========================================================================================
    # W3 — the WP-PROP-owned residual marker (WALLED, NOT landed) + the honesty ledger
    # =========================================================================================
-/

/-- ★★★ **WALLED (r19-scoped) — the identity-whisker UNITOR is the SOLE whisker-vs-1-cell residual not landed in
`StrictAxiomRel`.**  `= false` records that a walled whisker-coherence residual remains.  As of WP-PROP r19 the
associator (both duals) and the whisker left/right commute ARE `StrictAxiomRel` rows
(`WalkingBunchedBimonoidWhiskerCoherenceLanded`); this marker now tracks ONLY the identity-whisker unitor
`whiskerLeft (id c) X ~ X`, which stays OUT because it is chain-UNSOUND for a free `c`
(`whiskerIdentityUnitor_not_conv`, machine-checked) — landing it as a free row would falsify the shipped ★★
`Steiner/SoundnessFull.linearizeFullSoundness`.  Machine-checked here (all still valid): the five instances are
matrix-sound by `rfl` (`...MatrixSound`), the associator + unitor are non-parallel
(`...SourcesNotParallel` — true, but the r19 round showed non-parallel is NOT chain-unsound), and the existing
`vcompAssoc` is the boundary-parallel contrast.  The `recCombConv`-over-cells lift stays gated on the pinned
unitor.  The four star owners keep their name and `= false` value byte-intact (cross-file, not edited); NO
fabricated star flip.  Zero-axiom (per-decl `#assert_no_axioms` in the twin). -/
def fxBunchedBimonoid_whiskerOneCellCoherencesWalledNotLanded : Bool := false

end FX1Poly.Polygraph.Omega
