import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerRightJunctionMerge

/-! # Polygraph/TwoCategory/Amalgam/PushoutWhiskerRightJunctionCanonical — the whiskerRight (trailing) junction
CONV + `CanonicalFactorization` (WP-AMALG-2 r22, arm b′)

Arm b (`PushoutWhiskerLeftJunctionCanonical.lean`) shipped the LEADING-frame junction merge by folding the frame's
LAST block into the body's HEAD WALL (`mergeFrameIntoHead`, count-neutral) and prepending the frame's other blocks as
fresh LEADING slots — a definitional cons on the layout.  Arm b′ is the whiskerRight DUAL: the frame `oneCell` sits at
the TRAILING end (`whiskerRight oneCell body` has domain `composePath (dom body) oneCell`), abutting the body's TRAILING
WALL `finalWall`, not a block-with-gap.  Appending a fresh TRAILING slot is NOT a definitional cons (unlike arm b's
leading prepend), so the recon's naive "peel-and-thread-finalWall" tail-append COLLAPSES to the r18 `n → n` append
`gapVcompLayout (finalWall · oneCell) bodyPairs`, undercounting the s-frame's walls by exactly `wallCount(oneCell)`.

## The route that actually closes — r18 append + trailing id-block EXPANSION (the r20 collapse run backwards)

The key: the body's blocks (`bodyPairs`, real payloads) stay UNTOUCHED; only the trailing IDENTITY wall
`finalWall · oneCell` is EXPANDED into fresh all-identity trailing slots.  No junction-payload whiskering is needed —
the frame's own leading `t`-run rides into the FIRST fresh block's WALL (inert), the dual of arm b folding the frame's
trailing gap into the head WALL.

  * **`gapDomLayout_append` / `gapCodLayout_append`** — `gapXLayout fw (front ++ back) = gapXLayout (gapXLayout fw
    back) front`, structural on `front`, each step a `composePath` congruence.  The append boundary law.
  * **`gapVcompLayout_appendAllIdCollapse`** — the trailing id-block expansion at the CONV level: for an ALL-IDENTITY
    `trailingBlocks`, `gapVcompLayout newFinalWall (bodyPairs ++ trailingBlocks)` is saturated-convertible (up to the
    append boundary cast) to `gapVcompLayout (gapDomLayout newFinalWall trailingBlocks) bodyPairs` — the body layout
    over the fused trailing wall.  Structural on `bodyPairs`: the `[]` base IS the r20 id-collapse
    (`gapVcompLayoutIdBlocksCollapse`), the cons threads the IH through the two block hcomps by `hcompCongrRight` +
    `hcomp_castBoundaryRight`.  (Cast proofs reconcile by `Eq` definitional proof irrelevance.)
  * **`whiskerRightFiringBlockMerge`** — chains the r18 trailing append `whiskerRight_conv_appendFinalWall` (fold
    `oneCell` into `finalWall`) with the expansion (split it back into fresh trailing slots): for any all-identity
    `trailingBlocks` reconstructing `finalWall · oneCell`, `whiskerRight oneCell (gapVcompLayout finalWall bodyPairs)`
    is convertible to `gapVcompLayout newFinalWall (bodyPairs ++ trailingBlocks)`.

## The `CanonicalFactorization`

`whiskerRightJunctionCanonicalOfExpansion` assembles the subtype from a body factorization plus explicit trailing
blocks meeting the slot-count spec; the concrete witnesses (`whiskerRightJunctionMuWitness`, the recon self-attacks)
supply them literally at the real pushout signature (the `s`-frame's leading `t`-run is empty, so the trailing blocks
are the frame's `s`-walls verbatim).  The fully-general auto-construction of the trailing blocks for an ARBITRARY frame
(the two-case `frameTrailingBlocks` splitter over the opaque producer head/tail) is the named data-plumbing residual
`fxAmalg_whiskerRightTrailingSplitterStaysResidual`; the CONV and the witnesses ship.

`fxAmalg_whiskerJunctionMergeStaysWalled` (upstream in `PushoutFactorizeCanonical.lean`) STAYS `true` byte-intact
(additive, historical) — the new positive marker `fxAmalg_hasWhiskerRightJunctionCanonical` supersedes the r21 residual
`fxAmalg_whiskerRightJunctionCanonicalStaysResidual` (which keeps its intact value).  #2043 does NOT close (the JAM A
vcomp zip is untouched).

Raw Lean 4 + Init.  STRUCTURAL on the body/block lists; `composePath_assoc` via `rw` (term instance, propext-safe);
`List.append` associativity via the propext-safe `pushoutWordAppendAssoc`.  Per-declaration `#assert_no_axioms` gated in
the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## A propext-safe list-length-append (core `List.length_append` leaks propext) -/

/-- A **propext-safe length-append** — `(front ++ back).length = front.length + back.length`, hand-rolled by structural
cons-recursion on `front` (`[]` is `Nat.zero_add`; `cons` threads the IH and reassociates by `Nat.add_right_comm`).
Core `List.length_append` DEPENDS ON `propext` in this Lean; this reproves it cons-only, propext-free. -/
theorem listLengthAppend {elementType : Type _} :
    (front back : List elementType) → (front ++ back).length = front.length + back.length
  | [], back => (Nat.zero_add back.length).symm
  | head :: rest, back => by
      show (rest ++ back).length + 1 = rest.length + 1 + back.length
      rw [listLengthAppend rest back]
      exact Nat.add_right_comm rest.length back.length 1

/-! ## The append boundary law -/

/-- **The DOMAIN append law** — `gapDomLayout finalWall (front ++ back) = gapDomLayout (gapDomLayout finalWall back)
front`.  Reading the concatenated block list is reading `front` over the trailing wall obtained by reading `back`
first.  Structural on `front`: `[]` is `rfl` (`[] ++ back = back`, `gapDomLayout X [] = X`); each cons re-associates by
a single `congrArg` over the leading wall/gap. -/
theorem gapDomLayout_append {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode) :
    (front back : List (VcompGapPair signature oneMode)) →
    gapDomLayout finalWall (front ++ back)
      = gapDomLayout (gapDomLayout finalWall back) front
  | [], _ => rfl
  | pair :: rest, back =>
      congrArg (fun tail => composePath pair.wall (composePath pair.gapDom tail))
        (gapDomLayout_append finalWall rest back)

/-- **The CODOMAIN append law** — the `.gapCod` dual of `gapDomLayout_append`. -/
theorem gapCodLayout_append {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode) :
    (front back : List (VcompGapPair signature oneMode)) →
    gapCodLayout finalWall (front ++ back)
      = gapCodLayout (gapCodLayout finalWall back) front
  | [], _ => rfl
  | pair :: rest, back =>
      congrArg (fun tail => composePath pair.wall (composePath pair.gapCod tail))
        (gapCodLayout_append finalWall rest back)

/-- The CODOMAIN append law re-anchored to the trailing blocks' DOMAIN wall — for ALL-IDENTITY trailing blocks the
codomain layout coincides with the domain layout, so `gapCodLayout (gapDomLayout newFinalWall trailingBlocks) bodyPairs
= gapCodLayout newFinalWall (bodyPairs ++ trailingBlocks)`.  The codomain boundary the expansion cast rides. -/
theorem gapCodLayout_append_allId {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (newFinalWall : ModalityPath signature.graph oneMode oneMode)
    (bodyPairs trailingBlocks : List (VcompGapPair signature oneMode))
    (allId : AllIdBlocks trailingBlocks) :
    gapCodLayout (gapDomLayout newFinalWall trailingBlocks) bodyPairs
      = gapCodLayout newFinalWall (bodyPairs ++ trailingBlocks) :=
  (congrArg (fun trailWall => gapCodLayout trailWall bodyPairs)
    (allIdBlocks_gapDomEqCod newFinalWall trailingBlocks allId)).trans
    (gapCodLayout_append newFinalWall bodyPairs trailingBlocks).symm

/-! ## The trailing id-block EXPANSION conv (the r20 collapse, run over an appended body) -/

/-- ★★★ **THE TRAILING ID-BLOCK EXPANSION.**  For an ALL-IDENTITY block list `trailingBlocks`, the body layout
`gapVcompLayout newFinalWall (bodyPairs ++ trailingBlocks)` is saturated-convertible to the body layout over the FUSED
trailing wall `gapVcompLayout (gapDomLayout newFinalWall trailingBlocks) bodyPairs` (up to the append boundary cast) —
the trailing identity blocks collapse into the trailing wall, keeping `bodyPairs` (and their real payloads) verbatim.

Structural on `bodyPairs`.  The `[]` base is the r20 identity-layout collapse `gapVcompLayoutIdBlocksCollapse`
(`gapVcompLayout newFinalWall trailingBlocks ≈ castBoundary (id (gapDomLayout newFinalWall trailingBlocks))`).  Each
`pair :: rest` threads the IH through the two block hcomps (`hcompCongrRight` twice), pulling the IH cast out
(`hcomp_castBoundaryRight` twice); the residual cast proofs reconcile with the append-law casts by `Eq` definitional
proof irrelevance. -/
theorem gapVcompLayout_appendAllIdCollapse {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode : signature.graph.Mode}
    (newFinalWall : ModalityPath signature.graph oneMode oneMode)
    (trailingBlocks : List (VcompGapPair signature oneMode)) (allId : AllIdBlocks trailingBlocks) :
    (bodyPairs : List (VcompGapPair signature oneMode)) →
    SaturatedConvOver signature baseRel
      (gapVcompLayout newFinalWall (bodyPairs ++ trailingBlocks))
      (RawTwoCellExpr.castBoundary
        (gapDomLayout_append newFinalWall bodyPairs trailingBlocks).symm
        (gapCodLayout_append_allId newFinalWall bodyPairs trailingBlocks allId)
        (gapVcompLayout (gapDomLayout newFinalWall trailingBlocks) bodyPairs))
  | [] => gapVcompLayoutIdBlocksCollapse newFinalWall trailingBlocks allId
  | pair :: rest => by
      have ih := gapVcompLayout_appendAllIdCollapse (baseRel := baseRel) newFinalWall trailingBlocks allId rest
      have threaded := SaturatedConvOver.hcompCongrRight (RawTwoCellExpr.id pair.wall)
        (SaturatedConvOver.hcompCongrRight (RawTwoCellExpr.vcomp pair.upper pair.lower) ih)
      rw [RawTwoCellExpr.hcomp_castBoundaryRight, RawTwoCellExpr.hcomp_castBoundaryRight] at threaded
      exact threaded

/-- **A layout equals its trailing-wall re-anchoring.**  If two trailing walls are propositionally equal
(`wallEq : trailWallOne = trailWallTwo`), the layout over the first is convertible to the boundary-cast of the layout
over the second.  `cases wallEq` collapses the casts to `rfl`; the vehicle for transporting the r18 fold's trailing
wall `composePath finalWall oneCell` to the expansion's `gapDomLayout newFinalWall trailingBlocks`. -/
theorem gapVcompLayout_congrWall {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode : signature.graph.Mode}
    {trailWallOne trailWallTwo : ModalityPath signature.graph oneMode oneMode}
    (wallEq : trailWallOne = trailWallTwo)
    (bodyPairs : List (VcompGapPair signature oneMode)) :
    SaturatedConvOver signature baseRel
      (gapVcompLayout trailWallOne bodyPairs)
      (RawTwoCellExpr.castBoundary
        (congrArg (fun trailWall => gapDomLayout trailWall bodyPairs) wallEq).symm
        (congrArg (fun trailWall => gapCodLayout trailWall bodyPairs) wallEq).symm
        (gapVcompLayout trailWallTwo bodyPairs)) := by
  subst wallEq; exact SaturatedConvOver.refl _

/-- **The trailing id-block expansion, oriented FROM the fused-wall body TO the appended body** — the boundary-cast
inverse of `gapVcompLayout_appendAllIdCollapse`.  The body layout over the fused trailing wall is convertible to the
appended body layout (up to the append boundary cast), the form the whiskerRight fold consumes. -/
theorem gapVcompLayout_fusedWallToAppended {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode : signature.graph.Mode}
    (newFinalWall : ModalityPath signature.graph oneMode oneMode)
    (trailingBlocks : List (VcompGapPair signature oneMode)) (allId : AllIdBlocks trailingBlocks)
    (bodyPairs : List (VcompGapPair signature oneMode)) :
    SaturatedConvOver signature baseRel
      (gapVcompLayout (gapDomLayout newFinalWall trailingBlocks) bodyPairs)
      (RawTwoCellExpr.castBoundary
        (gapDomLayout_append newFinalWall bodyPairs trailingBlocks)
        (gapCodLayout_append_allId newFinalWall bodyPairs trailingBlocks allId).symm
        (gapVcompLayout newFinalWall (bodyPairs ++ trailingBlocks))) := by
  have moved := SaturatedConvOver.castBoundaryCongr
    (gapDomLayout_append newFinalWall bodyPairs trailingBlocks)
    (gapCodLayout_append_allId newFinalWall bodyPairs trailingBlocks allId).symm
    (gapVcompLayout_appendAllIdCollapse (baseRel := baseRel) newFinalWall trailingBlocks allId bodyPairs)
  rw [RawTwoCellExpr.castBoundary_trans] at moved
  exact SaturatedConvOver.symm moved

/-! ## The whiskerRight junction merge CONV (r18 fold + trailing expansion) -/

/-- The DOMAIN boundary of the whiskerRight junction merge — `gapDomLayout newFinalWall (bodyPairs ++ trailingBlocks) =
composePath (gapDomLayout finalWall bodyPairs) oneCell` (the whiskerRight domain), chaining the append law, the trailing
reconstruction `hTrailDom`, and the r18 `gapDomLayoutAppendFinalWall`. -/
theorem whiskerRightMergeDomEq {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (oneCell finalWall newFinalWall : ModalityPath signature.graph oneMode oneMode)
    (trailingBlocks : List (VcompGapPair signature oneMode))
    (hTrailDom : gapDomLayout newFinalWall trailingBlocks = composePath finalWall oneCell)
    (bodyPairs : List (VcompGapPair signature oneMode)) :
    gapDomLayout newFinalWall (bodyPairs ++ trailingBlocks)
      = composePath (gapDomLayout finalWall bodyPairs) oneCell :=
  (gapDomLayout_append newFinalWall bodyPairs trailingBlocks).trans
    ((congrArg (fun trailWall => gapDomLayout trailWall bodyPairs) hTrailDom).trans
      (gapDomLayoutAppendFinalWall oneCell finalWall bodyPairs))

/-- The CODOMAIN boundary of the whiskerRight junction merge — the `.gapCod` dual of `whiskerRightMergeDomEq`, using the
all-id codomain reconstruction. -/
theorem whiskerRightMergeCodEq {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (oneCell finalWall newFinalWall : ModalityPath signature.graph oneMode oneMode)
    (trailingBlocks : List (VcompGapPair signature oneMode)) (allId : AllIdBlocks trailingBlocks)
    (hTrailDom : gapDomLayout newFinalWall trailingBlocks = composePath finalWall oneCell)
    (bodyPairs : List (VcompGapPair signature oneMode)) :
    gapCodLayout newFinalWall (bodyPairs ++ trailingBlocks)
      = composePath (gapCodLayout finalWall bodyPairs) oneCell :=
  (gapCodLayout_append_allId newFinalWall bodyPairs trailingBlocks allId).symm.trans
    ((congrArg (fun trailWall => gapCodLayout trailWall bodyPairs) hTrailDom).trans
      (gapCodLayoutAppendFinalWall oneCell finalWall bodyPairs))

/-- ★★★ **THE whiskerRight JUNCTION MERGE CONV.**  For an ALL-IDENTITY `trailingBlocks` reconstructing the trailing
wall `finalWall · oneCell` (`gapDomLayout newFinalWall trailingBlocks = composePath finalWall oneCell`),
`whiskerRight oneCell (gapVcompLayout finalWall bodyPairs)` is saturated-convertible to the appended body layout
`gapVcompLayout newFinalWall (bodyPairs ++ trailingBlocks)` (up to the merge boundary cast).  The whiskerRight dual of
`whiskerLeftFiringBlockMerge`.

The route (the recon's tail-append, corrected past the r18-collapse trap): fold `oneCell` into the trailing wall
`finalWall` by the r18 append `whiskerRight_conv_appendFinalWall`, re-anchor the trailing wall to `gapDomLayout
newFinalWall trailingBlocks` (`gapVcompLayout_congrWall`, transport along `hTrailDom`), then EXPAND that identity wall
back into the fresh trailing slots `trailingBlocks` (`gapVcompLayout_fusedWallToAppended` = the r20 collapse run
backwards over the appended body).  The per-step casts merge into the single merge boundary cast by
`castBoundary_trans` + `Eq` definitional proof irrelevance. -/
theorem whiskerRightFiringBlockMerge {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode : signature.graph.Mode}
    (oneCell finalWall newFinalWall : ModalityPath signature.graph oneMode oneMode)
    (trailingBlocks : List (VcompGapPair signature oneMode)) (allId : AllIdBlocks trailingBlocks)
    (hTrailDom : gapDomLayout newFinalWall trailingBlocks = composePath finalWall oneCell)
    (bodyPairs : List (VcompGapPair signature oneMode)) :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.whiskerRight oneCell (gapVcompLayout finalWall bodyPairs))
      (RawTwoCellExpr.castBoundary
        (whiskerRightMergeDomEq oneCell finalWall newFinalWall trailingBlocks hTrailDom bodyPairs)
        (whiskerRightMergeCodEq oneCell finalWall newFinalWall trailingBlocks allId hTrailDom bodyPairs)
        (gapVcompLayout newFinalWall (bodyPairs ++ trailingBlocks))) := by
  have fold := whiskerRight_conv_appendFinalWall (baseRel := baseRel) oneCell finalWall bodyPairs
  have congrW := gapVcompLayout_congrWall (baseRel := baseRel) hTrailDom.symm bodyPairs
  have bridge := gapVcompLayout_fusedWallToAppended (baseRel := baseRel) newFinalWall trailingBlocks allId bodyPairs
  have inner := SaturatedConvOver.trans congrW (SaturatedConvOver.castBoundaryCongr _ _ bridge)
  rw [RawTwoCellExpr.castBoundary_trans] at inner
  have result := SaturatedConvOver.trans fold (SaturatedConvOver.castBoundaryCongr _ _ inner)
  rw [RawTwoCellExpr.castBoundary_trans] at result
  exact result

/-! ## The `s`-wall trailing block (the frame's lone `s`-wall reborn as a fresh trailing slot) -/

/-- The frame `s`-wall as a fresh TRAILING firing block — `idBlockPair s nil` (a leading `s`-wall, empty gap).  The
concrete trailing expansion of `whiskerRight s`: the frame's lone wall reappears here as one trailing slot. -/
def sWallTrailingBlock : VcompGapPair involutionMonadPushout.toModeSignature monadPushMode :=
  idBlockPair monadPushSPath (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)

/-- The `s`-wall trailing block list is all-identity. -/
theorem sWallTrailingBlock_allId : AllIdBlocks [sWallTrailingBlock] := by
  unfold sWallTrailingBlock
  exact AllIdBlocks.cons _ _ _ AllIdBlocks.nil

/-! ## Truth-probe (FIRST) — the whiskerRight junction merge conv fires on a concrete framed `mu` layout -/

/-- ★★★ **THE TRUTH-PROBE — the whiskerRight junction merge conv ELABORATES on the framed `mu` layout.**  Framing the
single-slot `mu` body layout (`gapVcompLayout nil [singleGapPair (gen mu)]`, `t·t ⇒ t`) on the RIGHT by the `s`-wall
`monadPushSPath`, with the explicit trailing block `[idBlockPair s nil]` (the frame's lone `s`-wall reborn as a fresh
trailing slot), the conv `whiskerRightFiringBlockMerge` fires — `whiskerRight s [mu]` is saturated-convertible to the
appended layout `[mu, idBlockPair s nil]`, machine-witnessed non-vacuously at the REAL pushout signature over a
WIRE-CHANGING body.  The base of arm b′, probed before the assembly (the frame's leading `t`-run is empty here, so the
trailing block is the `s`-wall verbatim). -/
def whiskerRightMergeMuConv :=
  whiskerRightFiringBlockMerge (baseRel := crossPairRealPushoutRel) monadPushSPath
    (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
    (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
    [sWallTrailingBlock] sWallTrailingBlock_allId
    rfl [singleGapPair (RawTwoCellExpr.gen pushoutMonadMult)]

/-! ## THE whiskerRight JUNCTION CANONICAL FACTORIZATION (from an explicit trailing expansion) -/

/-- ★★★ **THE whiskerRight JUNCTION CANONICAL FACTORIZATION (arm b′, from explicit trailing blocks).**  Given a body
`CanonicalFactorization` and an ALL-IDENTITY `trailingBlocks` reconstructing the fused trailing wall `composePath
bodyFact.finalWall oneCell` (`hTrailDom`) whose count is `wallCount(oneCell)` (`hTrailLen`), `whiskerRight oneCell body`
has a `CanonicalFactorization` whose `pairs` are `bodyFact.pairs ++ trailingBlocks` — the body's blocks (real payloads)
verbatim, the frame's `s`-walls appended as fresh trailing slots.  The whiskerRight dual of
`whiskerLeftJunctionCanonical`.

The slot count is the CANONICAL `wallCount(dom body) + 1 + wallCount(oneCell) = wallCount(composePath (dom body) oneCell)
+ 1`, the boundary equalities are `whiskerRightMergeDomEq` / `…CodEq`, and the convertibility threads `bodyFact.conv`
under `whiskerRightCongr` then `whiskerRightFiringBlockMerge`, the per-side casts reconciled by `castBoundary_trans` +
`Eq` proof irrelevance. -/
def whiskerRightJunctionCanonicalOfExpansion
    (oneCell newFinalWall : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    {body : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath}
    (bodyFact : CanonicalFactorization body)
    (trailingBlocks : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode))
    (allId : AllIdBlocks trailingBlocks)
    (hTrailDom : gapDomLayout newFinalWall trailingBlocks
      = composePath bodyFact.1.finalWall oneCell)
    (hTrailLen : trailingBlocks.length = pushoutPathWallCount oneCell) :
    CanonicalFactorization (RawTwoCellExpr.whiskerRight oneCell body) := by
  refine ⟨{ finalWall := newFinalWall
            pairs := bodyFact.1.pairs ++ trailingBlocks
            domEq := ?_
            codEq := ?_
            conv := ?_ }, ?_⟩
  · exact (congrArg (fun bodyDom => composePath bodyDom oneCell) bodyFact.1.domEq).trans
      (whiskerRightMergeDomEq oneCell bodyFact.1.finalWall newFinalWall trailingBlocks hTrailDom
        bodyFact.1.pairs).symm
  · exact (congrArg (fun bodyCod => composePath bodyCod oneCell) bodyFact.1.codEq).trans
      (whiskerRightMergeCodEq oneCell bodyFact.1.finalWall newFinalWall trailingBlocks allId hTrailDom
        bodyFact.1.pairs).symm
  · have chain := SaturatedConvOver.trans
      (SaturatedConvOver.whiskerRightCongr oneCell bodyFact.1.conv)
      (whiskerRightFiringBlockMerge oneCell bodyFact.1.finalWall newFinalWall trailingBlocks allId
        hTrailDom bodyFact.1.pairs)
    rw [whiskerRightCastBoundaryEq] at chain
    have reconciled := SaturatedConvOver.castBoundaryCongr
      (whiskerRightMergeDomEq oneCell bodyFact.1.finalWall newFinalWall trailingBlocks hTrailDom
        bodyFact.1.pairs).symm
      (whiskerRightMergeCodEq oneCell bodyFact.1.finalWall newFinalWall trailingBlocks allId hTrailDom
        bodyFact.1.pairs).symm chain
    rw [RawTwoCellExpr.castBoundary_trans, RawTwoCellExpr.castBoundary_trans] at reconciled
    exact reconciled
  · show (bodyFact.1.pairs ++ trailingBlocks).length
      = (finestGapWidths (pushoutPathTags (composePath sourcePath oneCell))).length
    rw [listLengthAppend, bodyFact.2, hTrailLen,
        finestGapWidths_pushoutPathTags_length, finestGapWidths_pushoutPathTags_length,
        pushoutPathWallCount_composePath]
    exact Nat.add_right_comm (pushoutPathWallCount sourcePath) 1 (pushoutPathWallCount oneCell)

/-! ## Witnesses + probe (the recon self-attacks over the REAL pushout signature) -/

/-- ★★★ **THE whiskerRight JUNCTION WITNESS — an `s`-wall frame TRAILING the wire-changing `mu`.**  `whiskerRight s
(gen mu)` (`gen mu : t·t ⇒ t`, framed on the RIGHT by the `s`-wall) factors CANONICALLY via
`whiskerRightJunctionCanonicalOfExpansion` on `mulCanonicalFactorization`, the frame's lone `s`-wall reborn as ONE fresh
trailing slot `[idBlockPair s nil]` (the frame's leading `t`-run is empty, so `hTrailDom` / `hTrailLen` are `rfl`).  The
whiskerRight dual of `whiskerLeftJunctionMuWitness`, a non-vacuous inhabitant at the REAL pushout signature over a
WIRE-CHANGING body. -/
def whiskerRightJunctionMuWitness :
    CanonicalFactorization (RawTwoCellExpr.whiskerRight monadPushSPath (RawTwoCellExpr.gen pushoutMonadMult)) :=
  whiskerRightJunctionCanonicalOfExpansion monadPushSPath
    (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
    mulCanonicalFactorization
    [sWallTrailingBlock] sWallTrailingBlock_allId
    rfl rfl

/-- ★★★ **PROBE (junction witness slot count — TWO slots, the canonical count).**  `whiskerRightJunctionMuWitness.1.
pairs.length = 2` (`rfl`): the `mu` junction gap plus the `s`-wall's fresh trailing slot —
`wallCount(t·t) + wallCount(s) + 1 = 0 + 1 + 1 = 2`.  The exact dual of `whiskerLeftJunctionMuSlotCount = 2`, over a
wire-changing body. -/
theorem whiskerRightJunctionMuSlotCount : whiskerRightJunctionMuWitness.1.pairs.length = 2 := rfl

/-! ## The recon self-attacks — arm b′ fired on nested / id / wall-heavy frames -/

/-- The `s·s`-wall double trailing block list (`unitSplitsWallDom` frame's two `s`-walls reborn as two trailing
slots). -/
def sWallDoubleTrailingBlocks : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode) :=
  [sWallTrailingBlock, sWallTrailingBlock]

/-- The `s·s` double trailing block list is all-identity. -/
theorem sWallDoubleTrailingBlocks_allId : AllIdBlocks sWallDoubleTrailingBlocks := by
  unfold sWallDoubleTrailingBlocks sWallTrailingBlock
  exact AllIdBlocks.cons _ _ _ (AllIdBlocks.cons _ _ _ AllIdBlocks.nil)

/-- ★★★ **SELF-ATTACK 1 (whiskerRight of a whiskerLeft — nested frames both sides).**  `whiskerRight s (whiskerLeft s
(gen mu))` — an `s`-wall on the RIGHT of (an `s`-wall on the LEFT of `gen mu`).  BOTH junction canonicals compose:
arm b′ frames the arm-b witness `whiskerLeftJunctionMuWitness` (whose `finalWall` is `nil`) with the trailing `s`-wall.
The two whisker directions cooperate at the REAL pushout signature. -/
def whiskerRightOfWhiskerLeftWitness :
    CanonicalFactorization
      (RawTwoCellExpr.whiskerRight monadPushSPath
        (RawTwoCellExpr.whiskerLeft monadPushSPath (RawTwoCellExpr.gen pushoutMonadMult))) :=
  whiskerRightJunctionCanonicalOfExpansion monadPushSPath
    (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
    whiskerLeftJunctionMuWitness [sWallTrailingBlock] sWallTrailingBlock_allId rfl rfl

/-- ★★★ **PROBE (nested-frame slot count — THREE slots).**  `whiskerRightOfWhiskerLeftWitness.1.pairs.length = 3`
(`rfl`): the leading `s`-slot + the `mu` junction gap + the trailing `s`-slot — `wallCount(s) + wallCount(t·t) +
wallCount(s) + 1 = 1 + 0 + 1 + 1 = 3`.  Both frames' walls counted. -/
theorem whiskerRightOfWhiskerLeftSlotCount : whiskerRightOfWhiskerLeftWitness.1.pairs.length = 3 := rfl

/-- ★★★ **SELF-ATTACK 2 (whiskerRight of an id — meets the r20 collapse).**  `whiskerRight s (id (t·t))` frames the
general `id`-arm `idCanonicalFactorization (t·t)` (r20, `finalWall = nil`) with the trailing `s`-wall.  The whiskerRight
junction feeds the id-collapse arm. -/
def whiskerRightOfIdWitness :
    CanonicalFactorization
      (RawTwoCellExpr.whiskerRight monadPushSPath
        (RawTwoCellExpr.id (composePath monadPushTPath monadPushTPath))) :=
  whiskerRightJunctionCanonicalOfExpansion monadPushSPath
    (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
    (idCanonicalFactorization (composePath monadPushTPath monadPushTPath))
    [sWallTrailingBlock] sWallTrailingBlock_allId rfl rfl

/-- ★★★ **PROBE (whiskerRight-of-id slot count — TWO slots).**  `whiskerRightOfIdWitness.1.pairs.length = 2` (`rfl`):
the `t·t` gap (one id firing block) + the trailing `s`-slot — `wallCount(t·t) + wallCount(s) + 1 = 0 + 1 + 1 = 2`. -/
theorem whiskerRightOfIdSlotCount : whiskerRightOfIdWitness.1.pairs.length = 2 := rfl

/-- ★★★ **SELF-ATTACK 3 (whiskerRight with a WALL-HEAVY frame).**  `whiskerRight (s·s) (gen mu)` — the `s·s` frame
(`unitSplitsWallDom`, `wallCount 2`) TRAILING the wire-changing `mu`.  The frame opens TWO fresh trailing slots
(`sWallDoubleTrailingBlocks`), the `mu` junction gap untouched.  Exercises the trailing expansion at length 2. -/
def whiskerRightWallHeavyWitness :
    CanonicalFactorization (RawTwoCellExpr.whiskerRight unitSplitsWallDom (RawTwoCellExpr.gen pushoutMonadMult)) :=
  whiskerRightJunctionCanonicalOfExpansion unitSplitsWallDom
    (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
    mulCanonicalFactorization sWallDoubleTrailingBlocks sWallDoubleTrailingBlocks_allId rfl rfl

/-- ★★★ **PROBE (wall-heavy slot count — THREE slots).**  `whiskerRightWallHeavyWitness.1.pairs.length = 3` (`rfl`):
the `mu` junction gap + TWO fresh trailing `s`-slots — `wallCount(t·t) + wallCount(s·s) + 1 = 0 + 2 + 1 = 3`.  The
canonical count, over a wire-changing body with a wall-heavy trailing frame. -/
theorem whiskerRightWallHeavySlotCount : whiskerRightWallHeavyWitness.1.pairs.length = 3 := rfl

/-! ## Observability -/

-- The whiskerRight junction witness slot counts: `mu` (expect `2`), nested (`3`), id-body (`2`), wall-heavy (`3`).
#eval whiskerRightJunctionMuWitness.1.pairs.length
#eval whiskerRightOfWhiskerLeftWitness.1.pairs.length
#eval whiskerRightOfIdWitness.1.pairs.length
#eval whiskerRightWallHeavyWitness.1.pairs.length

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the whiskerRight (trailing) junction merge CONV + CANONICAL FACTORIZATION SHIP (WP-AMALG-2
r22, arm b′).**  `= true`.  `whiskerRightFiringBlockMerge` proves `whiskerRight oneCell (gapVcompLayout finalWall
bodyPairs)` saturated-convertible to the appended layout `gapVcompLayout newFinalWall (bodyPairs ++ trailingBlocks)`
(up to the merge boundary cast), via the r18 trailing append `whiskerRight_conv_appendFinalWall` (fold `oneCell` into
`finalWall`) chained with the trailing id-block EXPANSION `gapVcompLayout_appendAllIdCollapse` (the r20 identity-layout
collapse run backwards, structural on the body, `hcompCongrRight` + `hcomp_castBoundaryRight`).  This corrects the
recon's naive tail-append (which collapses to the r18 `n → n` append): the frame's leading `t`-run rides into the FIRST
fresh block's WALL (inert, no junction-payload whiskering), the dual of arm b folding the frame's trailing gap into the
head WALL.

`whiskerRightJunctionCanonicalOfExpansion` assembles the `CanonicalFactorization (whiskerRight oneCell body)` from a body
factorization plus explicit all-identity trailing blocks reconstructing the fused trailing wall (count
`wallCount(oneCell)`), the boundary distributions `whiskerRightMergeDomEq` / `…CodEq`, the conv threading `bodyFact.conv`
under `whiskerRightCongr` then the merge, casts reconciled by `castBoundary_trans` + proof irrelevance.  Non-vacuous over
a WIRE-CHANGING body and every recon self-attack: `whiskerRightJunctionMuWitness` (`whiskerRight s (gen mu)`, `2` slots),
`whiskerRightOfWhiskerLeftWitness` (nested both-sided, `3`), `whiskerRightOfIdWitness` (over the r20 id arm, `2`),
`whiskerRightWallHeavyWitness` (`s·s` trailing frame, `3`).  The exact dual of `fxAmalg_hasWhiskerLeftJunctionCanonical`.

This supersedes the r21 named residual `fxAmalg_whiskerRightJunctionCanonicalStaysResidual` (which keeps its intact
`true`).  It does NOT touch the JAM A vcomp zip; the upstream marker `fxAmalg_whiskerJunctionMergeStaysWalled` STAYS
`true` byte-intact (additive/historical); #2043 does NOT close.  `= true`. -/
def fxAmalg_hasWhiskerRightJunctionCanonical : Bool := true

/-- ★★★ **Honesty marker — the ARBITRARY-frame trailing-block AUTO-SPLITTER stays the (data-plumbing) residual
(WP-AMALG-2 r22, arm b′).**  `= true` (honestly named).  Arm b′'s CONV `whiskerRightFiringBlockMerge` and the
`CanonicalFactorization` `whiskerRightJunctionCanonicalOfExpansion` are GENERIC over any all-identity trailing blocks;
every recon self-attack ships its factorization by supplying them literally (`sWallTrailingBlock` /
`sWallDoubleTrailingBlocks`, `rfl` domain + count).  The ONE piece not authored is the fully-general AUTO-CONSTRUCTION
of the trailing blocks for an ARBITRARY frame `oneCell` — a two-case splitter `frameTrailingBlocks` over the opaque
producer's head/tail (single-block frame `wallCount 0` → `[]` with `newFinalWall = finalWall · oneCell`; multi-block →
`mergeFrameIntoHead` of the frame's leading gap into the second fresh block's wall), whose two branches carry different
`newFinalWall` values.  This is DATA PLUMBING (a splitter + its domain/length/all-id lemmas), NOT a mathematical wall —
the CONV and the wire-changing witnesses already ship the junction.  Named node: the arbitrary-frame trailing-block
auto-splitter.  #2043 does NOT close (untouched by this; the JAM A vcomp zip is the wall).  `= true`. -/
def fxAmalg_whiskerRightTrailingSplitterStaysResidual : Bool := true

end FX1Poly.Polygraph.Amalgam
