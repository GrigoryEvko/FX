import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeVcomp
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadLawRelation
import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchSaturated

import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordVcompGen
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaGen
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDecisionGen
-- `one_le_cellSize` (the conv-FREE fuel lemma used by `monadNormalizeCellFueledGen`) now lives in the conv-FREE leaf
-- `MonadCellSize`; importing it directly (instead of `MonadWordProblem`) keeps this native-decider file off the
-- pure-bespoke Δ chain (MONAD-R7 r4 micro-relocation).
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadCellSize

/-! # WalkingMonad/MonadNormalizeGen — the born-generic normalize + the bespoke-free native decider
(POLY-TAB r6 monad re-founding, WAVE 2, Brick C — the completeness flip)

Assembles the born-generic completeness leg over `SaturatedConvOver monadModeSignature MonadLawRel`: the two whisker
`normalizeCell` cases, the `vcomp` case, the fueled recursion `monadNormalizeCellFueledGen`, and the packaged
`monadNormalizeGen : MonadNormalizesToCanonGen`.  Then the `convOfMapEqGen` reduction, the bespoke-free
canonicalization `monadSaturatedCanonicalizationGenNative`, the terminal native decider
`decideSaturatedConvOverMonadNative`, and the regression ties.  Every decl's constant-closure is free of
`MonadSaturatedTwoCellConv` (the exhaustive meta-walk in the audit twin certifies it).

Raw Lean 4 + Init; zero-axiom; STRUCTURAL (Nat fuel).  Per-declaration `#assert_no_axioms` in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The two WHISKER normalize cases, generic carrier -/

/-- ★ **Case `whiskerLeft W body` of `normalize`.**  Every left-whiskered free 2-cell is
`SaturatedConvOver monadModeSignature MonadLawRel`-convertible to the canonical word of its own fold, given the body already is.  The
canonical word of `whiskerLeft W body` is the body's canonical word with a `1`-run of length `W.length` prepended
(`canonCounts_whiskerLeft`); the conversion threads the induction hypothesis under the left whisker, pulls the cast
out of the body's canonical form, transports `W` to `t^W.length` (`monadPath_normalForm`), applies the LEFT whisker
word multiplicativity (`wordMul_whiskerLeftGen`), and collapses the boundary casts.  Pure free-2-category — no monad
law. -/
theorem monadNormalize_whiskerLeftGen {sourceMode middleMode targetMode : MonadMode}
    (oneCell : ModalityPath monadModeSignature.graph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath monadModeSignature.graph middleMode targetMode}
    (body : RawTwoCellExpr monadModeSignature oneCellG oneCellH)
    (ih : SaturatedConvOver monadModeSignature MonadLawRel body (canon body)) :
    SaturatedConvOver monadModeSignature MonadLawRel (RawTwoCellExpr.whiskerLeft oneCell body)
      (canon (RawTwoCellExpr.whiskerLeft oneCell body)) := by
  have hD : countsDomainPath (consReplicate 1 oneCell.length (canonCounts body))
      = composePath oneCell oneCellG := by
    rw [countsDomainPath_consReplicate_one, canonDomain_eq body]
    exact congrArg (fun p => composePath p oneCellG) (monadPath_normalForm oneCell).symm
  have hC : monadTPower (consReplicate 1 oneCell.length (canonCounts body)).length
      = composePath oneCell oneCellH := by
    rw [monadTPower_length_consReplicate_one, canonCodomain_eq body]
    exact congrArg (fun p => composePath p oneCellH) (monadPath_normalForm oneCell).symm
  rw [show canon (RawTwoCellExpr.whiskerLeft oneCell body)
        = RawTwoCellExpr.castBoundary hD hC
            (wordFromCounts (consReplicate 1 oneCell.length (canonCounts body)))
      from RawTwoCellExpr.castBoundary_wordCongr
        (canonDomain_eq (RawTwoCellExpr.whiskerLeft oneCell body))
        (canonCodomain_eq (RawTwoCellExpr.whiskerLeft oneCell body)) hD hC
        (canonCounts_whiskerLeft oneCell body)]
  refine SaturatedConvOver.trans
    (SaturatedConvOver.whiskerLeftCongr oneCell ih) ?_
  have outS : composePath oneCell (countsDomainPath (canonCounts body)) = composePath oneCell oneCellG :=
    congrArg (composePath oneCell) (canonDomain_eq body)
  have outT : composePath oneCell (monadTPower (canonCounts body).length) = composePath oneCell oneCellH :=
    congrArg (composePath oneCell) (canonCodomain_eq body)
  have pcS : composePath (monadTPower oneCell.length) (countsDomainPath (canonCounts body))
      = composePath oneCell (countsDomainPath (canonCounts body)) :=
    congrArg (fun p => composePath p (countsDomainPath (canonCounts body)))
      (monadPath_normalForm oneCell).symm
  have pcT : composePath (monadTPower oneCell.length) (monadTPower (canonCounts body).length)
      = composePath oneCell (monadTPower (canonCounts body).length) :=
    congrArg (fun p => composePath p (monadTPower (canonCounts body).length))
      (monadPath_normalForm oneCell).symm
  have hEq1 : RawTwoCellExpr.whiskerLeft oneCell (canon body)
      = RawTwoCellExpr.castBoundary (pcS.trans outS) (pcT.trans outT)
          (RawTwoCellExpr.whiskerLeft (monadTPower oneCell.length)
            (wordFromCounts (canonCounts body))) := by
    show RawTwoCellExpr.whiskerLeft oneCell
        (RawTwoCellExpr.castBoundary (canonDomain_eq body) (canonCodomain_eq body)
          (wordFromCounts (canonCounts body)))
      = _
    rw [RawTwoCellExpr.whiskerLeft_castBoundary,
        RawTwoCellExpr.whiskerLeft_pathCongr (monadPath_normalForm oneCell),
        RawTwoCellExpr.castBoundary_castBoundary]
    rfl
  rw [hEq1]
  have hcol := RawTwoCellExpr.castBoundary_double_collapse
    (countsDomainPath_consReplicate_one oneCell.length (canonCounts body))
    (monadTPower_length_consReplicate_one oneCell.length (canonCounts body))
    (pcS.trans outS) (pcT.trans outT) hD hC
    (wordFromCounts (consReplicate 1 oneCell.length (canonCounts body)))
  refine SaturatedConvOver.trans
    (SaturatedConvOver.castBoundaryCongr (pcS.trans outS) (pcT.trans outT)
      (wordMul_whiskerLeftGen oneCell.length (canonCounts body))) ?_
  exact hcol ▸ SaturatedConvOver.refl (baseRel := MonadLawRel) _

/-- ★ **Case `whiskerRight W body` of `normalize`.**  The right dual: every right-whiskered free 2-cell is
convertible to its own canonical word, whose counts is the body's counts with a `1`-run of length `W.length`
APPENDED (`canonCounts_whiskerRight`).  Same assembly through `whiskerRightCongr` + `whiskerRight_castBoundary` +
`whiskerRight_pathCongr` + `wordMul_whiskerRightGen` + the boundary-cast collapse.  Pure free-2-category — no monad
law. -/
theorem monadNormalize_whiskerRightGen {sourceMode middleMode targetMode : MonadMode}
    {oneCellF oneCellG : ModalityPath monadModeSignature.graph sourceMode middleMode}
    (oneCell : ModalityPath monadModeSignature.graph middleMode targetMode)
    (body : RawTwoCellExpr monadModeSignature oneCellF oneCellG)
    (ih : SaturatedConvOver monadModeSignature MonadLawRel body (canon body)) :
    SaturatedConvOver monadModeSignature MonadLawRel (RawTwoCellExpr.whiskerRight oneCell body)
      (canon (RawTwoCellExpr.whiskerRight oneCell body)) := by
  have hD : countsDomainPath (consAppend (canonCounts body) (monadOnes oneCell.length))
      = composePath oneCellF oneCell := by
    rw [countsDomainPath_consAppend_ones, canonDomain_eq body]
    exact congrArg (composePath oneCellF) (monadPath_normalForm oneCell).symm
  have hC : monadTPower (consAppend (canonCounts body) (monadOnes oneCell.length)).length
      = composePath oneCellG oneCell := by
    rw [monadTPower_length_consAppend_ones, canonCodomain_eq body]
    exact congrArg (composePath oneCellG) (monadPath_normalForm oneCell).symm
  rw [show canon (RawTwoCellExpr.whiskerRight oneCell body)
        = RawTwoCellExpr.castBoundary hD hC
            (wordFromCounts (consAppend (canonCounts body) (monadOnes oneCell.length)))
      from RawTwoCellExpr.castBoundary_wordCongr
        (canonDomain_eq (RawTwoCellExpr.whiskerRight oneCell body))
        (canonCodomain_eq (RawTwoCellExpr.whiskerRight oneCell body)) hD hC
        (canonCounts_whiskerRight oneCell body)]
  refine SaturatedConvOver.trans
    (SaturatedConvOver.whiskerRightCongr oneCell ih) ?_
  have outS : composePath (countsDomainPath (canonCounts body)) oneCell = composePath oneCellF oneCell :=
    congrArg (fun p => composePath p oneCell) (canonDomain_eq body)
  have outT : composePath (monadTPower (canonCounts body).length) oneCell = composePath oneCellG oneCell :=
    congrArg (fun p => composePath p oneCell) (canonCodomain_eq body)
  have pcS : composePath (countsDomainPath (canonCounts body)) (monadTPower oneCell.length)
      = composePath (countsDomainPath (canonCounts body)) oneCell :=
    congrArg (composePath (countsDomainPath (canonCounts body))) (monadPath_normalForm oneCell).symm
  have pcT : composePath (monadTPower (canonCounts body).length) (monadTPower oneCell.length)
      = composePath (monadTPower (canonCounts body).length) oneCell :=
    congrArg (composePath (monadTPower (canonCounts body).length)) (monadPath_normalForm oneCell).symm
  have hEq1 : RawTwoCellExpr.whiskerRight oneCell (canon body)
      = RawTwoCellExpr.castBoundary (pcS.trans outS) (pcT.trans outT)
          (RawTwoCellExpr.whiskerRight (monadTPower oneCell.length)
            (wordFromCounts (canonCounts body))) := by
    show RawTwoCellExpr.whiskerRight oneCell
        (RawTwoCellExpr.castBoundary (canonDomain_eq body) (canonCodomain_eq body)
          (wordFromCounts (canonCounts body)))
      = _
    rw [RawTwoCellExpr.whiskerRight_castBoundary,
        RawTwoCellExpr.whiskerRight_pathCongr (monadPath_normalForm oneCell),
        RawTwoCellExpr.castBoundary_castBoundary]
    rfl
  rw [hEq1]
  have hcol := RawTwoCellExpr.castBoundary_double_collapse
    (countsDomainPath_consAppend_ones (canonCounts body) oneCell.length)
    (monadTPower_length_consAppend_ones (canonCounts body) oneCell.length)
    (pcS.trans outS) (pcT.trans outT) hD hC
    (wordFromCounts (consAppend (canonCounts body) (monadOnes oneCell.length)))
  refine SaturatedConvOver.trans
    (SaturatedConvOver.castBoundaryCongr (pcS.trans outS) (pcT.trans outT)
      (wordMul_whiskerRightGen oneCell.length (canonCounts body))) ?_
  exact hcol ▸ SaturatedConvOver.refl (baseRel := MonadLawRel) _

/-! ## The vcomp normalize case, generic carrier -/

/-- ★ **Case `vcomp cellL cellR` of `normalize`.**  Every vertical composite is `SaturatedConvOver monadModeSignature MonadLawRel`-
convertible to the canonical word of its own fold, given both factors are.  The induction hypotheses give
`vcomp cellL cellR ≈ vcomp (canon cellL) (canon cellR)`; the two boundary casts extrude out of the vertical
composite (`vcomp_castBoundaryRight` / `vcomp_castBoundaryLeft` + cast fusion), exposing the VERTICAL word
multiplicativity `wordMul_vcompGen` under an outer cast; applying it lands `cast (word (composeCounts ccL ccR))`, which
the DATA bridge `canonCounts_vcomp` reconciles with `canon (vcomp cellL cellR)` (the boundary casts proof-
irrelevant).  This is the SOLE `normalizeCell` case that uses the monad LAWS (through `wordMul_vcompGen`). -/
theorem monadNormalize_vcompGen
    {sourcePath midPath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (cellL : RawTwoCellExpr monadModeSignature sourcePath midPath)
    (cellR : RawTwoCellExpr monadModeSignature midPath targetPath)
    (ihL : SaturatedConvOver monadModeSignature MonadLawRel cellL (canon cellL))
    (ihR : SaturatedConvOver monadModeSignature MonadLawRel cellR (canon cellR)) :
    SaturatedConvOver monadModeSignature MonadLawRel (RawTwoCellExpr.vcomp cellL cellR)
      (canon (RawTwoCellExpr.vcomp cellL cellR)) := by
  have hlen : (canonCounts cellL).length = listSum (canonCounts cellR) := by
    rw [canonCounts_length cellL, ← countsDomainPath_length_eq_listSum (canonCounts cellR),
        canonDomain_eq cellR]
  refine SaturatedConvOver.trans
    (SaturatedConvOver.trans
      (SaturatedConvOver.vcompCongrLeft cellR ihL)
      (SaturatedConvOver.vcompCongrRight (canon cellL) ihR)) ?_
  show SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.castBoundary (canonDomain_eq cellL) (canonCodomain_eq cellL)
          (wordFromCounts (canonCounts cellL)))
        (RawTwoCellExpr.castBoundary (canonDomain_eq cellR) (canonCodomain_eq cellR)
          (wordFromCounts (canonCounts cellR))))
      (canon (RawTwoCellExpr.vcomp cellL cellR))
  rw [RawTwoCellExpr.vcomp_castBoundaryRight, RawTwoCellExpr.castBoundary_castBoundary,
      RawTwoCellExpr.vcomp_castBoundaryLeft, RawTwoCellExpr.castBoundary_castBoundary]
  refine SaturatedConvOver.trans
    (SaturatedConvOver.castBoundaryCongr _ _
      (wordMul_vcompGen (canonCounts cellR) (canonCounts cellL) hlen)) ?_
  refine SaturatedConvOver.ofEq ?_
  rw [RawTwoCellExpr.castBoundary_castBoundary]
  exact RawTwoCellExpr.castBoundary_wordCongr _ _
    (canonDomain_eq (RawTwoCellExpr.vcomp cellL cellR))
    (canonCodomain_eq (RawTwoCellExpr.vcomp cellL cellR))
    (canonCounts_vcomp cellL cellR).symm

/-! ## The cell-level normalization interface + the fueled recursion, generic carrier -/

/-- The type of the cell-level normalization the completeness leg needs: every parallel free 2-cell of the walking
monad is `SaturatedConvOver monadModeSignature MonadLawRel`-convertible to the canonical Eilenberg–Zilber word of its own fold. -/
abbrev MonadNormalizesToCanonGen : Prop :=
  {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point} →
  (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) →
  SaturatedConvOver monadModeSignature MonadLawRel cell (canon cell)

/-- ★★ **The full cell-level normalization (STRUCTURAL on a `Nat` fuel).**  Every parallel free 2-cell of the
walking monad is `SaturatedConvOver monadModeSignature MonadLawRel`-convertible to the canonical Eilenberg–Zilber word of its own fold.
The recursion runs on a `Nat` fuel bounding the cell's structural size (the boundary mode indices are the constant
`MonadMode.point`, which blocks structural recursion directly on the cell), splitting via `match` into the two
`gen` leaves, the `id` case, the two whisker cases (all shipped, no monad law), and the `vcomp` case (the monad
laws through `wordMul_vcompGen`). -/
theorem monadNormalizeCellFueledGen : ∀ (fuel : Nat)
    {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath),
    cell.size ≤ fuel → SaturatedConvOver monadModeSignature MonadLawRel cell (canon cell)
  | 0, _, _, cell, hfuel =>
      absurd (Nat.le_trans (one_le_cellSize cell) hfuel) (Nat.not_succ_le_zero 0)
  | fuel + 1, _, _, cell, hfuel =>
      match cell, hfuel with
      | .gen MonadTwoCell.eta, _ => monadNormalize_genEtaGen
      | .gen MonadTwoCell.mu, _ => monadNormalize_genMuGen
      | .id path, _ => monadNormalize_idGen path
      | .vcomp cellL cellR, hf =>
          monadNormalize_vcompGen cellL cellR
            (monadNormalizeCellFueledGen fuel cellL
              (Nat.le_trans (Nat.le_add_right cellL.size cellR.size) (Nat.le_of_succ_le_succ hf)))
            (monadNormalizeCellFueledGen fuel cellR
              (Nat.le_trans (Nat.le_add_left cellR.size cellL.size) (Nat.le_of_succ_le_succ hf)))
      | .whiskerLeft oneCell body, hf =>
          monadNormalize_whiskerLeftGen oneCell body
            (monadNormalizeCellFueledGen fuel body (Nat.le_of_succ_le_succ hf))
      | .whiskerRight oneCell body, hf =>
          monadNormalize_whiskerRightGen oneCell body
            (monadNormalizeCellFueledGen fuel body (Nat.le_of_succ_le_succ hf))

/-- ★★ **The full cell-level normalization**, packaged as the interface `MonadNormalizesToCanonGen` — the sole
remaining ingredient of the completeness leg `convOfMapEq`. -/
theorem monadNormalizeGen : MonadNormalizesToCanonGen :=
  fun {_ _} cell => monadNormalizeCellFueledGen cell.size cell (Nat.le_refl _)

/-! ## The `convOfMapEqGen` reduction + the BESPOKE-FREE canonicalization + native decider -/

/-- ★ **`convOfMapEqGen`, reduced to the born-generic normalize.**  GIVEN `normalize : MonadNormalizesToCanonGen`
(every cell is generically saturated-convertible to its canonical word), two parallel cells with equal monotone maps
are generically convertible: `cellA ~ canon cellA = canon cellB ~ cellB`.  The generic twin of
`monadConvOfMapEq_ofNormalize`; `canon_eqOfMapEq` (a pure `Eq`) is REUSED.  Its constant-closure contains NO
`MonadSaturatedTwoCellConv`. -/
theorem monadConvOfMapEqGen_ofNormalizeGen (normalize : MonadNormalizesToCanonGen)
    {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    {cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (hmap : monadMonotoneMapOf cellA = monadMonotoneMapOf cellB) :
    SaturatedConvOver monadModeSignature MonadLawRel cellA cellB := by
  refine SaturatedConvOver.trans (normalize cellA) ?_
  rw [canon_eqOfMapEq cellA cellB hmap]
  exact SaturatedConvOver.symm (normalize cellB)

/-- ★★ **The BESPOKE-FREE walking-monad canonicalization.**  Its SOUNDNESS field is the born-generic
`monadMonotoneMapOf_mapEqOfConvGen`; its COMPLETENESS field is `monadConvOfMapEqGen_ofNormalizeGen monadNormalizeGen`
— the born-generic normalize.  Unlike the interim `monadSaturatedCanonicalizationGenViaBridge` (whose completeness
transports the bespoke normalize through `monadSaturated_to_generic`), this inhabitant's ENTIRE constant-closure is
free of `MonadSaturatedTwoCellConv` (the exhaustive meta-walk certifies it). -/
def monadSaturatedCanonicalizationGenNative : MonadSaturatedCanonicalizationGen where
  monotoneMapOf := monadMonotoneMapOf
  mapEqOfConvGen := monadMonotoneMapOf_mapEqOfConvGen
  convOfMapEqGen := fun hmap => monadConvOfMapEqGen_ofNormalizeGen monadNormalizeGen hmap

/-- ★★ **The BESPOKE-FREE walking-monad generic decider.**  Supplying the born-generic native canonicalization to
the born-generic decision assembly decides `SaturatedConvOver monadModeSignature MonadLawRel` on EVERY parallel pair
— BOTH halves of its verdict born-generic (soundness `monadMonotoneMapOf_mapEqOfConvGen`, completeness
`monadNormalizeGen`).  The wave-2 target the interim `decideSaturatedConvOverMonadInterim` reserved the name for. -/
def decideSaturatedConvOverMonadNative :
    DecidableSaturatedConvForRel monadModeSignature MonadLawRel :=
  monadSaturatedGenDecisionModulo monadSaturatedCanonicalizationGenNative

/-! ## Regression: the native decider decides the lane pairs (native / interim / old continuity in Table/LedgerR1) -/

/-- The native decider decides the size-3 associativity pair `t.t.t ⇒ t` (both fold `[0,0,0]`) to `true`. -/
def monadNativeDecidesTrue_assoc : Bool :=
  match decideSaturatedConvOverMonadNative monadAssocLeftCell monadAssocRightCell with
  | isTrue _ => true
  | isFalse _ => false

/-- The native decider decides the separating size-1 faces pair `t ⇒ t.t` (maps `[1]` vs `[0]`) to `false`. -/
def monadNativeDecidesFalse_faces : Bool :=
  match decideSaturatedConvOverMonadNative
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell) with
  | isTrue _ => true
  | isFalse _ => false

/-- The native decider returns `true` on the associativity pair (by `rfl`). -/
theorem monadNativeDecidesTrue_assoc_holds : monadNativeDecidesTrue_assoc = true := rfl

/-- The native decider returns `false` on the separating faces pair (by `rfl`) — the genuine `isFalse` separation. -/
theorem monadNativeDecidesFalse_faces_holds : monadNativeDecidesFalse_faces = false := rfl

/-- ★ **Regression: the native decider decides BOTH lane pairs correctly.**  The native decider folds each cell's
`monadMonotoneMapOf` and compares: the size-3 associativity pair `t.t.t ⇒ t` (both fold `[0,0,0]`) is decided
`isTrue` (`monadNativeDecidesTrue_assoc`), and the separating size-1 faces pair `t ⇒ t.t` (maps `[1]` vs `[0]`) is
decided `isFalse` (`monadNativeDecidesFalse_faces`) — by `rfl`.  (At r6 the interim generic decider
`decideSaturatedConvOverMonadInterim` and the old bespoke decider `monadSaturatedTwoCellDecision` branched on the
SAME `monadMonotoneMapOf` comparison and agreed on both pairs; that native / interim / old continuity — with the
interim decider retired in MONAD-R7 r2 S5 — is recorded historically in `Table/LedgerR1`.) -/
def monadNativeAgreesOnRegression : Bool :=
  (monadNativeDecidesTrue_assoc == true) && (monadNativeDecidesFalse_faces == false)

/-- Regression value: the native decider decides the associativity pair `isTrue` and the separating faces pair
`isFalse` (by `rfl`). -/
theorem monadNativeAgreesOnRegression_holds : monadNativeAgreesOnRegression = true := rfl

/-! ## Honesty markers -/

/-- **ESTABLISHED — the born-generic normalize `monadNormalizeGen` is COMPLETE, zero-axiom (POLY-TAB r6 WAVE 2).**
Every parallel free 2-cell is `SaturatedConvOver monadModeSignature MonadLawRel`-convertible to the canonical
Eilenberg–Zilber word of its own fold, proved DIRECTLY over the generic carrier (the five `normalizeCell` cases +
the fueled recursion re-founded ctor-for-ctor, the three bespoke law ctors folding into `ofRelation` of a
`MonadLawRel` row).  Its constant-closure contains NO `MonadSaturatedTwoCellConv`.  `= true`. -/
def fxMonad_hasMonadNormalizeGen : Bool := true

/-- ★★ **ESTABLISHED — the fully BESPOKE-FREE monad decider `decideSaturatedConvOverMonadNative` is COMPLETE,
zero-axiom (POLY-TAB r6 WAVE 2 — the completeness flip).**  The born-generic normalize `monadNormalizeGen` inhabits
the completeness field `convOfMapEqGen` of `monadSaturatedCanonicalizationGenNative`, whose SOUNDNESS field is the
born-generic `monadMonotoneMapOf_mapEqOfConvGen`; the decision assembly `monadSaturatedGenDecisionModulo` yields the
terminal `decideSaturatedConvOverMonadNative`, decided BOTH ways born-generic.  Its ENTIRE transitive
constant-closure is free of `MonadSaturatedTwoCellConv` (the exhaustive `includeStdlib := true` meta-walk in the
audit twin certifies it).  Decides both lane regression pairs correctly (`monadNativeAgreesOnRegression_holds` —
the associativity pair `isTrue`, the separating faces pair `isFalse`); the historical native / interim / old
verdict continuity is recorded in `Table/LedgerR1` (the r7-r2 section, the interim decider retired MONAD-R7 r2 S5).
This is what `fxMonad_hasGenericNativeDecider` (`MonadSaturatedDecisionGen`) now flips to `true` on.  `= true`. -/
def fxMonad_hasGenericNativeDeciderComplete : Bool := true

end FX1Poly.Polygraph.Amalgam
