import LeanFX2.Tools.DependencyAudit
import LeanFX2.Confluence.ConvTrans
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawDiamond
import LeanFX2.Confluence.RawParStarCong
import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdRename

namespace LeanFX2.Tools

/-! ## AuditConfluence — `#assert_no_axioms` checks for the
confluence cascade.  Covers Conv-level corollaries plus the
underlying raw-level Church-Rosser machinery that makes them
work. -/

#assert_no_axioms LeanFX2.Conv.refl
#assert_no_axioms LeanFX2.Conv.fromStep
#assert_no_axioms LeanFX2.Conv.transChains
#assert_no_axioms LeanFX2.Conv.toRawJoin
#assert_no_axioms LeanFX2.Conv.canonicalRaw
#assert_no_axioms LeanFX2.Conv.transRaw

/-! ### Asymmetric typed Conv.trans variants (#1590 PHASE7-CONV-TRANS Phase 2)

Asymmetric flavors where one side is a `StepStar` chain and the
other is a `Conv` ship at zero axioms because the typed midpoint is
inherited from the input `Conv`'s existential — no confluence call
required.  Strong subject-reduction with term construction is NOT
needed for these subsets. -/

#assert_no_axioms LeanFX2.Conv.trans_chainLeft
#assert_no_axioms LeanFX2.Conv.trans_chainRight
#assert_no_axioms LeanFX2.Conv.trans_step_left
#assert_no_axioms LeanFX2.Conv.trans_step_right
#assert_no_axioms LeanFX2.Conv.trans_fromStepLeft
#assert_no_axioms LeanFX2.Conv.trans_fromStepRight
#assert_no_axioms LeanFX2.Conv.trans_refl_left
#assert_no_axioms LeanFX2.Conv.trans_refl_right

/-! ### Raw-level confluence machinery (#1508)

The typed Conv corollaries above lift their proofs through these
raw-level theorems via `Step.parStar.toRawBridge`.  Per audit
ac74bd7e, these were missing from the curated audit catalogue —
their soundness was only checked via `#print axioms` in Smoke
files. -/

#assert_no_axioms LeanFX2.RawStep.par.cd_lemma
#assert_no_axioms LeanFX2.RawStep.par.diamond
#assert_no_axioms LeanFX2.RawStep.parStar.confluence

/-! ### parStar cong-rule lifter (mapStep pattern, #1646)

`RawStep.parStar.mapStep` is the raw analog of `StepStar.mapStep` —
the foundational cong-rule lifter used to collapse 21 four-line
refl/trans inductions in `RawParStarCong.lean` to one-line `mapStep`
invocations.  Per `feedback_lean_mapStep_pattern.md`, this is a
load-bearing kernel discipline reused everywhere parStar lifts a
single-step cong rule over the reflexive-transitive closure. -/

#assert_no_axioms LeanFX2.RawStep.parStar.mapStep

/-! ### Confluence cascade load-bearing helpers

`cd_dominates` is the OTHER half of the Tait-Martin-Löf complete-
development pair (`cd_lemma` above is one half): every term parallel-
reduces to its complete development.  Together they give the diamond
property, which strips to confluence.  Previously gated only via
`Smoke/AuditPhase6BCdDominates.lean`; promoting to strict per-decl
gate matches the discipline of recent commits d2e9d4a / f3df931 /
f13056a that swept the Step.par cascade.

`cd_rename` is the headline rename-commute theorem for the
complete-development function, with 18 per-case helpers
(`cdXCase_rename`) that compose into it through a case split on
the redex shape.  Each helper is propext-clean by enumeration of
the 73 RawTerm constructors plus a structural rfl/split. -/

#assert_no_axioms LeanFX2.RawStep.par.cd_dominates

#assert_no_axioms LeanFX2.RawTerm.cd_rename
#assert_no_axioms LeanFX2.RawTerm.cd_weaken

#assert_no_axioms LeanFX2.RawTerm.cdAppCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdPathAppCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdGlueElimCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdModElimCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdRefineElimCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdRecordProjCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdCodataDestCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdFstCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdSndCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdBoolElimCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdNatElimCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdNatRecCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdListElimCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdOptionMatchCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdEitherMatchCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdIdJCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdIdStrictRecCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdIdToEquivCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdUaToEquivApplyCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdEquivApplyCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdTranspCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdTranspPiCase_rename
#assert_no_axioms LeanFX2.RawTerm.cdHcompCase_rename

/-! ### cdTranspPiCase shape lemmas

Bidirectional case-split helpers for `cdTranspPiCase`: when the
recognizer fires, the case yields the β contractum; when it fails,
the case rebuilds via plain `transp` cong.  Used by `cd_dominates`'
transp arm to discharge the dispatch. -/

#assert_no_axioms LeanFX2.RawTerm.cdTranspPiCase_eq_contractum_of_some
#assert_no_axioms LeanFX2.RawTerm.cdTranspPiCase_eq_transp_of_none

end LeanFX2.Tools
