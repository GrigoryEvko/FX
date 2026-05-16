import LeanFX2.Term.StrengtheningImage

/-! # AuditTypedInversion — typed `Term.app_inv` family axiom audit.

Smoke audit for the typed structural inversion lemmas shipped in
`LeanFX2.Term.TypedInversion`.

## Coverage

Three inversion lemmas for `RawTerm.app` shape:

* `Term.app_inv` — universal form (output type `targetType` free,
  disjunction over `Term.app` / `Term.appPi` arms).
* `Term.app_inv_arrow` — arrow-output specialization.
* `Term.app_inv_pi`   — Π-output specialization.

## Cascade unblocks

These lemmas are the typed-η-redesign prerequisite per
`feedback_typed_eta_lam_inv_cascade_blocker_2026_05_16.md`.  Once
shipped, downstream consumers can recover typed `fnTerm` + `argTerm`
from a typed `Term.app`-shape body — load-bearing for `lift_lam`'s
η-arm, subject reduction app cases, and decidable conversion's
function-application reasoning.

Every shipped declaration must report "does not depend on any axioms".
The `LeanFX2Audit` target enforces this via `#assert_no_axioms` in
`Tools/AuditAll/AuditTerm.lean`. -/

namespace LeanFX2.SmokeTypedInversion

-- Universal and specialized inversions for `RawTerm.app` shape
#print axioms LeanFX2.Term.app_inv
#print axioms LeanFX2.Term.app_inv_arrow
#print axioms LeanFX2.Term.app_inv_pi

-- Typed weaken inversion at arrow type (Option form).  Thin wrapper
-- around `Term.unweaken?` specialized to `Ty.arrow A B` indices.
-- The universal existence form is gated on extending
-- `StrengtheningResult` with a `termRenames` field.
#print axioms LeanFX2.Term.weaken_inv_arrow_option

-- Supporting infrastructure shipped alongside the typed weaken
-- inversion cascade prerequisites.
#print axioms LeanFX2.Ty.weaken_inj
#print axioms LeanFX2.Term.weakenInverse_atVarZero

-- Typed strengthening image soundness scaffold.
#print axioms LeanFX2.Term.StrengtheningSoundness
#print axioms LeanFX2.Term.heq_cast_right
#print axioms LeanFX2.Term.heq_cast_left
#print axioms LeanFX2.Term.rename_var_heq
#print axioms LeanFX2.Term.partialStrengthenTypedVarOfSurvives_sound
#print axioms LeanFX2.Term.partialStrengthenTypedUnit_sound
#print axioms LeanFX2.Term.partialStrengthenTypedBoolTrue_sound
#print axioms LeanFX2.Term.partialStrengthenTypedBoolFalse_sound
#print axioms LeanFX2.Term.partialStrengthenTypedNatZero_sound
#print axioms LeanFX2.Term.partialStrengthenTypedInterval0_sound
#print axioms LeanFX2.Term.partialStrengthenTypedInterval1_sound
#print axioms LeanFX2.Term.partialStrengthenTypedListNilOfType_sound
#print axioms LeanFX2.Term.partialStrengthenTypedOptionNoneOfType_sound
#print axioms LeanFX2.Term.partialStrengthenTypedNatSucc_sound
#print axioms LeanFX2.Term.partialStrengthenTypedOptionSome_sound
#print axioms LeanFX2.Term.partialStrengthenTypedBoolElim_sound
#print axioms LeanFX2.Term.partialStrengthenTypedAppOfSuccess_sound
#print axioms LeanFX2.Term.partialStrengthenTypedApp_sound
#print axioms LeanFX2.Term.partialStrengthenTypedAppPiOfSuccess_sound
#print axioms LeanFX2.Term.partialStrengthenTypedAppPi_sound
#print axioms LeanFX2.Term.partialStrengthenTypedNatElim_sound
#print axioms LeanFX2.Term.partialStrengthenTypedNatRec_sound
#print axioms LeanFX2.Term.partialStrengthenTypedModIntro_sound
#print axioms LeanFX2.Term.partialStrengthenTypedModElim_sound
#print axioms LeanFX2.Term.partialStrengthenTypedSubsume_sound
#print axioms LeanFX2.Term.partialStrengthenTypedListCons_sound
#print axioms LeanFX2.Term.partialStrengthenTypedEitherInlOfRightType_sound
#print axioms LeanFX2.Term.partialStrengthenTypedEitherInrOfLeftType_sound
#print axioms LeanFX2.Term.partialStrengthenTypedPair_sound
#print axioms LeanFX2.Term.partialStrengthenTypedFst_sound
#print axioms LeanFX2.Term.partialStrengthenTypedSnd_sound
#print axioms LeanFX2.Term.partialStrengthenTypedIntervalOpp_sound
#print axioms LeanFX2.Term.partialStrengthenTypedIntervalMeet_sound
#print axioms LeanFX2.Term.partialStrengthenTypedIntervalJoin_sound
#print axioms LeanFX2.Term.partialStrengthenTypedUniverseCode_sound
#print axioms LeanFX2.Term.partialStrengthenTypedArrowCode_sound
#print axioms LeanFX2.Term.partialStrengthenTypedPiTyCode_sound
#print axioms LeanFX2.Term.partialStrengthenTypedSigmaTyCode_sound
#print axioms LeanFX2.Term.partialStrengthenTypedProductCode_sound
#print axioms LeanFX2.Term.partialStrengthenTypedSumCode_sound
#print axioms LeanFX2.Term.partialStrengthenTypedListCode_sound
#print axioms LeanFX2.Term.partialStrengthenTypedOptionCode_sound
#print axioms LeanFX2.Term.partialStrengthenTypedEitherCode_sound
#print axioms LeanFX2.Term.partialStrengthenTypedIdCode_sound
#print axioms LeanFX2.Term.partialStrengthenTypedEquivCode_sound
#print axioms LeanFX2.Term.partialStrengthenTypedRefl_sound
#print axioms LeanFX2.Term.partialStrengthenTypedOeqRefl_sound
#print axioms LeanFX2.Term.partialStrengthenTypedIdStrictRefl_sound
#print axioms LeanFX2.Term.partialStrengthenTypedEquivReflId_sound
#print axioms LeanFX2.Term.partialStrengthenTypedEquivReflIdAtId_sound
#print axioms LeanFX2.Term.partialStrengthenTypedFunextRefl_sound
#print axioms LeanFX2.Term.partialStrengthenTypedFunextReflAtId_sound

-- Phase 11: 3 eliminator OfSuccess soundness theorems via refactor.
-- Wrappers `partialStrengthenTypedListElim`/`OptionMatch`/`EitherMatch`
-- now delegate to term-mode OfSuccess variants whose soundness lifts
-- without traversing `Option.casesOn` discriminator inside the wrapper.
#print axioms LeanFX2.Term.partialStrengthenTypedListElimOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedListElimOfSuccess_sound
#print axioms LeanFX2.Term.partialStrengthenTypedOptionMatchOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedOptionMatchOfSuccess_sound
#print axioms LeanFX2.Term.partialStrengthenTypedEitherMatchOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedEitherMatchOfSuccess_sound

-- Phase 12: refinement producers soundness.
-- RefineIntro is direct (no internal type-pivot; predicateStrengthens is
-- supplied explicitly).  RefineElim follows the OfSuccess refactor pattern
-- since the wrapper internally cases on `baseType.partialStrengthen?` and
-- `predicate.partialStrengthen?` (the `Option.casesOn` discriminator wall).
#print axioms LeanFX2.Term.partialStrengthenTypedRefineIntro_sound
#print axioms LeanFX2.Term.partialStrengthenTypedRefineElimOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedRefineElimOfSuccess_sound

-- Phase 13: record producers soundness.
-- RecordIntro is direct: producer threads `fieldResult` through field
-- projections without destructuring.  RecordProj follows the OfSuccess
-- refactor since its wrapper internally cases on
-- `singleFieldType.partialStrengthen?` (Option.casesOn discriminator wall).
#print axioms LeanFX2.Term.partialStrengthenTypedRecordIntro_sound
#print axioms LeanFX2.Term.partialStrengthenTypedRecordProjOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedRecordProjOfSuccess_sound

-- Phase 14: codata producers soundness.
-- Both CodataUnfold and CodataDest need OfSuccess refactor.  CodataUnfold's
-- wrapper does App-style `rw + cases` on the arrow-decomposed transition
-- type strengthening; CodataDest's wrapper cases on the state-type and
-- output-type partial-strengthen pivots (Option.casesOn discriminator wall).
-- The OfSuccess variants take pre-decomposed witnesses so soundness `dsimp`
-- reduces past the body without re-encountering the wall.
#print axioms LeanFX2.Term.partialStrengthenTypedCodataUnfoldOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedCodataUnfoldOfSuccess_sound
#print axioms LeanFX2.Term.partialStrengthenTypedCodataDestOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedCodataDestOfSuccess_sound

-- Phase 15: session + cumulUp producers soundness.
-- All three are "direct" producers (no Option.casesOn discriminator
-- wall): the session protocol pivot is pre-witnessed by the
-- `protocolStrengthens` hypothesis, and cumulUp's source type is the
-- closed `Ty.universe lvl` whose partial-strengthen reduces
-- definitionally.  Soundness mirrors the producer's `change / rw /
-- cases` chain for session pairs, and a plain `cases codeTypeStrengthens`
-- for the cumulUp closed-universe case.
#print axioms LeanFX2.Term.partialStrengthenTypedSessionSend_sound
#print axioms LeanFX2.Term.partialStrengthenTypedSessionRecv_sound
#print axioms LeanFX2.Term.partialStrengthenTypedCumulUp_sound

-- Phase 16: HoTT-J univalence-β extraction soundness.
-- UaToEquiv is direct: all four type/raw pivots are pre-witnessed
-- (leftTy, rightTy, leftTyRaw, rightTyRaw), and the proof's typeStrengthens
-- unifies via a synthesized `expectedProofTypeStrengthens` rewrite on the
-- closed `Ty.id (Ty.universe ...)` shape.  Mirrors the producer's case
-- chain so the HEq congruence applies with one rfl-on-the-record discharge.
#print axioms LeanFX2.Term.partialStrengthenTypedUaToEquiv_sound

-- Phase 17: heterogeneous funext + univalence introduction soundness.
-- FunextIntroHet is the cleanest sound theorem in the cascade: the
-- producer has NO Term children — the strengthened result is built
-- purely from 4 strengthening witnesses on the type/raw pivots, so
-- soundness just derives 4 renames via partialStrengthen?_imp_rename
-- (lifted for the binder-scoped applies) and applies the HEq congruence.
-- UaIntroHet mirrors UaToEquiv with 6 pre-witnesses (carriers + raws +
-- forward/backward proof endpoints) and an equivWitness child.
-- OeqFunext is deferred this phase: dsimp does not reduce through the
-- oeqFunextPointwiseType reducible-def layer at the renamedTarget
-- projection site under the synthesized pointwiseExpectedStrengthens
-- cases chain — needs an explicit `show` or a different approach.
#print axioms LeanFX2.Term.partialStrengthenTypedFunextIntroHet_sound
#print axioms LeanFX2.Term.partialStrengthenTypedUaIntroHet_sound

-- Phase 18: cubical Glue introduction soundness.
-- GlueIntro is a direct producer with two Term children (baseValue and
-- partialValue) sharing a single `baseType` pre-witnessed by
-- `baseTypeStrengthens`.  Mirrors the producer's two-cases chain
-- (cases baseResult; rw + cases; cases partialResult; rw + cases) and
-- applies glueIntro_HEq_congr with the two pre-witnessed renames plus
-- the two sub-Terms' soundness HEqs.
--
-- DEFERRED (Phase 17 + Phase 18 both attempted, structurally blocked):
-- * OeqFunext: the HEq congruence expects `pointwiseProof2 : Term context
--   (oeqFunextPointwiseType (renamed X) (renamed Y) (renamed A)
--   (renamed B)) (renamed raw)` but `Term.rename ... targetPointwiseProof`
--   has type `Term sourceCtx ((oeqFunextPointwiseType X Y A B).rename
--   forward) ...`.  These differ propositionally via
--   `oeqFunextPointwiseType_rename` (Term/Rename.lean:208), driven by
--   the rename-weaken commutation `Ty.weaken_rename_commute`
--   (Foundation/Ty.lean:417), which is NOT definitional.  Lean inserts
--   a `⋯ ▸` cast in the expected `pointwiseProofHEq` type that
--   `pointwiseSound.termRenames` cannot satisfy.  Resolution needs ~30
--   LoC of HEq cast bridging using `oeqFunextPointwiseType_rename` to
--   transport `pointwiseSound.termRenames` to the cast shape (via
--   `HEq.trans` + explicit `▸` rewrite, or by constructing pointwiseHEq
--   with an explicit Eq.mpr coercion).
-- * GlueElim: wrapper does Option.casesOn on both base and boundary
--   pivots (full discriminator wall), needs OfSuccess refactor.
#print axioms LeanFX2.Term.partialStrengthenTypedGlueIntro_sound

end LeanFX2.SmokeTypedInversion
