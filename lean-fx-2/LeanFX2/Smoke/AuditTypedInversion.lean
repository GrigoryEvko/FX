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
#print axioms LeanFX2.Term.partialStrengthenTypedGlueIntro_sound

-- Phase 19: observational funext soundness — the cast-bridge unblock.
-- OeqFunext was deferred in Phase 17 + Phase 18 with a precise structural
-- blocker.  Phase 19 lands it by bridging the rename-distribution cast
-- on `oeqFunextPointwiseType` via the published commutation lemma
-- `oeqFunextPointwiseType_rename` (Term/Rename.lean:208).  Term.rename
-- itself uses that lemma with an explicit `▸` cast in the oeqFunext arm
-- (Term/Rename.lean:354-360), so soundness uses `Term.type_eq_cast_heq`
-- (Term/Pointwise/PointwiseAndCompositionInfrastructure.lean:416) +
-- `HEq.trans` + `HEq.symm` to transport `pointwiseSound.termRenames` to
-- the cast shape that `pointwiseProofHEq` expects.  Key insight: the
-- `▸` cast in Term.rename's oeqFunext arm matches the `▸` cast in the
-- HEq congruence's expected type, so the bridge is a single 4-line
-- `have castedHEq := HEq.symm (Term.type_eq_cast_heq typeEq _)`.
-- Adds one import: `LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure`.
-- GlueElim still deferred: wrapper does Option.casesOn on both base and
-- boundary pivots (full discriminator wall), needs OfSuccess refactor.
#print axioms LeanFX2.Term.partialStrengthenTypedOeqFunext_sound

-- Phase 20: HoTT-J identity-elimination soundness — OfSuccess refactor.
-- IdJ's wrapper does triple Option.casesOn on the witness's Ty.id
-- carrier/leftEndpoint/rightEndpoint pivots (the discriminator-wall
-- pattern from Refine/Record/Codata).  OfSuccess takes pre-decomposed
-- witnesses + the three Option-equations and ships zero-axiom direct.
-- Ty.id is a Ty constructor so Ty.rename distributes definitionally —
-- no cast bridge needed (unlike OeqFunext's reducible-def case).
-- OeqJ + IdStrictRec follow the same recipe (Ty.oeq, Ty.idStrict are
-- also constructors).  Tracked for Phase 21.
#print axioms LeanFX2.Term.partialStrengthenTypedIdJOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedIdJOfSuccess_sound

-- Phase 21: HoTT-J observational-equality + strict-identity-recursor
-- soundness — OfSuccess refactors mirror IdJ exactly.  Ty.oeq and
-- Ty.idStrict are Ty constructors, so Ty.rename distributes
-- definitionally — direct application of the HEq congruence per
-- Phase 20.  3 of 3 HoTT-J eliminators now zero-axiom.
#print axioms LeanFX2.Term.partialStrengthenTypedOeqJOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedOeqJOfSuccess_sound
#print axioms LeanFX2.Term.partialStrengthenTypedIdStrictRecOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedIdStrictRecOfSuccess_sound

-- Phase 22: equiv-application soundness — Equiv-family OfSuccess.
-- EquivApply has dual Option.casesOn on the witness's Ty.equiv
-- carrier-pair (carrierA + carrierB).  OfSuccess takes both
-- carrierSuccess witnesses pre-decomposed.  Ty.equiv is a Ty
-- constructor so Ty.rename distributes definitionally — direct
-- application of equivApply_HEq_congr.
#print axioms LeanFX2.Term.partialStrengthenTypedEquivApplyOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedEquivApplyOfSuccess_sound

-- Phase 23: equivalence-application soundness — second Equiv-family
-- OfSuccess.  EquivApp mirrors EquivApply (Phase 22) exactly with the
-- univalence-α `Term.equivApp` / `RawTerm.equivApp` constructor pair
-- instead of the β variants.  Same dual Option.casesOn on Ty.equiv
-- carrierA + carrierB.  Direct application of equivApp_HEq_congr.
#print axioms LeanFX2.Term.partialStrengthenTypedEquivAppOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedEquivAppOfSuccess_sound

-- Phase 24: cubical Glue-elimination soundness via OfSuccess split.  The
-- wrapper's `Ty.glue` Option.casesOn over base + boundary pivots becomes
-- pre-witnessed (baseSuccess, boundarySuccess) in the OfSuccess.  Direct
-- application of `glueElim_HEq_congr` (Atomic) — the carrier is a closed
-- Ty.glue ctor so `Ty.rename` distributes definitionally, no cast bridge.
#print axioms LeanFX2.Term.partialStrengthenTypedGlueElimOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedGlueElimOfSuccess_sound

-- Phase 25: dependent-binder LamPi soundness — first binder-producer
-- with a sound counterpart.  The blocker was that the two TermRenaming
-- proofs in `bodySound.termRenames` and the renamedTarget's `Term.rename`
-- have DIFFERENT TYPES (different second context arg: `sourceCtx.cons
-- domainType` vs `sourceCtx.cons (targetDomainType.rename forward)`).
-- Lean rejects them as different types since `TermRenaming` is a
-- dependent type and the contexts are propositionally but not
-- definitionally equal.  Fix: `subst domainRenames` early to unify the
-- contexts, then Lean's definitional proof irrelevance on
-- `TermRenaming : Prop` discharges the remaining proof equality.  No
-- `Ty.weaken_rename_commute` cast bridge needed for Π (the codomain is
-- just `codomainType`, not `codomainType.weaken`).  Pattern reusable
-- for any binder producer where the body's source-context binding type
-- is equal-by-strengthening to a renamed target type.
#print axioms LeanFX2.Term.partialStrengthenTypedLamPi_sound

-- Phase 26: non-dependent Lam soundness — extends LamPi's subst-early
-- recipe with the `.weaken` cast bridge.  Body has type `Term ...
-- codomainType.weaken bodyRaw`; `Term.rename` of `Term.lam` introduces
-- a `Ty.weaken_rename_commute rho codomainType ▸` cast to align the
-- body's type from `codomainType.weaken.rename rho.lift` to
-- `(codomainType.rename rho).weaken`.  After `subst domainRenames` +
-- `subst codomainRenames` (both via partialStrengthen?_imp_rename), the
-- wrapper's `bodyTypeStrengthens` dance unifies `targetBodyType` with
-- `targetCodomainType.weaken`, then `Term.type_eq_cast_heq` bridges the
-- body HEq to its casted form so `lam_HEq_congr rfl rfl bodyRawRenames
-- castedHEq` closes the goal.  Pattern reusable for any non-dependent
-- binder producer that uses `Ty.weaken` in the body's type.
#print axioms LeanFX2.Term.partialStrengthenTypedLam_sound

-- Phase 27: cubical Path-lambda soundness — same `Ty.weaken` cast
-- bridge as Lam, but with a closed `Ty.interval` binder (no domain
-- strengthening needed) and three extra explicit fields
-- (leftEndpoint, rightEndpoint, mode-univalent witness).  Validates
-- the Lam recipe's reach into the cubical fragment.  New helper
-- `Term.pathLam_HEq_congr` mirrors `Term.lam_HEq_congr` (HEq congruence
-- under codomain `.weaken`).
#print axioms LeanFX2.Term.partialStrengthenTypedPathLam_sound
#print axioms LeanFX2.Term.pathLam_HEq_congr

-- Phase 28: cubical Path-application via OfSuccess pattern.
-- PathApp's wrapper does a dual `Option.casesOn` on three Ty.path
-- pivots (carrier / leftEndpoint / rightEndpoint); the OfSuccess
-- form takes those as pre-witnessed strengthening parameters,
-- mirroring GlueElim/RefineElim/CodataDest.  Soundness composes via
-- `pathApp_HEq_congr` with renaming equalities recovered via
-- `partialStrengthen?_imp_rename`.  Pattern reusable for any
-- non-binder producer whose typed source carries a Ty constructor
-- with multiple type-level pivots (e.g. Transp, Hcomp).
#print axioms LeanFX2.Term.partialStrengthenTypedPathAppOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedPathAppOfSuccess_sound

-- Phase 29: cubical transport via OfSuccess pattern.
-- Transp's wrapper extracts pathResult + sourceResult typed witnesses
-- and aligns them by rewriting on `expectedPathTypeStrengthens` and
-- `sourceTypeStrengthens`.  The OfSuccess form takes the typed targets
-- plus 6 raw-level strengthening witnesses as parameters, sparing the
-- soundness proof from replicating that dance.  Composes via
-- `transp_HEq_congr` with 4 type/raw equalities from
-- `partialStrengthen?_imp_rename`.
#print axioms LeanFX2.Term.partialStrengthenTypedTranspOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedTranspOfSuccess_sound

-- Phase 34: typed-transport WRAPPER soundness — first wrapper
-- _sound shipped via the App-pattern (inline-construct wrapper +
-- parallel cases + Term.transp_HEq_congr).  Unlocks ~10 sibling
-- wrappers that share the App-pattern: Hcomp, HcompPath, IdJ, OeqJ,
-- IdStrictRec, EquivApp, EquivApply, EquivIntroHet, GlueElim,
-- RefineElim.  Wrappers blocked by `cases X : foo` internal option-
-- splits (ListElim, OptionMatch, EitherMatch, CodataDest,
-- CodataUnfold, EffectPerform, RecordProj, PathApp) require a
-- separate refactor — wrappers must take type-strengtheners as
-- parameters, not derive them from result.targetType.
#print axioms LeanFX2.Term.partialStrengthenTypedTransp_sound

-- Phase 30: homogeneous composition via OfSuccess pattern.
-- Hcomp's wrapper is the simplest non-binder OfSuccess target: single
-- carrierType pivot shared by both child terms.  The OfSuccess form
-- takes the typed children + carrier strengthening + raw witnesses.
-- Composes via `hcomp_HEq_congr` with one type equality from
-- `partialStrengthen?_imp_rename`.
#print axioms LeanFX2.Term.partialStrengthenTypedHcompOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedHcompOfSuccess_sound

-- Phase 35: Hcomp WRAPPER soundness — second App-pattern wrapper
-- _sound after Phase 34's Transp_sound.  The pattern: cases on two
-- StrengtheningResults, align cap type via carrier-strengthening,
-- discharge via `Term.hcomp_HEq_congr` with carrierRenames +
-- sidesSound.termRenames + capSound.termRenames.
#print axioms LeanFX2.Term.partialStrengthenTypedHcomp_sound

-- Phase 31: path-shaped homogeneous composition via OfSuccess pattern.
-- HcompPath's wrapper combines Hcomp's two-child structure with
-- PathApp's triple-pivot path-type strengthening (carrier + two
-- endpoints).  The OfSuccess form pre-witnesses all three Ty.path
-- pivots plus both child raw strengthenings + rename equations.
-- Composes via `hcompPath_HEq_congr` with three Ty/raw rename
-- equalities from `partialStrengthen?_imp_rename`.
#print axioms LeanFX2.Term.partialStrengthenTypedHcompPathOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedHcompPathOfSuccess_sound

-- Phase 32: heterogeneous-equivalence introduction via OfSuccess.
-- EquivIntroHet's wrapper does a 250-line cascade aligning the four
-- typed children plus four derived `equivIntroHet*InverseType`
-- structural strengthenings.  The OfSuccess form skips all that:
-- four typed targets + 4 strengthening witnesses (2 carriers,
-- forwardRaw, backwardRaw) + 2 rename equations.  The `targetRaw`
-- shape is `RawTerm.equivIntro targetForwardRaw targetBackwardRaw`
-- only — leftInvRaw and rightInvRaw are typed-only "ghost" proof
-- raws that don't appear in the schematic raw form.  Soundness
-- composes via `equivIntroHet_HEq_congr` (Atomic.lean:774) with
-- two Ty rename equalities plus four raw rename equations (the
-- last two leftInvRawRenames/rightInvRawRenames taken as direct
-- inputs), and casts the leftInv/rightInv soundness HEqs through
-- the `equivIntroHet*InverseType_rename` casts that Term.rename
-- inserts when pushing through equivIntroHet.
#print axioms LeanFX2.Term.partialStrengthenTypedEquivIntroHetOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedEquivIntroHetOfSuccess_sound

-- Phase 33: algebraic-effect performance via OfSuccess.  EffectPerform's
-- wrapper consumes pre-strengthened children and rebuilds the operation
-- signature + `CanPerform` evidence structurally at the target scope.
-- The OfSuccess form lifts this to the standard schema: 2 typed targets
-- (operationTag, arguments) + 5 strengthening witnesses (effectTag,
-- argumentCarrier, resultCarrier, operationRaw, argumentsRaw) + 3 rename
-- equations.  `OperationSignature.map` preserves `effectLabel` (a scope-
-- free tag) while mapping carriers through the renaming; `CanPerform.map`
-- dispatches on the proof's constructor (`direct` / `readViaWrite`) to
-- transport `EffectRow.Member` evidence definitionally.  Soundness leans
-- on `effectPerform_HEq_congr` (Atomic.lean:736) with the operation
-- signature aligned via two `Ty.partialStrengthen?_imp_rename` derivations
-- (argumentCarrier + resultCarrier) followed by `obtain` on the source
-- signature's three fields then `subst` of both carrier renames; the
-- `cases canPerformOperation` produces two branches both reduced to
-- `Term.effectPerform_HEq_congr` applications.
#print axioms LeanFX2.Term.partialStrengthenTypedEffectPerformOfSuccess
#print axioms LeanFX2.Term.partialStrengthenTypedEffectPerformOfSuccess_sound

-- Phase 36 (sidequest): WRAPPER soundness for codata-unfold producer.
-- Pattern: App-style wrapper that takes `outputTypeStrengthens` as an
-- explicit parameter (no internal `cases X : foo` option-split).  The
-- proof destructures `stateResult` and `transitionResult`, aligns the
-- transition's `Ty.arrow` shape via record-rewrite + `cases` on the
-- equation, then delegates to
-- `partialStrengthenTypedCodataUnfoldOfSuccess_sound` at the leaf.
-- Mirrors the recipe established for `Transp_sound` / `Hcomp_sound`.
#print axioms LeanFX2.Term.partialStrengthenTypedCodataUnfold_sound

-- Phase 37 (sidequest): WRAPPER soundness for effect-performance
-- producer.  Pattern: App-style wrapper that takes 3 strengtheners
-- (effectTagStrengthens, argumentCarrierStrengthens,
-- resultCarrierStrengthens) as explicit parameters; the proof
-- destructures `operationTagResult` and `argumentsResult`, aligns the
-- `Ty.effect`-shaped operation-tag type and the operation-signature
-- argument-carrier for the arguments-term type, then delegates to
-- `partialStrengthenTypedEffectPerformOfSuccess_sound`.  Threads the
-- `canPerformOperation` and the row-membership witnesses through
-- without case-splitting on them (OfSuccess_sound handles both
-- direct + readViaWrite cases internally).
#print axioms LeanFX2.Term.partialStrengthenTypedEffectPerform_sound

-- Phase 38 (sidequest): WRAPPER soundness for record-projection
-- producer.  Pattern: ListElim-shaped wrapper REFACTORED to App-style by
-- lifting its internal `cases fieldSuccess : singleFieldType.partialStrengthen?`
-- option-split into an explicit `fieldSuccess` parameter at the wrapper
-- signature.  The dispatcher arm at `PartialStrengthen.lean` does the
-- option-split before invoking the wrapper; the wrapper now just
-- destructures the record's `StrengtheningResult`, aligns the `Ty.record`
-- shape via record-rewrite + `cases`, and delegates to
-- `partialStrengthenTypedRecordProjOfSuccess`.  Soundness mirrors the
-- same case cascade and invokes `_OfSuccess_sound` at the leaf.
-- Confirms the empirically-validated workaround for the Lean 4.29.1
-- tactic-mode opacity that defeats internal `cases X : foo with` patterns
-- in wrapper-soundness proofs of the original ListElim-pattern shape.
#print axioms LeanFX2.Term.partialStrengthenTypedRecordProj_sound

-- Phase 39 (sidequest): WRAPPER soundness for refine-elimination
-- producer.  Pattern: ListElim-shaped wrapper REFACTORED to App-style
-- by lifting BOTH internal option-splits (`baseSuccess` on base type
-- and `predicateSuccess` on predicate under lift) into explicit
-- parameters at the wrapper signature.  The dispatcher arm at
-- `PartialStrengthen.lean` does the two option-splits before invoking
-- the wrapper.  The wrapper destructures the refined value's
-- `StrengtheningResult`, aligns the `Ty.refine` shape via record-
-- rewrite + `cases`, and delegates to
-- `partialStrengthenTypedRefineElimOfSuccess`.  Soundness mirrors the
-- same case cascade and invokes `_OfSuccess_sound` at the leaf.
-- Extends Phase 38's recipe to wrappers with 2-option-splits — the
-- App-pattern refactor scales uniformly to nested option-splits as
-- long as the OfSuccess leaf accepts all witnesses as parameters.
#print axioms LeanFX2.Term.partialStrengthenTypedRefineElim_sound

-- Phase 40 (sidequest): WRAPPER soundness for codata-destruction
-- producer.  Pattern: ListElim-shaped wrapper REFACTORED to App-style
-- by lifting BOTH internal option-splits (`stateSuccess` on state
-- carrier and `outputSuccess` on output type) into explicit parameters
-- at the wrapper signature.  Same recipe as Phase 39 RefineElim — the
-- App-pattern refactor for 2-option wrappers scales uniformly to any
-- pair of independent option-splits on type-level witnesses.  Dispatch
-- arm at `PartialStrengthen.lean` does both option-splits before
-- invoking the wrapper; the wrapper destructures the codata value's
-- `StrengtheningResult`, aligns the `Ty.codata` shape via record-
-- rewrite + `cases`, and delegates to
-- `partialStrengthenTypedCodataDestOfSuccess`.
#print axioms LeanFX2.Term.partialStrengthenTypedCodataDest_sound

-- Phase 41 (sidequest): WRAPPER soundness for cubical glue-elimination
-- producer.  Pattern: ListElim-shaped wrapper REFACTORED to App-style
-- by lifting BOTH internal option-splits (`baseSuccess` on base type
-- and `boundarySuccess` on boundary witness raw) into explicit
-- parameters.  Same recipe as Phase 39 RefineElim / Phase 40
-- CodataDest — confirms the App-pattern scales uniformly across the
-- entire family of 2-option-split wrappers, including those that mix
-- type-level (Ty) and raw-term-level (RawTerm) strengthening
-- witnesses.  Threads `modeIsUnivalent` through unchanged since it is
-- a mode-equality witness, not a strengthening pivot.
#print axioms LeanFX2.Term.partialStrengthenTypedGlueElim_sound

-- Phase 42 (sidequest): WRAPPER soundness for cubical path-shaped
-- homogeneous composition producer.  First 3-option-split wrapper in
-- the cascade: `partialStrengthenTypedHcompPath` takes the carrier
-- type, left endpoint, and right endpoint as three independent
-- strengthening witnesses (`carrierSuccess` is a Ty witness,
-- `leftSuccess` and `rightSuccess` are RawTerm witnesses on the path
-- endpoints).  Demonstrates the App-pattern scales beyond 2-option
-- wrappers — the `Option.mapThree` shape of `Ty.path`'s
-- `partialStrengthen?` arm is discharged by `change`+`rw [carrier,
-- left, right]; rfl`, identical structure to Phase 41's `Option.mapTwo`
-- discharge but with one extra option pivot.  Closes the path-related
-- producer coverage gap; remaining 3-option-split candidates include
-- `pathApp`, `glueIntro`, and the cubical eliminators.
#print axioms LeanFX2.Term.partialStrengthenTypedHcompPath_sound

-- Phase 43 (sidequest): WRAPPER soundness for cubical path-application
-- producer.  Sister of Phase 42 HcompPath — both ship 3-option-split
-- App-pattern wrappers over the same `Ty.path` pivots
-- (carrier/left/right).  Difference: `pathApp` returns a value at
-- `carrierType` (the path's element type), so the second result
-- (`intervalResult`) strengthens to `Ty.interval` — definitionally
-- preserved by partial strengthening — and that arm is discharged by
-- a trivial `cases intervalTypeStrengthens`.  Closes the second
-- cubical 3-option-split wrapper; combined with Phase 42 this brings
-- the path-elimination family to two zero-axiom shipped soundness
-- theorems.  Remaining cubical 3-option candidate: `glueIntro` (when
-- looked at carefully has Ty.glue's 2 pivots; ships via 2-option not
-- 3-option, so PathLam family is the next 3-option target).
#print axioms LeanFX2.Term.partialStrengthenTypedPathApp_sound

-- Phases 44-52 (sidequest mega-batch): WRAPPER soundness for the
-- nine remaining ListElim-pattern producers refactored to App-pattern.
-- Closes the producer coverage gap.  Each wrapper now takes its
-- type-pivot successes as explicit parameters (lifted from the
-- dispatcher's `cases X : foo` arms), and the soundness theorem
-- mirrors the wrapper's case-cascade and delegates to
-- `_OfSuccess_sound` with `.termRenames` HEq witnesses.  Coverage by
-- pivot count: 1-option (listElim/optionMatch element pivot),
-- 2-option (equivApp/equivApply/equivIntroHet carrier-pair),
-- 3-option (eitherMatch left/right/motive; idJ/oeqJ/idStrictRec
-- carrier/left/right).  All nine ship zero-axiom.  EquivIntroHet
-- inlines the 200-line cascade reconstructing the heterogeneous
-- inverse-law type-strengthens lemmas (via `RawTerm.partialStrengthen?_weaken_lift`
-- and `Ty.partialStrengthen?_weaken_lift` primitives), since its
-- proof children's types depend computationally on the previous
-- children's strengthened raw forms.
#print axioms LeanFX2.Term.partialStrengthenTypedListElim_sound
#print axioms LeanFX2.Term.partialStrengthenTypedOptionMatch_sound
#print axioms LeanFX2.Term.partialStrengthenTypedEitherMatch_sound
#print axioms LeanFX2.Term.partialStrengthenTypedIdJ_sound
#print axioms LeanFX2.Term.partialStrengthenTypedOeqJ_sound
#print axioms LeanFX2.Term.partialStrengthenTypedIdStrictRec_sound
#print axioms LeanFX2.Term.partialStrengthenTypedEquivApp_sound
#print axioms LeanFX2.Term.partialStrengthenTypedEquivApply_sound
#print axioms LeanFX2.Term.partialStrengthenTypedEquivIntroHet_sound

-- Phase 53 — dispatcher-level soundness leaves.  Six closed-leaf
-- arms of the `partialStrengthenTyped?` 78-arm dispatcher inverted
-- and lifted to `StrengtheningSoundness` via their matching wrapper
-- soundness.  These are the no-subterm-recursion arms; recursive
-- and var (option-cased) arms ship in follow-up commits.
#print axioms LeanFX2.Term.partialStrengthenTyped?_atUnit_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atBoolTrue_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atBoolFalse_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atNatZero_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atInterval0_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atInterval1_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atVar_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atNatSucc_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atOptionSome_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atModIntro_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atModElim_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atSubsume_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atIntervalOpp_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atIntervalMeet_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atIntervalJoin_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atListCons_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atListNil_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atOptionNone_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atEitherInl_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atEitherInr_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atPair_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atFst_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atSnd_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atApp_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atAppPi_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atBoolElim_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atNatElim_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atNatRec_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atListElim_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atOptionMatch_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atEitherMatch_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atRefl_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atOeqRefl_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atIdJ_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atOeqJ_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atOeqFunext_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atIdStrictRefl_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atIdStrictRec_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atPathApp_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atGlueElim_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atRecordIntro_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atRecordProj_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atRefineIntro_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atRefineElim_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atCumulUp_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atCodataUnfold_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atCodataDest_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atSessionSend_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atSessionRecv_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atEquivReflId_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atArrowCode_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atPiTyCode_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atSigmaTyCode_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atProductCode_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atSumCode_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atListCode_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atOptionCode_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atEitherCode_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atIdCode_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atEquivCode_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atUniverseCode_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atFunextRefl_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atEquivReflIdAtId_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atFunextReflAtId_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atEquivApp_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atEquivApply_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atUaToEquiv_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atEquivIntroHet_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atUaIntroHet_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atFunextIntroHet_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atEffectPerform_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atGlueIntro_imp_sound
#print axioms LeanFX2.Term.partialStrengthenTyped?_atPathLam_imp_sound

end LeanFX2.SmokeTypedInversion
