import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.CellSort
import FX1Poly.Core.GeneratorTagRoundTrip
import FX1Poly.Core.GeneratorFinitePolygraph
import FX1Poly.Core.GeneratorPolygraphMap
import FX1Poly.Core.GeneratorRedexHead
import FX1Poly.Core.GeneratorRedexHeadSoundness
import FX1Poly.Core.RawCellWordEncoding
import FX1Poly.Core.StepRewriteRuleMap
import FX1Poly.Core.StepWordRewriteSoundness
import FX1Poly.Core.StepWordRewriteEquivariance
import FX1Poly.Core.ConvWordJoinableBridge
import FX1Poly.Core.BetaEtaWordSystem
import FX1Poly.Core.MultisetOrder
import FX1Poly.Core.TerminationOrders
import FX1Poly.Core.RecursivePathOrder
import FX1Poly.Core.RecursiveEliminatorTermination
import FX1Poly.Core.RecursivePathOrderInductive
import FX1Poly.Core.RawIotaRpoBridge
import FX1Poly.Core.RawIotaRpoAssembly
import FX1Poly.Core.RawIotaFullStepSN
import FX1Poly.Core.EraseToRoseRenameInvariant
import FX1Poly.Core.EtaRpoEmbedding
import FX1Poly.Core.RawIotaEtaFullStepSN
import FX1Poly.Typed.RawIotaEtaOperationalSN
import FX1Poly.Typed.MilestoneAParityMatrix
import FX1Poly.Core.Newman
import FX1Poly.Core.DiamondConfluence
import FX1Poly.Core.TakahashiTriangle
import FX1Poly.Core.RawConfluence
import FX1Poly.Core.CommutationConfluence
import FX1Poly.Core.DeterministicConfluence
import FX1Poly.Core.KripkeReducibilityCandidate
import FX1Poly.Core.ReducibleTypeClosed
import FX1Poly.Core.PointwiseIffAlgebra
import FX1Poly.Core.StratifiedReducibleLevelCongr
import FX1Poly.Core.StratifiedReducibleMemberNeutral
import FX1Poly.Core.StratifiedReducibleMemberStepClosure
import FX1Poly.Core.StrongNormalizationSubterm
import FX1Poly.Core.StrongNormalizationCodeFormers
import FX1Poly.Core.StrongNormalizationModalEliminators
import FX1Poly.Core.StrongNormalizationUniverseModeBridges
import FX1Poly.Core.StrongNormalizationNatElim
import FX1Poly.Core.StrongNormalizationListElim
import FX1Poly.Core.StrongNormalizationMatch
import FX1Poly.Core.StrongNormalizationLinearFormers
import FX1Poly.Core.NatElimValueReducibility
import FX1Poly.Core.NatElimValueMember
import FX1Poly.Core.NatElimNeutralScrutineeMember
import FX1Poly.Core.RecursorReducibleScrutineeMember
import FX1Poly.Core.DataEliminatorReducibleScrutineeMember
import FX1Poly.Core.ListElimNeutralScrutineeMember
import FX1Poly.Core.DirectIotaEliminatorNeutralScrutineeMember
import FX1Poly.Core.MatchEliminatorNeutralScrutineeMember
import FX1Poly.Core.NeutralEliminatorMemberSmoke
import FX1Poly.Core.ListElimValueReducibility
import FX1Poly.Core.ListElimValueMember
import FX1Poly.Core.ApplicationStrongNormalizationForward
import FX1Poly.Core.BetaRedexStrongNormalization
import FX1Poly.Core.ListOptionIdCodeUniverseMembership
import FX1Poly.Core.EitherEquivCodeUniverseMembership
import FX1Poly.Core.LinearFormerUniverseMembership
import FX1Poly.Core.StrongNormalizationUnion
import FX1Poly.Core.StrongNormalizationBetaEtaUnion
import FX1Poly.Core.EtaPostponementOverBeta
import FX1Poly.Core.ModalEliminatorReducibility
import FX1Poly.Core.UniverseModeBridgeReducibility
import FX1Poly.Core.RawTermSubstLiftWeaken
import FX1Poly.Typed.ConvergentCanonicityBoundary
import FX1Poly.Core.SconingTaitCrossLeg
import FX1Poly.Core.SconingSNObjectUnique
import FX1Poly.Core.EtaRootClassifier
import FX1Poly.Core.ConvRenameReflection
import FX1Poly.Core.RawTermRenameInjective
import FX1Poly.Core.ConvRenameEquivariance
import FX1Poly.Core.FireRootEtaRedex
import FX1Poly.Core.NormalizeBetaEta
import FX1Poly.Typed.RawBetaNotRpoOrientable
import FX1Poly.Typed.SnTriangulationBundle
import FX1Poly.Typed.HonestCapstoneSignoff

/-! # FX1PolyAudit/AuditCoreTerminationOrders — core reduction-layer zero-axiom gates, shard 02 of 3 (split from the AuditCore monolith for parallel gate elaboration) -/

-- Full oriented-ι-reduction SN: lift oriented root-ι SN to the COMPATIBLE CLOSURE of IotaOrientedHeadStep —
-- oriented ι at the root OR inside ANY child context (IotaStep/IotaStepChildren, mirroring
-- Step/StepChildren; the two Phase-Z substituting succ-iotas are excluded, β-imported boundary). The
-- congruence case finally CONSUMES rpo_congruence: an ι step inside child position i changes
-- eraseChildren only at that position (prefix ++ child :: suffix → prefix ++ child' :: suffix, the child
-- RPO-decreasing by IH), and rpo_congruence lifts that to a node RPO-decrease. The here/there spine walk
-- builds the prefix ([] at head, eraseToRose head :: prefix one step in). Proven via the explicit mutual
-- recursor IotaStep.rec (the Step.subst pattern). IotaStep.toStep: sound sub-relation of the live Step.
-- iotaFullStep_wellFounded: the GENUINE oriented-ι SN (not just root), Tait-free (β + substituting succ-ι
-- imported, η shipped separately).
#assert_no_axioms FX1Poly.Core.IotaStep.rpoEmbeds
#assert_no_axioms FX1Poly.Core.IotaStep.toStep
#assert_no_axioms FX1Poly.Core.iotaFullStep_wellFounded
#assert_no_axioms FX1Poly.Core.IotaStep.congSmoke

-- eraseToRose rename-invariance (the eta-embedding substrate): `eraseToRose` forgets the payload and every
-- binder shift, so a rename (which only rewrites the var-arm payload + renames children) leaves the rose
-- image unchanged.  This is what lets eta-reduction RPO-decrease the SAME eraseToRose order the ι fragment
-- uses: each eta-contraction leaves a SUBTERM of the source modulo a weakening rename (etaLam/etaPathLam put
-- the inner function under one extra binder, reached by RawTerm.weaken), and weaken-invariance erases that
-- gap.  Proven by the mutual term+children recursion mirroring RawTerm.rename_pointwise (var arm closes
-- definitionally; non-var via rename_mkGen_of_ne_var + the children IH).  eraseToRose_weaken is the corollary
-- the binder eta arms consume directly.
#assert_no_axioms FX1Poly.Core.eraseToRose_rename
#assert_no_axioms FX1Poly.Core.eraseChildren_rename
#assert_no_axioms FX1Poly.Core.eraseToRose_weaken

-- Raw eta-contraction embeds into the eraseToRose RPO (the eta-analogue of IotaHeadStep.rpoEmbeds): every eta
-- source wraps its target in 1-2 generator layers, so the target is a SUBTERM of the source's rose image and
-- the source is Rpo-above it.  Precedence-agnostic (subtermEq/subtermStrict ignore prec) → holds for
-- iotaGenPrecedence, so eta decreases the SAME well-founded order ι uses — the union's shared
-- measure.  etaLam/etaPathLam consume eraseToRose_weaken (target under one binder via RawTerm.weaken);
-- etaGlueIntro is a direct child (one subtermEq); the rest reach a grandchild (subtermStrict ∘ subtermEq).
-- Proven via the explicit Step.eta.rec recursor (propext-clean), mirroring IotaStep.rpoEmbeds.
#assert_no_axioms FX1Poly.Core.Step.eta.rpoEmbeds

-- ★ Leg-3 TERM ENDPOINT: the FULL oriented-ι∪η reduction (root + congruence) is strongly normalizing by
-- ONE RPO, Tait-free.  IotaEtaStep = compatible closure of (IotaOrientedHeadStep ∨ Step.eta), mirroring
-- the full oriented-ι IotaStep.  IotaEtaStep.rpoEmbeds: root via Or.elim (oriented ι via
-- IotaHeadStep.rpoEmbeds fed the guard, η via Step.eta.rpoEmbeds, both at iotaGenPrecedence), congruence
-- via rpo_congruence.  iotaEtaFullStep_wellFounded: SN via Subrelation.wf + InvImage.wf over
-- iotaGenRpoWellFounded — the oriented ι/η fragment terminates on its OWN order, NOT through Tait (β +
-- the Phase-Z substituting succ-iotas stay imported).  toIotaEta: both fragments inject at the head.
-- etaCongSmoke: non-vacuity (η inside a congruence).
#assert_no_axioms FX1Poly.Core.IotaEtaStep.rpoEmbeds
#assert_no_axioms FX1Poly.Core.iotaEtaFullStep_wellFounded
#assert_no_axioms FX1Poly.Core.IotaEtaStep.isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.IotaOrientedHeadStep.toIotaEta
#assert_no_axioms FX1Poly.Core.Step.eta.toIotaEta
#assert_no_axioms FX1Poly.Core.IotaEtaStep.etaCongSmoke

-- Operational SN of the ι∪η fragment (Tait-free), the RPO-leg SN endpoint for the parity matrix:
-- harvest of iotaEtaFullStep_wellFounded via the generic relation-polymorphic Acc lemmas
-- (accessibleElementHasNoInfiniteChain / accessibleElementNotSelfRelated).  iotaEta_noInfiniteReduction:
-- NO infinite ι∪η reduction sequence, for EVERY raw term, no typing hypothesis (vs β's Ω/tripler which DO
-- diverge as raw terms).  irreflexive: no 1-cycle.  no_two_cycle: no 2-cycle a⟷b, via a constructed
-- alternating chain (role-swapping recursion, no parity arithmetic) fed to the no-infinite-reduction lemma.
#assert_no_axioms FX1Poly.Core.iotaEta_noInfiniteReduction
#assert_no_axioms FX1Poly.Core.IotaEtaStep.irreflexive
#assert_no_axioms FX1Poly.Core.alternatingSequence_steps
#assert_no_axioms FX1Poly.Core.IotaEtaStep.no_two_cycle

-- ★ PARITY-MATRIX: the 3-leg (Tait / sconing-via-STC / RPO-word) × 3-endpoint (SN / canonicity /
-- consistency) ledger + the HONEST three-way-capstone criterion.  parityCell is the honest 9-cell status
-- table; capstone_currentlyClosedOneWay (rfl): exactly ONE leg (Tait) is fully+independently proven across
-- all three endpoints; threeWayCapstone_not_yet_met (decide): the three-way capstone is NOT yet closed
-- (sconing SN bridged-to-Tait, RPO leg owns only the SN endpoint — Tait-free ι∪η, β imported, canon/consist
-- open).  rpoStrongNormalizationEndpoint: NON-VACUOUS witness (the operational-SN theorem behind the RPO×SN cell).
#assert_no_axioms FX1Poly.Core.ParityMatrix.capstone_currentlyClosedOneWay
#assert_no_axioms FX1Poly.Core.ParityMatrix.legBreakdown
#assert_no_axioms FX1Poly.Core.ParityMatrix.threeWayCapstone_not_yet_met
#assert_no_axioms FX1Poly.Core.ParityMatrix.rpoStrongNormalizationEndpoint

-- The honest convergence/canonicity boundary for the word/RPO leg: the convergent ι∪η presentation does NOT
-- yield canonicity, because its normal forms include non-canonical β-redexes.  appLamUnit = app(lam(unit))unit
-- is ι∪η-NORMAL (appLamUnit_iotaEtaNormal: no IotaEtaStep fires — root app matches no ι/η head-redex, the lam
-- and unit children are normal) yet β-reduces to the value unit (appLamUnit_betaStepsToUnit: Step.beta).  So
-- the convergent presentation halts on a non-value; canonicity requires β-normalization, and β is excluded
-- from the ι∪η word system (raw β is non-SN, Tait-imported).  convergentNormalFormNeedNotBeCanonical packages
-- the NO-GO; convergentNormalFormCanStillBeStronglyNormalizing notes the gap is ι∪η-normality vs canonicity,
-- not SN vs canonicity.  Inversions are direct propext-clean cases over a closed term whose root head matches
-- no redex arm.
#assert_no_axioms FX1Poly.Core.unit_iotaEtaNormal
#assert_no_axioms FX1Poly.Core.lamUnit_iotaEtaNormal
#assert_no_axioms FX1Poly.Core.appLamUnit_iotaEtaNormal
#assert_no_axioms FX1Poly.Core.appLamUnit_betaStepsToUnit
#assert_no_axioms FX1Poly.Core.convergentNormalFormNeedNotBeCanonical
#assert_no_axioms FX1Poly.Core.convergentNormalFormCanStillBeStronglyNormalizing

-- Cross-leg triangulation: the sconing leg and the Tait/Path-A leg produce SN over the SAME object — the
-- sconing-SN cell is bridged to Tait, not independent.  sconingScone_computable_eq_candidate: the sconing
-- witness's displayed predicate IS the reducibility candidate (rfl).  sconingScone_extraction_eq_candidateCR1:
-- the SN extraction IS CR1.  sconingSN_eq_taitComposition: for a well-typed term the sconing leg's extracted
-- SN is the identical witness CR1 (fundamental term typed) the Tait leg produces.  Genuine independence (a
-- second SN proof) would need a different `computable` — the synthetic STC logical relation — which the
-- shipped STC scaffold cannot supply zero-axiom (its ClosedMod is a one-constructor wrapper, not the HIT
-- closed modality, which pulls Quot.sound).  The STC ledger's logicalRelationConstruction rung is
-- witnessed by the BRIDGED construction (STC/FxLogicalRelation.lean — its semantic side is
-- definitionally the Tait pipeline, fxStcFundamental_semantic_isTaitWitness), and the
-- canonicityTheorem rung by the equally BRIDGED canonicityViaSTC (STC/FxBoolCanonicity.lean —
-- semantic side definitionally the kernel's closedBoolCanonicalForms); INDEPENDENCE remains
-- zero-axiom-blocked exactly as this note records, and the block is now FORMALIZED in
-- STC/FxIndependenceBoundary.lean (Prop-payload glues are syntax-determined; every inhabitant's
-- semantic component IS the kernel witness; the shipped ClosedMod is a definitional identity
-- retraction, not the HIT pushout).
#assert_no_axioms FX1Poly.Core.sconingScone_computable_eq_candidate
#assert_no_axioms FX1Poly.Core.normalizationScone_computable_eq_candidate
#assert_no_axioms FX1Poly.Core.sconingScone_and_normalizationScone_share_computable
#assert_no_axioms FX1Poly.Core.sconingScone_extraction_eq_candidateCR1
#assert_no_axioms FX1Poly.Core.sconingSN_eq_taitComposition

-- Generalization of the cross-leg triangulation to the WHOLE class of SN-scones: IsStronglyNormalizing is a
-- Prop, so by definitional proof irrelevance any two sconing witnesses extract the IDENTICAL SN proof
-- (sconingSN_objectUnique), hence any SN-scone's extracted SN IS the Tait CR1∘fundamental witness
-- (anySconingSN_eq_taitComposition), recovering sconingSN_eq_taitComposition as an instance
-- (sconingSN_eq_taitComposition_ofGeneral).  No sconing construction is an independent SN object — the cell is
-- bridgedToTait by theorem; independence can only live in the `computable` predicate, which is STC-blocked.
#assert_no_axioms FX1Poly.Core.sconingSN_objectUnique
#assert_no_axioms FX1Poly.Core.anySconingSN_eq_taitComposition
#assert_no_axioms FX1Poly.Core.sconingSN_eq_taitComposition_ofGeneral

-- The abstract Newman's lemma: terminating + weakly confluent implies confluent, the confluence analogue of
-- the termination orders, generic over any relation.  ReflTransClosure (an own RTC, since
-- Relation.ReflTransGen is Mathlib-only) + single/trans; Joinable/WeaklyConfluent/Confluent vocabulary;
-- newmanAux is the WF-induction tiling (WCR on the two first steps, IH at each reduct, compose); newman is the
-- headline.  Zero-axiom: cases on RTC is propext-clean since its indices are free vars, not ctor patterns.
#assert_no_axioms FX1Poly.Core.ReflTransClosure
#assert_no_axioms FX1Poly.Core.ReflTransClosure.single
#assert_no_axioms FX1Poly.Core.ReflTransClosure.trans
#assert_no_axioms FX1Poly.Core.Joinable
#assert_no_axioms FX1Poly.Core.WeaklyConfluent
#assert_no_axioms FX1Poly.Core.Confluent
#assert_no_axioms FX1Poly.Core.newmanAux
#assert_no_axioms FX1Poly.Core.newman

-- The diamond-implies-confluence route (strip lemma), the second abstract confluence path complementing
-- Newman: confluence from the diamond property alone, no termination.  ReflTransClosure.monotone/collapse
-- (the sandwich glue) + DiamondProperty + stripLemma (single strips against many) + diamondConfluence +
-- confluentOfDiamondSimulation (the parallel-reduction recipe: rel subset parRel subset RTC rel + parRel
-- diamond implies rel confluent — the recipe the TABLE lane's ParStepOverTable discharges).  Zero-axiom.
#assert_no_axioms FX1Poly.Core.ReflTransClosure.monotone
#assert_no_axioms FX1Poly.Core.ReflTransClosure.collapse
#assert_no_axioms FX1Poly.Core.DiamondProperty
#assert_no_axioms FX1Poly.Core.stripLemma
#assert_no_axioms FX1Poly.Core.diamondConfluenceAux
#assert_no_axioms FX1Poly.Core.diamondConfluence
#assert_no_axioms FX1Poly.Core.confluentOfDiamondSimulation

-- The Takahashi triangle lemma: the linear route to the parallel-reduction diamond.  A completeDevelopment
-- function with the TriangleProperty (every reduct steps to the source's complete development) yields
-- DiamondProperty.ofTriangle and Confluent.ofTriangle, reducing the parallel diamond from a quadratic
-- redex-pair join to the single linear "exhibit completeDevelopment + its triangle" obligation (Takahashi
-- 1995).  Composes with diamondConfluence; the TABLE lane (TableTakahashiTriangle) consumes it.
#assert_no_axioms FX1Poly.Core.DiamondProperty.ofTriangle
#assert_no_axioms FX1Poly.Core.Confluent.ofTriangle
-- The existential per-source form (HasMaximalReduct): generalizes the function-based TriangleProperty
-- (HasMaximalReduct.ofTriangle) and is the form a concrete parallel reduction discharges by structural
-- recursion on the source (no separately-defined total completeDevelopment function over RawTerm needed).
-- ofMaximalReduct yields the diamond; Confluent.ofMaximalReduct composes with diamondConfluence.
#assert_no_axioms FX1Poly.Core.HasMaximalReduct.ofTriangle
#assert_no_axioms FX1Poly.Core.DiamondProperty.ofMaximalReduct
#assert_no_axioms FX1Poly.Core.Confluent.ofMaximalReduct

-- ★ THE TABLE-ROUTED RAW CONFLUENCE (StepStarConfluenceViaTable.lean) — the bespoke-iota
-- retirement's decoupling brick.  The 17-row legacy table carries the same well-formedness
-- (legacyIotaRuleTable_isWf, four rfl-decidable enumeration checks) and scope-uniformity
-- (legacyIotaRuleTable_isScopeUniform, inherited through legacyRow_memFullTable) certificates as
-- the canonical 18-row table, so the generic orthogonal-systems table confluence instantiates at
-- it (StepOverTable.legacyConfluent).  The IOTA-T1 adequacy lifts to stars in both directions
-- (StepStar.toLegacyTableClosure / ReflTransClosure.legacyToStepStar), and the headlines
-- transport: StepStar.tableRouteConfluence (many-vs-many) + StepStar.tableRouteStrip
-- (one-vs-many) — NO parallel-reduction sandwich, NO complete development, NO per-iota
-- critical-pair matrix.
#assert_no_axioms FX1Poly.Core.legacyIotaRuleTable_isWf
#assert_no_axioms FX1Poly.Core.legacyIotaRuleTable_isScopeUniform
#assert_no_axioms FX1Poly.Core.StepOverTable.legacyConfluent
#assert_no_axioms FX1Poly.Core.StepStar.toLegacyTableClosure
#assert_no_axioms FX1Poly.Core.ReflTransClosure.legacyToStepStar
#assert_no_axioms FX1Poly.Core.StepStar.tableRouteConfluence
#assert_no_axioms FX1Poly.Core.StepStar.tableRouteStrip

-- The local one-step join (one-vs-one instance of the table confluence) — the shape the
-- historical per-iota critical-pair matrix (cd_lemma over the CriticalPairs/CdLemma enumeration,
-- now DELETED) proved by quadratic case analysis.  Every former cd_lemma consumer (the
-- accessibility Newman bridge, the beta-only fragment of the betaEta local Church-Rosser, the
-- certified word-rewrite reflection) now draws its local join from here.
#assert_no_axioms FX1Poly.Core.StepStar.localJoin

-- Unconditional raw confluence, discharged through the TABLE route
-- (StepStar.tableRouteConfluence above): global Church-Rosser for the raw StepStar relation with
-- no strong-normalization assumption (raw beta+iota is not SN).  The historical bespoke route
-- (ParStep per-iota mirror + complete development + Takahashi triangle) is RETIRED — the abstract
-- DiamondProperty/Confluent.ofTriangle vocabulary above survives for the table lane's own
-- Takahashi argument (TableTakahashiTriangle).
#assert_no_axioms FX1Poly.Core.StepStar.rawConfluence

-- The Newman-precursor strip property, unconditional via the table route
-- (StepStar.tableRouteStrip): a single Step out of a source joins against any StepStar chain out
-- of it.  A distinct statement from rawConfluence (one-vs-many vs many-vs-many);
-- confluence_of_strip turns it into the same Church-Rosser result.  No SN assumption.
#assert_no_axioms FX1Poly.Core.StepStar.rawStrip

-- Raw Conv (= StepStar.Join) is an unconditional equivalence relation.  Conv.refl / Conv.sym are structural;
-- Conv.trans is the consequence of Church-Rosser, discharged by StepStar.rawConfluence (which supplies the
-- confluence hypothesis), so Conv.trans + Conv.equivalence + the calc-enabling Trans instance hold
-- unconditionally, with no strong-normalization premise (raw beta+iota is not SN).  This is the foundation the
-- raw-layer conversion checker rests on.
#assert_no_axioms FX1Poly.Core.Conv.trans
#assert_no_axioms FX1Poly.Core.Conv.equivalence
#assert_no_axioms FX1Poly.Core.Conv.instTrans

-- Uniqueness of normal forms with no termination hypothesis.  StepStar.rawConfluence joins any two
-- reductions of a common source, so two normal reducts coincide whether or not the source terminates, making
-- "the normal form" a well-defined partial function on all raw terms.  The proof reuses Conv.eq_of_noStep +
-- isStepNormalForm_blocks_step, joining via rawConfluence.
#assert_no_axioms FX1Poly.Core.normalForm_unique_of_confluence

-- Conv equals normal-form equality with no SN hypothesis.  rawConfluence + normalForm_unique_of_confluence
-- discharge the per-term confluence witnesses, so the iff holds for any two terms that reduce to normal forms.
-- This separates decidable Conv into existence-of-normal-forms (the SN obligation, gated) and
-- correctness-of-normal-form-comparison (pure confluence, unconditional).  The decidable wrapper decides Conv
-- via instDecidableEqRawTerm given the normal-form witnesses, no SN premise.
#assert_no_axioms FX1Poly.Core.Conv.iff_normalForms_eq_of_confluence
#assert_no_axioms FX1Poly.Core.Conv.decidableOfNormalForms

-- The Path-B decider (polycell.md §2.3) with the confluence hypothesis discharged.  Conv.iff_normalForm_eq /
-- Conv.decidableOfNormalizer take a Normalizer and StepStar.HasConfluence; rawConfluence discharges the latter,
-- so a Normalizer alone decides Conv as normal-form equality.  The Normalizer (a total normal-form function)
-- remains the SN obligation (raw beta+iota has no global normalizer); the separate confluence assumption a
-- normalizer construction would otherwise also supply is what this discharges.
#assert_no_axioms FX1Poly.Core.Normalizer.conv_iff_normalForm_eq
#assert_no_axioms FX1Poly.Core.Normalizer.decidableConv

-- Hindley-Rosen via the diamond (abstract toolkit): the third confluence route after Newman (terminating)
-- and DiamondConfluence (single diamond).  Modular: it combines two separately-confluent relations whose
-- diamonds commute into a confluent union (the intended FX use: beta-parallel diamond + iota-parallel diamond +
-- beta/iota commute, without one monolithic 20-arm ParStep).  StronglyCommutes + DiamondProperty.union (4-way
-- case split) + confluentOfUnionDiamonds + confluentUnionOfParallelDiamonds (the two-relation generalization of
-- confluentOfDiamondSimulation).  Zero-axiom.
#assert_no_axioms FX1Poly.Core.StronglyCommutes
#assert_no_axioms FX1Poly.Core.DiamondProperty.union
#assert_no_axioms FX1Poly.Core.confluentOfUnionDiamonds
#assert_no_axioms FX1Poly.Core.confluentUnionOfParallelDiamonds

-- Deterministic confluence (abstract toolkit, fourth route): a deterministic (functional) relation is
-- confluent, since its reflexive-transitive reducts from a common source are linearly ordered.  Determinism
-- does not give the strict diamond (a normal form breaks it), so this is its own linear-chain induction.  The
-- route for deterministic reduction strategies (weak-head here, the deterministic NbE evaluator downstream).
-- IsDeterministic + confluentOfDeterministic + the concrete WeakHeadStep.hasConfluence (weak-head reduction is
-- Church-Rosser, from WeakHeadStep.deterministic).  Zero-axiom.
#assert_no_axioms FX1Poly.Core.IsDeterministic
#assert_no_axioms FX1Poly.Core.confluentOfDeterministicAux
#assert_no_axioms FX1Poly.Core.confluentOfDeterministic
#assert_no_axioms FX1Poly.Core.WeakHeadStep.hasConfluence

-- A reducibility candidate is closed under renaming, in the Kripke-indexed form: IsKripkeReducibilityCandidate
-- (CR1 members-SN + CR2 closed-under-Step) survives KripkeCand.transport along any renaming with no hypothesis
-- (the index precomposes; laws read off at the composed index).  The bare same-scope ReducibleTypeStep form is
-- false (the piType same-scope argument quantifier has a counterexample at a renamed Pi-type), so the Kripke
-- index is what carries renaming-closure.  Predicate-level companion is kripkeArrowDep_transport_pointwise.
#assert_no_axioms FX1Poly.Core.IsKripkeReducibilityCandidate
#assert_no_axioms FX1Poly.Core.IsKripkeReducibilityCandidate.transport

-- Pointwise-saturation of the dependent reducibility relation (the level-free fundamental theorem's
-- choice-free piIntro keystone): `ReducibleTypeClosed` is closed under pointwise-iff by construction, so it
-- carries the canonical member-predicate candidate that bare `ReducibleType` does not.  Gated per-declaration
-- here, outside the AuditCoreSubstrate sweep's import closure.
#assert_no_axioms FX1Poly.Core.ReducibleTypeClosed
#assert_no_axioms FX1Poly.Core.ReducibleType.toClosed
#assert_no_axioms FX1Poly.Core.ReducibleType.closedAtMemberPredicate

-- Equivalence-relation algebra of candidate pointwise-iff (the transport algebra the reducibility model
-- threads through every `ReducibleType.deterministic` candidate transfer and the `ReducibleType.ofPointwiseIff`
-- congruence-closure cascade).
#assert_no_axioms FX1Poly.Core.PointwiseIff.refl
#assert_no_axioms FX1Poly.Core.PointwiseIff.symm
#assert_no_axioms FX1Poly.Core.PointwiseIff.trans

-- Candidate-congruence of the stratified reducibility step-functor under lower-existence-equivalence: the
-- inductive step of level-irrelevance (Pi case via ofPointwiseIff, universe case via the lower-existence
-- equivalence).  The level-0 degenerate base means it does not bootstrap full irrelevance alone (see the module
-- docstring); it is the hard core a level argument reuses.
#assert_no_axioms FX1Poly.Core.ReducibleTypeStep.existsCongr

-- Fuel-zero boundary witness: unlike universe-code domains, neutral classifiers can genuinely have
-- members at fuel zero, so the dependent-formation telescope's base-level branch cannot be discharged by
-- a generic contradiction.
#assert_no_axioms FX1Poly.Core.IsReducibleMemberAt.variableClassifierHasVariableMemberAtZero

-- Strong-normalization inverse lemmas for dependent type-code children.  These are the subterm
-- accessibility projections needed by structural arguments over reducible Pi/Sigma type values.
#assert_no_axioms FX1Poly.Core.StepStar.domain_isStronglyNormalizing_of_piTyCode
#assert_no_axioms FX1Poly.Core.StepStar.codomain_isStronglyNormalizing_of_piTyCode
#assert_no_axioms FX1Poly.Core.StepStar.domain_isStronglyNormalizing_of_sigmaTyCode
#assert_no_axioms FX1Poly.Core.StepStar.codomain_isStronglyNormalizing_of_sigmaTyCode

-- CR2 / CR3 closure lifted to the semantic-membership layer (the forward-Step, forward-StepStar, and
-- neutral-backward companions of the CR1 membership corollary; the Tait closure bricks the fundamental
-- theorem's neutral and reduction-stable cases consume).
#assert_no_axioms FX1Poly.Core.IsReducibleMemberAt.closedUnderStep
#assert_no_axioms FX1Poly.Core.IsReducibleMemberAt.closedUnderStepStar
#assert_no_axioms FX1Poly.Core.IsReducibleMemberAt.neutralExpansion

-- Structural SN closure completing the universe-code former family: the one-child listCode/optionCode
-- congruence inversions + SN, the three-child idCode inversion + SN, and the reusable three-child congruence
-- SN combinator (the three-child analogue of the one/two-child versions).  The SN half of "the code is a
-- reducible member of El"; SN is fuel-independent.
#assert_no_axioms FX1Poly.Core.Step.from_listCode
#assert_no_axioms FX1Poly.Core.Step.from_optionCode
#assert_no_axioms FX1Poly.Core.Step.from_idCode
#assert_no_axioms FX1Poly.Core.StepStar.isStronglyNormalizing_of_threeChildCong
#assert_no_axioms FX1Poly.Core.StepStar.listCode_isStronglyNormalizing_of_element
#assert_no_axioms FX1Poly.Core.StepStar.optionCode_isStronglyNormalizing_of_element
#assert_no_axioms FX1Poly.Core.StepStar.idCode_isStronglyNormalizing_of_type_endpoints
