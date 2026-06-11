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
import FX1Poly.Core.WordRewriteMisalignment
import FX1Poly.Core.ConvWordJoinableBridge
import FX1Poly.Core.BetaEtaWordSystem
import FX1Poly.Core.MultisetOrder
import FX1Poly.Core.TerminationOrders
import FX1Poly.Core.RecursivePathOrder
import FX1Poly.Core.RecursiveEliminatorTermination
import FX1Poly.Core.IotaNonRecursiveTermination
import FX1Poly.Core.RecursiveIotaSizeGrowth
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
import FX1Poly.Core.StepParallelConfluence
import FX1Poly.Core.TakahashiTriangle
import FX1Poly.Core.ParallelReduction
import FX1Poly.Core.CompleteDevelopment
import FX1Poly.Core.ParStepSubstRename
import FX1Poly.Core.ParStepSubstPointwise
import FX1Poly.Core.ParStepInversion
import FX1Poly.Core.CompleteDevelopmentParStep
import FX1Poly.Core.ParStepTriangle
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

/-! # FX1PolyAudit/AuditCoreCellsAndIota — core reduction-layer zero-axiom gates, shard 01 of 3 (split from the AuditCore monolith for parallel gate elaboration) -/

#assert_no_axioms FX1Poly.Core.CellSort
#assert_no_axioms FX1Poly.Core.CellSort.all
#assert_no_axioms FX1Poly.Core.CellSort.toCode
#assert_no_axioms FX1Poly.Core.CellSort.ofCode?
#assert_no_axioms FX1Poly.Core.CellSort.ofCode?_toCode
#assert_no_axioms FX1Poly.Core.CellSort.all_length


-- §11.6.4 Generator-table validation: the FX0 prefix-code tag assignment
-- `Generator.toNat` is collision-free (injective), proved via the explicit left
-- inverse `Generator.fromTag` and its per-constructor round-trip.  The head byte
-- of the cell serialization therefore uniquely identifies the generator.
#assert_no_axioms FX1Poly.Core.Generator.fromTag
#assert_no_axioms FX1Poly.Core.Generator.fromTag_toNat
#assert_no_axioms FX1Poly.Core.Generator.toNat_injective

-- The FX kernel as a finite polygraph over the 197-Generator table.  The generators are indexed injectively
-- (toNat_injective) and boundedly (toNat_lt) into Fin 197, with the total inverse table fromTag (round-trip
-- fromTag_toNat + range-totality fromTag_total_on_range); each carries its dimension (arity) and boundary
-- (binderShifts), coherently (binderShifts_length_eq_arity).  fxKernelPolygraph bundles all of it.  Zero-axiom
-- via cases + bounded decide with raised maxRecDepth (plain decide, not native_decide).
#assert_no_axioms FX1Poly.Core.Generator.toNat_lt
#assert_no_axioms FX1Poly.Core.Generator.fromTag_total_on_range

-- GeneratorRedexHead (HON-2): the operational-liveness axis of the honesty ledger. Generator.hasRedexHead
-- decides whether a Step fires at the ROOT of a cell headed by g — the 11 eliminator generators (β: gen_app;
-- ι: boolElim/fst/snd/natElim/natRec/listElim/optionMatch/eitherMatch/idJ/idStrictRec), exactly
-- RawTerm.hasRootStepSource's set. Canonical value-formers (lam/boolTrue/pair) are NOT redex heads (live as
-- VALUES via the static axis); the recursive/strict eliminators (natElim/natRec/listElim/idStrictRec) REDUCE
-- but are statically reserved — the operational axis's marginal tier contribution. Zero-axiom (decide over
-- DecidableEq Generator, no wildcard match; every witness rfl). Soundness (false ⟹ no root Step) is HON-6.
#assert_no_axioms FX1Poly.Core.Generator.hasRedexHead
#assert_no_axioms FX1Poly.Core.hasRedexHead_app
#assert_no_axioms FX1Poly.Core.hasRedexHead_boolElim
#assert_no_axioms FX1Poly.Core.hasRedexHead_natElim
#assert_no_axioms FX1Poly.Core.hasRedexHead_natRec
#assert_no_axioms FX1Poly.Core.hasRedexHead_listElim
#assert_no_axioms FX1Poly.Core.hasRedexHead_idStrictRec
#assert_no_axioms FX1Poly.Core.hasRedexHead_lam
#assert_no_axioms FX1Poly.Core.hasRedexHead_boolTrue
#assert_no_axioms FX1Poly.Core.hasRedexHead_pair
#assert_no_axioms FX1Poly.Core.hasRedexHead_piTyCode
#assert_no_axioms FX1Poly.Core.hasRedexHead_hilbertSpace
#assert_no_axioms FX1Poly.Core.hasRedexHead_quantumGate

-- GeneratorRedexHeadSoundness (HON-6): the operational-inertness SOUNDNESS of hasRedexHead (HON-2). A
-- generator the redex-head classifier rejects fires NO root redex for ANY cell built on it — universally, in
-- the kernel's own no-root-redex vocabulary. hasRedexHead_false_imp_fireRootRedex_none is the computational
-- statement (fireRootRedex = none, the firing used by reduceOnce/normalize); hasRedexHead_false_imp_no_root_redex
-- is the normal-form statement (hasRootStepSource = false, the !-half of isStepNormalFormBool), derived via the
-- shipped fireRootRedex_eq_none_imp_hasRootStepSource_false (no re-extraction). The instances cover a reserved
-- head (hilbertSpace) and a value head (lam, live via the static axis, not a redex head). This is the operational
-- half of semanticTier soundness (HON-7); reserved ⟹ hasRedexHead = false, so it applies to every reserved
-- generator. Zero-axiom (rw + Bool.noConfusion disequality extraction, dsimp + 11 dif_neg; no Bool.or_eq_false_iff).
#assert_no_axioms FX1Poly.Core.hasRedexHead_false_imp_fireRootRedex_none
#assert_no_axioms FX1Poly.Core.hasRedexHead_false_imp_no_root_redex
#assert_no_axioms FX1Poly.Core.hilbertSpace_no_root_redex
#assert_no_axioms FX1Poly.Core.lam_no_root_redex
-- EtaRootClassifier (HON-15): closes the η gap HON-6 documented. hasRedexHead (HON-2) is β/ι-only, so it brands
-- gen_lam etc. inert — yet lam (app (weaken f) var0) η-contracts. hasEtaSourceHead = the 5 η-source heads
-- (lam/pair/pathLam/modIntro/glueIntro); hasRedexHeadBetaEta = hasRedexHead || hasEtaSourceHead, the honest βη
-- operational classifier. Step.eta is ROOT-ONLY (no congruence arm), so hasRootEtaSource_false_imp_no_root_eta is
-- exact (cases step <;> Bool.noConfusion, each arm an etaXxxSource whose head computes the detector true).
-- hasRedexHeadBetaEta_false_imp_betaEta_inert = HON-6 (β/ι root-source) + the η lemma, the total βη-inertness
-- soundness over Step.betaEta = Step ∨ Step.eta. lam_etaLive_betaInert pins the honest gain. Zero-axiom.
#assert_no_axioms FX1Poly.Core.Generator.hasEtaSourceHead
#assert_no_axioms FX1Poly.Core.Generator.hasRedexHeadBetaEta
#assert_no_axioms FX1Poly.Core.RawTerm.hasRootEtaSource
#assert_no_axioms FX1Poly.Core.hasEtaSourceHead_lam
#assert_no_axioms FX1Poly.Core.hasEtaSourceHead_pair
#assert_no_axioms FX1Poly.Core.hasEtaSourceHead_pathLam
#assert_no_axioms FX1Poly.Core.hasEtaSourceHead_modIntro
#assert_no_axioms FX1Poly.Core.hasEtaSourceHead_glueIntro
#assert_no_axioms FX1Poly.Core.hasEtaSourceHead_hilbertSpace
#assert_no_axioms FX1Poly.Core.hasEtaSourceHead_app
#assert_no_axioms FX1Poly.Core.lam_etaLive_betaInert
#assert_no_axioms FX1Poly.Core.hasRootEtaSource_etaLamSource
#assert_no_axioms FX1Poly.Core.hasRootEtaSource_etaPairSource
#assert_no_axioms FX1Poly.Core.hasRootEtaSource_etaPathLamSource
#assert_no_axioms FX1Poly.Core.hasRootEtaSource_etaModIntroSource
#assert_no_axioms FX1Poly.Core.hasRootEtaSource_etaGlueIntroSource
#assert_no_axioms FX1Poly.Core.hasRootEtaSource_false_imp_no_root_eta
#assert_no_axioms FX1Poly.Core.hasRedexHeadBetaEta_false_imp_betaEta_inert
#assert_no_axioms FX1Poly.Core.fxKernelPolygraph

-- The explicit Generator-to-polygraph-generator map.  PolygraphGenerator presents each former with its
-- boundary (tag + child arity + child boundary shifts, coherently); toPolygraphGenerator is the presentation
-- map; _injective is faithful (distinct generators present distinctly, via toNat_injective); _boundary/_tag
-- confirm the presented data is binderShifts/toNat (rfl); _recoversGenerator is invertible (fromTag
-- round-trips the presented tag).  Zero-axiom: record literal over toNat/arity/binderShifts; rfl projections;
-- congrArg into toNat_injective.
#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator
#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator_injective
#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator_boundary
#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator_tag
#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator_recoversGenerator

-- The dim-1 free-monoid rule-word encoding of the RawCell composite layer, the start of the FX-Conv-to-word
-- bridge.  encodeRuleWord reads off the ordered generating-cell rule ids (the dim-1 rewrite-rule alphabet,
-- distinct from the term-formers): objects/identities to the empty word, generatingCell to [ruleId],
-- composites to ++.  The per-constructor rules are rfl; _assoc + _identity_left/_right are the monoid
-- homomorphism onto the free monoid (List ++ / [] with assoc + two-sided unit); length_eq_generatingCellCount
-- is faithfulness to the rewrite content.  Zero-axiom: structural recursion + local propext-free list/Nat lemmas.
#assert_no_axioms FX1Poly.Core.RawCell.encodeRuleWord
#assert_no_axioms FX1Poly.Core.encodeRuleWord_termBase
#assert_no_axioms FX1Poly.Core.encodeRuleWord_generatingCell
#assert_no_axioms FX1Poly.Core.encodeRuleWord_verticalComposite
#assert_no_axioms FX1Poly.Core.encodeRuleWord_horizontalComposite
#assert_no_axioms FX1Poly.Core.encodeRuleWord_identityCell
#assert_no_axioms FX1Poly.Core.encodeRuleWord_assoc
#assert_no_axioms FX1Poly.Core.encodeRuleWord_identity_left
#assert_no_axioms FX1Poly.Core.encodeRuleWord_identity_right
#assert_no_axioms FX1Poly.Core.RawCell.generatingCellCount
#assert_no_axioms FX1Poly.Core.encodeRuleWord_length_eq_generatingCellCount

-- Each FX reduction as a rewrite rule over the term-code word monoid.  Uses the faithful RawTerm.toCode
-- (head tag + payload + children) as the bridge encode.  toCode_mkGen (rfl head-tag rule) + toCode_ne_nil
-- (every code begins with the head tag, so non-degenerate rules).  Step.inducedRewriteRule maps a reduction to
-- the rule (redex.toCode, reduct.toCode); projections rfl + both-sides-non-empty.  fxStepSystem is the
-- generated rule system (a rule is in it iff it is some reduction's code-pair); inducedRewriteRule_mem proves
-- every Step lands in it by construction.  Zero-axiom: rfl / cases + cons_ne_nil / existential-intro with rfl
-- witnesses.
#assert_no_axioms FX1Poly.Core.toCode_mkGen
#assert_no_axioms FX1Poly.Core.toCode_ne_nil
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_leftHandSide
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_rightHandSide
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_leftHandSide_ne_nil
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_rightHandSide_ne_nil
#assert_no_axioms FX1Poly.Core.fxStepSystem
#assert_no_axioms FX1Poly.Core.Step.inducedRewriteRule_mem_fxStepSystem

-- The forward half of the term-code-word bridge: FX reduction embeds into word rewriting over the
-- term-code monoid.  FxWordRewritesOneStep is one-step word rewriting (List Nat) under an FxTermRewriteRule
-- system (fire + left/right context closure).  Step.toWordRewrite is single-step soundness (the fire of the
-- system rule, with no typed-SN side condition since fxStepSystem holds every instantiated reduction as a
-- top-level rule).  FxWordRewritesMany is the refl-trans closure with single/trans + context lifts (a
-- congruence preorder); StepStar.toWordRewrites is many-step soundness by induction over the chain.
-- Zero-axiom: Prop inductives + constructor application + structural inductions.
#assert_no_axioms FX1Poly.Core.FxWordRewritesOneStep
#assert_no_axioms FX1Poly.Core.Step.toWordRewrite
#assert_no_axioms FX1Poly.Core.FxWordRewritesMany
#assert_no_axioms FX1Poly.Core.FxWordRewritesMany.single
#assert_no_axioms FX1Poly.Core.FxWordRewritesMany.trans
#assert_no_axioms FX1Poly.Core.FxWordRewritesMany.underLeftContext
#assert_no_axioms FX1Poly.Core.FxWordRewritesMany.underRightContext
#assert_no_axioms FX1Poly.Core.StepStar.toWordRewrites

-- WordRewriteMisalignment — the SN-134 verdict.  The serializer is preorder [tag, payload] pairs, and word
-- rewriting fires at ANY offset: the beta-redex code [3,0,2,0,1,0,0,0,1,0] reads at ODD offset as five
-- variable leaves (gen_var.toNat = 0), so a left-nested pair-of-variables host — a Step-NORMAL form —
-- contains a misaligned occurrence and its code word-rewrites.  Hence the word→term inversion is FALSE
-- (even asking only for SOME term reduct), word rewriting is strictly coarser than term rewriting, and —
-- with untypedWordReductionDiverges — BOTH hypotheses of the full-system convergent-presentation decision
-- fail: an honest word-layer decision must decode to the term layer first.

#assert_no_axioms FX1Poly.Core.misalignmentRedex_steps
#assert_no_axioms FX1Poly.Core.misalignmentRule_mem_fxStepSystem
#assert_no_axioms FX1Poly.Core.misalignedPairHost_isNormal
#assert_no_axioms FX1Poly.Core.misalignedPairHost_code
#assert_no_axioms FX1Poly.Core.fxWordRewritesOneStep_firesOnNormalImage
#assert_no_axioms FX1Poly.Core.wordStepInversion_isFalse

-- Rename/subst-equivariance of the Step-to-word bridge + system-level inversion.  The soundness commutes
-- with the term rename/subst actions (Step.toWordRewrite_rename/_subst, StepStar.toWordRewrites_rename, via
-- Step.rename/Step.subst/StepStar.rename) and the generated system is closed under both
-- (fxStepSystem_rename_mem/_subst_mem).  fxStepSystem_imp_step inverts the system (every rule comes from a
-- Step) + _leftHandSide/_rightHandSide_ne_nil (no degenerate rules).  The reverse word-to-Step direction is
-- not part of this gate (the free word monoid and toCode payload-collapse on universe codes make full
-- completeness non-derivable here).  Zero-axiom.
#assert_no_axioms FX1Poly.Core.Step.toWordRewrite_rename
#assert_no_axioms FX1Poly.Core.StepStar.toWordRewrites_rename
#assert_no_axioms FX1Poly.Core.Step.toWordRewrite_subst
#assert_no_axioms FX1Poly.Core.fxStepSystem_rename_mem
#assert_no_axioms FX1Poly.Core.fxStepSystem_subst_mem
#assert_no_axioms FX1Poly.Core.fxStepSystem_imp_step
#assert_no_axioms FX1Poly.Core.fxStepSystem_leftHandSide_ne_nil
#assert_no_axioms FX1Poly.Core.fxStepSystem_rightHandSide_ne_nil

-- The Conv-to-word-joinability bridge (forward half).  Conv is term joinability (StepStar.Join = common
-- reduct); FxWordJoinable is the ConvertibleModulo for the FX term-code word monoid (common word reduct).
-- Conv.toWordJoinable maps both StepStar legs via StepStar.toWordRewrites with common = commonTerm.toCode.
-- refl/symm establish a reflexive-symmetric relation; this gate does not include trans (which needs word
-- confluence) or the reverse direction (the word-to-term completeness gap).  Zero-axiom.
#assert_no_axioms FX1Poly.Core.FxWordJoinable
#assert_no_axioms FX1Poly.Core.FxWordJoinable.refl
#assert_no_axioms FX1Poly.Core.FxWordJoinable.symm
#assert_no_axioms FX1Poly.Core.FxWordJoinable.ofWordRewritesMany
#assert_no_axioms FX1Poly.Core.Conv.toWordJoinable
#assert_no_axioms FX1Poly.Core.Step.toWordJoinable

-- The certified beta/iota/eta word-rewrite system.  fxStepSystem covers beta/iota (over Step); eta lives in
-- Step.eta, so fxBetaEtaStepSystem enumerates the full system over Step.betaEta (= Step or Step.eta).  Generic
-- membership + single-step soundness (fire) reuse the generic FxWordRewrites*; fxStepSystem_imp_fxBetaEtaStepSystem
-- embeds the beta/iota system (Or.inl); Step/Step.eta.toBetaEtaWordRewrite certify beta/iota (Or.inl) and eta
-- (Or.inr) rules.  Step.betaEtaStar.toWordRewrites is the many-step eta-inclusive soundness.  Zero-axiom.
#assert_no_axioms FX1Poly.Core.fxBetaEtaStepSystem
#assert_no_axioms FX1Poly.Core.Step.betaEta.inducedRewriteRule
#assert_no_axioms FX1Poly.Core.Step.betaEta.inducedRewriteRule_mem_fxBetaEtaStepSystem
#assert_no_axioms FX1Poly.Core.Step.betaEta.toWordRewrite
#assert_no_axioms FX1Poly.Core.fxStepSystem_imp_fxBetaEtaStepSystem
#assert_no_axioms FX1Poly.Core.Step.toBetaEtaWordRewrite
#assert_no_axioms FX1Poly.Core.Step.eta.toBetaEtaWordRewrite
#assert_no_axioms FX1Poly.Core.Step.betaEtaStar.toWordRewrites

-- The Dershowitz-Manna multiset ordering + its well-foundedness, the foundational termination order.
-- Mechanized zero-axiom over Init only: a true multiset is the quotient of List by permutation, but Quot.sound
-- is banned, so MultisetRedOne is an existential on plain List (prefix ++ removed :: suffix shrinks to
-- prefix ++ added ++ suffix, added all below removed).  isWellFounded is the Dershowitz-Manna theorem via the
-- nested-Acc argument (emptyAccessible + consAccessible with the accAppendBelow inner helper).  Inversion by
-- obtain + cases prefixList (clean List split, no indexed-cases propext leak).  replaceHead/underContext make
-- the order constructible.  Zero-axiom.
#assert_no_axioms FX1Poly.Core.MultisetRedOne
#assert_no_axioms FX1Poly.Core.MultisetRedOne.replaceHead
#assert_no_axioms FX1Poly.Core.MultisetRedOne.underContext
#assert_no_axioms FX1Poly.Core.MultisetRedOne.emptyAccessible
#assert_no_axioms FX1Poly.Core.MultisetRedOne.consAccessible
#assert_no_axioms FX1Poly.Core.MultisetRedOne.isWellFounded

-- The lexicographic list order + well-foundedness (the lex companion to the multiset order, the comparison
-- LPO uses for arguments and RPO for lex-status symbols) + measure-based termination certificates over both
-- orders.  LexListStep is the existential-on-List lex single step (length-matched tails); isWellFounded via
-- length-indexed nested accessibility.  wellFounded_of_multisetMeasure/_lexMeasure turn a measure-decrease
-- into WellFounded via InvImage.wf.  Zero-axiom: List-existential inversion (cases commonPrefix), defeq length
-- + local length_append, Nat.noConfusion directly (absurd + succ_ne_zero leaks propext).
#assert_no_axioms FX1Poly.Core.LexListStep
#assert_no_axioms FX1Poly.Core.LexListStep.length_eq
#assert_no_axioms FX1Poly.Core.LexListStep.emptyAccessible
#assert_no_axioms FX1Poly.Core.LexListStep.consAccessible
#assert_no_axioms FX1Poly.Core.LexListStep.accessibleByLength
#assert_no_axioms FX1Poly.Core.LexListStep.isWellFounded
#assert_no_axioms FX1Poly.Core.wellFounded_of_multisetMeasure
#assert_no_axioms FX1Poly.Core.wellFounded_of_lexMeasure

-- The RPO termination certificate: precedence times argument-order, lexicographically.  LexPair is the lex
-- product of two relations as a disjunction (not the indexed Prod.Lex, whose cases leaks propext via the
-- pair-index); isWellFounded by nested Acc with rcases on the Or.  wellFounded_of_precedenceMultisetMeasure /
-- _LexMeasure are the RPO certificates for multiset-status / lex-status symbols: a step terminates if the
-- precedence rank decreases or stays equal while the argument measure decreases.  Zero-axiom: Or-inversion +
-- InvImage.wf.
#assert_no_axioms FX1Poly.Core.LexPair
#assert_no_axioms FX1Poly.Core.LexPair.pairAccessible
#assert_no_axioms FX1Poly.Core.LexPair.isWellFounded
#assert_no_axioms FX1Poly.Core.wellFounded_of_lexPairMeasure
#assert_no_axioms FX1Poly.Core.wellFounded_of_precedenceMultisetMeasure
#assert_no_axioms FX1Poly.Core.wellFounded_of_precedenceLexMeasure
-- ★ SPIKE: the RECURSIVE-eliminator ι-pattern terminates via the shipped multiset RPO certificate,
-- INDEPENDENT of β and typed-SN (the Leg-3 "β-imported boundary"). The fxSystem termination imports
-- typed-SN because it encodes β (raw β is non-terminating); η-SN is shipped; the open ι piece
-- splits — non-recursive ι is size-decreasing, the RECURSIVE eliminator (natElim-succ DUPLICATES the recursive
-- call on a SMALLER scrutinee) needs the multiset (Dershowitz-Manna) RPO. This models that hard core: ElimStep
-- elim(k+1) ↝ branch(elim k, elim k), terminated by recScrutineeMultiset over Nat.lt via
-- wellFounded_of_precedenceMultisetMeasure — NO β, NO Tait. listAppendAssoc is propext-free (List.append_assoc
-- DEPENDS ON propext). De-risking model; the real Step ι-arms over RawTerm are the multi-firing follow-on.
#assert_no_axioms FX1Poly.Core.listAppendAssoc
#assert_no_axioms FX1Poly.Core.MultisetRedOne.appendRight
#assert_no_axioms FX1Poly.Core.MultisetRedOne.appendLeft
#assert_no_axioms FX1Poly.Core.elimStep_decreasesMultiset
#assert_no_axioms FX1Poly.Core.recursiveEliminatorTerminates
#assert_no_axioms FX1Poly.Core.recursiveEliminatorTerminates.smoke
-- ★ Leg 3: the NON-recursive ι fragment over the REAL kernel terminates by RawTerm.size,
-- INDEPENDENT of β and typed-SN. The 13 non-recursive ι arms (branch-selection bool/nat/list/option-none,
-- fst/snd projection, idJ/idStrictRec base, optionSome/eitherInl/eitherInr applied-branch) strictly
-- decrease size; toStep ties the fragment to the live Step relation (NOT a toy like the recursive RecTerm
-- model); SN via Subrelation.wf + InvImage.wf RawTerm.size — the EXACT shape of the shipped η-SN. The 3
-- recursive arms (RecursiveEliminatorTermination above) and η-SN (Step.etaStar) complete Leg-3 ι/η; the β
-- boundary stays honestly Tait-imported. AC-normalization is explicit Nat.add_right_comm (simp-AC + ac_rfl
-- both leak propext).
#assert_no_axioms FX1Poly.Core.IotaNonRecursiveStep.toStep
#assert_no_axioms FX1Poly.Core.IotaNonRecursiveStep.size_decreases
#assert_no_axioms FX1Poly.Core.iotaNonRecursiveStep_wellFounded
#assert_no_axioms FX1Poly.Core.IotaNonRecursiveStep.isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.IotaNonRecursiveStep.isStronglyNormalizing.smoke
-- ★ Leg 3 contrast: the RECURSIVE ι arm natElimSucc INCREASES RawTerm.size by branchSize + 13
-- (grows with the zero branch) over the REAL kernel: the Phase-Z succ-iota SUBSTITUTES, and a step branch
-- using its induction-hypothesis variable twice (app (var 0) (var 0)) DUPLICATES the recursive call — and
-- with it the arbitrary zero branch it carries. So the size route (IotaNonRecursiveStep.size_decreases)
-- does NOT extend to the recursive arms, and NO flat measure dominated by size survives the duplication.
-- Moreover the substituting succ-iota shares beta's duplication shape (betaNotOrientableByErasure), which
-- is exactly why the Phase-Z re-scope moves it to the beta-imported boundary (IotaOrientedHeadStep keeps
-- only the non-substituting arms); typed SN covers it through Tait. beta stays Tait-imported (raw beta is
-- non-SN).
#assert_no_axioms FX1Poly.Core.natElimSucc_isRealStep
#assert_no_axioms FX1Poly.Core.natElimSuccReduct_size_eq
#assert_no_axioms FX1Poly.Core.natElimSucc_size_increases
#assert_no_axioms FX1Poly.Core.natElimSucc_size_increase_at_least_branch

-- The genuine INDUCTIVE recursive path order: the generic rose-tree RPO with multiset status,
-- positivity-accepted (subterm clause split into subtermEq/subtermStrict to avoid the kernel's nested-Or
-- rejection; multiset witnesses inlined to avoid passing the inductive to the external MultisetRedOne).
-- rpo_orients_natElim ORIENTS the branch-duplication obstruction arm — redex ≻ reduct for natElim(succ n) z s
-- with an ARBITRARY duplicated branch s — exactly what every flat measure failed; the subterm
-- property tames the duplication. fxPrecedence_wellFounded is the first WF ingredient. The full RPO
-- well-foundedness (Nipkow/Buchholz nested accessibility, fed by MultisetRedOne.consAccessible) is the crux.
#assert_no_axioms FX1Poly.Core.RpoInductive.rpo_orients_natElim
#assert_no_axioms FX1Poly.Core.RpoInductive.fxPrecedence_wellFounded

-- RPO well-foundedness: the Nipkow/Buchholz nested-accessibility theorem, zero-axiom and with
-- NO size measure. acc_node uses the rose-tree recursor twice (top-level wrapper + the predecessor's
-- predAcc, which supplies the precedence/multiset cases their children accessible — breaking the apparent
-- circularity); the four-clause Rpo inversion via `cases` is propext-clean. rpoWellFounded :
-- WellFounded prec → WellFounded (RpoBelow prec); fxRpoWellFounded instantiates it at fxPrecedence, so the
-- branch-duplication obstruction arm (oriented by rpo_orients_natElim) sits in a genuine well-founded order.
#assert_no_axioms FX1Poly.Core.RpoInductive.rpoWellFounded
#assert_no_axioms FX1Poly.Core.RpoInductive.fxRpoWellFounded

-- RPO congruence: the order is a CONGRUENCE — replacing one child by an RPO-smaller child makes
-- the node RPO-smaller (via the multiset clause: a single Dershowitz-Manna decrease, unchanged children
-- dominated as subterms, the replacement dominated through the larger child). This is the monotonicity /
-- compatibility-with-contexts that turns the root-redex order into a genuine REWRITE order — the load-bearing
-- ingredient that lifts a child-context ι step to a node-level RPO decrease. The four List append/membership
-- helpers it consumes are propext-clean re-proofs (Init's List.append_assoc and friends leak propext).
#assert_no_axioms FX1Poly.Core.RpoInductive.rpo_congruence
#assert_no_axioms FX1Poly.Core.RpoInductive.rpo_congruence_head

-- RawTerm RPO bridge: the generic rose-tree RPO instantiated at the REAL kernel. eraseToRose
-- forgets RawTerm's scope/binder-shift structure to a RoseTerm Generator; realGenPrecedence ranks the
-- recursive eliminators above gen_app. Post Phase-Z re-scope: ONLY listElimCons remains a live RPO-oriented
-- recursive Step (listElimConsRaw_isStep confirms the redex/reduct pair really is the live constructor; its
-- app-chain reduct is RPO-dominated by the redex). The natElim/natRec succ-iotas now SUBSTITUTE and are
-- NOT erasure-orientable — their pre-migration arity-3 app-chain orientations survive only as ROSE-level
-- boundary records (rpo_orients_iotaNatElimSucc / iotaNatRecSucc over RoseTerm; the retired arity-3 shape
-- is no longer even RawTerm-expressible against the live arity-4 generator table). realGenRpoWellFounded
-- gives the order is well-founded. beta + the substituting succ-iotas stay Tait-imported.
#assert_no_axioms FX1Poly.Core.RawIotaRpo.listElimConsRaw_isStep
#assert_no_axioms FX1Poly.Core.RawIotaRpo.rpo_orients_iotaNatElimSucc
#assert_no_axioms FX1Poly.Core.RawIotaRpo.rpo_orients_iotaNatRecSucc
#assert_no_axioms FX1Poly.Core.RawIotaRpo.rpo_orients_iotaListElimCons
#assert_no_axioms FX1Poly.Core.RawIotaRpo.realGenRpoWellFounded

-- The β boundary of the rose-tree RPO is a THEOREM, not a hand-typed verdict. The bridge orients the
-- terminating ι/η fragment (realGenRpoWellFounded above), but no type-blind well-founded order on the
-- eraseToRose-erased syntax can orient raw β: Ω = (λx. x x)(λx. x x) β-steps to ITSELF, so its single
-- erasure would have to sit strictly below itself — a self-loop accessibleElementNotSelfRelated refutes.
-- This forces the rose-tree-word-rewriting leg to cover strong normalization only as a partial fragment;
-- full β-SN routes through Tait (Ω is untypable), exactly as RawIotaRpoBridge already imports.
#assert_no_axioms FX1Poly.Core.RawIotaRpo.betaNotOrientableByErasure

-- SN triangulation bundle: "SN proven once (Tait), triangulated twice" consolidated against the parity
-- ledger. snColumnIsHonest pins the SN column = (provenIndependent, bridgedToTait, partialFragment) by rfl;
-- snPrimaryTait is Leg 1 (Tait, the one independent proof); snConfirmSconingBridged is Leg 2 (sconing = Tait
-- object, proof irrelevance); snConfirmRpoFragment + snRpoBetaBoundary are Leg 3 (ι∪η fragment SN, Tait-free,
-- with β provably non-orientable so β stays Tait-imported).
#assert_no_axioms FX1Poly.Core.ParityMatrix.snColumnIsHonest
#assert_no_axioms FX1Poly.Core.ParityMatrix.snPrimaryTait
#assert_no_axioms FX1Poly.Core.ParityMatrix.snConfirmSconingBridged
#assert_no_axioms FX1Poly.Core.ParityMatrix.snConfirmRpoFragment
#assert_no_axioms FX1Poly.Core.ParityMatrix.snRpoBetaBoundary

-- Honest capstone sign-off: the honest Milestone-A criterion (Tait proves all 3 endpoints; SN triangulated
-- twice — sconing bridged + RPO fragment) is MET (honestCapstoneMet_holds, rfl on the ledger), WHILE the naive
-- three-independent-ways criterion is NOT (and cannot be, per the SN NO-GOs) —
-- honestCapstone_met_while_threeWay_unreachable. The sconing-consistency cell is now bridgedToTait (the honesty
-- fix), so the ledger column stays honest.
#assert_no_axioms FX1Poly.Core.ParityMatrix.honestCapstoneMet
#assert_no_axioms FX1Poly.Core.ParityMatrix.honestCapstoneMet_holds
#assert_no_axioms FX1Poly.Core.ParityMatrix.honestCapstone_met_while_threeWay_unreachable

-- Oriented root-ι SN assembly (Phase-Z re-scope EXECUTED): unify the non-recursive arms + the
-- listElim-cons recursive arm into ONE order over the ORIENTED fragment of the CANONICAL
-- FX1Poly.Core.IotaHeadStep (IotaOrientedHeadStep = IotaHeadStep ∧ the isNatRecursorSuccRedex guard is
-- false — the two Phase-Z SUBSTITUTING natElim/natRec succ-iotas join the β-imported boundary, exactly
-- betaNotOrientableByErasure's situation). iotaGenRank bumps optionMatch/eitherMatch to rank 2 (their
-- reduct app(branch,value) has head gen_app, which outranks the redex head under the recursive-arm
-- precedence — wrong direction; the bump fixes it). rpoOrientsAppliedFirst/Second orient the 3
-- applied-branch arms; IotaHeadStep.rpoEmbeds covers the 14 oriented arms (the 2 substituting arms
-- discharge via Bool.noConfusion on the guard). iotaOrientedHeadStep_wellFounded: the oriented root-ι
-- fragment is SN by ONE RPO via Subrelation.wf + InvImage.wf eraseToRose, Tait-free (the unification).
#assert_no_axioms FX1Poly.Core.RawIotaRpo.iotaGenPrecedence_wellFounded
#assert_no_axioms FX1Poly.Core.RawIotaRpo.rpoOrientsAppliedFirst
#assert_no_axioms FX1Poly.Core.RawIotaRpo.rpoOrientsAppliedSecond
#assert_no_axioms FX1Poly.Core.RawIotaRpo.iotaGenRpoWellFounded
#assert_no_axioms FX1Poly.Core.RawTerm.isNatRecursorSuccRedex
#assert_no_axioms FX1Poly.Core.IotaHeadStep.rpoEmbeds
#assert_no_axioms FX1Poly.Core.iotaOrientedHeadStep_wellFounded
#assert_no_axioms FX1Poly.Core.IotaOrientedHeadStep.isStronglyNormalizing
#assert_no_axioms FX1Poly.Core.IotaOrientedHeadStep.listElimConsSmoke
