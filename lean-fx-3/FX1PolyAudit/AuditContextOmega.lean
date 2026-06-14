import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.ContextOmega.Interface
import FX1Poly.Tier0.ContextOmega.Comprehension
import FX1Poly.Tier0.ContextOmega.Uemura
import FX1Poly.Tier0.ContextOmega.Colimits
import FX1Poly.Tier0.ContextOmega.DimensionalFunctor
import FX1Poly.Tier0.ContextOmega.ModalLock
import FX1Poly.Tier0.ContextOmega.Initiality
import FX1Poly.Tier0.ContextOmega.Biequivalence
import FX1Poly.Tier0.ContextOmega.Strictification
import FX1Poly.Tier0.ContextOmega.ExplicitSubstitution
import FX1Poly.Tier0.ContextOmega.SubstitutionFree
import FX1Poly.Tier0.ContextOmega.Fibration
import FX1Poly.Tier0.ContextOmega.Sconing
import FX1Poly.Tier0.ContextOmega.MultimodalNormalization
import FX1Poly.Tier0.ContextOmega.SimplicialModel
import FX1Poly.Tier0.ContextOmega.InfinityCwF
import FX1Poly.Tier0.ContextOmega.FibrationCategory
import FX1Poly.Tier0.ContextOmega.LocalCartesianClosure
import FX1Poly.Tier0.ContextOmega.BeckChevalleyCoherence
import FX1Poly.Tier0.ContextOmega.GlobalSectionsModality

/-! # AuditContextOmega — zero-axiom gate for context-0 (the context ω-category)

The Tier-0 context ω-category design-lock: the FX instance bridges to the
shipped renaming CwR + global sections, and the honest construction ledger
records the context slice in the four-axis vocabulary.  Every pin must be free
of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- The FX context ω-category is the shipped substrate, re-presented.
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_base_eq_renamingVecRMC
#assert_no_axioms
  FX1Poly.Tier0.ContextOmega.fxContextOmega_globalSections_eq_renamingVecGlobalSections
#assert_no_axioms
  FX1Poly.Tier0.ContextOmega.fxContextOmega_globalSections_terminal_subsingleton

-- The honest construction ledger (what is built).
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_hasRepresentableBase
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_hasGlobalSections

-- The honest construction ledger (the recorded gaps → context-1 … context-21).
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_hasNoComprehensionPromoted
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_hasNoUemuraBijection
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_hasNoRightAdjointTranspension
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_hasNoModalLock
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_hasNoDimTwoHomotopy
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxContextOmega_hasNoStandaloneModalRMC

-- context-1: the comprehension universal property over the FX term base.
#assert_no_axioms FX1Poly.Tier0.ContextOmega.comprehensionSplit_comprehensionPair
#assert_no_axioms FX1Poly.Tier0.ContextOmega.comprehensionPair_comprehensionSplit
#assert_no_axioms FX1Poly.Tier0.ContextOmega.comprehensionBijection

-- context-2 (SN-088): the Uemura bijection — type-formers ARE representable nat-transformations.
-- formerComprehension = ★ the keystone (every former is representable); the bundle round-trips are
-- the bijection; formerDeterminedByGenericClassifier = the generic-element converse.
#assert_no_axioms FX1Poly.Tier0.ContextOmega.IsRepresentableFormer
#assert_no_axioms FX1Poly.Tier0.ContextOmega.formerComprehension
#assert_no_axioms FX1Poly.Tier0.ContextOmega.piFormerComprehension
#assert_no_axioms FX1Poly.Tier0.ContextOmega.sigmaFormerComprehension
#assert_no_axioms FX1Poly.Tier0.ContextOmega.RepresentableTypeFormer.ofFormer
#assert_no_axioms FX1Poly.Tier0.ContextOmega.RepresentableTypeFormer.toFormer
#assert_no_axioms FX1Poly.Tier0.ContextOmega.RepresentableTypeFormer.toFormer_ofFormer
#assert_no_axioms FX1Poly.Tier0.ContextOmega.RepresentableTypeFormer.ofFormer_toFormer
#assert_no_axioms FX1Poly.Tier0.ContextOmega.piRepresentableFormer
#assert_no_axioms FX1Poly.Tier0.ContextOmega.sigmaRepresentableFormer
#assert_no_axioms FX1Poly.Tier0.ContextOmega.piRepresentableFormer_toFormer
#assert_no_axioms FX1Poly.Tier0.ContextOmega.sigmaRepresentableFormer_toFormer
#assert_no_axioms FX1Poly.Tier0.ContextOmega.formerDeterminedByGenericClassifier

-- context-3 (the colimit half): finite coproducts of contexts + the initial empty context.
-- coproductHomBijection = the coproduct universal property in hom-set form;
-- emptyContextInitial_unique = the empty context is the initial object.
#assert_no_axioms FX1Poly.Tier0.ContextOmega.coproductCopair
#assert_no_axioms FX1Poly.Tier0.ContextOmega.coproductSplit
#assert_no_axioms FX1Poly.Tier0.ContextOmega.coproductSplit_coproductCopair
#assert_no_axioms FX1Poly.Tier0.ContextOmega.coproductCopair_coproductSplit
#assert_no_axioms FX1Poly.Tier0.ContextOmega.coproductHomBijection
#assert_no_axioms FX1Poly.Tier0.ContextOmega.emptyContextMorphism
#assert_no_axioms FX1Poly.Tier0.ContextOmega.emptyContextInitial_unique

-- context-3 (the dimensional-functor half): the weakening endofunctor `Ω` of the adjoint string.
-- liftUnderBinder_identity/_compose = the vec-level lift functor laws; dimExtend = the endofunctor
-- on objects (with functor laws); dimExtendMap = its action on morphisms (naturality at the lifted vec).
#assert_no_axioms FX1Poly.Tier0.SubstVec.liftUnderBinder_identity
#assert_no_axioms FX1Poly.Tier0.SubstVec.liftUnderBinder_compose
#assert_no_axioms FX1Poly.Tier0.ContextOmega.dimExtend
#assert_no_axioms FX1Poly.Tier0.ContextOmega.dimExtendMap
#assert_no_axioms FX1Poly.Tier0.ContextOmega.dimExtend_typeCellFamily_sections
#assert_no_axioms FX1Poly.Tier0.ContextOmega.dimExtendMap_displayClassifier_component

-- context-4 (the modal lock `◐` + LOCK 2-functoriality): the endofunctor infrastructure, the
-- dimension lock as a concrete endofunctor on the context base, and the lock ↔ dimExtend bridge.
-- RawEndofunctor + identity/comp = the LOCK 2-functoriality skeleton (◐_id = Id, locks compose);
-- dimensionLock = the modal lock for the dimension modality; dimensionLockSquared = ◐∘◐ adds two
-- variables; dimExtend_sections_eq_lockReindex = dimExtend is reindexing along the lock (◐^*).
#assert_no_axioms FX1Poly.Tier0.RawEndofunctor
#assert_no_axioms FX1Poly.Tier0.RawEndofunctor.identity
#assert_no_axioms FX1Poly.Tier0.RawEndofunctor.comp
#assert_no_axioms FX1Poly.Tier0.ContextOmega.dimensionLock
#assert_no_axioms FX1Poly.Tier0.ContextOmega.dimensionLock_objectMap
#assert_no_axioms FX1Poly.Tier0.ContextOmega.dimensionLockSquared_objectMap
#assert_no_axioms FX1Poly.Tier0.ContextOmega.dimExtend_sections_eq_succ
#assert_no_axioms FX1Poly.Tier0.ContextOmega.dimExtend_sections_eq_lockReindex

-- context-5 (initiality): the syntactic context objects are the INITIAL context-algebra (Lawvere's
-- natural-numbers object). ContextAlgebra = the object-level model data; interpretScope = the unique
-- interpretation (Nat.rec); interpretScope_unique = ★ object-level initiality (Nat-induction
-- uniqueness, zero-axiom); syntacticContextAlgebra/interpretScope_syntactic_id = the self-initiality
-- fixed point along the lock.
#assert_no_axioms FX1Poly.Tier0.ContextOmega.ContextAlgebra
#assert_no_axioms FX1Poly.Tier0.ContextOmega.ContextAlgebra.interpretScope
#assert_no_axioms FX1Poly.Tier0.ContextOmega.ContextAlgebra.interpretScope_zero
#assert_no_axioms FX1Poly.Tier0.ContextOmega.ContextAlgebra.interpretScope_succ
#assert_no_axioms FX1Poly.Tier0.ContextOmega.ContextAlgebra.interpretScope_unique
#assert_no_axioms FX1Poly.Tier0.ContextOmega.syntacticContextAlgebra
#assert_no_axioms FX1Poly.Tier0.ContextOmega.interpretScope_syntactic_id

-- context-6 (biequivalence): the four semantic presentations (CwF / natural model / RMC / CwA /
-- contextual category) agree on the FX context base. naturalModelDisplayProjection/GenericElement =
-- Awodey's display map `p` + generic element `q`; naturalModelExtensionDecomposes = representability
-- IS the CwF comprehension; scopeContextGrade(_empty/_extend) = Cartmell's contextual length grading
-- bridging to context-5's NNO; presentationsBiequivalent = ★ the object+hom-set core of the
-- biequivalence (the 2-functor coherences are the recorded funext boundary).
#assert_no_axioms FX1Poly.Tier0.ContextOmega.naturalModelDisplayProjection
#assert_no_axioms FX1Poly.Tier0.ContextOmega.naturalModelGenericElement
#assert_no_axioms FX1Poly.Tier0.ContextOmega.naturalModelExtensionDecomposes
#assert_no_axioms FX1Poly.Tier0.ContextOmega.scopeContextGrade
#assert_no_axioms FX1Poly.Tier0.ContextOmega.scopeContextGrade_empty
#assert_no_axioms FX1Poly.Tier0.ContextOmega.scopeContextGrade_extend
#assert_no_axioms FX1Poly.Tier0.ContextOmega.presentationsBiequivalent

-- context-7 (strictification): the FX context base is ALREADY SPLIT — substitution is strictly
-- functorial on the nose, so the local-universes / right-adjoint-splitting coherence construction
-- (Lumsdaine–Warren) is the identity strictification here. reindexType = the display-map pullback;
-- reindexType_identity/_compose = ★ the strict coherence laws A[id]=A / A[σ∘τ]=A[σ][τ] (equalities,
-- the coherence iso is rfl); substitutionStrictlyAssociative/UnitalLeft/Right = the precomposition
-- essence (the base category is strict, not bi-); reindexType_typeCellFamily = reindexing IS
-- substitution; familyReindexingStrictlyFunctorial/fxBaseSubstCategoryIsStrict/fxBaseIsSplitModel =
-- ★ the headline (the FX base is a split model, coherence solved on the nose).
#assert_no_axioms FX1Poly.Tier0.ContextOmega.reindexType
#assert_no_axioms FX1Poly.Tier0.ContextOmega.reindexType_identity
#assert_no_axioms FX1Poly.Tier0.ContextOmega.reindexType_compose
#assert_no_axioms FX1Poly.Tier0.ContextOmega.substitutionStrictlyAssociative
#assert_no_axioms FX1Poly.Tier0.ContextOmega.substitutionStrictlyUnitalLeft
#assert_no_axioms FX1Poly.Tier0.ContextOmega.substitutionStrictlyUnitalRight
#assert_no_axioms FX1Poly.Tier0.ContextOmega.reindexType_typeCellFamily
#assert_no_axioms FX1Poly.Tier0.ContextOmega.familyReindexingStrictlyFunctorial
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxBaseSubstCategoryIsStrict
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxBaseIsSplitModel

-- context-8 (explicit substitution λσ): the FX base realizes the ACCL λσ substitution calculus
-- (substitution as a SubstVec, propagation as the meta-level subst/compose) and the σ-fragment is
-- convergent. substMapRule = ★ Map ((a·s)∘t = a[t]·(s∘t)); substSurjectivePairing = ★ SCons (the
-- substitution η, via the comprehension universal property); fxRealizesLambdaSigmaCalculus = all 9
-- σ-rules bundled; sigmaTripleConfluent = ★ the σ-fragment is Church-Rosser (a triple substitution
-- converges); sigmaSubstitutionTotal = σ terminates automatically (subst is a total meta-function —
-- the Melliès non-termination of object-level λσ is sidestepped by construction, recorded in header).
#assert_no_axioms FX1Poly.Tier0.ContextOmega.substMapRule
#assert_no_axioms FX1Poly.Tier0.ContextOmega.substSurjectivePairing
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxRealizesLambdaSigmaCalculus
#assert_no_axioms FX1Poly.Tier0.ContextOmega.sigmaTripleConfluent
#assert_no_axioms FX1Poly.Tier0.ContextOmega.sigmaSubstitutionTotal

-- context-9 (substitution-free structural algorithm, SFMTT): Nuyts' substitution-free MTT realized on
-- the FX base — substitution is admissible (the meta-level `RawTerm.subst`), the only structural binder
-- operation is the lift `s ↦ ⟨v0, s∘↑⟩`. structuralLiftIsModalLock = ★ the lift IS context-4's modal
-- lock action (by rfl) — "substitution-free under modal locks" holds by construction;
-- structuralLiftRespectsIdentity/Composition = the lift is functorial (the completeness substrate);
-- substitutionFreeAgreesWithSubstitution = ★ SFMTT soundness (structural lift = kernel lift on terms);
-- singleSubstitutionIsStructural = the structural β-rule (subst0 = singleton substitution);
-- substitutionFreeStructuralAlgorithmUnderLock = ★ the headline bundle (the derivation-level
-- biconditional is the recorded funext boundary).
#assert_no_axioms FX1Poly.Tier0.ContextOmega.structuralLiftIsModalLock
#assert_no_axioms FX1Poly.Tier0.ContextOmega.structuralLiftRespectsIdentity
#assert_no_axioms FX1Poly.Tier0.ContextOmega.structuralLiftRespectsComposition
#assert_no_axioms FX1Poly.Tier0.ContextOmega.substitutionFreeAgreesWithSubstitution
#assert_no_axioms FX1Poly.Tier0.ContextOmega.singleSubstitutionIsStructural
#assert_no_axioms FX1Poly.Tier0.ContextOmega.substitutionFreeStructuralAlgorithmUnderLock

-- context-10 (comprehension category / Jacobs fibration): the FX context base IS a split
-- comprehension fibration with the Beck-Chevalley condition.  fibredWeakening = the fibred weakening
-- functor π^* (reindexing along the display map); ★ beckChevalleyDisplaySquare = the Beck-Chevalley
-- naturality square (substitution commutes with the display map, weakening ∘ lift σ = σ ∘ weakening) —
-- the genuinely-new zero-axiom theorem via weakening_compose_cons; cartesianLift = the Cartesian
-- morphism σ⁺; cartesianLift_coversBase = it covers σ; fibrationIsSplit = strict cleavage (split
-- fibration); comprehensionPullbackUniversalProperty = the display-map representability (cons_unique);
-- dependentSumAdjunctionBijection = Σ ⊣ π^* via comprehension; dependentProductIsRepresentableFormer =
-- π^* ⊣ Π via the representable former; jacobsComprehensionFibrationCore = ★ the headline (the full
-- hom-set adjunctions over arbitrary families are the recorded funext boundary).
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fibredWeakening
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fibredWeakening_eq_reindexAlongDisplay
#assert_no_axioms FX1Poly.Tier0.ContextOmega.cartesianLift
#assert_no_axioms FX1Poly.Tier0.ContextOmega.beckChevalleyDisplaySquare
#assert_no_axioms FX1Poly.Tier0.ContextOmega.cartesianLift_coversBase
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fibrationIsSplit
#assert_no_axioms FX1Poly.Tier0.ContextOmega.comprehensionPullbackUniversalProperty
#assert_no_axioms FX1Poly.Tier0.ContextOmega.dependentSumAdjunctionBijection
#assert_no_axioms FX1Poly.Tier0.ContextOmega.dependentProductIsRepresentableFormer
#assert_no_axioms FX1Poly.Tier0.ContextOmega.jacobsComprehensionFibrationCore

-- context-11 (synthetic Tait computability / STC over the context base + relative induction): the FX
-- context base's scone (Artin gluing of syntax with global sections) is where the canonicity/normalization
-- logical relation lives.  ★ relativeInductionEquivalence = the closed-term scone realization is a
-- two-sided iso (glued model ≃ syntax-with-computability, the relative-induction equivalence);
-- relativeInductionLift = STC relative induction (every closed term lifts to a computability witness,
-- splitting realization); openModalPartAlwaysLifts = the syntax-only/open-modal scone trivially extracts;
-- boolCanonicityViaRelativeInduction = bool canonicity (inhabited + SN computability domain);
-- consistencyViaRelativeInduction = empty consistency (no extraction); syntheticTaitComputabilityCore =
-- ★ the headline (full glued-model QIIT recursor over all syntax is the recorded funext boundary).
#assert_no_axioms FX1Poly.Tier0.ContextOmega.relativeInductionEquivalence
#assert_no_axioms FX1Poly.Tier0.ContextOmega.relativeInductionLift
#assert_no_axioms FX1Poly.Tier0.ContextOmega.openModalPartAlwaysLifts
#assert_no_axioms FX1Poly.Tier0.ContextOmega.boolCanonicityViaRelativeInduction
#assert_no_axioms FX1Poly.Tier0.ContextOmega.consistencyViaRelativeInduction
#assert_no_axioms FX1Poly.Tier0.ContextOmega.syntheticTaitComputabilityCore

-- context-12 (Gratzer multimodal NbE over the modal base): the shipped NbE normalizer `RawTerm.normalize`
-- IS Gratzer's normalization function, living over the context ω-category.  ★ normalFormsStableUnderReindexing
-- = the genuinely-new modal lemma (NbE normal forms are stable under ANY reindexing `rename rho`, so they
-- form a presheaf over the modal base; proved via Step.reflectRename); dimensionLockObjectActionIsScopeSuccessor
-- = the lock shifts the index by one (the lock's base reindexing IS weakening); normalFormStableUnderDimensionLock
-- = the lock's-reindexing instance (normal forms stable under term weakening); multimodalNormalFormIsReachedAndNormal
-- = the Gratzer nf (every SN term reduces to a structurally-normal output, total on well-typed via SN-043);
-- multimodalNormalizationSoundComplete = the NbE characterization (Conv IS normal-form equality);
-- conversionDecidableOverModalBase = the Gratzer payoff (decidable Conv on the SN fragment);
-- multimodalNormalizationCore = ★ the headline (the full presheaf-NbE-model recursor + the normalize/rename
-- commutation are the recorded funext boundary).
#assert_no_axioms FX1Poly.Tier0.ContextOmega.normalFormsStableUnderReindexing
#assert_no_axioms FX1Poly.Tier0.ContextOmega.dimensionLockObjectActionIsScopeSuccessor
#assert_no_axioms FX1Poly.Tier0.ContextOmega.normalFormStableUnderDimensionLock
#assert_no_axioms FX1Poly.Tier0.ContextOmega.multimodalNormalFormIsReachedAndNormal
#assert_no_axioms FX1Poly.Tier0.ContextOmega.multimodalNormalizationSoundComplete
#assert_no_axioms FX1Poly.Tier0.ContextOmega.conversionDecidableOverModalBase
#assert_no_axioms FX1Poly.Tier0.ContextOmega.multimodalNormalizationCore

-- context-13 (Kapulkin-Lumsdaine simplicial model): the univalent universe in sSet.  A SEMANTIC model over
-- a DIFFERENT base (sSet, not the FX syntactic context category), the classical Voevodsky/KL construction —
-- NOT mechanizable zero-axiom (needs simplicial-homotopy machinery + classical choice).  Shipped is the
-- honest SemanticModelLedger (reused by context-22..26) + the KL record + flag pins
-- (providesUnivalentUniverse / requiresClassicalMetatheory / baseIsNotFXSyntactic / isNotMechanizedInFX /
-- role = relativeConsistency).  ★ fxConsistencyIsConstructiveNotModelDependent = the genuine cross-reference
-- (FX's empty-consistency is CONSTRUCTIVE via the shipped consistencyViaRelativeInduction, so FX does not
-- depend on the simplicial model; the model is an ADDITIONAL classical relative-consistency anchor for the
-- univalence extension); simplicialModelLedgerHonest = the headline ledger bundle.  The model itself is the
-- recorded classical-construction boundary.
#assert_no_axioms FX1Poly.Tier0.ContextOmega.kapulkinLumsdaineLedger_providesUnivalentUniverse
#assert_no_axioms FX1Poly.Tier0.ContextOmega.kapulkinLumsdaineLedger_roleIsRelativeConsistency
#assert_no_axioms FX1Poly.Tier0.ContextOmega.kapulkinLumsdaineLedger_requiresClassicalMetatheory
#assert_no_axioms FX1Poly.Tier0.ContextOmega.kapulkinLumsdaineLedger_baseIsNotFXSyntactic
#assert_no_axioms FX1Poly.Tier0.ContextOmega.kapulkinLumsdaineLedger_isNotMechanizedInFX
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxConsistencyIsConstructiveNotModelDependent
#assert_no_axioms FX1Poly.Tier0.ContextOmega.simplicialModelLedgerHonest

-- context-14 ((∞,1)-CwF / natural model in an ∞-topos): the comprehension ∞-category whose universe is the
-- ∞-topos' object classifier (univalent by construction).  Another SEMANTIC model over a higher-categorical
-- base (an ∞-topos, not the FX syntactic context category) — NOT mechanizable zero-axiom (∞-groupoids need
-- simplicial machinery or Quot.sound HITs).  Shipped is the honest infinityToposNaturalModelLedger (reusing
-- the context-13 SemanticModelLedger) + flag pins (providesUnivalentUniverse / roleIsRelativeConsistency /
-- requiresClassicalMetatheory / baseIsNotFXSyntactic / isNotMechanizedInFX).  ★
-- fxNaturalModelIsZeroTruncationOfInfinityCwF = the genuine cross-reference (the shipped zero-axiom
-- comprehensionBijection — the FX 1-categorical comprehension's strict hom-set bijection — IS the
-- 0-truncation of the (∞,1)-natural-model representability); simplicialModelIsAConcreteInfinityTopos = the
-- simplicial model (context-13) is a concrete ∞-topos instance; infinityCwFLedgerHonest = the headline.  The
-- ∞-topos natural model + object classifier are the recorded higher-categorical / classical boundary.
#assert_no_axioms FX1Poly.Tier0.ContextOmega.infinityToposNaturalModelLedger_providesUnivalentUniverse
#assert_no_axioms FX1Poly.Tier0.ContextOmega.infinityToposNaturalModelLedger_roleIsRelativeConsistency
#assert_no_axioms FX1Poly.Tier0.ContextOmega.infinityToposNaturalModelLedger_requiresClassicalMetatheory
#assert_no_axioms FX1Poly.Tier0.ContextOmega.infinityToposNaturalModelLedger_baseIsNotFXSyntactic
#assert_no_axioms FX1Poly.Tier0.ContextOmega.infinityToposNaturalModelLedger_isNotMechanizedInFX
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxNaturalModelIsZeroTruncationOfInfinityCwF
#assert_no_axioms FX1Poly.Tier0.ContextOmega.simplicialModelIsAConcreteInfinityTopos
#assert_no_axioms FX1Poly.Tier0.ContextOmega.infinityCwFLedgerHonest

-- context-15 (Avigad-Kapulkin-Lumsdaine fibration category on contexts): the syntactic category of
-- contexts with display maps as fibrations + Id-type path objects is a Brown fibration category.  Unlike
-- context-13/14 this is built ON the FX contexts — so the CATEGORICAL axioms are GENUINE RECOGNITION over
-- shipped substrate (fibrations = display maps, pullback-stable = the shipped beckChevalleyDisplaySquare,
-- every object fibrant, path object from gen_idCode + gen_refl).  Shipped is the BrownFibrationCategoryLedger
-- with the structural-vs-homotopy per-axiom split + flag pins.  ★ pullbackStabilityViaBeckChevalley = the
-- genuine anchor (the shipped zero-axiom BC square IS Brown's FC3 pullback-stability);
-- fibrationPullbackCoversBaseViaCartesianLift = the Cartesian-lift anchor (FC3 existence, via shipped
-- cartesianLift_coversBase); fxFibrationCategoryStructurallyRealized = the headline.  The HOMOTOPY axioms
-- (weak-equivalence class, the homotopy category as a localisation) are the recorded boundary.
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxBrownFibrationCategoryLedger_fibrationsAreDisplayMaps
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxBrownFibrationCategoryLedger_fibrationsPullbackStable
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxBrownFibrationCategoryLedger_everyObjectFibrant
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxBrownFibrationCategoryLedger_pathObjectFromIdAndRefl
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxBrownFibrationCategoryLedger_baseIsFXSyntacticContext
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxBrownFibrationCategoryLedger_weakEquivalenceClassNotMechanized
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxBrownFibrationCategoryLedger_homotopyCategoryNotConstructed
#assert_no_axioms FX1Poly.Tier0.ContextOmega.pullbackStabilityViaBeckChevalley
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fibrationPullbackCoversBaseViaCartesianLift
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxFibrationCategoryStructurallyRealized

-- context-16 (democratic contexts + local cartesian closure): the FX context base is locally cartesian
-- closed (the Σ ⊣ π* ⊣ Π adjoint string + Id) and democratic (contexts are iterated Σ closed types, the
-- empty context terminal).  RECOGNITION over shipped substrate (like context-10/15, NOT a different base).
-- Shipped is the DemocraticLccLedger + flag pins.  ★ localCartesianClosureViaAdjointString = the genuine
-- anchor (the shipped dependentSumAdjunctionBijection + dependentProductIsRepresentableFormer ARE the LCC
-- adjoint string Σ_A ⊣ π_A* ⊣ Π_A); ★ emptyContextIsTerminalDemocraticBase = a genuinely-new zero-axiom
-- fact (SubstVec target 0 = PUnit, so every substitution into the empty context is unique by PUnit eta —
-- ◇ is terminal, the democratic base); democraticLccStructurallyRealized = the headline.  The full
-- democratic equivalence {⟨Γ⟩} ≅ Γ over whole families is the recorded funext-adjacent boundary.
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxDemocraticLccLedger_hasDependentSum
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxDemocraticLccLedger_hasDependentProduct
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxDemocraticLccLedger_hasIdentityTypes
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxDemocraticLccLedger_isLocallyCartesianClosed
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxDemocraticLccLedger_emptyContextIsTerminal
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxDemocraticLccLedger_isDemocratic
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxDemocraticLccLedger_fullDemocraticEquivalenceNotMechanized
#assert_no_axioms FX1Poly.Tier0.ContextOmega.localCartesianClosureViaAdjointString
#assert_no_axioms FX1Poly.Tier0.ContextOmega.emptyContextIsTerminalDemocraticBase
#assert_no_axioms FX1Poly.Tier0.ContextOmega.democraticLccStructurallyRealized

-- context-17 (Beck-Chevalley coherence: dependent-adjoint naturality at full strength).  context-10
-- proved BC for the display map π only; context-17 extends it to BOTH dependent adjoints: the
-- former-substitution facts piFormerCode_subst/sigmaFormerCode_subst (structural rfl), the genuine
-- ★ piFormerBeckChevalleyNaturality / sigmaFormerBeckChevalleyNaturality (Π/Σ commute with subst via
-- the SAME Cartesian lift σ⁺ = cartesianLift), and ★ dependentAdjointBeckChevalleyAtFullStrength = the
-- headline (display π + left adjoint Σ + right adjoint Π all commute with subst via one σ⁺).  The full
-- fibred Beck-Chevalley iso over whole families is the recorded funext boundary.
#assert_no_axioms FX1Poly.Tier0.ContextOmega.piFormerCode_subst
#assert_no_axioms FX1Poly.Tier0.ContextOmega.sigmaFormerCode_subst
#assert_no_axioms FX1Poly.Tier0.ContextOmega.piFormerBeckChevalleyNaturality
#assert_no_axioms FX1Poly.Tier0.ContextOmega.sigmaFormerBeckChevalleyNaturality
#assert_no_axioms FX1Poly.Tier0.ContextOmega.dependentAdjointBeckChevalleyAtFullStrength

-- context-18 (global sections / flat ♭, the LOPS18 no-go).  RECOGNITION over the FX base
-- (baseIsFXSyntacticContext): the global-sections modality ♭=Δ∘Γ has its Γ object action realized —
-- ★ globalSectionsObjectActionIsClosedTerms = Γ at the term family IS the closed terms RawTerm 0, via
-- the shipped two-sided iso (SUBSTVEC-6) — and is stateable via the Fitch lock ◐ —
-- ★ flatModalityStateableViaDimensionLock = context-4's dimensionLock.  The LOPS18 boundary (Γ not a
-- fibred functor; the tiny-interval internal univalent universe) is recorded absent.
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxGlobalSectionsModalityLedger_globalSectionsObjectActionRealized
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxGlobalSectionsModalityLedger_flatModalityStateableViaLock
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxGlobalSectionsModalityLedger_baseIsFXSyntacticContext
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxGlobalSectionsModalityLedger_flatComonadNotFullyInternalized
#assert_no_axioms FX1Poly.Tier0.ContextOmega.fxGlobalSectionsModalityLedger_tinyIntervalUniverseNotConstructed
#assert_no_axioms FX1Poly.Tier0.ContextOmega.globalSectionsObjectActionIsClosedTerms
#assert_no_axioms FX1Poly.Tier0.ContextOmega.flatModalityStateableViaDimensionLock
#assert_no_axioms FX1Poly.Tier0.ContextOmega.globalSectionsModalityRecognized

end FX1PolyAudit
