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

end FX1PolyAudit
