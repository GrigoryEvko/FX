import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.ContextOmega.Interface
import FX1Poly.Tier0.ContextOmega.Comprehension
import FX1Poly.Tier0.ContextOmega.Uemura
import FX1Poly.Tier0.ContextOmega.Colimits
import FX1Poly.Tier0.ContextOmega.DimensionalFunctor
import FX1Poly.Tier0.ContextOmega.ModalLock
import FX1Poly.Tier0.ContextOmega.Initiality

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

end FX1PolyAudit
