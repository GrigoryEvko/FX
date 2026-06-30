import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.ContextOfContextsClassifier

/-! # FX1PolyAudit/.../ContextOfContextsClassifier — zero-axiom gate for context-38

Per-declaration zero-axiom gate for `context-38`'s deliverable
(`FX1Poly/Tier0/Context/ContextOfContextsClassifier.lean`): the CONTEXT-OF-CONTEXTS classifier with
PARADOX-FREE STRATIFIED self-classification.  The Tarski universe of context-codes, the classification
relation, the discrete (scope) witness over the real context substrate, the Cantor/Russell diagonal showing
impredicative same-level self-classification is impossible (the Girard kernel), and the stratified
self-classification one level up (paradox-free because `Type u : Type (u+1)` predicatively).  The IMPREDICATIVE
self-classification (`Type : Type`, Girard-inconsistent) is the honest `false` marker; the morphism /
naturality action and the Core table-native row are the honest cross-axis `×type` siblings (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The Tarski universe of context-codes + the classification relation
#assert_no_axioms FX1Poly.Tier0.ContextFamilyClassifier
#assert_no_axioms FX1Poly.Tier0.ContextFamilyClassifier.Classifies
#assert_no_axioms FX1Poly.Tier0.ContextFamilyClassifier.classifies_decode
#assert_no_axioms FX1Poly.Tier0.ContextFamilyClassifier.universe

-- The discrete witness over the real context substrate
#assert_no_axioms FX1Poly.Tier0.scopeContextClassifier
#assert_no_axioms FX1Poly.Tier0.scopeContextClassifier_classifies_fin

-- The Girard / Cantor / Russell kernel — impredicative same-level self-classification is impossible
#assert_no_axioms FX1Poly.Tier0.boolEqNotSelfAbsurd
#assert_no_axioms FX1Poly.Tier0.contextClassifier_noImpredicativeSelfClassification

-- The stratified self-classification — paradox-free, one level up
#assert_no_axioms FX1Poly.Tier0.stratifiedSelfClassifier
#assert_no_axioms FX1Poly.Tier0.stratifiedSelfClassifier_classifies_universe
#assert_no_axioms FX1Poly.Tier0.discreteClassifier_isParadoxFree

-- Honesty markers + smokes
#assert_no_axioms FX1Poly.Tier0.fxContextOfContexts_hasStratifiedSelfClassification
#assert_no_axioms FX1Poly.Tier0.fxContextOfContexts_hasParadoxFreedom
#assert_no_axioms FX1Poly.Tier0.fxContextOfContexts_hasImpredicativeSelfClassification
#assert_no_axioms FX1Poly.Tier0.fxContextOfContexts_isOverCoreIotaTable
#assert_no_axioms FX1Poly.Tier0.scopeContextClassifier_decode_zero_smoke
#assert_no_axioms FX1Poly.Tier0.stratifiedSelfClassifier_decode_smoke

end FX1PolyAudit
