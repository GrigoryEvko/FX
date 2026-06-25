import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Equality.Eta.EtaRootClassifier

/-! # FX1PolyAudit.Core.Equality.Eta.EtaRootClassifier

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Equality.Eta.EtaRootClassifier`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

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

end FX1PolyAudit
