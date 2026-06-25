import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.Frontier.ProvabilityGlpRc

/-! # FX1PolyAudit/AuditTier0ModeFrontierProvabilityGlpRc — zero-axiom gate for the mode-23 RC frontier

Per-declaration zero-axiom gate for the mode-23 frontier deliverable
(`FX1Poly/Tier0/Mode/Frontier/ProvabilityGlpRc.lean`): the Dashkov–Beklemishev strictly-positive Reflection
Calculus RC, its core derivability, derived lemmas, a sound bounded-fuel checker, and the headline RC
**soundness** against the diamond duals of the GLP `boxAt` modalities.

  * `RCFormula` / `RCProves` — the strictly-positive formula syntax + the RC derivability sequent relation;
  * the derived RC lemmas (`topRefl`, `andSwap`, `andCongr`, `andAssocRight`/`andAssocLeft`, `diamondChain`,
    `diamondCollapse`);
  * `rcFormulaBeq` + `rcFormulaBeq_sound` — propext-clean structural formula equality + its soundness;
  * `rcCheck` + `rcCheck_sound` — the bounded-fuel SOUND checker (a decidable certificate on a sub-fragment);
  * `diamondAt` / `RCInterpret` / `GLPFrame` / ★★ `RCProves_sound` — the diamond semantics over `boxAt` and the
    RC soundness theorem (every RC derivation is valid on every GLP frame);
  * `Worm` / `wormToFormula` / `wormDrop` + `wormToFormula_head_topMono` / `wormDrop_length_lt` — the worm
    algebraic skeleton feeding the (deferred) ordinal analysis.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`.  Building this file fails on any leak. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.RCFormula
#assert_no_axioms FX1Poly.Tier0.RCProves
#assert_no_axioms FX1Poly.Tier0.RCProves.topRefl
#assert_no_axioms FX1Poly.Tier0.RCProves.andSwap
#assert_no_axioms FX1Poly.Tier0.RCProves.andCongr
#assert_no_axioms FX1Poly.Tier0.RCProves.andAssocRight
#assert_no_axioms FX1Poly.Tier0.RCProves.andAssocLeft
#assert_no_axioms FX1Poly.Tier0.RCProves.diamondChain
#assert_no_axioms FX1Poly.Tier0.RCProves.diamondCollapse
#assert_no_axioms FX1Poly.Tier0.RCProves.diamondWorm_ofJoin
#assert_no_axioms FX1Poly.Tier0.rcFormulaBeq
#assert_no_axioms FX1Poly.Tier0.rcFormulaBeq_sound
#assert_no_axioms FX1Poly.Tier0.rcCheck
#assert_no_axioms FX1Poly.Tier0.rcCheck_sound
#assert_no_axioms FX1Poly.Tier0.diamondAt
#assert_no_axioms FX1Poly.Tier0.RCInterpret
#assert_no_axioms FX1Poly.Tier0.GLPFrame
#assert_no_axioms FX1Poly.Tier0.RCProves_sound
#assert_no_axioms FX1Poly.Tier0.rcCheckConjIntro
#assert_no_axioms FX1Poly.Tier0.rcCheckConjElim
#assert_no_axioms FX1Poly.Tier0.rcCheckDiamond
#assert_no_axioms FX1Poly.Tier0.rcCheckConjIntro_sound
#assert_no_axioms FX1Poly.Tier0.rcCheckConjElim_sound
#assert_no_axioms FX1Poly.Tier0.rcCheckDiamond_sound
#assert_no_axioms FX1Poly.Tier0.rcBoolAndLeft
#assert_no_axioms FX1Poly.Tier0.rcBoolAndRight
#assert_no_axioms FX1Poly.Tier0.rcBoolOrElim
#assert_no_axioms FX1Poly.Tier0.wormToFormula
#assert_no_axioms FX1Poly.Tier0.wormDrop
#assert_no_axioms FX1Poly.Tier0.wormToFormula_head_topMono
#assert_no_axioms FX1Poly.Tier0.wormDrop_length_lt
#assert_no_axioms FX1Poly.Tier0.wormPrecedes
#assert_no_axioms FX1Poly.Tier0.wormPrecedes_wellFounded
#assert_no_axioms FX1Poly.Tier0.wormDrop_precedes
#assert_no_axioms FX1Poly.Tier0.wormCons_topMono
#assert_no_axioms FX1Poly.Tier0.rcCheck_certifies_levelDrop
#assert_no_axioms FX1Poly.Tier0.rcCheck_certifies_diamondConjElim

end FX1PolyAudit
