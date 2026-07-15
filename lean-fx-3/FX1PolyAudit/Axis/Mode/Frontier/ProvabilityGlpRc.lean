import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Mode.Frontier.ProvabilityGlpRc

/-! # FX1PolyAudit/AuditAxisModeFrontierProvabilityGlpRc — zero-axiom gate for the mode-23 RC frontier

Per-declaration zero-axiom gate for the mode-23 frontier deliverable
(`FX1Poly/Axis/Mode/Frontier/ProvabilityGlpRc.lean`): the Dashkov–Beklemishev strictly-positive Reflection
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

#assert_no_axioms FX1Poly.Axis.RCFormula
#assert_no_axioms FX1Poly.Axis.RCProves
#assert_no_axioms FX1Poly.Axis.RCProves.topRefl
#assert_no_axioms FX1Poly.Axis.RCProves.andSwap
#assert_no_axioms FX1Poly.Axis.RCProves.andCongr
#assert_no_axioms FX1Poly.Axis.RCProves.andAssocRight
#assert_no_axioms FX1Poly.Axis.RCProves.andAssocLeft
#assert_no_axioms FX1Poly.Axis.RCProves.diamondChain
#assert_no_axioms FX1Poly.Axis.RCProves.diamondCollapse
#assert_no_axioms FX1Poly.Axis.RCProves.diamondWorm_ofJoin
#assert_no_axioms FX1Poly.Axis.rcFormulaBeq
#assert_no_axioms FX1Poly.Axis.rcFormulaBeq_sound
#assert_no_axioms FX1Poly.Axis.rcCheck
#assert_no_axioms FX1Poly.Axis.rcCheck_sound
#assert_no_axioms FX1Poly.Axis.diamondAt
#assert_no_axioms FX1Poly.Axis.RCInterpret
#assert_no_axioms FX1Poly.Axis.GLPFrame
#assert_no_axioms FX1Poly.Axis.RCProves_sound
#assert_no_axioms FX1Poly.Axis.rcCheckConjIntro
#assert_no_axioms FX1Poly.Axis.rcCheckConjElim
#assert_no_axioms FX1Poly.Axis.rcCheckDiamond
#assert_no_axioms FX1Poly.Axis.rcCheckConjIntro_sound
#assert_no_axioms FX1Poly.Axis.rcCheckConjElim_sound
#assert_no_axioms FX1Poly.Axis.rcCheckDiamond_sound
#assert_no_axioms FX1Poly.Axis.rcBoolAndLeft
#assert_no_axioms FX1Poly.Axis.rcBoolAndRight
#assert_no_axioms FX1Poly.Axis.rcBoolOrElim
#assert_no_axioms FX1Poly.Axis.wormToFormula
#assert_no_axioms FX1Poly.Axis.wormDrop
#assert_no_axioms FX1Poly.Axis.wormToFormula_head_topMono
#assert_no_axioms FX1Poly.Axis.wormDrop_length_lt
#assert_no_axioms FX1Poly.Axis.wormPrecedes
#assert_no_axioms FX1Poly.Axis.wormPrecedes_wellFounded
#assert_no_axioms FX1Poly.Axis.wormDrop_precedes
#assert_no_axioms FX1Poly.Axis.wormCons_topMono
#assert_no_axioms FX1Poly.Axis.rcCheck_certifies_levelDrop
#assert_no_axioms FX1Poly.Axis.rcCheck_certifies_diamondConjElim

end FX1PolyAudit
