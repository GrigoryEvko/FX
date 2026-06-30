import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.ContextSscCwFPresentation

/-! # FX1PolyAudit/.../ContextSscCwFPresentation — zero-axiom gate for context-28

Per-declaration zero-axiom gate for `context-28`'s deliverable
(`FX1Poly/Tier0/Context/ContextSscCwFPresentation.lean`): the single-substitution-calculus (`term-26`)
algebra PRESENTS the CwF `fxBaseSubstCategory`, at the STRICT term-algebra level.  The named carrier
category, the iterated generation/spanning theorem (the genuinely-new content — the SSC comprehension
operations generate every morphism down to the initial context), the packaged strict CwF-presentation
datum with its witness (every CwF / presentation law wired to a shipped proof), the honesty markers,
the backed flip, and the smokes.  The FULL up-to-iso biequivalence to the other model notions
(`×type+term`, needing `Quot.sound` + `funext`) is the honest deferral (`= false`,
`context-6`/`fib-8`); the Core table-native row is the honest cross-axis sibling (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The named carrier category
#assert_no_axioms FX1Poly.Tier0.sscSubstitutionCategory
#assert_no_axioms FX1Poly.Tier0.sscSubstitutionCategory_object_eq_nat
#assert_no_axioms FX1Poly.Tier0.sscSubstitutionCategory_morphism_eq_substVec

-- The iterated generation / spanning theorem (the new content)
#assert_no_axioms FX1Poly.Tier0.SubstVec.IsGeneratedBySsc
#assert_no_axioms FX1Poly.Tier0.SubstVec.cons_head_tail
#assert_no_axioms FX1Poly.Tier0.SubstVec.isGeneratedBySsc_complete

-- The packaged strict CwF-presentation datum + its witness
#assert_no_axioms FX1Poly.Tier0.SscCwFPresentation
#assert_no_axioms FX1Poly.Tier0.sscPresentsCwF

-- Honesty markers + backed flip
#assert_no_axioms FX1Poly.Tier0.fxContextSscCwF_hasSscCwFPresentation
#assert_no_axioms FX1Poly.Tier0.fxContextSscCwF_hasStrictSubstitutionCategory
#assert_no_axioms FX1Poly.Tier0.fxContextSscCwF_hasFullBiequivalence
#assert_no_axioms FX1Poly.Tier0.fxContextSscCwF_isOverCoreIotaTable
#assert_no_axioms FX1Poly.Tier0.fxContextSscCwF_isBacked

-- Smokes
#assert_no_axioms FX1Poly.Tier0.sscPresentsCwF_emptyIsGenerated_smoke
#assert_no_axioms FX1Poly.Tier0.sscPresentsCwF_singletonIsGenerated_smoke
#assert_no_axioms FX1Poly.Tier0.sscSubstitutionCategory_eq_base

end FX1PolyAudit
