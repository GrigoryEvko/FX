import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.ContextBiInitiality

/-! # FX1PolyAudit/.../ContextBiInitiality — zero-axiom gate for context-39

Per-declaration zero-axiom gate for `context-39`'s deliverable
(`FX1Poly/Tier0/Context/ContextBiInitiality.lean`): the context category is BI-INITIAL in the (∞,ω)-category
of models, at the STRICT / object level — reusing `context-5`'s initial syntactic context structure.  The
model interface, the unique interpreting morphism (existence + pointwise-uniqueness), the packaged strict
bi-initiality datum with its witness, and the non-vacuity (faithful embedding into the telescope model).  The
WEAK (∞,ω) bi-initiality — substitution action (`×term`), type/term presheaf uniqueness (`×type`), the QIIT
quotient (`Quot.sound`), and up-to-coherent-equivalence higher naturality (`funext`) — is the honest deferral
(`= false`, same boundary as `fib-5c`/`fib-5d`); the Core table-native row is the honest cross-axis sibling
(`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The model interface + the interpreting morphism
#assert_no_axioms FX1Poly.Tier0.ContextModel
#assert_no_axioms FX1Poly.Tier0.SyntacticContextMorphismInto
#assert_no_axioms FX1Poly.Tier0.syntacticContextInitialMorphism
#assert_no_axioms FX1Poly.Tier0.syntacticContextInitialMorphism_unique
#assert_no_axioms FX1Poly.Tier0.syntacticContext_interpretation_unique_pointwise

-- The packaged strict bi-initiality datum + its witness
#assert_no_axioms FX1Poly.Tier0.SyntacticContextBiInitiality
#assert_no_axioms FX1Poly.Tier0.syntacticContextBiInitiality

-- Non-vacuity
#assert_no_axioms FX1Poly.Tier0.syntacticContextInitialMorphism_faithful

-- Honesty markers + smokes
#assert_no_axioms FX1Poly.Tier0.fxContextBiInitiality_hasStrictBiInitiality
#assert_no_axioms FX1Poly.Tier0.fxContextBiInitiality_hasWeakInfinityOmegaBiInitiality
#assert_no_axioms FX1Poly.Tier0.fxContextBiInitiality_isOverCoreIotaTable
#assert_no_axioms FX1Poly.Tier0.syntacticContextBiInitiality_interpret_self_identity_smoke
#assert_no_axioms FX1Poly.Tier0.syntacticContext_unique_pointwise_smoke

end FX1PolyAudit
