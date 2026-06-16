import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.Realizability

/-! # FX1PolyAudit/AuditTier0ContextRealizability — zero-axiom gate for context-24's realizability model

Per-declaration zero-axiom gate for `context-24`'s context-side deliverable
(`FX1Poly/Tier0/Context/Realizability.lean`): the realizability model's BASE + the combinatory substrate —
the `CombinatoryAlgebra` (the realizers) with the derived `I = S K K` / `B = S (K S) K` combinators and their
laws (generic theorems in any CA), assemblies (`Assembly`) and tracked maps (`AssemblyMorphism`), the category
of assemblies `Asm(A)` (`assemblyCategory`) as a `RawCategory` (laws by `rfl`, no `funext`), the modest-set
refinement (`isModest`) + the terminal assembly, and a non-vacuity witness (`trivialCombinatoryAlgebra`).
The realizability type structure (Id/Π/Σ + soundness), the modest-set universe / effective topos, and number
realizability over the canonical PCA `K₁` are the honest `×type` / concrete-substrate deferrals (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The combinatory-algebra substrate + derived combinators
#assert_no_axioms FX1Poly.Tier0.CombinatoryAlgebra
#assert_no_axioms FX1Poly.Tier0.CombinatoryAlgebra.identityCombinator
#assert_no_axioms FX1Poly.Tier0.CombinatoryAlgebra.apply_identityCombinator
#assert_no_axioms FX1Poly.Tier0.CombinatoryAlgebra.composeCombinator
#assert_no_axioms FX1Poly.Tier0.CombinatoryAlgebra.apply_composeCombinator

-- Assemblies + the category Asm(A)
#assert_no_axioms FX1Poly.Tier0.Assembly
#assert_no_axioms FX1Poly.Tier0.AssemblyMorphism
#assert_no_axioms FX1Poly.Tier0.AssemblyMorphism.identityMorphism
#assert_no_axioms FX1Poly.Tier0.AssemblyMorphism.composeMorphism
#assert_no_axioms FX1Poly.Tier0.assemblyCategory

-- Modest sets + a concrete object
#assert_no_axioms FX1Poly.Tier0.Assembly.isModest
#assert_no_axioms FX1Poly.Tier0.terminalAssembly
#assert_no_axioms FX1Poly.Tier0.terminalAssembly_isModest
#assert_no_axioms FX1Poly.Tier0.indiscreteBoolAssembly
#assert_no_axioms FX1Poly.Tier0.indiscreteBoolAssembly_not_isModest

-- Non-vacuity witness for the substrate
#assert_no_axioms FX1Poly.Tier0.trivialCombinatoryAlgebra

-- The model datum + honesty markers + smoke
#assert_no_axioms FX1Poly.Tier0.RealizabilityModelData
#assert_no_axioms FX1Poly.Tier0.fxRealizabilityModel
#assert_no_axioms FX1Poly.Tier0.fxRealizabilityModel_hasRealizabilityTypeStructure
#assert_no_axioms FX1Poly.Tier0.fxRealizabilityModel_hasModestSetUniverse
#assert_no_axioms FX1Poly.Tier0.fxRealizabilityModel_hasNumberRealizability
#assert_no_axioms FX1Poly.Tier0.assemblyCategory_identityLeft_smoke

end FX1PolyAudit
