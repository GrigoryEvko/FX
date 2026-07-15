import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.Realizability

/-! # FX1PolyAudit/AuditAxisContextRealizability — zero-axiom gate for context-24's realizability model

Per-declaration zero-axiom gate for `context-24`'s context-side deliverable
(`FX1Poly/Axis/Context/Realizability.lean`): the realizability model's BASE + the combinatory substrate —
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
#assert_no_axioms FX1Poly.Axis.CombinatoryAlgebra
#assert_no_axioms FX1Poly.Axis.CombinatoryAlgebra.identityCombinator
#assert_no_axioms FX1Poly.Axis.CombinatoryAlgebra.apply_identityCombinator
#assert_no_axioms FX1Poly.Axis.CombinatoryAlgebra.composeCombinator
#assert_no_axioms FX1Poly.Axis.CombinatoryAlgebra.apply_composeCombinator

-- Assemblies + the category Asm(A)
#assert_no_axioms FX1Poly.Axis.Assembly
#assert_no_axioms FX1Poly.Axis.AssemblyMorphism
#assert_no_axioms FX1Poly.Axis.AssemblyMorphism.identityMorphism
#assert_no_axioms FX1Poly.Axis.AssemblyMorphism.composeMorphism
#assert_no_axioms FX1Poly.Axis.assemblyCategory

-- Modest sets + a concrete object
#assert_no_axioms FX1Poly.Axis.Assembly.isModest
#assert_no_axioms FX1Poly.Axis.terminalAssembly
#assert_no_axioms FX1Poly.Axis.terminalAssembly_isModest
#assert_no_axioms FX1Poly.Axis.indiscreteBoolAssembly
#assert_no_axioms FX1Poly.Axis.indiscreteBoolAssembly_not_isModest

-- Non-vacuity witness for the substrate
#assert_no_axioms FX1Poly.Axis.trivialCombinatoryAlgebra

-- The model datum + honesty markers + smoke
#assert_no_axioms FX1Poly.Axis.RealizabilityModelData
#assert_no_axioms FX1Poly.Axis.fxRealizabilityModel
#assert_no_axioms FX1Poly.Axis.fxRealizabilityModel_hasRealizabilityTypeStructure
#assert_no_axioms FX1Poly.Axis.fxRealizabilityModel_hasModestSetUniverse
#assert_no_axioms FX1Poly.Axis.fxRealizabilityModel_hasNumberRealizability
#assert_no_axioms FX1Poly.Axis.assemblyCategory_identityLeft_smoke

end FX1PolyAudit
