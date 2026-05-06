import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2
import LeanFX2.FX1.LeanKernel.Name
import LeanFX2.FX1.LeanKernel.Level
import LeanFX2.FX1.LeanKernel.Expr
import LeanFX2.FX1.LeanKernel.Substitution
import LeanFX2.FX1.LeanKernel.Reduction
import LeanFX2.FX1.LeanKernel.Inductive
import LeanFX2.FX1.LeanKernel.HasType
import LeanFX2.FX1.LeanKernel.Check
import LeanFX2.FX1.LeanKernel.Soundness
import LeanFX2.FX1.LeanKernel.Audit
import LeanFX2.FX1
import LeanFX2.FX1Bridge

namespace LeanFX2.Tools


/-! ## Gates: extern-dep gates (extracted from AuditAll lines 36-71). -/

-- FX1 executable extern-dependency gates.  These are narrower than the axiom
-- gates: they fail if a checker-critical executable primitive delegates to
-- Lean host runtime code such as `String.decEq` or host `Nat.beq`.
#assert_no_extern_dependencies LeanFX2.FX1.NaturalNumber.beq
#assert_no_extern_dependencies LeanFX2.FX1.NaturalNumber.eqResult
#assert_no_extern_dependencies LeanFX2.FX1.Name.beq
#assert_no_extern_dependencies LeanFX2.FX1.Name.eqResult
#assert_no_extern_dependencies LeanFX2.FX1.Level.beq
#assert_no_extern_dependencies LeanFX2.FX1.Expr.beq
#assert_no_extern_dependencies LeanFX2.FX1.Declaration.hasName
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findByName?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findByNameResultInDeclarations?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findByNameResult?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findTypeByNameFromResult?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findTypeByName?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findTransparentDefinitionResultInDeclarations?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findTransparentDefinitionResult?
#assert_no_extern_dependencies LeanFX2.FX1.Environment.findTransparentValue?
#assert_no_extern_dependencies LeanFX2.FX1.Context.lookupTypeFromResult?
#assert_no_extern_dependencies LeanFX2.FX1.Context.lookupTypeInEntries?
#assert_no_extern_dependencies LeanFX2.FX1.Context.lookupType?
#assert_no_extern_dependencies LeanFX2.FX1.Expr.headStep?
#assert_no_extern_dependencies LeanFX2.FX1.Expr.whnfResultWithFuel
#assert_no_extern_dependencies LeanFX2.FX1.Expr.whnfWithFuel
#assert_no_extern_dependencies LeanFX2.FX1.Expr.weakHeadFuel
#assert_no_extern_dependencies LeanFX2.FX1.Expr.whnf
#assert_no_extern_dependencies LeanFX2.FX1.Expr.weakHeadFuelAdd
#assert_no_extern_dependencies LeanFX2.FX1.Expr.defEqFuel
#assert_no_extern_dependencies LeanFX2.FX1.Expr.isDefEqWithFuel
#assert_no_extern_dependencies LeanFX2.FX1.Expr.isDefEq
#assert_no_extern_dependencies LeanFX2.FX1.Level.checkerBeq
#assert_no_extern_dependencies LeanFX2.FX1.Expr.checkerBeq
#assert_no_extern_dependencies LeanFX2.FX1.Expr.checkBoolFromResult?
#assert_no_extern_dependencies LeanFX2.FX1.Expr.checkBoolFromCoreType?
#assert_no_extern_dependencies LeanFX2.FX1.Expr.inferCore?
#assert_no_extern_dependencies LeanFX2.FX1.Expr.checkCore?

end LeanFX2.Tools
