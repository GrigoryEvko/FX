import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.Forcing

/-! # FX1PolyAudit/AuditAxisContextForcing — zero-axiom gate for context-26's forcing model

Per-declaration zero-axiom gate for `context-26`'s context-side deliverable
(`FX1Poly/Axis/Context/Forcing.lean`): forcing as a CwF (Jaber–Lewertowski–Pédrot–Tabareau–Sozeau) — the
conditions preorder (`ForcingPoset`), its thin `RawCategory` (`conditionCategory`, laws by `rfl` via `Prop`-hom
proof irrelevance), the forcing model's category of CONTEXTS as presheaves over the conditions
(`forcingContextCategory := presheafCategory (conditionCategory P)`, the `context-25` subsumption pinned by
`fxForcing_subsumes_presheaf_smoke`), the Kripke monotone forcing relation (`ForcingPredicate`), and the
CONCRETE Cohen single-bit independence (`cohenBitPoset` + `forcesTrue`/`forcesFalse` + `cohenBit_independence`
+ `cohenBit_someTrue_someFalse_incompatible` — the bit forced each way by incompatible deciding conditions,
undecided by the empty condition).  The forcing translation, the syntactic independence theorem, and the
forcing universe are the honest `×type` deferrals (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The conditions preorder + its thin category
#assert_no_axioms FX1Poly.Axis.ForcingPoset
#assert_no_axioms FX1Poly.Axis.conditionCategory
#assert_no_axioms FX1Poly.Axis.forcingContextCategory

-- The Kripke forcing relation
#assert_no_axioms FX1Poly.Axis.ForcingPredicate

-- Concrete Cohen forcing of a single generic bit
#assert_no_axioms FX1Poly.Axis.cohenBitPoset
#assert_no_axioms FX1Poly.Axis.forcesTrue
#assert_no_axioms FX1Poly.Axis.forcesFalse
#assert_no_axioms FX1Poly.Axis.cohenBit_independence
#assert_no_axioms FX1Poly.Axis.cohenBit_someTrue_someFalse_incompatible

-- The model datum + honesty markers
#assert_no_axioms FX1Poly.Axis.ForcingModelData
#assert_no_axioms FX1Poly.Axis.fxForcingModel
#assert_no_axioms FX1Poly.Axis.fxForcingModel_hasForcingTranslation
#assert_no_axioms FX1Poly.Axis.fxForcingModel_hasIndependenceTheorem
#assert_no_axioms FX1Poly.Axis.fxForcingModel_hasForcingUniverse

-- Smoke: the subsumption of context-25's presheaf category
#assert_no_axioms FX1Poly.Axis.fxForcing_subsumes_presheaf_smoke

end FX1PolyAudit
