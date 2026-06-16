import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.Forcing

/-! # FX1PolyAudit/AuditTier0ContextForcing — zero-axiom gate for context-26's forcing model

Per-declaration zero-axiom gate for `context-26`'s context-side deliverable
(`FX1Poly/Tier0/Context/Forcing.lean`): forcing as a CwF (Jaber–Lewertowski–Pédrot–Tabareau–Sozeau) — the
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
#assert_no_axioms FX1Poly.Tier0.ForcingPoset
#assert_no_axioms FX1Poly.Tier0.conditionCategory
#assert_no_axioms FX1Poly.Tier0.forcingContextCategory

-- The Kripke forcing relation
#assert_no_axioms FX1Poly.Tier0.ForcingPredicate

-- Concrete Cohen forcing of a single generic bit
#assert_no_axioms FX1Poly.Tier0.cohenBitPoset
#assert_no_axioms FX1Poly.Tier0.forcesTrue
#assert_no_axioms FX1Poly.Tier0.forcesFalse
#assert_no_axioms FX1Poly.Tier0.cohenBit_independence
#assert_no_axioms FX1Poly.Tier0.cohenBit_someTrue_someFalse_incompatible

-- The model datum + honesty markers
#assert_no_axioms FX1Poly.Tier0.ForcingModelData
#assert_no_axioms FX1Poly.Tier0.fxForcingModel
#assert_no_axioms FX1Poly.Tier0.fxForcingModel_hasForcingTranslation
#assert_no_axioms FX1Poly.Tier0.fxForcingModel_hasIndependenceTheorem
#assert_no_axioms FX1Poly.Tier0.fxForcingModel_hasForcingUniverse

-- Smoke: the subsumption of context-25's presheaf category
#assert_no_axioms FX1Poly.Tier0.fxForcing_subsumes_presheaf_smoke

end FX1PolyAudit
