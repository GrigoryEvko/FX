import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.ContextDefinitionalUnivalence

/-! # FX1PolyAudit/.../ContextDefinitionalUnivalence — zero-axiom gate for context-31

Per-declaration zero-axiom gate for `context-31`'s deliverable
(`FX1Poly/Tier0/Context/ContextDefinitionalUnivalence.lean`): DEFINITIONAL univalence at the context category
— the `Id_U ↝ Equiv` reduction, the context-side analog of the TYPE-axis `type-7`.  The context-universe code
algebra, the smart-constructor normalizer realizing the reduction, the `rfl` definitional univalence
(`Id_U(A,B)` and `Equiv(A,B)` share a normal form), canonicity (the normalizer eliminates the universe-Id
redex), the reduction relation + the size-drop strong-normalization (structural fuel, no `WellFounded.fix`),
decidable conversion, and the bridge feeding the reduction into `context-30`'s `idToIso`.  The Core
table-native `type-7` row is the honest cross-axis `×type` sibling (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The code algebra + its operations
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode.headIsUniverseObj
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode.reassembleId
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode.normalize
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode.hasUnivalenceRedex
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode.size

-- Definitional univalence (the rfl core) + canonicity
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode.idOverUniverseObject_normalize_eq
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode.reassembleId_hasNoUnivalenceRedex
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode.normalize_hasNoUnivalenceRedex

-- The reduction relation + strong normalization (size-drop + structural fuel)
#assert_no_axioms FX1Poly.Tier0.ContextUnivStep
#assert_no_axioms FX1Poly.Tier0.ContextUnivStep.size_lt
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode.accessibleUnderStep_ofSizeBelow
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode.isStronglyNormalizing

-- Decidable conversion + the definitional-univalence payoff
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode.Conv
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode.Conv.decidable
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode.Conv.refl
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode.Conv.symm
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode.Conv.trans
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode.contextDefinitionalUnivalence
#assert_no_axioms FX1Poly.Tier0.ContextUnivCode.univalenceRule_reduces

-- Bridge to context-30 + honesty markers + smoke
#assert_no_axioms FX1Poly.Tier0.definitionalUnivalence_idToIso
#assert_no_axioms FX1Poly.Tier0.fxContextDefinitionalUnivalence_idReducesToEquiv
#assert_no_axioms FX1Poly.Tier0.fxContextDefinitionalUnivalence_hasDecidableConversion
#assert_no_axioms FX1Poly.Tier0.fxContextDefinitionalUnivalence_isOverCoreIotaTable
#assert_no_axioms FX1Poly.Tier0.contextDefinitionalUnivalence_smoke

end FX1PolyAudit
