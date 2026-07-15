import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.ContextDirectedUnivalence

/-! # FX1PolyAudit/.../ContextDirectedUnivalence — zero-axiom gate for context-34 (reduction)

Per-declaration zero-axiom gate for `context-34`'s deliverable
(`FX1Poly/Axis/Context/ContextDirectedUnivalence.lean`): DIRECTED univalence at the context category — the
`Hom_U ↝ Fun` reduction, the DIRECTED analog of the sibling `context-31` (`Id_U ↝ Equiv`).  The
context-universe code algebra, the smart-constructor normalizer realizing the reduction, the `rfl` definitional
directed univalence (`Hom_U(A,B)` and `Fun(A,B)` share a normal form), canonicity (the normalizer eliminates
the universe-Hom redex), the reduction relation + the size-drop strong normalization (structural fuel, no
`WellFounded.fix`), decidable conversion, and the bridge feeding the reduction into the apparatus's `homToFun`.
The Core table-native directed-univalence row is the honest cross-axis `×type` sibling (`= false`); the full
Segal / Rezk-complete directed univalence axiom (which needs funext) is the honest `×type` deferral
(`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The code algebra + its operations
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode.headIsUniverseObj
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode.reassembleHom
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode.normalize
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode.hasDirectedUnivalenceRedex
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode.size

-- Definitional directed univalence (the rfl core) + canonicity
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode.homOverUniverseObject_normalize_eq
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode.reassembleHom_hasNoDirectedUnivalenceRedex
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode.normalize_hasNoDirectedUnivalenceRedex

-- The reduction relation + strong normalization (size-drop + structural fuel)
#assert_no_axioms FX1Poly.Axis.ContextDirectedUnivStep
#assert_no_axioms FX1Poly.Axis.ContextDirectedUnivStep.size_lt
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode.accessibleUnderStep_ofSizeBelow
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode.isStronglyNormalizing

-- Decidable conversion + the directed-univalence payoff
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode.Conv
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode.Conv.decidable
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode.Conv.refl
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode.Conv.symm
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode.Conv.trans
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode.contextDirectedUnivalence
#assert_no_axioms FX1Poly.Axis.ContextDirectedCode.directedUnivalenceRule_reduces

-- Bridge to the apparatus + honesty markers + smoke
#assert_no_axioms FX1Poly.Axis.directedUnivalence_homToFun
#assert_no_axioms FX1Poly.Axis.fxContextDirectedUnivalence_homReducesToFun
#assert_no_axioms FX1Poly.Axis.fxContextDirectedUnivalence_hasDecidableConversion
#assert_no_axioms FX1Poly.Axis.fxContextDirectedUnivalence_isOverCoreIotaTable
#assert_no_axioms FX1Poly.Axis.fxContextDirectedUnivalence_hasFullSegalDirectedUA
#assert_no_axioms FX1Poly.Axis.contextDirectedUnivalence_smoke

end FX1PolyAudit
