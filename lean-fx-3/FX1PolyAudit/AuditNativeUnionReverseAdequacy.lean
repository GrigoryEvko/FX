import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.HasTypeNativeUnionMatchInversion
import FX1Poly.Typed.HasTypeNativeUnionPathProjInversion
import FX1Poly.Typed.HasTypeNativeUnionRecursiveInversion
import FX1Poly.Typed.HasTypeNativeUnionReverseAdequacy
import FX1Poly.Typed.HasTypeNativeUnionTwoPathVerdict

/-! # FX1PolyAudit/AuditNativeUnionReverseAdequacy — NATIVE-37 part d audit shard (the union/family
    REVERSE adequacy: the honesty half — the union restricted to each eliminator head inverts back to the
    bespoke engine).

Per-declaration zero-axiom gate for NATIVE-37 part d: the eight remaining per-head inversions over
`HasTypeNativeUnion` (boolElim / optionMatch / eitherMatch / idJ / fst / snd / natRec / listElim — the
four representatives pathLam / lam / natElim / natSucc were gated in `AuditNativeUnionInversion`), the
per-family reverse adequacies (the surplus halves + the relativized reconstruction halves — listElim
relativized like the rest since the NATIVE-42 re-shape), the two-path canonical-path verdict for natSucc (the bespoke
natSucc predecessor inversion, the embedding⟹row subsumption, the computed-number witness, the embedding
refutation, and the strict-generality packaging), and the reverse-adequacy coverage record / witness.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## (1) The eight remaining per-head inversions -/

#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.invertAtBoolElimHead
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.invertAtOptionMatchHead
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.invertAtEitherMatchHead
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.invertAtIdJHead
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.invertAtFstHead
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.invertAtSndHead
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.invertAtNatRecHead
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.invertAtListElimHead

/-! ## (2) ★ Reverse adequacy — the surplus halves -/

#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.boolElimSurplus
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.optionMatchSurplus
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.eitherMatchSurplus
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.idJSurplus
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.fstSurplus
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.sndSurplus
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.natElimSurplus
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.natRecSurplus

/-! ## (2) ★ Reverse adequacy — the relativized reconstruction halves -/

#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.toBoolElimRelativized
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.toOptionMatchRelativized
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.toEitherMatchRelativized
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.toIdJRelativized
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.toFstRelativized
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.toSndRelativized
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.toNatElimRelativized
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.toNatRecRelativized

/-! ## (2) ★ Reverse adequacy — listElim (relativized since the NATIVE-42 re-shape) -/

#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.listElimSurplus
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.toListElimRelativized

/-! ## (3) ★ The two-path canonical-path verdict (natSucc) -/

#assert_no_axioms FX1Poly.Typed.HasTypeDescNatIntro.invertNatSucc
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.natSuccEmbeddingSubsumedByRow
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.computedNumberTypedAtNat
#assert_no_axioms FX1Poly.Typed.HasTypeDescNatIntro.natSuccOfComputedNumberHasNoEmbedding
#assert_no_axioms FX1Poly.Typed.HasTypeNativeUnion.natSuccRowStrictlyMoreGeneralThanEmbedding

/-! ## (5) Coverage record + witness -/

#assert_no_axioms FX1Poly.Typed.NativeUnionReverseAdequacyCoverage
#assert_no_axioms FX1Poly.Typed.nativeUnionReverseAdequacyCoverageWitness

end FX1PolyAudit
