import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutMonotoneReflection

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutMonotoneReflection — zero-axiom gate for the signature-generic
arity fold and the pushout non-convertibility reflection (WP-AMALG r7)

Per-declaration zero-axiom gate: the generic arity fold and its faithfulness cross-check, the structural-fragment
invariance, the convertibility-soundness bundle and the generic `eqOfStep`/`eqOfConv`/`eqOfConvFull` reductions, the
pushout congruence (empty-relation `ofRelation`), the concrete separation the fold computes (each `rfl` / `decide`),
and the conditional live isFalse.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- the signature-generic arity fold + faithfulness
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityFoldStepAtom
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_eq_monadMonotoneMapOf

-- structural-fragment invariance (generic, unconditional)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_congr_of_spine_eq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_eq_of_interchangeFreeStep

-- the soundness bundle + the generic convertibility-invariance reductions
#assert_no_axioms FX1Poly.Polygraph.Amalgam.ArityFoldConvSound
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_eqOfStep
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_eqOfConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_eqOfConvFull

-- the pushout congruence
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityFoldEqRel_of_emptyPushoutRow
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityFoldPushoutCongruence

-- the concrete separation + conditional live isFalse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairAlpha_arityMap
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairBeta_arityMap
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPair_arityMapsDiffer
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairPushoutNonConv

-- the bundle inhabited for the monad + the unconditional monad-face cross-check
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadArityFoldConvSound
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadFaces_arityMapsDiffer
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadFaces_notFullConv

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasArityFoldReflection
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasPushoutArityFoldConvSoundness

end FX1PolyAudit
