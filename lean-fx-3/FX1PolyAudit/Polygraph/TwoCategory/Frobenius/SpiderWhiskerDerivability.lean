import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderWhiskerDerivability

/-! # FX1PolyAudit.Polygraph.TwoCategory.Frobenius.SpiderWhiskerDerivability — zero-axiom gate (WP-FROB r8, FROB-8)

Per-declaration zero-axiom gate for whisker derivability: the row-generated congruence `SpiderConvRows` and its
soundness embedding / partition soundness / derived suffix congruence (P1), the crossing-free fragment predicate,
the canonical-form matches, the row-generated straightening witnesses and the pure-crossing-row witnesses (P2), the
crossing-completeness hook and the two whisker-derivability conditionals (P3), the non-vacuity witnesses (P5), and
the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- FROB-8 P1: the row-generated congruence + soundness embedding + partition soundness + the derived contextual leg
#assert_no_axioms FX1Poly.Polygraph.SpiderConvRows
#assert_no_axioms FX1Poly.Polygraph.spiderConvRows_toSpiderConv
#assert_no_axioms FX1Poly.Polygraph.spiderConvRows_partitionSound
#assert_no_axioms FX1Poly.Polygraph.spiderConvTable_toSpiderConvRows
#assert_no_axioms FX1Poly.Polygraph.spiderConvRows_suffixCongruence

-- FROB-8 P2: the crossing-free fragment predicate + the canonical-form matches
#assert_no_axioms FX1Poly.Polygraph.isCrossingFreeAtom
#assert_no_axioms FX1Poly.Polygraph.isCrossingFreeWord
#assert_no_axioms FX1Poly.Polygraph.canonicalSpiderOf_3_1_eq_frobAssocLhs
#assert_no_axioms FX1Poly.Polygraph.canonicalSpiderOf_2_2_eq_frobLeftRhs

-- FROB-8 P2: the row-generated straightening witnesses + the pure-crossing-row transport witnesses
#assert_no_axioms FX1Poly.Polygraph.spiderConvRows_straighten_assocRhs
#assert_no_axioms FX1Poly.Polygraph.spiderConvRows_straighten_frobLeftLhs
#assert_no_axioms FX1Poly.Polygraph.straighteningWitnesses_isCrossingFree
#assert_no_axioms FX1Poly.Polygraph.spiderConvRows_crossingInvolution
#assert_no_axioms FX1Poly.Polygraph.spiderConvRows_yangBaxter

-- FROB-9 (r9): the third crossing generator (distant commute) completing the Coxeter/Matsumoto triad
#assert_no_axioms FX1Poly.Polygraph.spiderConvRows_distantCommute
#assert_no_axioms FX1Poly.Polygraph.spiderConvRows_distantCommute_distinct

-- FROB-9 (r9): the transport-vs-rerun wall analysis — the all-crossing predicate + the detour-unsoundness witness
#assert_no_axioms FX1Poly.Polygraph.isAllCrossingAtom
#assert_no_axioms FX1Poly.Polygraph.isAllCrossingWord
#assert_no_axioms FX1Poly.Polygraph.brauerConvFree7_crossing_relates_noncrossing

-- FROB-8 P3: the crossing-completeness hook + the two whisker-derivability conditionals
#assert_no_axioms FX1Poly.Polygraph.CrossingCompletenessHook
#assert_no_axioms FX1Poly.Polygraph.spiderConvRows_complete_ofHook
#assert_no_axioms FX1Poly.Polygraph.spiderConvRows_whisker_ofHook

-- FROB-8 P5: non-vacuity — distinct-word row identifications, the bone generator, properness
#assert_no_axioms FX1Poly.Polygraph.spiderConvRows_frobLeft_frobRight_lhs
#assert_no_axioms FX1Poly.Polygraph.spiderConvRows_frobLeft_frobRight_distinct
#assert_no_axioms FX1Poly.Polygraph.spiderConvRows_frobLeft_frobRight_partitionAgrees
#assert_no_axioms FX1Poly.Polygraph.spiderConvRows_bone_identifies_distinct
#assert_no_axioms FX1Poly.Polygraph.spiderConvRows_H_not_identity

-- FROB-8: the honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasWhiskerRowGeneration
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasCrossingFreeStraightening
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasWhiskerDerivabilityConditional

-- FROB-9 (r9): the crossing-straightening residual isolated to the row-level suffix congruence
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasCrossingStraighteningSuffixResidual

end FX1PolyAudit
