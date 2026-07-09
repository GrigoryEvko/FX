import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutBundle

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutBundle — zero-axiom gate for the signature-generic arity-fold
ENGINE, the discipline-routed convertibility-soundness bundle, and the LIVE hypothesis-free pushout isFalse (the
#2043 milestone, WP-AMALG r8)

Per-declaration zero-axiom gate: the generic fold engine + step helpers, the face/degen arity discipline, the width
/ mapsInto / map-length / factorization / localEmbed laws (each threading the discipline through its `_gen` base
case), the vcomp/whisker/hcomp homomorphisms + the Godement interchange invariance, the bundle assembled from any
discipline, the monad instance, the interpreter length invariant, the pushout discipline + bundle instance, and the
unconditional milestone `crossPairPushoutNonConvUnconditional`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- the generic fold engine + step helpers
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonoProcessSpine
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityRunMonoCell
#assert_no_axioms FX1Poly.Polygraph.Amalgam.HasFaceDegenArity
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityRunMonoCell_gen_face
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityRunMonoCell_gen_degen

-- the fold decomposition + peel/shift laws + the run-cell bridge
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonoProcessSpine_spineDiff
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityRunMonoCell_vcomp
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityRunMonoCell_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityRunMonoCell_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_eq_runMonoCell

-- length-width invariant, mapsInto, map-length (discipline threaded)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityRunMonoCell_width_gen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityRunMonoCell_width
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityRunMonoCell_mapsInto_gen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityRunMonoCell_mapsInto
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityRunMonoCell_map_length

-- the factorization + the vcomp homomorphism + its two congruences
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityRunMonoCell_mapFactor_gen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityRunMonoCell_mapFactor
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityRunMonoCell_vcomp_map
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_vcomp
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_vcompCongrLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_vcompCongrRight

-- the generator local-map values + whole-cell length/mapsInto
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_gen_face
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_gen_degen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_length
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_mapsInto

-- the whisker embedding crux + the two whisker-congruence cases
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityRunMonoCell_localEmbed_gen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityRunMonoCell_localEmbed
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_whiskerLeftCongr
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_whiskerRightCongr

-- the hcomp + Godement interchange invariance + the bundle from any discipline
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_hcomp
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityMonotoneMapOf_interchange
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityFoldConvSound_ofDiscipline

-- the walking-monad instance (re-derives the bundle via the discipline)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadHasFaceDegenArity
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadArityFoldConvSound_ofDiscipline

-- the interpreter length invariant (the new brick)
#assert_no_axioms FX1Poly.Polygraph.Amalgam.interpretWordFrom_length

-- the pushout discipline + bundle instance + THE MILESTONE
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutTwoGenWordArity
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutHasFaceDegenArity
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutArityFoldConvSound
#assert_no_axioms FX1Poly.Polygraph.Amalgam.crossPairPushoutNonConvUnconditional

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasLiveMonadPushoutBundle
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasGeneralPushoutDispatch

end FX1PolyAudit
