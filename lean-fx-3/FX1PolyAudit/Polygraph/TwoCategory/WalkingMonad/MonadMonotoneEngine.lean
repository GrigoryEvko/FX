import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadMonotoneEngine

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadMonotoneEngine — zero-axiom gate (the monotone-fold engine + laws at context)

Per-declaration zero-axiom gate for the walking-monad monotone-fold engine: the spine-list fold engine, the
fold-decomposition, the vcomp / whisker / right-context laws, the length-width invariant, the bridge, the three
monad laws sound for the fold at an ARBITRARY left-whisker context, and the non-vacuity witnesses.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.monadMonoProcessSpine
#assert_no_axioms FX1Poly.Polygraph.monadRunMonoCell
#assert_no_axioms FX1Poly.Polygraph.monadMonoProcessSpine_spineDiff
#assert_no_axioms FX1Poly.Polygraph.monadRunMonoCell_vcomp
#assert_no_axioms FX1Poly.Polygraph.monadRunMonoCell_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.monadRunMonoCell_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.monadRunMonoCell_rightContext_irrelevant
#assert_no_axioms FX1Poly.Polygraph.monadEtaWidthShift
#assert_no_axioms FX1Poly.Polygraph.monadMuWidthShift
#assert_no_axioms FX1Poly.Polygraph.monadRunMonoCell_width_gen
#assert_no_axioms FX1Poly.Polygraph.monadRunMonoCell_width
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_eq_runMonoCell
#assert_no_axioms FX1Poly.Polygraph.monadWhiskerT_length
#assert_no_axioms FX1Poly.Polygraph.monadWhiskerTTT_length
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_whiskeredLeftUnit_atContext
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_whiskeredIdT_atContext
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_whiskeredLeftUnit_sound
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_whiskeredRightUnit_atContext
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_whiskeredRightUnit_sound
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_whiskeredAssoc_sound
#assert_no_axioms FX1Poly.Polygraph.monadMergeThenUnitRight
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_idTThenT
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_mergeThenUnitRight
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_separates_idTThenT_mergeThenUnitRight
#assert_no_axioms FX1Poly.Polygraph.monadMonotoneMapOf_identifies_leftUnit_idT
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasMonotoneMapEngineAndLawsAtContext
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasFullMapEqOfConvAndCompleteness

end FX1PolyAudit
