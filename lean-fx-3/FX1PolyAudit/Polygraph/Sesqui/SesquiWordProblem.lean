import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Sesqui.SesquiWordProblem

/-! # FX1PolyAudit/Polygraph/Sesqui/SesquiWordProblem — zero-axiom gate

Per-declaration zero-axiom gate for the free-sesquicategory ordered-whisker word
problem: the hand-rolled 1-cell / frame / frame-list carriers and their
constructors, the own `append` / `beq` / whisker-action operations and their
structural soundness lemmas, the ordered-frame `normalize`, the `SesquiConv`
congruence (interchange EXCLUDED) with every constructor, whisker-functoriality
soundness, the sound-and-complete decision, and the interchange / premonoidal-
centre wall markers.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Sesqui.Frame
#assert_no_axioms FX1Poly.Polygraph.Sesqui.Frame.beq
#assert_no_axioms FX1Poly.Polygraph.Sesqui.Frame.beq_refl
#assert_no_axioms FX1Poly.Polygraph.Sesqui.Frame.eq_of_beq
#assert_no_axioms FX1Poly.Polygraph.Sesqui.Frame.mk
#assert_no_axioms FX1Poly.Polygraph.Sesqui.Frame.reify
#assert_no_axioms FX1Poly.Polygraph.Sesqui.FrameList
#assert_no_axioms FX1Poly.Polygraph.Sesqui.FrameList.append
#assert_no_axioms FX1Poly.Polygraph.Sesqui.FrameList.append_assoc
#assert_no_axioms FX1Poly.Polygraph.Sesqui.FrameList.append_nil
#assert_no_axioms FX1Poly.Polygraph.Sesqui.FrameList.beq
#assert_no_axioms FX1Poly.Polygraph.Sesqui.FrameList.beq_refl
#assert_no_axioms FX1Poly.Polygraph.Sesqui.FrameList.cons
#assert_no_axioms FX1Poly.Polygraph.Sesqui.FrameList.eq_of_beq
#assert_no_axioms FX1Poly.Polygraph.Sesqui.FrameList.nil
#assert_no_axioms FX1Poly.Polygraph.Sesqui.FrameList.reify
#assert_no_axioms FX1Poly.Polygraph.Sesqui.OneCell
#assert_no_axioms FX1Poly.Polygraph.Sesqui.OneCell.append
#assert_no_axioms FX1Poly.Polygraph.Sesqui.OneCell.append_assoc
#assert_no_axioms FX1Poly.Polygraph.Sesqui.OneCell.append_nil
#assert_no_axioms FX1Poly.Polygraph.Sesqui.OneCell.beq
#assert_no_axioms FX1Poly.Polygraph.Sesqui.OneCell.beq_refl
#assert_no_axioms FX1Poly.Polygraph.Sesqui.OneCell.cons
#assert_no_axioms FX1Poly.Polygraph.Sesqui.OneCell.eq_of_beq
#assert_no_axioms FX1Poly.Polygraph.Sesqui.OneCell.nil
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.refl
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.symm
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.trans
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.vcompAssoc
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.vcompCongr
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.vcompIdLeft
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.vcompIdRight
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.whiskerCommute
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.whiskerLeftComposite
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.whiskerLeftCongr
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.whiskerLeftId
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.whiskerLeftNil
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.whiskerLeftVcomp
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.whiskerRightComposite
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.whiskerRightCongr
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.whiskerRightId
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.whiskerRightNil
#assert_no_axioms FX1Poly.Polygraph.Sesqui.SesquiConv.whiskerRightVcomp
#assert_no_axioms FX1Poly.Polygraph.Sesqui.TwoCell
#assert_no_axioms FX1Poly.Polygraph.Sesqui.TwoCell.gen
#assert_no_axioms FX1Poly.Polygraph.Sesqui.TwoCell.id
#assert_no_axioms FX1Poly.Polygraph.Sesqui.TwoCell.vcomp
#assert_no_axioms FX1Poly.Polygraph.Sesqui.TwoCell.whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.Sesqui.TwoCell.whiskerRight
#assert_no_axioms FX1Poly.Polygraph.Sesqui.decideSesquiEq
#assert_no_axioms FX1Poly.Polygraph.Sesqui.decideSesquiEq_iff_sesquiConv
#assert_no_axioms FX1Poly.Polygraph.Sesqui.decideSesquiEq_of_sesquiConv
#assert_no_axioms FX1Poly.Polygraph.Sesqui.natBeqSelf
#assert_no_axioms FX1Poly.Polygraph.Sesqui.normalize
#assert_no_axioms FX1Poly.Polygraph.Sesqui.normalize_eq_of_sesquiConv
#assert_no_axioms FX1Poly.Polygraph.Sesqui.not_sesquiConv_of_decideSesquiEq_false
#assert_no_axioms FX1Poly.Polygraph.Sesqui.sesquiConv_of_normalize_eq
#assert_no_axioms FX1Poly.Polygraph.Sesqui.sesquiConv_reify_append
#assert_no_axioms FX1Poly.Polygraph.Sesqui.sesquiConv_reify_normalize
#assert_no_axioms FX1Poly.Polygraph.Sesqui.sesquiConv_reify_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.Sesqui.sesquiConv_reify_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.Sesqui.sqwHasInterchangeCompleteness
#assert_no_axioms FX1Poly.Polygraph.Sesqui.sqwHasPremonoidalCentreCharacterization
#assert_no_axioms FX1Poly.Polygraph.Sesqui.sqwHasSesquiWordProblem
#assert_no_axioms FX1Poly.Polygraph.Sesqui.whiskerFrame_commute
#assert_no_axioms FX1Poly.Polygraph.Sesqui.whiskerFrames_commute
#assert_no_axioms FX1Poly.Polygraph.Sesqui.whiskerLeftFrame
#assert_no_axioms FX1Poly.Polygraph.Sesqui.whiskerLeftFrame_append
#assert_no_axioms FX1Poly.Polygraph.Sesqui.whiskerLeftFrames
#assert_no_axioms FX1Poly.Polygraph.Sesqui.whiskerLeftFrames_append
#assert_no_axioms FX1Poly.Polygraph.Sesqui.whiskerLeftFrames_composite
#assert_no_axioms FX1Poly.Polygraph.Sesqui.whiskerLeftFrames_nil
#assert_no_axioms FX1Poly.Polygraph.Sesqui.whiskerRightFrame
#assert_no_axioms FX1Poly.Polygraph.Sesqui.whiskerRightFrame_append
#assert_no_axioms FX1Poly.Polygraph.Sesqui.whiskerRightFrames
#assert_no_axioms FX1Poly.Polygraph.Sesqui.whiskerRightFrames_append
#assert_no_axioms FX1Poly.Polygraph.Sesqui.whiskerRightFrames_composite
#assert_no_axioms FX1Poly.Polygraph.Sesqui.whiskerRightFrames_nil

end FX1PolyAudit
