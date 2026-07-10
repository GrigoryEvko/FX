import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringLabelWordTracking

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringLabelWordTracking — zero-axiom gate (STRING-JOINT r1)

Per-declaration zero-axiom gate for the label-boundary-word tracking heart: the `pathLabels`-hom, the generic
splice / de-splice append lemmas (including the `listRemoveTwoAt` cons-succ reduction and the length-2 middle
packaging), and the two `advanceLabels`-tracks-`pathLabels` per-step preservation lemmas (cup / cap).  Must be free
of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringPathLabels_composePath
#assert_no_axioms FX1Poly.Polygraph.listInsertAt_append_atPrefix
#assert_no_axioms FX1Poly.Polygraph.listRemoveTwoAt_cons_succ
#assert_no_axioms FX1Poly.Polygraph.listRemoveTwoAt_append_atPrefix
#assert_no_axioms FX1Poly.Polygraph.listRemoveTwoAt_append_middle
#assert_no_axioms FX1Poly.Polygraph.stringAdvanceLabels_tracks_cup
#assert_no_axioms FX1Poly.Polygraph.stringAdvanceLabels_tracks_cap

end FX1PolyAudit
