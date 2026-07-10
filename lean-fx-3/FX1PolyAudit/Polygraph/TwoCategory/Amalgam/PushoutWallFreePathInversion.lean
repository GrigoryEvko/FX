import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreePathInversion

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWallFreePathInversion — zero-axiom gate for the wall-free
1-cell converse `pathInvert` and its two round-trips (WP-AMALG-2 r11, B2)

Per-declaration zero-axiom gate for the monad single-mode / endo-generator facts, the letter converse, `pathInvert`,
the word-level round-trip helper, both path-level round-trips, the wall-free-image lemma, and the concrete probes.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadOnlyMode
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadGenEndpoints
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadLetterOfWallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pathInvert
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadEmbedInvert_word
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapPath_inclRight_pathInvert
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapPath_inclRight_wallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pathInvert_mapPath_inclRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.tRunTwoWallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadEndoLetter
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadEndoTwoT
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pathInvert_forward_probe
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pathInvert_reverse_probe
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasWallFreePathInversion

end FX1PolyAudit
