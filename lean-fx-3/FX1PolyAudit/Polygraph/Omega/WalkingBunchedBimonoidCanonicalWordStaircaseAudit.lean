import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordStaircase

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordStaircaseAudit — zero-axiom gate for the
canonical reduced-word engine: the Coxeter–Moser comb (`combInsertData`), the one-level normal form, the recursive
staircase (`recComb`), the descending run, and the `mentionsOnlyBelow` certificate, with the r9 / r11 pins and the
permutation round-trip (WP-PROP r14, #2033).

Per-declaration `#assert_no_axioms` on every def / theorem / marker, PLUS independent (non-fuel) `#print axioms` on
the engine defs, the round-trip pin, and the marker.  The project `#assert_no_axioms` macro is fuel-based; the
independent `#print axioms` closes the gate. -/

namespace FX1PolyAudit

-- C0 — the canonical-word DATA engine.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDescendingPositions
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidMentionsOnlyBelow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombInsertData
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombNormalizeForm
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb

-- C0 — the r9 / r11 pins + the round-trip.
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb_r9_stuck_word
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb_r11_left
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb_r11_right
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombNormalizeForm_r11_left_fixed
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb_braidPairUnifies
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb_r9_roundTrip
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidBraidPairPermShared

-- The C0 marker.
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_canonicalWordStaircaseEngineShipped

-- Independent (non-fuel) axiom prints on the engine defs, the round-trip pin, and the marker.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCombInsertData
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb_r9_stuck_word
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRecComb_r9_roundTrip
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_canonicalWordStaircaseEngineShipped

end FX1PolyAudit
