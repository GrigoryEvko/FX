import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.FreeTwoCellMonotoneMap

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellMonotoneMap — zero-axiom gate (the Schanuel–Street monotone-map model)

Per-declaration zero-axiom gate for the SATURATED walking-adjunction monotone-map keystone: the `MonotoneMap`
algebra (`composeMap` / `idMap` / face `faceMap` / degeneracy `degenMap` and their indexing lemmas), the headline
SIMPLICIAL IDENTITY `σ_i ∘ δ_i = id` (`composeMap_faceMap_degenMap`) and the snake collapse it powers
(`snakeCollapseAtWidth`), the structural fold `monotoneMapOf`, the triangle identities in the model (seed +
whiskered), and the structural-fragment soundness leg.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.monotoneMapGet
#assert_no_axioms FX1Poly.Tier0.ascendingFrom
#assert_no_axioms FX1Poly.Tier0.composeMap
#assert_no_axioms FX1Poly.Tier0.idMap
#assert_no_axioms FX1Poly.Tier0.ascendingFrom_length
#assert_no_axioms FX1Poly.Tier0.ascendingFrom_get
#assert_no_axioms FX1Poly.Tier0.composeMap_length
#assert_no_axioms FX1Poly.Tier0.composeMap_get
#assert_no_axioms FX1Poly.Tier0.listExtById
#assert_no_axioms FX1Poly.Tier0.composeMap_idMap_left
#assert_no_axioms FX1Poly.Tier0.faceFrom
#assert_no_axioms FX1Poly.Tier0.degenFrom
#assert_no_axioms FX1Poly.Tier0.faceMap
#assert_no_axioms FX1Poly.Tier0.degenMap
#assert_no_axioms FX1Poly.Tier0.faceFrom_length
#assert_no_axioms FX1Poly.Tier0.degenFrom_length
#assert_no_axioms FX1Poly.Tier0.faceFrom_get_lt
#assert_no_axioms FX1Poly.Tier0.faceFrom_get_ge
#assert_no_axioms FX1Poly.Tier0.degenFrom_get_le
#assert_no_axioms FX1Poly.Tier0.degenFrom_get_succ
#assert_no_axioms FX1Poly.Tier0.degenFrom_faceFrom_pointwise
#assert_no_axioms FX1Poly.Tier0.composeMap_faceMap_degenMap
#assert_no_axioms FX1Poly.Tier0.composeMap_faceMap_degenMap_smoke
#assert_no_axioms FX1Poly.Tier0.idMap_length
#assert_no_axioms FX1Poly.Tier0.faceMap_length
#assert_no_axioms FX1Poly.Tier0.degenMap_length
#assert_no_axioms FX1Poly.Tier0.composeMap_idMap_eq
#assert_no_axioms FX1Poly.Tier0.snakeCollapseAtWidth
#assert_no_axioms FX1Poly.Tier0.blockOf
#assert_no_axioms FX1Poly.Tier0.monoStepAtom
#assert_no_axioms FX1Poly.Tier0.monotoneMapOf
#assert_no_axioms FX1Poly.Tier0.monotoneMapOf_unit
#assert_no_axioms FX1Poly.Tier0.monotoneMapOf_counit
#assert_no_axioms FX1Poly.Tier0.monotoneMapOf_leftSnake_eq_id
#assert_no_axioms FX1Poly.Tier0.monotoneMapOf_rightSnake_eq_id
#assert_no_axioms FX1Poly.Tier0.monotoneMapOf_whiskeredLeftSnake_via_simplicialIdentity
#assert_no_axioms FX1Poly.Tier0.monotoneMapOf_whiskeredLeftId_eq
#assert_no_axioms FX1Poly.Tier0.monotoneMapOf_whiskeredLeftTriangle
#assert_no_axioms FX1Poly.Tier0.monotoneMapOf_congr_of_spine_eq
#assert_no_axioms FX1Poly.Tier0.monotoneMapOf_eq_of_interchangeFreeStep
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSaturatedMonotoneMapFold
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSaturatedMonotoneMapTriangleFree
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSaturatedMonotoneMapGodementSoundness
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSaturatedMonotoneMapFaithfulness

end FX1PolyAudit
