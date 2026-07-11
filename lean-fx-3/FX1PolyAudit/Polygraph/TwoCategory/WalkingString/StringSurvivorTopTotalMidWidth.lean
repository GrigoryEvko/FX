import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSurvivorTopTotalMidWidth

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringSurvivorTopTotalMidWidth — zero-axiom gate
(FC-3 r29, M2a: the survivor-top total is the mid-width)

Per-declaration zero-axiom gate for the string survivor-top-total-is-mid-width keystone over the walking
ADJOINT-TRIPLE signature: the pure-cap seed facts (fresh count zero → every endpoint / survivor `< bc`), the
cup-block floor-homogeneity fold, the value-surjectivity image cover, the keystone
`stringSurvivorTopTotal_eq_midWidth`, and the two concrete truth-probes on the genuine mixed string valley
`[ε] ++ [η']`.  Every declaration must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`.  The project `#assert_no_axioms` macro is fuel-based; the independent `#print axioms` lines below are the
trusted cross-check. -/

namespace FX1PolyAudit

-- the pure-cap fresh-id seed facts (every endpoint / survivor of a pure-cap matching sits below `bc`)
#assert_no_axioms FX1Poly.Polygraph.stringAtomsFreshTotal_ofAllCapArity
#assert_no_axioms FX1Poly.Polygraph.stringProcessSpine_nextFresh_ofAllCapArity
#assert_no_axioms FX1Poly.Polygraph.stringProcessSpine_nextFresh_ofAllCapArity_seed
#assert_no_axioms FX1Poly.Polygraph.stringProcessSpine_links_below_ofAllCapArity_seed
#assert_no_axioms FX1Poly.Polygraph.stringProcessSpine_openWires_below_ofAllCapArity_seed

-- the cup-block floor-homogeneity fold + the value-surjectivity image cover
#assert_no_axioms FX1Poly.Polygraph.stringProcessSpine_edgesFloorHomogeneous_ofAllCupArity
#assert_no_axioms FX1Poly.Polygraph.stringProcessSpine_wireOrderImageCover_ofAllCupArity

-- ★ the keystone (M2a): survivor-top total = mid-width
#assert_no_axioms FX1Poly.Polygraph.stringSurvivorTopTotal_eq_midWidth

-- the two concrete truth-probes (fire the keystone end-to-end on the mixed valley `[ε] ++ [η']`)
#assert_no_axioms FX1Poly.Polygraph.stringSurvivorTopTotal_eq_midWidth_firesOnMixedValley
#assert_no_axioms FX1Poly.Polygraph.stringSurvivorTopTotal_mixedValley_isZero

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxString_hasSurvivorTopTotalMidWidth

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringAtomsFreshTotal_ofAllCapArity
#print axioms FX1Poly.Polygraph.stringProcessSpine_nextFresh_ofAllCapArity
#print axioms FX1Poly.Polygraph.stringProcessSpine_nextFresh_ofAllCapArity_seed
#print axioms FX1Poly.Polygraph.stringProcessSpine_links_below_ofAllCapArity_seed
#print axioms FX1Poly.Polygraph.stringProcessSpine_openWires_below_ofAllCapArity_seed
#print axioms FX1Poly.Polygraph.stringProcessSpine_edgesFloorHomogeneous_ofAllCupArity
#print axioms FX1Poly.Polygraph.stringProcessSpine_wireOrderImageCover_ofAllCupArity
#print axioms FX1Poly.Polygraph.stringSurvivorTopTotal_eq_midWidth
#print axioms FX1Poly.Polygraph.stringSurvivorTopTotal_eq_midWidth_firesOnMixedValley
#print axioms FX1Poly.Polygraph.stringSurvivorTopTotal_mixedValley_isZero
#print axioms FX1Poly.Polygraph.fxString_hasSurvivorTopTotalMidWidth

end FX1PolyAudit
