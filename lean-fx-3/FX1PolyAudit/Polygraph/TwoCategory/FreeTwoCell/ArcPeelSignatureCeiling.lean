import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPeelSignatureCeiling

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcPeelSignatureCeiling — zero-axiom gate (mode-3 floor, arity ceiling)

Per-declaration zero-axiom gate for the arc peel's arity-ceiling witness: the toy one-object crossing signature
(`crossGraph` / `crossStrandPair` / `crossModeSignature` / `crossAtom`), the width smokes, the box-arm facts
(`crossAtom_stepArcAtom_recordsNoCupEvent` / `_recordsNoCapEvent` — a `2⇒2` crossing records no cup/cap event),
the concrete non-cup/cap witness (`crossAtom_isNotCupOrCap`), the adjunction arity-lock re-export
(`adjunctionAtom_hasCupOrCapArity`), and the honesty markers.

`#assert_no_axioms` (the project's fuel-based macro) AND an independent `#print axioms` per declaration — the two
are cross-checked because the fuel-based walk is not trusted alone.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`.  NOT registered in `AuditAll` beyond the parent's unified
registration. -/

namespace FX1PolyAudit

-- the toy crossing signature
#assert_no_axioms FX1Poly.Polygraph.crossGraph
#assert_no_axioms FX1Poly.Polygraph.crossStrandPair
#assert_no_axioms FX1Poly.Polygraph.crossModeSignature
#assert_no_axioms FX1Poly.Polygraph.crossAtom

-- the width smokes
#assert_no_axioms FX1Poly.Polygraph.crossAtom_generatorDom_length
#assert_no_axioms FX1Poly.Polygraph.crossAtom_generatorCod_length

-- the box-arm facts + the concrete non-cup/cap witness
#assert_no_axioms FX1Poly.Polygraph.crossAtom_stepArcAtom_recordsNoCupEvent
#assert_no_axioms FX1Poly.Polygraph.crossAtom_stepArcAtom_recordsNoCapEvent
#assert_no_axioms FX1Poly.Polygraph.crossAtom_isNotCupOrCap

-- the adjunction arity-lock re-export
#assert_no_axioms FX1Poly.Polygraph.adjunctionAtom_hasCupOrCapArity

-- honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcPeelArityCeiling
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcPeelGeneralSignature

/-! ## Independent `#print axioms` cross-check (the fuel-based macro is not trusted alone) -/

#print axioms FX1Poly.Polygraph.crossModeSignature
#print axioms FX1Poly.Polygraph.crossAtom
#print axioms FX1Poly.Polygraph.crossAtom_stepArcAtom_recordsNoCupEvent
#print axioms FX1Poly.Polygraph.crossAtom_stepArcAtom_recordsNoCapEvent
#print axioms FX1Poly.Polygraph.crossAtom_isNotCupOrCap
#print axioms FX1Poly.Polygraph.adjunctionAtom_hasCupOrCapArity

end FX1PolyAudit
