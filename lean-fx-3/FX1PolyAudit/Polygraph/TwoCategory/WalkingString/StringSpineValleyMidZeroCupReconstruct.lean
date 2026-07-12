import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineValleyMidZeroCupReconstruct

/-! # FX1PolyAudit/…/WalkingString/StringSpineValleyMidZeroCupReconstruct — zero-axiom gate
(FC-3 r35, M3: the mid-width-`0` cup-block reconstruction shift-sim port)

Per-declaration zero-axiom gate for the string mid-width-`0` cup-block reconstruction over the walking
ADJOINT-TRIPLE signature: the target Prop `StringMidZeroCupBlockReconstruct`, the DISCHARGED headline
`stringMidZeroCupBlockReconstruct_holds` (the floor-`0` top-top cup-arc partner is the pure fresh-leg shift landed
on the matching carrier — the generic `MatchingShiftSim` fold + N1/N2 floor separation + `findPartnerScan_mapCongr`,
POSITIVITY-FREE), the mixed-valley truth-probe firing and its `decide` mid-width cross-check, and the honesty
marker.  The `SMZ` privates (the four star helpers `cupRunLoopsIrrelSMZ` / `findPartnerScan_allFailSMZ` /
`wholeCupPartnerShiftSMZ` / `cupWholeSimSMZ`, `allFalseCountZeroSMZ`, and the range/map/`Nat.blt` plumbing) are
`private`, so they are covered TRANSITIVELY by the headline: axiom dependency propagates through the proof term, so
`stringMidZeroCupBlockReconstruct_holds` reporting no axioms forces every private it uses to be axiom-free too.
Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`.
The project `#assert_no_axioms` macro is fuel-based; the independent `#print axioms` lines below are the trusted
cross-check. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.StringMidZeroCupBlockReconstruct
#assert_no_axioms FX1Poly.Polygraph.stringMidZeroCupBlockReconstruct_holds
#assert_no_axioms FX1Poly.Polygraph.stringMidZeroCupBlockReconstruct_holds_firesOnMixedValley
#assert_no_axioms FX1Poly.Polygraph.stringMidZeroCupBlockReconstruct_probe_midWidthIsZero
#assert_no_axioms FX1Poly.Polygraph.fxString_hasMidZeroCupBlockReconstruct

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.StringMidZeroCupBlockReconstruct
#print axioms FX1Poly.Polygraph.stringMidZeroCupBlockReconstruct_holds
#print axioms FX1Poly.Polygraph.stringMidZeroCupBlockReconstruct_holds_firesOnMixedValley
#print axioms FX1Poly.Polygraph.stringMidZeroCupBlockReconstruct_probe_midWidthIsZero
#print axioms FX1Poly.Polygraph.fxString_hasMidZeroCupBlockReconstruct

end FX1PolyAudit
