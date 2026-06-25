import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Canonicity.Core.NatUnionReducesToNumeral

/-! # FX1PolyAudit/AuditNatUnionReducesToNumeral
    — zero-axiom gate for the reduces-to-numeral form of Nat canonicity over the single union judgment

`HasTypeUnion.closedNatDataCandidateFromNormalization` / `…closedNatReducesToNumeralFromNormalization`:
the machine-checked reduction of closed-Nat canonicity to the deferred union SN/SR arc — union SN of the
subject plus along-reduction nat-typing of its reachable normal forms assemble `dataTaitCandidate
IsNatNumeral` membership, and `dataTaitCandidate.closedReducesToValue` extracts "reduces to a deep
numeral".  Must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.closedNatDataCandidateFromNormalization
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.closedNatReducesToNumeralFromNormalization

end FX1PolyAudit
