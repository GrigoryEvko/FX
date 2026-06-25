import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Substrate.Neutral.NeutralSubstReflection

/-! # FX1PolyAudit/.../NeutralSubstReflection — zero-axiom gate for the reverse neutral reflection

`IsNeutral.noClosedSubstImage`: no neutral term is the closed-term image of a substitution — the reverse of
`IsNeutral.rename`, the scope-1 reflection the native consistency bypass (#1697) consumes.  Must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega` (the indexed `childCons`
injection drilling is exactly where a partial-match `propext` leak would arise — the index is fixed by the
constructor so full-enumeration `cases`/`injection` stays clean). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.IsNeutral.noClosedSubstImage

end FX1PolyAudit
