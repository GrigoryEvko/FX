import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.List.ListElimDependentMember

/-! # FX1PolyAudit.Core.Eliminators.List.ListElimDependentMember

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.List.ListElimDependentMember`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- DEP-LIST #1729 (sub-B): the BINARY recursive-eliminator twin — the dependent `listElim` member.  Same
-- structured-value recursion as nat, but the `cons`-ι fires to a NESTED app spine (`app (app (app consBranch
-- head) tail) (listElim … tail)`) NOT a substitution, so nat's `succBranchSubstClosed` becomes a
-- `consBranchApplicationClosed` (head SN + tail candidate member + recursive cell member → app-spine member); the
-- recursion descends the TAIL (the `cons` constructor's recursive argument).  Consumes the sub-A eliminator
-- stones (`listConsStructuredMember_tail`, the binary cell SN reflectors, cons-inversion).
#assert_no_axioms FX1Poly.Core.listElimDependentReducibleMember

end FX1PolyAudit
