import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.Core.RecursiveEliminatorTermination

/-! # FX1PolyAudit.Core.Metatheory.Normalization.Core.RecursiveEliminatorTermination

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.Core.RecursiveEliminatorTermination`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- ★ SPIKE: the RECURSIVE-eliminator ι-pattern terminates via the shipped multiset RPO certificate,
-- INDEPENDENT of β and typed-SN (the Leg-3 "β-imported boundary"). The fxSystem termination imports
-- typed-SN because it encodes β (raw β is non-terminating); η-SN is shipped; the open ι piece
-- splits — non-recursive ι is size-decreasing, the RECURSIVE eliminator (natElim-succ DUPLICATES the recursive
-- call on a SMALLER scrutinee) needs the multiset (Dershowitz-Manna) RPO. This models that hard core: ElimStep
-- elim(k+1) ↝ branch(elim k, elim k), terminated by recScrutineeMultiset over Nat.lt via
-- wellFounded_of_precedenceMultisetMeasure — NO β, NO Tait. listAppendAssoc is propext-free (List.append_assoc
-- DEPENDS ON propext). De-risking model; the real Step ι-arms over RawTerm are the multi-firing follow-on.
#assert_no_axioms FX1Poly.Core.listAppendAssoc

#assert_no_axioms FX1Poly.Core.MultisetRedOne.appendRight

#assert_no_axioms FX1Poly.Core.MultisetRedOne.appendLeft

#assert_no_axioms FX1Poly.Core.elimStep_decreasesMultiset

#assert_no_axioms FX1Poly.Core.recursiveEliminatorTerminates

#assert_no_axioms FX1Poly.Core.recursiveEliminatorTerminates.smoke

end FX1PolyAudit
