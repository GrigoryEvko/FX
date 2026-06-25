import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Nat.NatElimValueMember

/-! # FX1PolyAudit.Core.Eliminators.Nat.NatElimValueMember

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.Nat.NatElimValueMember`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Value-case natElim reducibility with the recursor-SN obligation discharged: replaces the bespoke
-- redexStronglyNormalizing hypothesis of natElimValueReducibility with the universal candidate properties CR1
-- (members are SN) + CR2 (membership forward-closed under Step) + succBranchTerminates.  The scrutinee-fixed
-- cell-SN recursor (natElimNormalScrutineeCellStronglyNormalizing) does a double Acc induction over the
-- branches, carrying the branch interface forward via CR2, with the iota-reduct SN coming from its membership
-- via CR1, so it needs no bespoke succContractumTerminates.  The pure Tait value-recursor argument over a
-- fixed result candidate (fuel-independent).
#assert_no_axioms FX1Poly.Core.natElimNormalScrutineeCellStronglyNormalizing

#assert_no_axioms FX1Poly.Core.natElimValueMember

-- The dependent-recursor twin: identical discharge (CR1 + CR2 + succBranchTerminates replacing
-- redexStronglyNormalizing) via the natRec scrutinee-fixed cell-SN recursor, gen_natRec's five-way
-- Step.from_natRec inversion matching natElim's.
#assert_no_axioms FX1Poly.Core.natRecNormalScrutineeCellStronglyNormalizing

#assert_no_axioms FX1Poly.Core.natRecValueMember

-- FTGEN-11.1: the SELF-CONTAINED value-case arms — the substituted-reduct membership is no longer a caller
-- premise but DISCHARGED FROM THE structural IsNatValue IH.  The scrutinee-keyed cell-SN recursor keys its
-- reduct interface on the fixed scrutinee's decomposition (only ever the predecessor witnessing value =
-- natSuccCell predecessor), which the branch-universal IH supplies; the sole remaining premise is
-- succBranchSubstClosed (the branch's substitution-closure, the irreducible fundamental-theorem content).
#assert_no_axioms FX1Poly.Core.natElimCellStronglyNormalizingScrutineeKeyed

#assert_no_axioms FX1Poly.Core.natElimValueMemberSelfContained

#assert_no_axioms FX1Poly.Core.natRecCellStronglyNormalizingScrutineeKeyed

#assert_no_axioms FX1Poly.Core.natRecValueMemberSelfContained

-- FTGEN-11.2 / DEP-NAT-CORE: the OPEN-SCOPE structured-value generalization — IsNatValue (succ^k zero)
-- widened to IsNatStructured (succ^k of zero OR of a NORMAL NEUTRAL).  Three-case induction: the zero/succ
-- numeral cases reuse the scrutinee-keyed cell-SN recursor verbatim; the NEW neutralNormal base routes a
-- normal-neutral scrutinee through natElim/natRec_neutralScrutinee_isStronglyNormalizing + IsNeutral.natElim/
-- natRec + the CR3 neutral bridge.  This is the genuine recursive Core member the dependent nat FT consumes.
#assert_no_axioms FX1Poly.Core.natElimStructuredValueMember

#assert_no_axioms FX1Poly.Core.natRecStructuredValueMember

end FX1PolyAudit
