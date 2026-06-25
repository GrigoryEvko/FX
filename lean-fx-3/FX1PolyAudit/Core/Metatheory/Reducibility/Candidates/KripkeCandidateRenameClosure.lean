import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Reducibility.Candidates.KripkeCandidateRenameClosure

/-! # FX1PolyAudit.Core.Metatheory.Reducibility.Candidates.KripkeCandidateRenameClosure

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Reducibility.Candidates.KripkeCandidateRenameClosure`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Kripke-indexed candidates make arrow rename-closure definitional.  Non-dependent presheaf
-- functoriality + the arrow rename-closure.
#assert_no_axioms FX1Poly.Core.transport_transport_pointwise

#assert_no_axioms FX1Poly.Core.kripkeArrow_transport_pointwise

-- Dependent Kripke arrow (the Pi case): codomain family transport functoriality + dependent rename-closure.
#assert_no_axioms FX1Poly.Core.codFamily_transport_transport_pointwise

#assert_no_axioms FX1Poly.Core.kripkeArrowDep_transport_pointwise

-- CR1 for the Kripke arrow (non-dependent + dependent): members are strongly normalizing (Tait argument).
#assert_no_axioms FX1Poly.Core.kripkeArrow_stronglyNormalizing

#assert_no_axioms FX1Poly.Core.kripkeArrowDep_stronglyNormalizing

-- CR2 for the Kripke arrow (non-dependent + dependent): forward Step closure.
#assert_no_axioms FX1Poly.Core.kripkeArrow_forwardStep

#assert_no_axioms FX1Poly.Core.kripkeArrowDep_forwardStep

-- CR3 for the non-dependent Kripke arrow: Girard neutral backward closure — the PAUSED brick, now unblocked
-- by the full arbitrary-renaming Step reflection-with-image (Step.reflectRename, StepRenameReflectAssembly).
-- A neutral function all of whose Step-reducts are in the arrow is in the arrow: app of neutral head is
-- neutral, codomain-CR3 closes it, head-steps reflect via Step.reflectRename + the all-reducts hypothesis,
-- arg-steps run the inner Tait accessibility induction on the domain-CR1 strongly-normalizing argument. This
-- COMPLETES the non-dependent Kripke arrow CR bundle (CR1/CR2/CR3) — a prerequisite ingredient for the open
-- Kripke logical relation that the GrownCtxConv-5 (#842) context-conversion piElim residual requires.
#assert_no_axioms FX1Poly.Core.kripkeArrow_neutralBackwardClosure

-- The SN Kripke candidate (the Kripke-model interpretation of a NEUTRAL type code): the index-IGNORING
-- candidate whose members at every renaming index are exactly the strongly-normalizing terms (the
-- `ReducibleTypeStep.neutral` SN candidate lifted to the renaming-indexed family).  Rename-INVARIANT
-- (transport along any renaming is the IDENTITY, `Iff.rfl`) — the semantic reason context conversion is FREE
-- on the neutral-type interpretation of the open GrownCtxConv-5 (#842) type-validity residual — plus CR1 (members are
-- strongly normalizing, definitionally).  Wires the Kripke arrow substrate to the type-level neutral
-- interpretation, the first concrete piece of the open typed logical-relation model.
#assert_no_axioms FX1Poly.Core.snKripkeCand_transport_pointwise

#assert_no_axioms FX1Poly.Core.snKripkeCand_stronglyNormalizing

end FX1PolyAudit
