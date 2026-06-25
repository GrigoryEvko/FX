import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Reducibility.Candidates.KripkeReducibilityCandidate

/-! # FX1PolyAudit.Core.Metatheory.Reducibility.Candidates.KripkeReducibilityCandidate

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Reducibility.Candidates.KripkeReducibilityCandidate`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- A reducibility candidate is closed under renaming, in the Kripke-indexed form: IsKripkeReducibilityCandidate
-- (CR1 members-SN + CR2 closed-under-Step) survives KripkeCand.transport along any renaming with no hypothesis
-- (the index precomposes; laws read off at the composed index).  The bare same-scope ReducibleTypeStep form is
-- false (the piType same-scope argument quantifier has a counterexample at a renamed Pi-type), so the Kripke
-- index is what carries renaming-closure.  Predicate-level companion is kripkeArrowDep_transport_pointwise.
#assert_no_axioms FX1Poly.Core.IsKripkeReducibilityCandidate

#assert_no_axioms FX1Poly.Core.IsKripkeReducibilityCandidate.transport

end FX1PolyAudit
