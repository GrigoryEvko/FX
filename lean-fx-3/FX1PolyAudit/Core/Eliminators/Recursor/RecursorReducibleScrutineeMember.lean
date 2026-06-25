import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Recursor.RecursorReducibleScrutineeMember

/-! # FX1PolyAudit.Core.Eliminators.Recursor.RecursorReducibleScrutineeMember

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Eliminators.Recursor.RecursorReducibleScrutineeMember`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The general-scrutinee regime of the Nat recursor: the full outer recursion.  The Nat data candidate
-- CanonicalFormsPredicate IsNatValue builds in the value-or-neutral dichotomy (SN and
-- neutral-or-reaches-a-numeral), so a reducible scrutinee splits exactly into the two regimes: neutral implies
-- the stuck cell is a member by CR3; value implies natElimValueReducibility lands the numeral cell, and
-- ofStepStarReachingValue lifts it back through the scrutinee congruence (the lift needs the numeral cell to
-- reach a value, extracted by refuting its neutrality via <recursor>_notNeutral_ofNatValueScrutinee).  The
-- open-scope generalization of the closed natElimClosedIsMember (where the neutral disjunct is vacuous).
#assert_no_axioms FX1Poly.Core.natElim_notNeutral_ofNatValueScrutinee

#assert_no_axioms FX1Poly.Core.natRec_notNeutral_ofNatValueScrutinee

#assert_no_axioms FX1Poly.Core.natElimReducibleScrutineeMember

#assert_no_axioms FX1Poly.Core.natRecReducibleScrutineeMember

-- The general-scrutinee regime of the List recursor: the listElim twin of the Nat general-scrutinee
-- dispatch, bringing the three recursive eliminators (natElim/natRec/listElim) to general-scrutinee parity.
-- Same dispatch on the List candidate's value-or-neutral disjunct, via listElimValueReducibility +
-- ofStepStarReachingValue (StepStar.listElimScrutinee), with the value side extracted by
-- listElim_notNeutral_ofListValueScrutinee.
#assert_no_axioms FX1Poly.Core.listElim_notNeutral_ofListValueScrutinee

#assert_no_axioms FX1Poly.Core.listElimReducibleScrutineeMember

end FX1PolyAudit
