import LeanFX2.Reduction.Cumul

/-! # Smoke/AuditPhase12A2Cumul — kernel-sprint A2 audit

This file gates every Conv.cumul-flavored theorem and the supporting
typed `Term.universeCode` ctor.  Every entry MUST report
"does not depend on any axioms" under strict policy
(no propext, no Quot.sound, no Classical.choice).

If any entry reports a non-trivial axiom, the deliverable is NOT
shipped — either rewrite cleanly or delete.
-/

namespace LeanFX2

-- Foundation: the typed Term.universeCode ctor itself
#print axioms Term.universeCode

-- Raw layer: RawTerm.universeCode
#print axioms RawTerm.universeCode

-- Conv.cumul shipped theorems
#print axioms Conv.cumul_refl
#print axioms Conv.cumul_proof_irrel
#print axioms Conv.cumul_raw_shared
#print axioms Conv.cumul_outer_eq

end LeanFX2
