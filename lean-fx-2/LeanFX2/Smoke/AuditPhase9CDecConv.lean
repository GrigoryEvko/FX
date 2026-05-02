import LeanFX2.Algo.DecConv

/-! Phase 9.C DecConv exports zero-axiom audit.

`Term.checkConv` is the typed surface API for fuel-bounded
βι-conversion checking, delegating to `RawTerm.checkConv` on the
raw projection.  `checkConv_sound` lifts soundness from the raw
side.  `Conv.toRawCheckConvWitness` is the typed-Conv → raw-join
bridge (renames `Conv.toRawJoin` for consumer-facing convenience).

Combined with `Conv.toRawJoin` (Phase 6.F), these three theorems
form the canonical entry points for downstream code that wants to
either verify a typed `Conv` or compute its raw witness.
-/

namespace LeanFX2.SmokePhase9CDecConv

#print axioms LeanFX2.Term.checkConv
#print axioms LeanFX2.Term.checkConv_sound
#print axioms LeanFX2.Conv.toRawCheckConvWitness

end LeanFX2.SmokePhase9CDecConv
