import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.OmegacE.IdempotentSystem

/-! # FX1PolyAudit.Tier0.OmegacE.IdempotentSystem

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.OmegacE.IdempotentSystem`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- FIRST CONCRETE NON-EMPTY TERMINATING PRESENTATION (IdempotentSystem.lean): the idempotent rule [c,c] → [c],
-- a non-trivial length-reducing system. Unlike the empty system (which rewrites NOTHING), this one genuinely
-- FIRES (idempotentRule_fires — the non-vacuity witness contrasting rewritesOneStep_emptySystem_absurd) and
-- is the first NON-trivial discharge of IsTerminating (idempotentSystem_isTerminating, via the length measure
-- 1 < 2). Scope: termination + non-vacuity; the full decidable word problem additionally needs a WordReducer
-- (rule-matching reduceOnce) and HasLocalConfluence (critical pair [c,c,c] joins at [c,c] both ways) — the
-- slices below.
#assert_no_axioms FX1Poly.OmegacE.idempotentRule

#assert_no_axioms FX1Poly.OmegacE.idempotentSystem

#assert_no_axioms FX1Poly.OmegacE.idempotentRule_fires

#assert_no_axioms FX1Poly.OmegacE.idempotentSystem_isLengthReducing

#assert_no_axioms FX1Poly.OmegacE.idempotentSystem_isTerminating

end FX1PolyAudit
