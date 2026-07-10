import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Rewriting.WordSystems.EmptySystem

/-! # FX1PolyAudit.Polygraph.OmegacE.EmptySystem

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.OmegacE.EmptySystem`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- FIRST CONCRETE CONVERGENT PRESENTATION (EmptySystem.lean): the empty (free-monoid) rule system discharges
-- BOTH abstract hypotheses end-to-end — no word rewrites (rewritesOneStep_emptySystem_absurd), identity
-- normalizer (emptyWordNormalizer), vacuous confluence (emptyHasConfluence) — so its word problem is
-- decidable AND is exactly SYNTACTIC EQUALITY (convertibleModulo_emptySystem_iff_eq), reconnecting dim-2
-- convertibility to dim-1 free-monoid equality. The dim-2 analog of the closed-SN smoke corpus: proof the
-- abstract machinery is non-vacuous.
#assert_no_axioms FX1Poly.OmegacE.emptyRewriteSystem

#assert_no_axioms FX1Poly.OmegacE.rewritesOneStep_emptySystem_absurd

#assert_no_axioms FX1Poly.OmegacE.emptyWordNormalizer

#assert_no_axioms FX1Poly.OmegacE.emptyHasConfluence

#assert_no_axioms FX1Poly.OmegacE.convertibleModulo_emptySystem_iff_eq

#assert_no_axioms FX1Poly.OmegacE.decidableConvertibleModulo_emptySystem

end FX1PolyAudit
