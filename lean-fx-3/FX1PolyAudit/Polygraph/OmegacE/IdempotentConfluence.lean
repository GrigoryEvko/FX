import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.OmegacE.IdempotentConfluence

/-! # FX1PolyAudit.Polygraph.OmegacE.IdempotentConfluence

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.OmegacE.IdempotentConfluence`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- IDEMPOTENT CONFLUENCE LAYER — STRUCTURAL CHARACTERIZATION (IdempotentConfluence.lean): one-step idempotent
-- rewriting IS "collapse one [c,c] to [c] in context" — rewriteOneStep_decomposition (forward: induction on
-- the rewrite, context ctors extend A/B) + rewriteOneStep_ofDecomposition (backward: fire under both contexts).
-- The inversion that turns the inductive RewritesOneStep into an explicit redex position = the critical-pair
-- extraction tool local confluence consumes. listAppendAssoc = propext-free append associativity (core
-- List.append_assoc carries propext — the Word.lean discipline). Scope: the structural characterization;
-- HasLocalConfluence (the [c,c,c] overlap analysis) + decidability are the slice below.
#assert_no_axioms FX1Poly.OmegacE.listAppendAssoc

#assert_no_axioms FX1Poly.OmegacE.rewriteOneStep_decomposition

#assert_no_axioms FX1Poly.OmegacE.rewriteOneStep_ofDecomposition

-- IDEMPOTENT LOCAL CONFLUENCE + DECIDABILITY (IdempotentConfluence.lean): the capstone — the FIRST non-trivial
-- FULLY-DECIDED ωcE system. listPrefixSplit (overlap combinatorial core) + joinableWhenLeftShorter (the 3
-- overlap cases: []/[c] collapse to equal reducts, c::c::mid' is the disjoint commuting case) ⟹
-- idempotentHasLocalConfluence (trichotomy on redex positions) ⟹ decidableConvertibleModulo_idempotentSystem
-- (via decidableConvertibleModulo_ofConvergent: local confluence + shipped termination + shipped reducer).
-- PROPEXT DISCIPLINE: simp (even simp only with clean lemmas) pulls propext — ALL list reasoning is rw-only,
-- via singleConsAppend/doubleConsAppend (rfl redex-collapsers, also avoiding injection's [].append artifacts)
-- + listAppendNil + explicit-arg listAppendAssoc. Validates newman + the convergent-presentation decision
-- end-to-end on a real genuinely-rewriting presentation (the empty system is vacuous).
#assert_no_axioms FX1Poly.OmegacE.listAppendNil

#assert_no_axioms FX1Poly.OmegacE.singleConsAppend

#assert_no_axioms FX1Poly.OmegacE.doubleConsAppend

#assert_no_axioms FX1Poly.OmegacE.listPrefixSplit

#assert_no_axioms FX1Poly.OmegacE.joinable_of_wordEq

#assert_no_axioms FX1Poly.OmegacE.joinableWhenLeftShorter

#assert_no_axioms FX1Poly.OmegacE.idempotentHasLocalConfluence

#assert_no_axioms FX1Poly.OmegacE.decidableConvertibleModulo_idempotentSystem

end FX1PolyAudit
