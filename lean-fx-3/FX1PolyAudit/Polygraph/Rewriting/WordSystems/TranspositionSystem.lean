import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Rewriting.WordSystems.TranspositionSystem

/-! # FX1PolyAudit.Polygraph.OmegacE.TranspositionSystem

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.OmegacE.TranspositionSystem`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- FIRST CONCRETE LENGTH-PRESERVING PRESENTATION (TranspositionSystem.lean): the adjacent-transposition rule
-- [a,b] → [b,a], the complement of the length-REDUCING idempotent system. The first system in the
-- length-PRESERVING class (IsLengthPreservingSystem) — the simplest convergent class for which length is NOT a
-- termination measure (decided by bounded search over the finite same-length word set). transpositionRule_fires
-- is the non-vacuity witness; transpositionSystem_isLengthPreserving is the headline certificate; the three
-- length-invariance corollaries (one-step / many-step / convertibility) instantiate the shipped preservation
-- lemmas and establish that the whole reduction/convertibility graph of a word stays within fixed length (the
-- bounded-search-decidability substrate). Scope: the SYSTEM + length invariants + non-vacuity; termination
-- (inversion measure, needs a ≠ b), orthogonal local confluence, and the bounded-search decision are the
-- slices below.
#assert_no_axioms FX1Poly.OmegacE.transpositionRule

#assert_no_axioms FX1Poly.OmegacE.transpositionSystem

#assert_no_axioms FX1Poly.OmegacE.transpositionRule_fires

#assert_no_axioms FX1Poly.OmegacE.transpositionSystem_isLengthPreserving

#assert_no_axioms FX1Poly.OmegacE.transpositionSystem_rewritesOneStep_length_preserved

#assert_no_axioms FX1Poly.OmegacE.transpositionSystem_rewritesMany_length_preserved

#assert_no_axioms FX1Poly.OmegacE.transpositionSystem_convertibleModulo_length_preserved

-- TRANSPOSITION TERMINATION MEASURE (TranspositionSystem.lean): the inversion-count measure infrastructure
-- for the transposition termination proof. The system is length-PRESERVING, so length is no measure; the
-- inversion count (firstCell-before-secondCell ordered pairs) strictly decreases per swap. countOccurrences +
-- aBeforeBInversions are the measure; the two append-homomorphism lemmas (countOccurrences_append,
-- aBeforeBInversions_append with its cross-term count-product) are the reusable core the strict-decrease
-- proof's context cases consume. ZERO-AXIOM DISCIPLINE: aBeforeBInversions_append avoids Nat.add_mul (leaks
-- propext) via Nat.add_comm 1 _ + Nat.succ_mul, and avoids ac_rfl (leaks propext + Quot.sound) via explicit
-- Nat.add_assoc/add_left_comm canonicalization.
#assert_no_axioms FX1Poly.OmegacE.countOccurrences

#assert_no_axioms FX1Poly.OmegacE.aBeforeBInversions

#assert_no_axioms FX1Poly.OmegacE.countOccurrences_append

#assert_no_axioms FX1Poly.OmegacE.aBeforeBInversions_append

-- TRANSPOSITION TERMINATION COMPLETE (TranspositionSystem.lean): the termination proof. The inversion
-- measure decreases per swap, so the length-PRESERVING transposition system is terminating — the genuine
-- NON-length certificate (complement of the idempotent system's length-reducing one). countOccurrences_preserved_by_step
-- (multiset invariance) → aBeforeBInversions_decreases (strict decrease, needs firstCell ≠ secondCell) →
-- transpositionSystem_isTerminating (Subrelation into InvImage (·<·) measure, mirroring IsTerminating_of_lengthReducing).
-- All zero-axiom (the if-residual base cases close by default-transparency rfl; no Nat.add_mul / ac_rfl).
-- Orthogonal local confluence + bounded-search decidability are the slices below.
#assert_no_axioms FX1Poly.OmegacE.countOccurrences_preserved_by_step

#assert_no_axioms FX1Poly.OmegacE.aBeforeBInversions_decreases

#assert_no_axioms FX1Poly.OmegacE.transpositionSystem_isTerminating

end FX1PolyAudit
