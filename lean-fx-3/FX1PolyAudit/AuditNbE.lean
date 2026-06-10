import FX1PolyAudit.AuditGen
-- Leaf modules of the NbE slice (importing these transitively loads
-- every migrated FX1Poly.NbE declaration: DesignDecision,
-- ReductionStrategy, NormalizerSignature flow into Quote and
-- StrictNormalizer).
import FX1Poly.NbE.Quote
import FX1Poly.NbE.StrictNormalizer
import FX1Poly.NbE.DecisionComplexity

/-! # FX1PolyAudit/AuditNbE — namespace zero-axiom sweep for the NbE slice

Persistent zero-axiom gate for the normalization-by-evaluation
substrate.  The slice carries the NbE design markers
(`NbEDesignChoice` / `ReductionStrategy` hybrid + call-by-name), the
signature-level `Normalizer` / `Quote` / `StrictNormalizer` contracts,
and the canonical identity `quoteRaw` instance plus the eval-then-quote
pipeline composition.

The slice is interface-level: structure declarations, flat
marker enums, and `rfl`-closed cross-reference theorems.  The two
`deriving DecidableEq` enums are non-indexed, so their `decEq`
instances are propext-free — confirmed by this sweep.

The `#audit_namespace` walk loads every declaration under
`FX1Poly.NbE` and fails the build at the first axiom leak (including
`propext` / `Quot.sound` / `Classical.choice`).
-/

#audit_namespace FX1Poly.NbE

-- DecisionComplexity.lean — the generic §11.8.7 STRICT-COMPLEXITY witness schema for decision
-- procedures (the sibling of StrictNormalizer for deciders that are not term normalizers).
#assert_no_axioms FX1Poly.NbE.DecisionComplexity
#assert_no_axioms FX1Poly.NbE.DecisionComplexity.fieldCount_correct
