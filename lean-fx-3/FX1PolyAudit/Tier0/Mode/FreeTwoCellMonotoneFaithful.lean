import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.FreeTwoCellMonotoneFaithful

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellMonotoneFaithful — zero-axiom gate (mode-9 keystone, YES-direction)

Per-declaration zero-axiom gate for the Eilenberg–Zilber staircase reconstruction half of the Schanuel–Street
keystone: the canonical word arithmetic (`leftRightPow` + `blockOf_leftRightPow` + `leftRightPow_add`), the two
EZ staircase STEPS and their realization (`monotoneMapOf_rawFaceStep` realizes the FACE; `monotoneMapOf_rawDegenStep`
realizes the DEGENERACY), the identity staircase realization, and the reconstruction RESIDUAL reduction
(`convOfMapEq_of_canonicalStaircase`: a `CanonicalStaircaseData` yields the keystone's `convOfMapEq`;
`canonicalizationOfStaircaseData` assembles the full `AdjunctionSaturatedCanonicalization`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Canonical word arithmetic
#assert_no_axioms FX1Poly.Tier0.leftRightPow_length_succ
#assert_no_axioms FX1Poly.Tier0.blockOf_leftRightPow
#assert_no_axioms FX1Poly.Tier0.leftRightPow_add
#assert_no_axioms FX1Poly.Tier0.leftRightPow_one

-- The face (cup) staircase step + realization
#assert_no_axioms FX1Poly.Tier0.runMonoCell_adjunctionUnit_snd
#assert_no_axioms FX1Poly.Tier0.runMonoCell_adjunctionCounit_snd
#assert_no_axioms FX1Poly.Tier0.monotoneMapOf_rawFaceStep

-- The degeneracy (cap) staircase step + realization
#assert_no_axioms FX1Poly.Tier0.composePath_singleLeft_singleRight
#assert_no_axioms FX1Poly.Tier0.adjunctionRightThenLeft_eq
#assert_no_axioms FX1Poly.Tier0.composePath_singleLeft_then_singleRight
#assert_no_axioms FX1Poly.Tier0.blockOf_leftRightPow_succ_odd
#assert_no_axioms FX1Poly.Tier0.blockOf_leftContext
#assert_no_axioms FX1Poly.Tier0.degenStepSource_eq
#assert_no_axioms FX1Poly.Tier0.monotoneMapOf_rawDegenStep

-- The identity staircase + realization
#assert_no_axioms FX1Poly.Tier0.monotoneMapOf_id
#assert_no_axioms FX1Poly.Tier0.monotoneMapOf_canonicalIdentityCell

-- The reconstruction residual reduction + keystone assembly
#assert_no_axioms FX1Poly.Tier0.convOfMapEq_of_canonicalStaircase
#assert_no_axioms FX1Poly.Tier0.canonicalizationOfStaircaseData

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSaturatedMonotoneMapStaircaseStep
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSaturatedMonotoneMapFaithfulnessReduction
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMonotoneRouteFaithfulnessReconstructed

end FX1PolyAudit
