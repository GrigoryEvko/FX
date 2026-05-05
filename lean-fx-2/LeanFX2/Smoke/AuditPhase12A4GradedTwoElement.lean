import LeanFX2.Graded.Instances.Security
import LeanFX2.Graded.Instances.Effect
import LeanFX2.Graded.Instances.Observability
import LeanFX2.Graded.Instances.Reentrancy
import LeanFX2.Graded.Instances.FPOrder
import LeanFX2.Graded.Instances.Mutation
import LeanFX2.Graded.Instances.NatResource
import LeanFX2.Graded.Instances.Lifetime
import LeanFX2.Graded.Instances.Provenance
import LeanFX2.Graded.Instances.Trust
import LeanFX2.Graded.Instances.Representation
import LeanFX2.Graded.Instances.ClockDomain
import LeanFX2.Graded.Instances.Complexity
import LeanFX2.Graded.Instances.Precision
import LeanFX2.Graded.Instances.Space
import LeanFX2.Graded.Instances.Overflow
import LeanFX2.Graded.Instances.Size
import LeanFX2.Graded.Instances.Version

/-! # AuditPhase12A4GradedTwoElement — D5.4 partial: graded semiring
instances for finite chains and bounded resource dimensions.

Phase 12.A.4 partial closure for D5.4 (21 graded semiring instances).
The first wave ships five canonical chain instances:

* `SecurityGrade`        (dim 5)  — `unclassified < classified` (2-chain)
* `ObservabilityGrade`   (dim 11) — `opaque < transparent` (2-chain)
* `ReentrancyGrade`      (dim 19) — `nonReentrant < reentrant` (2-chain)
* `FPOrderGrade`         (dim 17) — `strict < reassociate` (2-chain)
* `MutationGrade`        (dim 18) — `immutable < appendOnly <
                                       monotonic < readWrite` (4-chain)

Each follows the canonical totally-ordered-chain Boolean-algebra
encoding:
* `+` = lattice join (∨ / max)      — combining accumulates upward
* `*` = lattice meet (∧ / min)      — scaling annihilates with `0`
* `0` = lattice bottom              — additive identity
* `1` = lattice top                 — multiplicative identity
* `≤` = chain order                 — uni-directional subsumption

All 17 GradeSemiring laws (3 add-monoid + 2 mul-monoid + 2 distrib +
2 annihilation + 2 preorder + 2 monotonicity + 4 identity refl)
discharged by full case enumeration over the closed inductive (4 to
256 sub-cases per law) — no `decide`, no `simp` over the typeclass,
no tactics that risk axiom emission.

Wildcards (`_`) over multi-ctor enums can leak propext through the match
compiler (per `feedback_lean_zero_axiom_match.md`); this audit
verifies these instances stay axiom-clean under `#print axioms`.

Remaining D5.4 instances (TBD per-need):
* `UsageGrade` (dim 3)              — already shipped (3-element
                                       `{0, 1, ω}`)
* `EffectGrade` (dim 4)             — shipped as `GradeJoinSemilattice`
                                       over effect rows; deliberately
                                       not a semiring because join-only
                                       lattices cannot satisfy
                                       annihilation
* `LifetimeGrade` (dim 7)           — shipped as `GradeJoinSemilattice`
                                       over named-region obligation rows
* `ProvenanceGrade` (dim 8)         — shipped as `GradeJoinSemilattice`
                                       over known provenance rows plus
                                       unknown top
* `TrustGrade` (dim 9)              — shipped as 5-chain trust-debt
                                       lattice
* `RepresentationGrade` (dim 10)    — shipped as 5-chain
                                       layout-exposure lattice
* `ClockDomainGrade` (dim 12)       — shipped as `GradeJoinSemilattice`
                                       over combinational/sync(name)
                                       with conflict predicate
* `ComplexityGrade` (dim 13)        — shipped as bounded-or-unbounded
                                       cost semiring
* `PrecisionGrade` (dim 14)         — shipped as `GradeJoinSemilattice`
                                       over rational ULP-bound facts
                                       plus unbounded top
* `SpaceGrade` (dim 15)             — shipped as allocation strategy ×
                                       bounded-or-unbounded byte bound
* `OverflowGrade` (dim 16)          — shipped as `GradeJoinSemilattice`
                                       over exact/wrap/trap/saturate
                                       with explicit conflict
* `SizeGrade` (dim 20)              — shipped as bounded-or-unbounded
                                       codata observation-depth semiring
* `VersionGrade` (dim 21)           — shipped as `GradeJoinSemilattice`
                                       over version labels and adapter
                                       edges

Every declaration listed must report "does not depend on any axioms".
-/

-- D5.4 numeric-resource clean Nat lemmas
#print axioms LeanFX2.Graded.Instances.NatResource.mulRightDistribClean
#print axioms LeanFX2.Graded.Instances.NatResource.mulAssocClean

-- D5.4 Security (dim 5)
#print axioms LeanFX2.Graded.Instances.SecurityGrade
#print axioms LeanFX2.Graded.Instances.SecurityGrade.add
#print axioms LeanFX2.Graded.Instances.SecurityGrade.mul
#print axioms LeanFX2.Graded.Instances.SecurityGrade.le
#print axioms LeanFX2.Graded.Instances.instGradeSemiringSecurityGrade

-- D5.4 Observability (dim 11)
#print axioms LeanFX2.Graded.Instances.ObservabilityGrade
#print axioms LeanFX2.Graded.Instances.ObservabilityGrade.add
#print axioms LeanFX2.Graded.Instances.ObservabilityGrade.mul
#print axioms LeanFX2.Graded.Instances.ObservabilityGrade.le
#print axioms LeanFX2.Graded.Instances.instGradeSemiringObservabilityGrade

-- D5.4 Reentrancy (dim 19)
#print axioms LeanFX2.Graded.Instances.ReentrancyGrade
#print axioms LeanFX2.Graded.Instances.ReentrancyGrade.add
#print axioms LeanFX2.Graded.Instances.ReentrancyGrade.mul
#print axioms LeanFX2.Graded.Instances.ReentrancyGrade.le
#print axioms LeanFX2.Graded.Instances.instGradeSemiringReentrancyGrade

-- D5.4 FPOrder (dim 17)
#print axioms LeanFX2.Graded.Instances.FPOrderGrade
#print axioms LeanFX2.Graded.Instances.FPOrderGrade.add
#print axioms LeanFX2.Graded.Instances.FPOrderGrade.mul
#print axioms LeanFX2.Graded.Instances.FPOrderGrade.le
#print axioms LeanFX2.Graded.Instances.instGradeSemiringFPOrderGrade

-- D5.4 Mutation (dim 18, 4-chain)
#print axioms LeanFX2.Graded.Instances.MutationGrade
#print axioms LeanFX2.Graded.Instances.MutationGrade.add
#print axioms LeanFX2.Graded.Instances.MutationGrade.mul
#print axioms LeanFX2.Graded.Instances.MutationGrade.le
#print axioms LeanFX2.Graded.Instances.instGradeSemiringMutationGrade

-- D5.4 Effect (dim 4, bounded join-semilattice over effect rows)
#print axioms LeanFX2.Graded.GradeJoinSemilattice
#print axioms LeanFX2.Graded.GradeJoinSemilattice.joinAll
#print axioms LeanFX2.Graded.instGradeJoinSemilatticeUnit
#print axioms LeanFX2.Graded.Instances.EffectGrade
#print axioms LeanFX2.Graded.Instances.instGradeJoinSemilatticeEffectGrade

-- D5.4 Lifetime (dim 7, bounded join-semilattice over region rows)
#print axioms LeanFX2.Graded.Instances.LifetimeGrade
#print axioms LeanFX2.Graded.Instances.LifetimeGrade.Member
#print axioms LeanFX2.Graded.Instances.LifetimeGrade.subset
#print axioms LeanFX2.Graded.Instances.LifetimeGrade.join
#print axioms LeanFX2.Graded.Instances.LifetimeGrade.member_append_left
#print axioms LeanFX2.Graded.Instances.LifetimeGrade.member_append_right
#print axioms LeanFX2.Graded.Instances.LifetimeGrade.member_append_inv
#print axioms LeanFX2.Graded.Instances.instGradeJoinSemilatticeLifetimeGrade

-- D5.4 Provenance (dim 8, known provenance rows plus unknown top)
#print axioms LeanFX2.Graded.Instances.ProvenanceFact
#print axioms LeanFX2.Graded.Instances.ProvenanceRow
#print axioms LeanFX2.Graded.Instances.ProvenanceRow.Member
#print axioms LeanFX2.Graded.Instances.ProvenanceRow.subset
#print axioms LeanFX2.Graded.Instances.ProvenanceRow.join
#print axioms LeanFX2.Graded.Instances.ProvenanceRow.member_append_left
#print axioms LeanFX2.Graded.Instances.ProvenanceRow.member_append_right
#print axioms LeanFX2.Graded.Instances.ProvenanceRow.member_append_inv
#print axioms LeanFX2.Graded.Instances.ProvenanceGrade
#print axioms LeanFX2.Graded.Instances.ProvenanceGrade.join
#print axioms LeanFX2.Graded.Instances.ProvenanceGrade.le
#print axioms LeanFX2.Graded.Instances.instGradeJoinSemilatticeProvenanceGrade

-- D5.4 Trust (dim 9, 5-chain trust-debt lattice)
#print axioms LeanFX2.Graded.Instances.TrustGrade
#print axioms LeanFX2.Graded.Instances.TrustGrade.add
#print axioms LeanFX2.Graded.Instances.TrustGrade.mul
#print axioms LeanFX2.Graded.Instances.TrustGrade.le
#print axioms LeanFX2.Graded.Instances.instGradeSemiringTrustGrade

-- D5.4 Representation (dim 10, 5-chain layout-exposure lattice)
#print axioms LeanFX2.Graded.Instances.RepresentationGrade
#print axioms LeanFX2.Graded.Instances.RepresentationGrade.add
#print axioms LeanFX2.Graded.Instances.RepresentationGrade.mul
#print axioms LeanFX2.Graded.Instances.RepresentationGrade.le
#print axioms LeanFX2.Graded.Instances.instGradeSemiringRepresentationGrade

-- D5.4 Clock domain (dim 12, bounded join-semilattice with conflict)
#print axioms LeanFX2.Graded.Instances.ClockDomainGrade
#print axioms LeanFX2.Graded.Instances.ClockDomainGrade.Member
#print axioms LeanFX2.Graded.Instances.ClockDomainGrade.subset
#print axioms LeanFX2.Graded.Instances.ClockDomainGrade.hasConflict
#print axioms LeanFX2.Graded.Instances.ClockDomainGrade.join
#print axioms LeanFX2.Graded.Instances.ClockDomainGrade.member_append_left
#print axioms LeanFX2.Graded.Instances.ClockDomainGrade.member_append_right
#print axioms LeanFX2.Graded.Instances.ClockDomainGrade.member_append_inv
#print axioms LeanFX2.Graded.Instances.instGradeJoinSemilatticeClockDomainGrade

-- D5.4 Complexity (dim 13, bounded-or-unbounded cost semiring)
#print axioms LeanFX2.Graded.Instances.ComplexityGrade
#print axioms LeanFX2.Graded.Instances.ComplexityGrade.add
#print axioms LeanFX2.Graded.Instances.ComplexityGrade.mul
#print axioms LeanFX2.Graded.Instances.ComplexityGrade.le
#print axioms LeanFX2.Graded.Instances.instGradeSemiringComplexityGrade

-- D5.4 Precision (dim 14, rational ULP-bound facts plus unbounded top)
#print axioms LeanFX2.Graded.Instances.ULPBound
#print axioms LeanFX2.Graded.Instances.ULPBound.denominator
#print axioms LeanFX2.Graded.Instances.PrecisionFact
#print axioms LeanFX2.Graded.Instances.PrecisionRow
#print axioms LeanFX2.Graded.Instances.PrecisionRow.Member
#print axioms LeanFX2.Graded.Instances.PrecisionRow.subset
#print axioms LeanFX2.Graded.Instances.PrecisionRow.join
#print axioms LeanFX2.Graded.Instances.PrecisionRow.member_append_left
#print axioms LeanFX2.Graded.Instances.PrecisionRow.member_append_right
#print axioms LeanFX2.Graded.Instances.PrecisionRow.member_append_inv
#print axioms LeanFX2.Graded.Instances.PrecisionGrade
#print axioms LeanFX2.Graded.Instances.PrecisionGrade.join
#print axioms LeanFX2.Graded.Instances.PrecisionGrade.le
#print axioms LeanFX2.Graded.Instances.instGradeJoinSemilatticePrecisionGrade

-- D5.4 Space (dim 15, allocation strategy plus byte-bound semiring)
#print axioms LeanFX2.Graded.Instances.AllocStrategy
#print axioms LeanFX2.Graded.Instances.AllocStrategy.add
#print axioms LeanFX2.Graded.Instances.AllocStrategy.mul
#print axioms LeanFX2.Graded.Instances.AllocStrategy.le
#print axioms LeanFX2.Graded.Instances.SpaceGrade
#print axioms LeanFX2.Graded.Instances.SpaceGrade.add
#print axioms LeanFX2.Graded.Instances.SpaceGrade.mul
#print axioms LeanFX2.Graded.Instances.SpaceGrade.le
#print axioms LeanFX2.Graded.Instances.instGradeSemiringSpaceGrade

-- D5.4 Overflow (dim 16, bounded join-semilattice with conflict)
#print axioms LeanFX2.Graded.Instances.OverflowGrade
#print axioms LeanFX2.Graded.Instances.OverflowGrade.join
#print axioms LeanFX2.Graded.Instances.OverflowGrade.le
#print axioms LeanFX2.Graded.Instances.instGradeJoinSemilatticeOverflowGrade

-- D5.4 Size (dim 20, bounded-or-unbounded codata observation depth)
#print axioms LeanFX2.Graded.Instances.SizeGrade
#print axioms LeanFX2.Graded.Instances.SizeGrade.add
#print axioms LeanFX2.Graded.Instances.SizeGrade.mul
#print axioms LeanFX2.Graded.Instances.SizeGrade.le
#print axioms LeanFX2.Graded.Instances.instGradeSemiringSizeGrade

-- D5.4 Version (dim 21, bounded join-semilattice over adapter evidence)
#print axioms LeanFX2.Graded.Instances.VersionFact
#print axioms LeanFX2.Graded.Instances.VersionGrade
#print axioms LeanFX2.Graded.Instances.VersionGrade.Member
#print axioms LeanFX2.Graded.Instances.VersionGrade.subset
#print axioms LeanFX2.Graded.Instances.VersionGrade.join
#print axioms LeanFX2.Graded.Instances.VersionGrade.member_append_left
#print axioms LeanFX2.Graded.Instances.VersionGrade.member_append_right
#print axioms LeanFX2.Graded.Instances.VersionGrade.member_append_inv
#print axioms LeanFX2.Graded.Instances.instGradeJoinSemilatticeVersionGrade
