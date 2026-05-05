import LeanFX2.Graded.Instances.Security
import LeanFX2.Graded.Instances.Observability
import LeanFX2.Graded.Instances.Reentrancy
import LeanFX2.Graded.Instances.FPOrder
import LeanFX2.Graded.Instances.Mutation
import LeanFX2.Graded.Instances.NatResource
import LeanFX2.Graded.Instances.Trust
import LeanFX2.Graded.Instances.Complexity
import LeanFX2.Graded.Instances.Space
import LeanFX2.Graded.Instances.Size

/-! # AuditPhase12A4GradedTwoElement — D5.4 partial: graded semiring
instances along chains of size 2 and 4.

Phase 12.A.4 partial closure for D5.4 (21 graded semiring instances).
This commit ships five canonical chain instances:

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

Wildcards (`_`) over multi-ctor enums leak propext through the match
compiler (per `feedback_lean_zero_axiom_match.md`); this audit
verifies all five instances pass the strict no-wildcards discipline.

Remaining D5.4 instances (TBD per-need):
* `UsageGrade` (dim 3)              — already shipped (3-element
                                       `{0, 1, ω}`)
* `EffectGrade` (dim 4)             — needs `GradeJoinSemilattice`
                                       since join-only lattices
                                       cannot be GradeSemirings with
                                       annihilation (`+ = * = ∨`
                                       breaks `mul_zero_left`)
* `LifetimeGrade` (dim 7)           — region-variable preorder
* `ProvenanceGrade` (dim 8)         — origin-label lattice
* `TrustGrade` (dim 9)              — shipped as 5-chain trust-debt
                                       lattice
* `RepresentationGrade` (dim 10)    — preorder over layout attrs
* `ClockDomainGrade` (dim 12)       — `combinational + sync(c)`
                                       partial structure
* `ComplexityGrade` (dim 13)        — shipped as a `Nat`-backed
                                       real semiring
* `PrecisionGrade` (dim 14)         — Rat (sum-monoid)
* `SpaceGrade` (dim 15)             — shipped as a `Nat`-backed
                                       real semiring
* `OverflowGrade` (dim 16)          — `{exact, wrap, trap, sat}`
                                       partial lattice
* `SizeGrade` (dim 20)              — shipped as a `Nat`-backed
                                       codata observation-depth
                                       semiring
* `VersionGrade` (dim 21)           — version-label lattice with
                                       adapter edges

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

-- D5.4 Trust (dim 9, 5-chain trust-debt lattice)
#print axioms LeanFX2.Graded.Instances.TrustGrade
#print axioms LeanFX2.Graded.Instances.TrustGrade.add
#print axioms LeanFX2.Graded.Instances.TrustGrade.mul
#print axioms LeanFX2.Graded.Instances.TrustGrade.le
#print axioms LeanFX2.Graded.Instances.instGradeSemiringTrustGrade

-- D5.4 Complexity (dim 13, Nat-backed semiring)
#print axioms LeanFX2.Graded.Instances.ComplexityGrade
#print axioms LeanFX2.Graded.Instances.ComplexityGrade.add
#print axioms LeanFX2.Graded.Instances.ComplexityGrade.mul
#print axioms LeanFX2.Graded.Instances.ComplexityGrade.le
#print axioms LeanFX2.Graded.Instances.instGradeSemiringComplexityGrade

-- D5.4 Space (dim 15, Nat-backed semiring)
#print axioms LeanFX2.Graded.Instances.SpaceGrade
#print axioms LeanFX2.Graded.Instances.SpaceGrade.add
#print axioms LeanFX2.Graded.Instances.SpaceGrade.mul
#print axioms LeanFX2.Graded.Instances.SpaceGrade.le
#print axioms LeanFX2.Graded.Instances.instGradeSemiringSpaceGrade

-- D5.4 Size (dim 20, Nat-backed codata observation depth)
#print axioms LeanFX2.Graded.Instances.SizeGrade
#print axioms LeanFX2.Graded.Instances.SizeGrade.add
#print axioms LeanFX2.Graded.Instances.SizeGrade.mul
#print axioms LeanFX2.Graded.Instances.SizeGrade.le
#print axioms LeanFX2.Graded.Instances.instGradeSemiringSizeGrade
