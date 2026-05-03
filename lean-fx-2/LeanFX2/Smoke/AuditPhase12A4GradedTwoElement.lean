import LeanFX2.Graded.Instances.Security
import LeanFX2.Graded.Instances.Observability
import LeanFX2.Graded.Instances.Reentrancy
import LeanFX2.Graded.Instances.FPOrder

/-! # AuditPhase12A4SecurityGrade — D5.4 partial: 2-element graded
semiring instances.

Phase 12.A.4 partial closure for D5.4 (21 graded semiring instances).
This commit ships four canonical 2-element Boolean-algebra
instances:

* `SecurityGrade`        (dim 5)  — `unclassified < classified`
* `ObservabilityGrade`   (dim 11) — `opaque < transparent`
* `ReentrancyGrade`      (dim 19) — `nonReentrant < reentrant`
* `FPOrderGrade`         (dim 17) — `strict < reassociate`

Each follows the canonical 2-element Boolean-algebra encoding:
* `+` = lattice join (∨)            — combining accumulates
* `*` = lattice meet (∧)            — scaling annihilates with `0`
* `0` = lattice bottom              — additive identity
* `1` = lattice top                 — multiplicative identity
* `≤` = `bottom ≤ top` only         — uni-directional subsumption

All 17 GradeSemiring laws (3 add-monoid + 2 mul-monoid + 2 distrib +
2 annihilation + 2 preorder + 2 monotonicity + 4 identity refl)
discharged by full case enumeration (2-, 4-, or 8-case `match`)
over the closed 2-element inductive — no `decide`, no `simp` over
the typeclass, no tactics that risk axiom emission.

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
* `TrustGrade` (dim 9)              — 5-element chain
                                       `Verified > ... > External`
* `RepresentationGrade` (dim 10)    — preorder over layout attrs
* `ClockDomainGrade` (dim 12)       — `combinational + sync(c)`
                                       partial structure
* `ComplexityGrade` (dim 13)        — Nat (real semiring)
* `PrecisionGrade` (dim 14)         — Rat (sum-monoid)
* `SpaceGrade` (dim 15)             — Nat (like Complexity)
* `OverflowGrade` (dim 16)          — `{exact, wrap, trap, sat}`
                                       partial lattice
* `MutationGrade` (dim 18)          — 4-chain
                                       `immutable < append_only <
                                       monotonic < read_write`
* `SizeGrade` (dim 20)              — codata observation depth
* `VersionGrade` (dim 21)           — version-label lattice with
                                       adapter edges

Every declaration listed must report "does not depend on any axioms".
-/

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
