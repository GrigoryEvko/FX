import FX.Kernel.Grade

/-!
# Tier class instance resolution tests (T7/T8)

Compile-time checks that every grade dim's tier-class membership
resolves correctly and that the tier-generic theorems in
`FX/Kernel/Grade/Tier.lean` actually fire over the concrete
instances.

A failed test here is a build failure — the tier class abstraction
is either broken (an instance doesn't actually satisfy the class
laws it claims) or the generic theorem wasn't specialized to the
concrete type at resolution time.  Either failure is a silent
correctness hole that this file guards against.

Covers §6.3's tier taxonomy as reified in `Tier.lean`:

  * TierSRing → Usage only (strict commutative semiring with
    annihilation).
  * TierSIdem → 7 dims (Effect, Security, Trust, Observability,
    FpOrder, Mutation, Reentrancy).
  * TierSComm → 4 dims (Complexity, Precision, Space, Size) plus
    all TierSIdem/TierSRing by inheritance.
  * TierS → all of TierSComm plus Provenance would live here if
    Phase-1 gave it commutative add (it doesn't — Provenance
    instances GradeCarrier only, and that's documented in T6a).
  * TierL → 3 dims (Representation, Clock, Overflow-reclassified).
  * TierT → Protocol.
  * TierV → Version.
-/

namespace Tests.Kernel.Grade.Tier

open FX.Kernel

/-! ## Tier-class resolution

Each `example` below asks Lean to resolve the stated tier-class
instance for the named carrier.  If the instance chain is broken
— e.g., an extends relation fails, or a required field is missing
— the example fails to elaborate and the file fails to build.
The presence of each line is the test. -/

example : TierSRing Usage          := inferInstance

example : TierSIdem Effect         := inferInstance
example : TierSIdem Security       := inferInstance
example : TierSIdem Trust          := inferInstance
example : TierSIdem Observability  := inferInstance
example : TierSIdem FpOrder        := inferInstance
example : TierSIdem Mutation       := inferInstance
example : TierSIdem Reentrancy     := inferInstance

example : TierSComm Complexity     := inferInstance
example : TierSComm Precision      := inferInstance
example : TierSComm Space          := inferInstance
example : TierSComm Size           := inferInstance

example : TierL Representation     := inferInstance
example : TierL Clock              := inferInstance
example : TierL Overflow           := inferInstance

example : TierT Protocol           := inferInstance

example : TierV Version            := inferInstance

example : GradeCarrier Provenance  := inferInstance
example : GradeCarrier Region      := inferInstance

/-! ## Inheritance chain sanity

`TierSRing ⊂ TierSComm ⊂ TierS ⊂ GradeCarrier`.  Each containment
is checked via `inferInstance` — if Lean can resolve a weaker class
from a stronger one, the `extends` relation is intact. -/

example : TierSComm  Usage := inferInstance
example : TierS      Usage := inferInstance
example : GradeCarrier Usage := inferInstance

example : TierSComm  Effect := inferInstance
example : TierS      Effect := inferInstance
example : GradeCarrier Effect := inferInstance

example : TierS      Complexity := inferInstance
example : GradeCarrier Complexity := inferInstance

/-! ## Tier-generic theorems fire on concrete instances

Each example specializes a generic theorem from `Tier.lean` to a
concrete dim.  If the tier-generic machinery is intact, these
proofs go through with zero per-dim case analysis.  Conversely, if
a generic theorem depends on a law the instance doesn't provide,
the proof fails at elaboration.

`TierSIdem.mul_idem` via Security — tests the idempotent path. -/
example : (inferInstance : TierSIdem Security).mul Security.classified Security.classified
        = Security.classified :=
  TierSIdem.mul_idem Security.classified

/-- `TierSIdem.mul_idem` via Mutation — tests the 4-element lattice. -/
example : (inferInstance : TierSIdem Mutation).mul Mutation.readWrite Mutation.readWrite
        = Mutation.readWrite :=
  TierSIdem.mul_idem Mutation.readWrite

/-- `TierSIdem.mul_eq_add'` via Effect — witnesses that for join-
    lattice dims, `mul` and `add` are truly the same operation. -/
example : (inferInstance : TierSIdem Effect).mul Effect.io_ Effect.io_
        = (inferInstance : TierSIdem Effect).add Effect.io_ Effect.io_ :=
  TierSIdem.mul_eq_add' Effect.io_ Effect.io_

/-- `TierSRing.zero_mul_zero` via Usage — the ONLY dim that satisfies
    strict zero annihilation per the T6a audit. -/
example : (inferInstance : TierSRing Usage).mul Usage.zero Usage.zero
        = Usage.zero :=
  TierSRing.zero_mul_zero

/-- `TierSRing.zero_mul_add` via Usage — distribution composed with
    annihilation.  `0 * (b + c) = 0` holds iff the instance
    provides BOTH left_distrib AND zero_mul — which is exactly
    what TierSRing demands. -/
example : (inferInstance : TierSRing Usage).mul Usage.zero
            ((inferInstance : TierSRing Usage).add Usage.one Usage.omega)
        = Usage.zero :=
  TierSRing.zero_mul_add Usage.one Usage.omega

/-- `TierSComm.mul_add_comm` via Complexity — the Nat-arithmetic
    sanity-check: `mul (add a b) c = mul c (add a b)` via
    `mul_comm` inherited through TierSComm. -/
example : (inferInstance : TierSComm Complexity).mul
            ((inferInstance : TierSComm Complexity).add 3 4) 5
        = (inferInstance : TierSComm Complexity).mul 5
            ((inferInstance : TierSComm Complexity).add 3 4) :=
  TierSComm.mul_add_comm 3 4 5

/-! ## Aggregate Grade theorem (T7 core)

`mul_comm_of_same_provenance` is the aggregate counterpart to the
existing `add_comm_of_same_provenance`.  Together they prove
conditional commutativity on the full 21-dim vector. -/

/-- Two identical grades trivially commute under `Grade.mul`. -/
example : Grade.mul Grade.default Grade.default
        = Grade.mul Grade.default Grade.default := rfl

/-- Symmetric form: `mul g g = mul g g` via the aggregate theorem. -/
example (grade : Grade) : Grade.mul grade grade = Grade.mul grade grade :=
  Grade.mul_comm_of_same_provenance grade grade rfl

end Tests.Kernel.Grade.Tier
