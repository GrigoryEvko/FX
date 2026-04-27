import FX.Kernel.Grade.Usage
import FX.Kernel.Grade.Security
import FX.Kernel.Grade.Trust
import FX.Kernel.Grade.Observability
import FX.Kernel.Grade.FpOrder
import FX.Kernel.Grade.Reentrancy
import FX.Kernel.Grade.Mutation
import FX.Kernel.Grade.Overflow
import FX.Kernel.Grade.Effect
import FX.Kernel.Grade.Lifetime
import FX.Kernel.Grade.Provenance
import FX.Kernel.Grade.Representation
import FX.Kernel.Grade.Clock
import FX.Kernel.Grade.Complexity
import FX.Kernel.Grade.Precision
import FX.Kernel.Grade.Space
import FX.Kernel.Grade.Size
import FX.Kernel.Grade.Protocol
import FX.Kernel.Grade.Version

/-!
# Grade (aggregator)

This file is the aggregator for the per-dimension grade modules
under `FX/Kernel/Grade/`.  Each dimension lives in its own file;
this one imports them and defines the `Grade` record plus
pointwise operations.

Phase 2.2 covers 19 of the 21 dimensions from `fx_design.md` §6.3:

Tier S (semiring, finite & fully decidable):
  * Usage         (dim 3)
  * Security      (dim 5)
  * Trust         (dim 9)
  * Observability (dim 11)
  * Overflow      (dim 16)    — Tier-S nominally; algebra is partial
  * FpOrder       (dim 17)
  * Mutation      (dim 18)
  * Reentrancy    (dim 19)

Tier S (bitmask-style):
  * Effect        (dim 4)

Tier S (with infinite data):
  * Lifetime      (dim 7)     — region variables
  * Provenance    (dim 8)
  * Complexity    (dim 13)    — declared operation-count budget (Nat, +)
  * Precision     (dim 14)    — declared ULP error bound (Nat, +)
  * Space         (dim 15)    — declared allocation budget (Nat, +)
  * Size          (dim 20)    — codata observation depth (finite n | omega)

Tier L (lattice with validity):
  * Representation (dim 10)
  * Clock          (dim 12)   — hardware clock domains; partial
                                 join on sync(a) × sync(b), a ≠ b

Tier T (protocol placeholder):
  * Protocol       (dim 6)    — coarse two-element carrier
                                 `{consumed, active}`; partial
                                 combine on mixed states.  Full
                                 session-type algebra deferred to
                                 a Phase-6 Protocol-aware typing
                                 layer.

Tier V (lattice with adapter edges):
  * Version        (dim 21)   — `Nat`-labelled version lattice
                                 with `Nat.max` combine.  Adapter
                                 graph (§15.4) sits above this
                                 kernel interface.

Deferred to later phases: Type and Refinement (Tier F, handled
by elaboration).  Precision's Phase-2 carrier is the naive ULP-
addition model per §6.3 dim 14; condition-number-aware
tightening (Higham §3.3, FPTaylor) is a future revision that
preserves the current interface.

## Partial joins

Four dimensions (Overflow, Representation, Clock, Protocol)
have **partial** parallel combine — certain pairs are invalid.
The aggregator's `add` and `mul` return `Option Grade`: `none`
when any single dimension reports invalidity.  A kernel site
encountering `none` reports the corresponding typing error
(T047 for representation, `O_mix` for overflow, `CD001` for
clock, `S004`/`S005` for protocol).
-/

namespace FX.Kernel

/--
The grade vector.  One field per Phase-1 dimension.  Ordering
chosen to group finite Tier-S dimensions first, then bitmask,
then infinite-Tier-S, then Tier-L.
-/
structure Grade where
  -- Tier S, finite
  usage         : Usage
  security      : Security
  trust         : Trust
  observability : Observability
  fpOrder       : FpOrder
  reentrancy    : Reentrancy
  mutation      : Mutation
  overflow      : Overflow
  -- Tier S, bitmask
  effect        : Effect
  -- Tier S, infinite
  lifetime      : Region
  provenance    : Provenance
  complexity    : Complexity
  precision     : Precision
  space         : Space
  size          : Size
  -- Tier L (partial ops)
  representation : Representation
  clock          : Clock
  -- Tier T (protocol placeholder; partial)
  protocol       : Protocol
  -- Tier V (version lattice)
  version        : Version
  deriving Repr

/-- `Grade` is inhabited by its `default` (most-restrictive
    every dimension).  Needed so downstream structures holding
    a `Grade` field (like `CtxEntry`) can derive their own
    `Inhabited`. -/
instance : Inhabited Grade where
  default :=
    { usage          := Usage.one
    , security       := Security.classified
    , trust          := Trust.external
    , observability  := Observability.opaq
    , fpOrder        := FpOrder.strict
    , reentrancy     := Reentrancy.nonReentrant
    , mutation       := Mutation.immutable
    , overflow       := Overflow.exact
    , effect         := Effect.tot
    , lifetime       := Region.static
    , provenance     := Provenance.unknown
    , complexity     := 0
    , precision      := 0
    , space          := 0
    , size           := Size.omega
    , representation := Representation.native
    , clock          := Clock.combinational
    , protocol       := Protocol.active
    , version        := Version.unversioned }

namespace Grade

/--
Structural equality as a `Bool`.  Field-by-field, using each
dimension's own `DecidableEq` except Provenance which has a
custom `beq` (because its `List Provenance` recursion blocks
auto-derivation).

Conversion checking (`FX/Kernel/Conversion.lean`) compares
grades via this rather than `decide (g₁ = g₂)` precisely
because `DecidableEq Grade` cannot be synthesized.
-/
def beq (leftGrade rightGrade : Grade) : Bool :=
  decide (leftGrade.usage          = rightGrade.usage)          &&
  decide (leftGrade.security       = rightGrade.security)       &&
  decide (leftGrade.trust          = rightGrade.trust)          &&
  decide (leftGrade.observability  = rightGrade.observability)  &&
  decide (leftGrade.fpOrder        = rightGrade.fpOrder)        &&
  decide (leftGrade.reentrancy     = rightGrade.reentrancy)     &&
  decide (leftGrade.mutation       = rightGrade.mutation)       &&
  decide (leftGrade.overflow       = rightGrade.overflow)       &&
  decide (leftGrade.effect         = rightGrade.effect)         &&
  decide (leftGrade.lifetime       = rightGrade.lifetime)       &&
  Provenance.beq leftGrade.provenance rightGrade.provenance     &&
  decide (leftGrade.complexity     = rightGrade.complexity)     &&
  decide (leftGrade.precision      = rightGrade.precision)      &&
  decide (leftGrade.space          = rightGrade.space)          &&
  decide (leftGrade.size           = rightGrade.size)           &&
  decide (leftGrade.representation = rightGrade.representation) &&
  decide (leftGrade.clock          = rightGrade.clock)          &&
  decide (leftGrade.protocol       = rightGrade.protocol)       &&
  decide (leftGrade.version        = rightGrade.version)

instance : BEq Grade := ⟨beq⟩

/--
The default grade: most restrictive every dimension.  Matches
the §1.2 design principle "deny by default, grant by permission".

  * usage = 1 (linear, default mode)
  * security = classified (default)
  * trust = external (no proof yet)
  * observability = opaq (CT-safe by default)
  * fpOrder = strict
  * reentrancy = nonReentrant
  * mutation = immutable
  * overflow = exact (must prove no overflow)
  * effect = tot (no side effects)
  * lifetime = static (permanent — safest default)
  * provenance = unknown (until elaborator classifies)
  * precision = 0 (exact — no declared FP error budget)
  * representation = native (compiler chooses)
-/
def default : Grade :=
  { usage          := Usage.one
  , security       := Security.classified
  , trust          := Trust.external
  , observability  := Observability.opaq
  , fpOrder        := FpOrder.strict
  , reentrancy     := Reentrancy.nonReentrant
  , mutation       := Mutation.immutable
  , overflow       := Overflow.exact
  , effect         := Effect.tot
  , lifetime       := Region.static
  , provenance     := Provenance.unknown
  , complexity     := 0
  , precision      := 0
  , space          := 0
  , size           := Size.omega
  , representation := Representation.native
  , clock          := Clock.combinational
  , protocol       := Protocol.active
  , version        := Version.unversioned }

/--
The "ghost everywhere" grade: erased dimension-wise.  Useful for
compile-time-only bindings the kernel knows carry no runtime
state.
-/
def ghost : Grade :=
  { default with usage := Usage.zero }

/--
The "shared borrow" grade — `Usage.omega` on a binder that may
be referenced multiple times in the body.  Other dimensions stay
at their defaults so the grade vector still carries the full
21-dim picture (classified-by-default security, strict FP order,
etc.).

Surface-syntax origin: the elaborator's `modeToGrade` maps both
`ref x: T` (§7.1 shared borrow, duplicable) and `affine x: T`
(§7.4 at-most-once, drop permitted) to this grade.  Affine's ≤1
semantics is safely over-approximated by ω: permitting extra
uses never rejects a valid affine program; tightening to a
proper `≤ 1` lattice element is a follow-up once the Usage
semiring grows a fourth atom.
-/
def shared : Grade :=
  { default with usage := Usage.omega }

/-!
## Pointwise operations

Parallel combine (`add`) and sequential combine (`mul`) are
pointwise lifts of each dimension's operation.  Where the
dimension's operation is partial (Overflow, Representation,
Clock), the lift returns `Option Grade`; we use an `Option`
monad pattern to short-circuit the whole grade as invalid if
any single dimension rejects.
-/

/--
Pointwise parallel combine.  Returns `none` on any partial-dim
failure.
-/
def add (leftGrade rightGrade : Grade) : Option Grade := do
  let combinedOverflow       ← Overflow.add leftGrade.overflow rightGrade.overflow
  let combinedRepresentation ← Representation.add leftGrade.representation rightGrade.representation
  let combinedClock          ← Clock.add leftGrade.clock rightGrade.clock
  let combinedProtocol       ← Protocol.add leftGrade.protocol rightGrade.protocol
  pure
    { usage         := Usage.add         leftGrade.usage         rightGrade.usage
    , security      := Security.add      leftGrade.security      rightGrade.security
    , trust         := Trust.add         leftGrade.trust         rightGrade.trust
    , observability := Observability.add leftGrade.observability rightGrade.observability
    , fpOrder       := FpOrder.add       leftGrade.fpOrder       rightGrade.fpOrder
    , reentrancy    := Reentrancy.add    leftGrade.reentrancy    rightGrade.reentrancy
    , mutation      := Mutation.add      leftGrade.mutation      rightGrade.mutation
    , overflow      := combinedOverflow
    , effect        := Effect.add        leftGrade.effect        rightGrade.effect
    , lifetime      := Region.add        leftGrade.lifetime      rightGrade.lifetime
    , provenance    := Provenance.add    leftGrade.provenance    rightGrade.provenance
    , complexity    := Complexity.add    leftGrade.complexity    rightGrade.complexity
    , precision     := Precision.add     leftGrade.precision     rightGrade.precision
    , space         := Space.add         leftGrade.space         rightGrade.space
    , size          := Size.add          leftGrade.size          rightGrade.size
    , representation := combinedRepresentation
    , clock         := combinedClock
    , protocol      := combinedProtocol
    , version       := Version.add       leftGrade.version       rightGrade.version }

/-- Pointwise sequential combine. -/
def mul (leftGrade rightGrade : Grade) : Option Grade := do
  let combinedOverflow       ← Overflow.mul leftGrade.overflow rightGrade.overflow
  let combinedRepresentation ← Representation.mul leftGrade.representation rightGrade.representation
  let combinedClock          ← Clock.mul leftGrade.clock rightGrade.clock
  let combinedProtocol       ← Protocol.mul leftGrade.protocol rightGrade.protocol
  pure
    { usage         := Usage.mul         leftGrade.usage         rightGrade.usage
    , security      := Security.mul      leftGrade.security      rightGrade.security
    , trust         := Trust.mul         leftGrade.trust         rightGrade.trust
    , observability := Observability.mul leftGrade.observability rightGrade.observability
    , fpOrder       := FpOrder.mul       leftGrade.fpOrder       rightGrade.fpOrder
    , reentrancy    := Reentrancy.mul    leftGrade.reentrancy    rightGrade.reentrancy
    , mutation      := Mutation.mul      leftGrade.mutation      rightGrade.mutation
    , overflow      := combinedOverflow
    , effect        := Effect.mul        leftGrade.effect        rightGrade.effect
    , lifetime      := Region.mul        leftGrade.lifetime      rightGrade.lifetime
    , provenance    := Provenance.mul    leftGrade.provenance    rightGrade.provenance
    , complexity    := Complexity.mul    leftGrade.complexity    rightGrade.complexity
    , precision     := Precision.mul     leftGrade.precision     rightGrade.precision
    , space         := Space.mul         leftGrade.space         rightGrade.space
    , size          := Size.mul          leftGrade.size          rightGrade.size
    , representation := combinedRepresentation
    , clock         := combinedClock
    , protocol      := combinedProtocol
    , version       := Version.mul       leftGrade.version       rightGrade.version }

/--
Wood-Atkey division, applied in the Usage dimension only.

The Pi-intro rule uses context division `context / g` where the
scaling is by the binder's **usage** grade, not the whole grade
vector.  Other dimensions compose pointwise but do not divide in
the Wood-Atkey sense.  We expose `div` as a unary scaling of a
grade by a Usage factor, matching how it is used in `Typing.lean`.
-/
def divByUsage (grade : Grade) (usageDivisor : Usage) : Grade :=
  { grade with usage := Usage.div grade.usage usageDivisor }

/--
Pointwise subsumption.  `g1 ≤ g2` iff every dimension is `≤`
pointwise.  The three partial-operation dimensions are not
special here — subsumption is total on each carrier, the partial
behavior lives only in `add`/`mul`.
-/
def LessEq (leftGrade rightGrade : Grade) : Prop :=
  leftGrade.usage         ≤ rightGrade.usage         ∧
  leftGrade.security      ≤ rightGrade.security      ∧
  leftGrade.trust         ≤ rightGrade.trust         ∧
  leftGrade.observability ≤ rightGrade.observability ∧
  leftGrade.fpOrder       ≤ rightGrade.fpOrder       ∧
  leftGrade.reentrancy    ≤ rightGrade.reentrancy    ∧
  leftGrade.mutation      ≤ rightGrade.mutation      ∧
  leftGrade.overflow      ≤ rightGrade.overflow      ∧
  leftGrade.effect        ≤ rightGrade.effect        ∧
  leftGrade.lifetime      ≤ rightGrade.lifetime      ∧
  leftGrade.provenance    ≤ rightGrade.provenance    ∧
  leftGrade.complexity    ≤ rightGrade.complexity    ∧
  leftGrade.precision     ≤ rightGrade.precision     ∧
  leftGrade.space         ≤ rightGrade.space         ∧
  leftGrade.size          ≤ rightGrade.size          ∧
  leftGrade.representation ≤ rightGrade.representation ∧
  leftGrade.clock         ≤ rightGrade.clock         ∧
  leftGrade.protocol      ≤ rightGrade.protocol      ∧
  leftGrade.version       ≤ rightGrade.version

instance : LE Grade := ⟨LessEq⟩

theorem LessEq.refl (grade : Grade) : grade ≤ grade :=
  ⟨ Usage.LessEq.refl _, Security.LessEq.refl _, Trust.LessEq.refl _
  , Observability.LessEq.refl _, FpOrder.LessEq.refl _, Reentrancy.LessEq.refl _
  , Mutation.LessEq.refl _, Overflow.LessEq.refl _, Effect.LessEq.refl _
  , Region.LessEq.refl _, Provenance.LessEq.refl _
  , Complexity.LessEq.refl _, Precision.LessEq.refl _
  , Space.LessEq.refl _, Size.LessEq.refl _
  , Representation.LessEq.refl _, Clock.LessEq.refl _
  , Protocol.LessEq.refl _, Version.LessEq.refl _ ⟩

theorem LessEq.trans {lowerGrade middleGrade upperGrade : Grade}
    (lowerLeMiddle : lowerGrade ≤ middleGrade)
    (middleLeUpper : middleGrade ≤ upperGrade) :
    lowerGrade ≤ upperGrade :=
  let ⟨usageLow, securityLow, trustLow, observabilityLow, fpOrderLow,
       reentrancyLow, mutationLow, overflowLow, effectLow, lifetimeLow,
       provenanceLow, complexityLow, precisionLow, spaceLow, sizeLow,
       representationLow, clockLow, protocolLow, versionLow⟩ := lowerLeMiddle
  let ⟨usageHigh, securityHigh, trustHigh, observabilityHigh, fpOrderHigh,
       reentrancyHigh, mutationHigh, overflowHigh, effectHigh, lifetimeHigh,
       provenanceHigh, complexityHigh, precisionHigh, spaceHigh, sizeHigh,
       representationHigh, clockHigh, protocolHigh, versionHigh⟩ := middleLeUpper
  ⟨ Usage.LessEq.trans usageLow usageHigh
  , Security.LessEq.trans securityLow securityHigh
  , Trust.LessEq.trans trustLow trustHigh
  , Observability.LessEq.trans observabilityLow observabilityHigh
  , FpOrder.LessEq.trans fpOrderLow fpOrderHigh
  , Reentrancy.LessEq.trans reentrancyLow reentrancyHigh
  , Mutation.LessEq.trans mutationLow mutationHigh
  , Overflow.LessEq.trans overflowLow overflowHigh
  , Effect.LessEq.trans effectLow effectHigh
  , Region.LessEq.trans lifetimeLow lifetimeHigh
  , Provenance.LessEq.trans provenanceLow provenanceHigh
  , Complexity.LessEq.trans complexityLow complexityHigh
  , Precision.LessEq.trans precisionLow precisionHigh
  , Space.LessEq.trans spaceLow spaceHigh
  , Size.LessEq.trans sizeLow sizeHigh
  , Representation.LessEq.trans representationLow representationHigh
  , Clock.LessEq.trans clockLow clockHigh
  , Protocol.LessEq.trans protocolLow protocolHigh
  , Version.LessEq.trans versionLow versionHigh ⟩

/-!
## Aggregator-level semiring laws (Q48)

Per-dimension semiring laws in `FX/Kernel/Grade/*.lean` lift
pointwise to the full `Grade` vector subject to two caveats:

 1. **Partial dimensions** (Overflow, Representation, Clock,
    Protocol) may reject some combinations — `add`/`mul` return
    `Option Grade`.  The laws respect this: if either side
    fails, the other does too under the same operation.

 2. **Provenance is intentionally non-commutative** — its `add`
    aggregates into a list `[a, b]` vs `[b, a]`, which are
    structurally different (see `FX/Kernel/Grade/Provenance.lean`
    module docstring).  Elaborator-level normalization flattens
    this post-hoc; the kernel algebra stays structural.  So
    aggregate `add_comm` only holds when the two grades AGREE
    on provenance; we state this as a conditional theorem.

These theorems form the trusted-base contract that downstream
proofs consume.
-/

/-- Conditional commutativity: when two grades agree on their
    provenance component, their `add` is commutative.  The
    non-commutative Provenance.add is the only obstacle in the
    general case (documented in its module); every other
    dimension has unconditional `add_comm`. -/
theorem add_comm_of_same_provenance (leftGrade rightGrade : Grade)
    (provenanceAgree : leftGrade.provenance = rightGrade.provenance) :
    Grade.add leftGrade rightGrade = Grade.add rightGrade leftGrade := by
  simp only [Grade.add]
  rw [Overflow.add_comm, Representation.add_comm,
      Clock.add_comm, Protocol.add_comm]
  cases Overflow.add rightGrade.overflow leftGrade.overflow <;>
  cases Representation.add rightGrade.representation leftGrade.representation <;>
  cases Clock.add rightGrade.clock leftGrade.clock <;>
  cases Protocol.add rightGrade.protocol leftGrade.protocol <;>
    simp [Usage.add_comm, Security.add_comm, Trust.add_comm,
          Observability.add_comm, FpOrder.add_comm, Reentrancy.add_comm,
          Mutation.add_comm, Effect.add_comm, Region.add_comm,
          Complexity.add_comm, Precision.add_comm, Space.add_comm,
          Size.add_comm, Version.add_comm, provenanceAgree]

/-- Conditional commutativity for sequential combine.  Mirror of
    `add_comm_of_same_provenance`: when two grades agree on their
    provenance component, their `mul` is commutative.  Every
    non-Provenance dim has a named `mul_comm` theorem (landed by
    Q48/T7; the Nat-arithmetic dims Complexity/Precision/Space
    gained theirs in T9 as uniform re-exports of `Nat.add_comm`),
    so the proof follows exactly the `add_comm` shape: rewrite
    each partial-op's mul comm, case-split on the four
    `Option`-valued partial operations, then `simp` with
    unconditional per-dim mul comm lemmas.

    Tier-architecture correspondence (T9): each referenced
    `Dim.mul_comm` is the witness the dim's tier instance provides
    as its `mul_comm` field.  This proof retrieves them by name
    for compactness; consumers that want instance-based dispatch
    call `TierSComm.mul_comm'` through `inferInstance`. -/
theorem mul_comm_of_same_provenance (leftGrade rightGrade : Grade)
    (provenanceAgree : leftGrade.provenance = rightGrade.provenance) :
    Grade.mul leftGrade rightGrade = Grade.mul rightGrade leftGrade := by
  simp only [Grade.mul]
  rw [Overflow.mul_comm, Representation.mul_comm,
      Clock.mul_comm, Protocol.mul_comm]
  cases Overflow.mul rightGrade.overflow leftGrade.overflow <;>
  cases Representation.mul rightGrade.representation leftGrade.representation <;>
  cases Clock.mul rightGrade.clock leftGrade.clock <;>
  cases Protocol.mul rightGrade.protocol leftGrade.protocol <;>
    simp [Usage.mul_comm, Security.mul_comm, Trust.mul_comm,
          Observability.mul_comm, FpOrder.mul_comm, Reentrancy.mul_comm,
          Mutation.mul_comm, Effect.mul_comm, Region.mul_comm,
          Complexity.mul_comm, Precision.mul_comm, Space.mul_comm,
          Size.mul_comm, Version.mul_comm, provenanceAgree]

end Grade

end FX.Kernel
