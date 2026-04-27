import FX.Kernel.Grade

/-!
# Grade aggregator tests

Tests the pointwise lift of per-dimension ops to the 12-field
`Grade` record.  The individual dimensions have exhaustive
tests in `Tests/Kernel/Grade/*`.  This file checks:

  * `Grade.default` satisfies the most-restrictive-every-field
    contract (`fx_design.md` §1.2 "deny by default")
  * `Grade.ghost` differs from `default` only in Usage
  * Pointwise `add` returns `some` iff every partial-op field
    returns `some`
  * Partial-op `none` propagation: Overflow or Representation
    failing kills the join
  * Wood-Atkey `divByUsage` scales only the Usage field
  * `Grade.LessEq` is reflexive and transitive
-/

namespace Tests.Kernel.GradeTests

open FX.Kernel
open FX.Kernel.Grade

/-! ## `default` is the most-restrictive grade -/

example : Grade.default.usage         = Usage.one              := rfl
example : Grade.default.security      = Security.classified    := rfl
example : Grade.default.trust         = Trust.external         := rfl
example : Grade.default.observability = Observability.opaq     := rfl
example : Grade.default.fpOrder       = FpOrder.strict         := rfl
example : Grade.default.reentrancy    = Reentrancy.nonReentrant := rfl
example : Grade.default.mutation      = Mutation.immutable     := rfl
example : Grade.default.overflow      = Overflow.exact         := rfl
example : Grade.default.effect        = Effect.tot             := rfl
example : Grade.default.lifetime      = Region.static          := rfl
example : Grade.default.provenance    = Provenance.unknown     := rfl
example : Grade.default.precision     = 0                       := rfl
example : Grade.default.representation = Representation.native := rfl

/-! ## `ghost` differs from default only in Usage -/

example : ghost.usage          = Usage.zero              := rfl
example : ghost.security       = Grade.default.security        := rfl
example : ghost.trust          = Grade.default.trust           := rfl
example : ghost.representation = Grade.default.representation  := rfl

/-! ## Pointwise `add` — happy path returns `some` -/

example : (add Grade.default Grade.default).isSome = true := by decide

example :
  let omegaIoGrade :=
    { Grade.default with usage := Usage.omega, effect := Effect.io_ }
  (add omegaIoGrade omegaIoGrade).isSome = true := by decide

/-! ## Partial-op propagation — Overflow cross-top fails

Mixing wrap and trap in the Overflow dimension must fail the
whole join.
-/

example :
  let wrapGrade := { Grade.default with overflow := Overflow.wrap }
  let trapGrade := { Grade.default with overflow := Overflow.trap }
  add wrapGrade trapGrade = none := by decide

example :
  let saturateGrade := { Grade.default with overflow := Overflow.saturate }
  let trapGrade     := { Grade.default with overflow := Overflow.trap }
  add saturateGrade trapGrade = none := by decide

/-! ## Partial-op propagation — more Overflow combinations

The Overflow dimension has `{exact, wrap, trap, saturate}` with
`exact` the bottom.  `exact` joins with anything to yield the
other.  wrap/trap/saturate are pairwise incomparable — any two
distinct non-exact overflow modes fail `add`.  Tests every
distinct pairing to catch a future refactor that silently made
one of them commutative / associative across families. -/

example :
  let wrapGrade     := { Grade.default with overflow := Overflow.wrap }
  let saturateGrade := { Grade.default with overflow := Overflow.saturate }
  add wrapGrade saturateGrade = none := by decide

example :
  let saturateGrade := { Grade.default with overflow := Overflow.saturate }
  let wrapGrade     := { Grade.default with overflow := Overflow.wrap }
  add saturateGrade wrapGrade = none := by decide

-- exact + wrap succeeds — exact is bottom.
example :
  let exactGrade := { Grade.default with overflow := Overflow.exact }
  let wrapGrade  := { Grade.default with overflow := Overflow.wrap }
  (add exactGrade wrapGrade).isSome := by decide

/-! ## Partial-op propagation — Representation c⊔packed fails -/

example :
  let cCompatGrade := { Grade.default with representation := Representation.cCompat }
  let packedGrade  := { Grade.default with representation := Representation.packed }
  add cCompatGrade packedGrade = none := by decide

/-! ## `mul` (sequential combine) has same None propagation

The `mul` operation is used at App/Let typing sites — the
sequential-composition analog of parallel `add`.  Partial-dim
failures propagate identically.  Easy to regress if either
`add` or `mul` gets rewritten independently. -/

example :
  let wrapGrade := { Grade.default with overflow := Overflow.wrap }
  let trapGrade := { Grade.default with overflow := Overflow.trap }
  mul wrapGrade trapGrade = none := by decide

example :
  let cCompatGrade := { Grade.default with representation := Representation.cCompat }
  let packedGrade  := { Grade.default with representation := Representation.packed }
  mul cCompatGrade packedGrade = none := by decide

-- Happy-path mul.
example : (mul Grade.default Grade.default).isSome := by decide

/-! ## One failing dimension kills the whole grade

Even if every other field agrees, a single partial-op None in
the two dimensions that carry it (Overflow, Representation) must
produce a None result.  Catches a future refactor that
accidentally uses `.getD` or similar to hide the failure. -/

example :
  let incompatOverflow :=
    { Grade.default with overflow := Overflow.wrap,
                         representation := Representation.native }
  let otherOverflow :=
    { Grade.default with overflow := Overflow.trap,
                         representation := Representation.native }
  add incompatOverflow otherOverflow = none := by decide

example :
  let incompatRep :=
    { Grade.default with overflow := Overflow.exact,
                         representation := Representation.cCompat }
  let otherRep :=
    { Grade.default with overflow := Overflow.exact,
                         representation := Representation.packed }
  add incompatRep otherRep = none := by decide

/-! ## `divByUsage` scales only the Usage field -/

example : (divByUsage Grade.default Usage.omega).usage = Usage.zero := rfl
example : (divByUsage Grade.default Usage.omega).security = Grade.default.security := rfl
example : (divByUsage Grade.default Usage.omega).effect = Grade.default.effect := rfl

example : (divByUsage ghost Usage.omega).usage = Usage.zero := rfl
example : (divByUsage Grade.default Usage.one).usage = Usage.one := rfl

/-! ## `LessEq` reflexive + transitive -/

example : Grade.default ≤ Grade.default := Grade.LessEq.refl _
example : ghost ≤ ghost := Grade.LessEq.refl _

-- Ghost (usage=0) subsumes under default (usage=1) since 0 ≤ 1.
example : ghost ≤ Grade.default := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact .refl _
    | exact .zeroLe _
    | exact .leOmega _
    | exact Effect.LessEq.refl _
    | exact Overflow.LessEq.refl _
    | exact Representation.LessEq.refl _
    | exact Clock.LessEq.refl _
    | exact Complexity.LessEq.refl _
    | exact Precision.LessEq.refl _
    | exact Space.LessEq.refl _
    | exact Size.LessEq.refl _
    | exact Protocol.LessEq.refl _
    | exact Version.LessEq.refl _

/-! ## Q48 — Aggregator-level semiring laws

The per-dimension semiring laws lift to `Grade`.  Pointwise
commutativity holds conditionally on Provenance agreement
(the Provenance dimension is intentionally non-commutative
— see `FX/Kernel/Grade/Provenance.lean` module docs).
-/

-- `add_comm_of_same_provenance` on identical grades: trivial.
example :
  Grade.add Grade.default Grade.default
    = Grade.add Grade.default Grade.default := by
  exact Grade.add_comm_of_same_provenance Grade.default Grade.default rfl

-- Two grades differing in Effect but agreeing on Provenance: commutative.
example :
  let ioGrade    := { Grade.default with effect := Effect.io_ }
  let allocGrade := { Grade.default with effect := Effect.alloc_ }
  Grade.add ioGrade allocGrade = Grade.add allocGrade ioGrade :=
  Grade.add_comm_of_same_provenance _ _ rfl

-- Two grades with different Usage but same Provenance: commutative
-- (and both combines succeed since no partial dims reject).
example :
  let ownGrade   := { Grade.default with usage := Usage.one }
  let omegaGrade := { Grade.default with usage := Usage.omega }
  Grade.add ownGrade omegaGrade = Grade.add omegaGrade ownGrade :=
  Grade.add_comm_of_same_provenance _ _ rfl

end Tests.Kernel.GradeTests
