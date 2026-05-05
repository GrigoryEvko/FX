import LeanFX2.Graded.GradeVector
import LeanFX2.Graded.Instances.Usage
import LeanFX2.Graded.Instances.Effect
import LeanFX2.Graded.Instances.Security
import LeanFX2.Graded.Instances.Observability
import LeanFX2.Graded.Instances.Reentrancy
import LeanFX2.Graded.Instances.FPOrder
import LeanFX2.Graded.Instances.Mutation
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

/-! # Graded/Dimensions21 — honest registry for FX's 21 dimensions

This module is the D5.4 aggregation layer.  It registers all twenty-one
FX dimensions while preserving the algebra each dimension actually has:

* semiring dimensions feed the existing Wood/Atkey `GradeVector`;
* join-semilattice dimensions feed a parallel join vector;
* structural dimensions are tracked as slots, not faked as grades.

The split is intentional.  Effects, lifetime rows, provenance rows,
clock domains, precision evidence, overflow modes, and version evidence
accumulate by least upper bound, but they do not satisfy semiring
annihilation.  Type, refinement, and protocol structure are already
kernel data in other layers and are not D5.4 grade carriers.

Zero-axiom verified per declaration. -/

namespace LeanFX2.Graded

open LeanFX2.Graded.Instances

/-! ## Dimension slots and algebra classes -/

/-- The twenty-one FX dimension slots, in specification order. -/
inductive DimensionSlot : Type
  | typeKind
  | refinement
  | usage
  | effect
  | security
  | protocol
  | lifetime
  | provenance
  | trust
  | representation
  | observability
  | clockDomain
  | complexity
  | precision
  | space
  | overflow
  | fpOrder
  | mutation
  | reentrancy
  | size
  | version
  deriving DecidableEq, Repr

/-- Algebra currently registered for a dimension slot. -/
inductive DimensionAlgebraKind : Type
  | structural
  | semiring
  | joinSemilattice
  deriving DecidableEq, Repr

/-- One-indexed dimension number from the FX specification. -/
def DimensionSlot.number : DimensionSlot → Nat
  | .typeKind => 1
  | .refinement => 2
  | .usage => 3
  | .effect => 4
  | .security => 5
  | .protocol => 6
  | .lifetime => 7
  | .provenance => 8
  | .trust => 9
  | .representation => 10
  | .observability => 11
  | .clockDomain => 12
  | .complexity => 13
  | .precision => 14
  | .space => 15
  | .overflow => 16
  | .fpOrder => 17
  | .mutation => 18
  | .reentrancy => 19
  | .size => 20
  | .version => 21

/-- Stable ASCII display name for a dimension slot. -/
def DimensionSlot.displayName : DimensionSlot → String
  | .typeKind => "type"
  | .refinement => "refinement"
  | .usage => "usage"
  | .effect => "effect"
  | .security => "security"
  | .protocol => "protocol"
  | .lifetime => "lifetime"
  | .provenance => "provenance"
  | .trust => "trust"
  | .representation => "representation"
  | .observability => "observability"
  | .clockDomain => "clock_domain"
  | .complexity => "complexity"
  | .precision => "precision"
  | .space => "space"
  | .overflow => "overflow"
  | .fpOrder => "fp_order"
  | .mutation => "mutation"
  | .reentrancy => "reentrancy"
  | .size => "size"
  | .version => "version"

/-- Algebra class attached to each slot at D5.4 closure. -/
def DimensionSlot.algebraKind : DimensionSlot → DimensionAlgebraKind
  | .typeKind => .structural
  | .refinement => .structural
  | .usage => .semiring
  | .effect => .joinSemilattice
  | .security => .semiring
  | .protocol => .structural
  | .lifetime => .joinSemilattice
  | .provenance => .joinSemilattice
  | .trust => .semiring
  | .representation => .semiring
  | .observability => .semiring
  | .clockDomain => .joinSemilattice
  | .complexity => .semiring
  | .precision => .joinSemilattice
  | .space => .semiring
  | .overflow => .joinSemilattice
  | .fpOrder => .semiring
  | .mutation => .semiring
  | .reentrancy => .semiring
  | .size => .semiring
  | .version => .joinSemilattice

/-- All dimension slots in specification order. -/
def allDimensionSlots : List DimensionSlot :=
  [ .typeKind
  , .refinement
  , .usage
  , .effect
  , .security
  , .protocol
  , .lifetime
  , .provenance
  , .trust
  , .representation
  , .observability
  , .clockDomain
  , .complexity
  , .precision
  , .space
  , .overflow
  , .fpOrder
  , .mutation
  , .reentrancy
  , .size
  , .version
  ]

/-- D5.4 registry contains exactly twenty-one FX dimension slots. -/
theorem allDimensionSlots_length :
    allDimensionSlots.length = 21 := rfl

/-! ## Join-semilattice vector -/

/-- A registered join dimension: carrier type plus its bounded
join-semilattice instance. -/
structure JoinDimension : Type 1 where
  carrier : Type
  semilattice : GradeJoinSemilattice carrier

/-- A vector carrying one join-semilattice grade per registered join
dimension. -/
def JoinGradeVector : List JoinDimension → Type
  | [] => Unit
  | head :: tail => head.carrier × JoinGradeVector tail

/-- Bottom join-grade vector. -/
def JoinGradeVector.bottom :
    ∀ {dimensions : List JoinDimension}, JoinGradeVector dimensions
  | [] => ()
  | head :: tail =>
      (head.semilattice.bottom, @JoinGradeVector.bottom tail)

/-- Pointwise join for join-grade vectors. -/
def JoinGradeVector.join :
    ∀ {dimensions : List JoinDimension},
      JoinGradeVector dimensions →
      JoinGradeVector dimensions →
      JoinGradeVector dimensions
  | [], _, _ => ()
  | head :: tail, (firstHead, firstTail), (secondHead, secondTail) =>
      (head.semilattice.join firstHead secondHead,
       @JoinGradeVector.join tail firstTail secondTail)

/-- Pointwise preorder for join-grade vectors. -/
def JoinGradeVector.le :
    ∀ {dimensions : List JoinDimension},
      JoinGradeVector dimensions →
      JoinGradeVector dimensions →
      Prop
  | [], _, _ => True
  | head :: tail, (firstHead, firstTail), (secondHead, secondTail) =>
      head.semilattice.le firstHead secondHead ∧
      @JoinGradeVector.le tail firstTail secondTail

/-- Pointwise join-vector preorder is reflexive. -/
theorem JoinGradeVector.le_refl :
    ∀ {dimensions : List JoinDimension} (someVector : JoinGradeVector dimensions),
      JoinGradeVector.le someVector someVector
  | [], () => True.intro
  | head :: _, (someHead, someTail) =>
      ⟨head.semilattice.le_refl someHead, JoinGradeVector.le_refl someTail⟩

/-- Pointwise join-vector preorder is transitive. -/
theorem JoinGradeVector.le_trans :
    ∀ {dimensions : List JoinDimension}
      (firstVector secondVector thirdVector : JoinGradeVector dimensions),
      JoinGradeVector.le firstVector secondVector →
      JoinGradeVector.le secondVector thirdVector →
      JoinGradeVector.le firstVector thirdVector
  | [], _, _, _, _, _ => True.intro
  | head :: _, (firstHead, firstTail), (secondHead, secondTail),
      (thirdHead, thirdTail), ⟨headLeFirst, tailLeFirst⟩,
      ⟨headLeSecond, tailLeSecond⟩ =>
      ⟨head.semilattice.le_trans firstHead secondHead thirdHead
          headLeFirst headLeSecond,
       JoinGradeVector.le_trans firstTail secondTail thirdTail
          tailLeFirst tailLeSecond⟩

/-- Bottom is below every join-grade vector. -/
theorem JoinGradeVector.bottom_le :
    ∀ {dimensions : List JoinDimension} (someVector : JoinGradeVector dimensions),
      JoinGradeVector.le JoinGradeVector.bottom someVector
  | [], () => True.intro
  | head :: _, (someHead, someTail) =>
      ⟨head.semilattice.bottom_le someHead,
       JoinGradeVector.bottom_le someTail⟩

/-- Left operand is below pointwise join. -/
theorem JoinGradeVector.le_join_left :
    ∀ {dimensions : List JoinDimension}
      (leftVector rightVector : JoinGradeVector dimensions),
      JoinGradeVector.le leftVector
        (JoinGradeVector.join leftVector rightVector)
  | [], _, _ => True.intro
  | head :: _, (leftHead, leftTail), (rightHead, rightTail) =>
      ⟨head.semilattice.le_join_left leftHead rightHead,
       JoinGradeVector.le_join_left leftTail rightTail⟩

/-- Right operand is below pointwise join. -/
theorem JoinGradeVector.le_join_right :
    ∀ {dimensions : List JoinDimension}
      (leftVector rightVector : JoinGradeVector dimensions),
      JoinGradeVector.le rightVector
        (JoinGradeVector.join leftVector rightVector)
  | [], _, _ => True.intro
  | head :: _, (leftHead, leftTail), (rightHead, rightTail) =>
      ⟨head.semilattice.le_join_right leftHead rightHead,
       JoinGradeVector.le_join_right leftTail rightTail⟩

/-- Pointwise join is monotone in both operands. -/
theorem JoinGradeVector.join_mono :
    ∀ {dimensions : List JoinDimension}
      (leftLow leftHigh rightLow rightHigh : JoinGradeVector dimensions),
      JoinGradeVector.le leftLow leftHigh →
      JoinGradeVector.le rightLow rightHigh →
      JoinGradeVector.le
        (JoinGradeVector.join leftLow rightLow)
        (JoinGradeVector.join leftHigh rightHigh)
  | [], _, _, _, _, _, _ => True.intro
  | head :: _, (leftLowHead, leftLowTail),
      (leftHighHead, leftHighTail), (rightLowHead, rightLowTail),
      (rightHighHead, rightHighTail), ⟨leftHeadLe, leftTailLe⟩,
      ⟨rightHeadLe, rightTailLe⟩ =>
      ⟨head.semilattice.join_least_upper_bound leftLowHead rightLowHead
          (head.semilattice.join leftHighHead rightHighHead)
          (head.semilattice.le_trans leftLowHead leftHighHead
            (head.semilattice.join leftHighHead rightHighHead)
            leftHeadLe
            (head.semilattice.le_join_left leftHighHead rightHighHead))
          (head.semilattice.le_trans rightLowHead rightHighHead
            (head.semilattice.join leftHighHead rightHighHead)
            rightHeadLe
            (head.semilattice.le_join_right leftHighHead rightHighHead)),
       JoinGradeVector.join_mono leftLowTail leftHighTail
          rightLowTail rightHighTail leftTailLe rightTailLe⟩

/-! ## Registry entries with algebra-kind witnesses -/

/-- Semiring registry entry tying a dimension slot to its carrier and
proving that the slot is classified as semiring-backed. -/
structure SemiringDimensionEntry : Type 1 where
  slot : DimensionSlot
  dimension : Dimension
  isSemiringSlot : slot.algebraKind = .semiring

/-- Join-semilattice registry entry tying a dimension slot to its carrier
and proving that the slot is classified as join-backed. -/
structure JoinDimensionEntry : Type 1 where
  slot : DimensionSlot
  dimension : JoinDimension
  isJoinSemilatticeSlot : slot.algebraKind = .joinSemilattice

/-- Structural registry entry for dimensions tracked by kernel syntax or
typing objects rather than by D5.4 grade payloads. -/
structure StructuralDimensionEntry : Type where
  slot : DimensionSlot
  isStructuralSlot : slot.algebraKind = .structural

/-! ## Concrete D5.4 registry -/

def usageDimension : Dimension :=
  { carrier := UsageGrade, semiring := inferInstance }

def securityDimension : Dimension :=
  { carrier := SecurityGrade, semiring := inferInstance }

def trustDimension : Dimension :=
  { carrier := TrustGrade, semiring := inferInstance }

def representationDimension : Dimension :=
  { carrier := RepresentationGrade, semiring := inferInstance }

def observabilityDimension : Dimension :=
  { carrier := ObservabilityGrade, semiring := inferInstance }

def complexityDimension : Dimension :=
  { carrier := ComplexityGrade, semiring := inferInstance }

def spaceDimension : Dimension :=
  { carrier := SpaceGrade, semiring := inferInstance }

def fpOrderDimension : Dimension :=
  { carrier := FPOrderGrade, semiring := inferInstance }

def mutationDimension : Dimension :=
  { carrier := MutationGrade, semiring := inferInstance }

def reentrancyDimension : Dimension :=
  { carrier := ReentrancyGrade, semiring := inferInstance }

def sizeDimension : Dimension :=
  { carrier := SizeGrade, semiring := inferInstance }

def effectJoinDimension : JoinDimension :=
  { carrier := EffectGrade, semilattice := inferInstance }

def lifetimeJoinDimension : JoinDimension :=
  { carrier := LifetimeGrade, semilattice := inferInstance }

def provenanceJoinDimension : JoinDimension :=
  { carrier := ProvenanceGrade, semilattice := inferInstance }

def clockDomainJoinDimension : JoinDimension :=
  { carrier := ClockDomainGrade, semilattice := inferInstance }

def precisionJoinDimension : JoinDimension :=
  { carrier := PrecisionGrade, semilattice := inferInstance }

def overflowJoinDimension : JoinDimension :=
  { carrier := OverflowGrade, semilattice := inferInstance }

def versionJoinDimension : JoinDimension :=
  { carrier := VersionGrade, semilattice := inferInstance }

/-- Semiring dimensions in specification order, paired with their slots
and algebra-kind witnesses. -/
def semiringDimensionEntries21 : List SemiringDimensionEntry :=
  [ { slot := .usage
    , dimension := usageDimension
    , isSemiringSlot := rfl }
  , { slot := .security
    , dimension := securityDimension
    , isSemiringSlot := rfl }
  , { slot := .trust
    , dimension := trustDimension
    , isSemiringSlot := rfl }
  , { slot := .representation
    , dimension := representationDimension
    , isSemiringSlot := rfl }
  , { slot := .observability
    , dimension := observabilityDimension
    , isSemiringSlot := rfl }
  , { slot := .complexity
    , dimension := complexityDimension
    , isSemiringSlot := rfl }
  , { slot := .space
    , dimension := spaceDimension
    , isSemiringSlot := rfl }
  , { slot := .fpOrder
    , dimension := fpOrderDimension
    , isSemiringSlot := rfl }
  , { slot := .mutation
    , dimension := mutationDimension
    , isSemiringSlot := rfl }
  , { slot := .reentrancy
    , dimension := reentrancyDimension
    , isSemiringSlot := rfl }
  , { slot := .size
    , dimension := sizeDimension
    , isSemiringSlot := rfl }
  ]

/-- Join-semilattice dimensions in specification order, paired with
their slots and algebra-kind witnesses. -/
def joinDimensionEntries21 : List JoinDimensionEntry :=
  [ { slot := .effect
    , dimension := effectJoinDimension
    , isJoinSemilatticeSlot := rfl }
  , { slot := .lifetime
    , dimension := lifetimeJoinDimension
    , isJoinSemilatticeSlot := rfl }
  , { slot := .provenance
    , dimension := provenanceJoinDimension
    , isJoinSemilatticeSlot := rfl }
  , { slot := .clockDomain
    , dimension := clockDomainJoinDimension
    , isJoinSemilatticeSlot := rfl }
  , { slot := .precision
    , dimension := precisionJoinDimension
    , isJoinSemilatticeSlot := rfl }
  , { slot := .overflow
    , dimension := overflowJoinDimension
    , isJoinSemilatticeSlot := rfl }
  , { slot := .version
    , dimension := versionJoinDimension
    , isJoinSemilatticeSlot := rfl }
  ]

/-- Structural dimensions that are registered but not D5.4 algebra
carriers, paired with algebra-kind witnesses. -/
def structuralDimensionEntries21 : List StructuralDimensionEntry :=
  [ { slot := .typeKind
    , isStructuralSlot := rfl }
  , { slot := .refinement
    , isStructuralSlot := rfl }
  , { slot := .protocol
    , isStructuralSlot := rfl }
  ]

/-- Semiring dimensions in specification order, excluding structural
and join-only slots. -/
def semiringDimensions21 : List Dimension :=
  semiringDimensionEntries21.map SemiringDimensionEntry.dimension

/-- Semiring dimension slots in the same order as `semiringDimensions21`. -/
def semiringDimensionSlots21 : List DimensionSlot :=
  semiringDimensionEntries21.map SemiringDimensionEntry.slot

/-- Join-semilattice dimensions in specification order. -/
def joinDimensions21 : List JoinDimension :=
  joinDimensionEntries21.map JoinDimensionEntry.dimension

/-- Join-semilattice dimension slots in the same order as
`joinDimensions21`. -/
def joinDimensionSlots21 : List DimensionSlot :=
  joinDimensionEntries21.map JoinDimensionEntry.slot

/-- Structural dimensions that are registered but not D5.4 algebra
carriers. -/
def structuralDimensionSlots21 : List DimensionSlot :=
  structuralDimensionEntries21.map StructuralDimensionEntry.slot

theorem semiringDimensions21_length :
    semiringDimensions21.length = 11 := rfl

theorem semiringDimensionSlots21_length :
    semiringDimensionSlots21.length = 11 := rfl

theorem joinDimensions21_length :
    joinDimensions21.length = 7 := rfl

theorem joinDimensionSlots21_length :
    joinDimensionSlots21.length = 7 := rfl

theorem structuralDimensionSlots21_length :
    structuralDimensionSlots21.length = 3 := rfl

theorem structuralDimensionEntries21_length :
    structuralDimensionEntries21.length = 3 := rfl

theorem semiringDimensionEntries21_length :
    semiringDimensionEntries21.length = 11 := rfl

theorem joinDimensionEntries21_length :
    joinDimensionEntries21.length = 7 := rfl

theorem semiringDimensions21_slots_length_match :
    semiringDimensions21.length = semiringDimensionSlots21.length := rfl

theorem joinDimensions21_slots_length_match :
    joinDimensions21.length = joinDimensionSlots21.length := rfl

/-- D5.4 FX grade vector: semiring grades plus join-semilattice grades.
Structural dimensions live in the kernel typing objects and are tracked
by their slots rather than by this value-level grade payload. -/
structure FXGradeVector21 : Type where
  semiringGrades : GradeVector semiringDimensions21
  joinGrades : JoinGradeVector joinDimensions21

namespace FXGradeVector21

/-- Most restrictive / empty grade vector for all D5.4 algebraic
dimensions. -/
def bottom : FXGradeVector21 where
  semiringGrades := GradeVector.zero
  joinGrades := JoinGradeVector.bottom

/-- Multiplicative identity for semiring-backed dimensions, paired with
bottom for join-only dimensions.  This is an identity for the semiring
projection of `compose`; join-only identities are intentionally stated by
preorder lemmas because `GradeJoinSemilattice` does not require equality
normalization laws. -/
def one : FXGradeVector21 where
  semiringGrades := GradeVector.one
  joinGrades := JoinGradeVector.bottom

/-- Pointwise composition for D5.4 algebraic grade payloads.  Semiring
slots use `GradeVector.add`; join-only slots use `JoinGradeVector.join`. -/
def join (firstVector secondVector : FXGradeVector21) : FXGradeVector21 where
  semiringGrades :=
    GradeVector.add firstVector.semiringGrades secondVector.semiringGrades
  joinGrades :=
    JoinGradeVector.join firstVector.joinGrades secondVector.joinGrades

/-- Sequential / closure composition for D5.4 algebraic grade payloads.
Semiring-backed dimensions use `GradeVector.mul`; join-only dimensions
accumulate by join because their carriers deliberately do not satisfy
annihilating semiring multiplication. -/
def compose (firstVector secondVector : FXGradeVector21) : FXGradeVector21 where
  semiringGrades :=
    GradeVector.mul firstVector.semiringGrades secondVector.semiringGrades
  joinGrades :=
    JoinGradeVector.join firstVector.joinGrades secondVector.joinGrades

/-- Pointwise preorder for all D5.4 algebraic grade payloads. -/
def le (firstVector secondVector : FXGradeVector21) : Prop :=
  GradeVector.le firstVector.semiringGrades secondVector.semiringGrades ∧
  JoinGradeVector.le firstVector.joinGrades secondVector.joinGrades

/-- D5.4 payload preorder is reflexive. -/
theorem le_refl (someVector : FXGradeVector21) :
    le someVector someVector :=
  ⟨GradeVector.le_refl someVector.semiringGrades,
   JoinGradeVector.le_refl someVector.joinGrades⟩

/-- D5.4 payload preorder is transitive. -/
theorem le_trans
    (firstVector secondVector thirdVector : FXGradeVector21)
    (firstLeSecond : le firstVector secondVector)
    (secondLeThird : le secondVector thirdVector) :
    le firstVector thirdVector :=
  ⟨GradeVector.le_trans
      firstVector.semiringGrades secondVector.semiringGrades thirdVector.semiringGrades
      firstLeSecond.left secondLeThird.left,
   JoinGradeVector.le_trans
      firstVector.joinGrades secondVector.joinGrades thirdVector.joinGrades
      firstLeSecond.right secondLeThird.right⟩

/-- Join-grade bottom is below the join-grade component.  The semiring
component intentionally has no matching generic theorem: `GradeSemiring`
does not state that zero is the least element. -/
theorem joinGrades_bottom_le (someVector : FXGradeVector21) :
    JoinGradeVector.le bottom.joinGrades someVector.joinGrades :=
  JoinGradeVector.bottom_le someVector.joinGrades

/-- The semiring projection of `compose` has `one` as a left identity. -/
theorem compose_semiring_one_left (someVector : FXGradeVector21) :
    (compose one someVector).semiringGrades = someVector.semiringGrades :=
  GradeVector.mul_one_left someVector.semiringGrades

/-- The semiring projection of `compose` has `one` as a right identity. -/
theorem compose_semiring_one_right (someVector : FXGradeVector21) :
    (compose someVector one).semiringGrades = someVector.semiringGrades :=
  GradeVector.mul_one_right someVector.semiringGrades

/-- The left join-only payload is below the join-only payload of
`compose`. -/
theorem compose_join_left_le
    (firstVector secondVector : FXGradeVector21) :
    JoinGradeVector.le firstVector.joinGrades
      (compose firstVector secondVector).joinGrades :=
  JoinGradeVector.le_join_left firstVector.joinGrades secondVector.joinGrades

/-- The right join-only payload is below the join-only payload of
`compose`. -/
theorem compose_join_right_le
    (firstVector secondVector : FXGradeVector21) :
    JoinGradeVector.le secondVector.joinGrades
      (compose firstVector secondVector).joinGrades :=
  JoinGradeVector.le_join_right firstVector.joinGrades secondVector.joinGrades

/-- Pointwise `join` is monotone for the aggregate D5.4 payload. -/
theorem join_mono
    (firstLow firstHigh secondLow secondHigh : FXGradeVector21)
    (firstLe : le firstLow firstHigh)
    (secondLe : le secondLow secondHigh) :
    le (join firstLow secondLow) (join firstHigh secondHigh) :=
  ⟨GradeVector.add_mono
      firstLow.semiringGrades firstHigh.semiringGrades
      secondLow.semiringGrades secondHigh.semiringGrades
      firstLe.left secondLe.left,
   JoinGradeVector.join_mono
      firstLow.joinGrades firstHigh.joinGrades
      secondLow.joinGrades secondHigh.joinGrades
      firstLe.right secondLe.right⟩

/-- Pointwise `compose` is monotone for the aggregate D5.4 payload. -/
theorem compose_mono
    (firstLow firstHigh secondLow secondHigh : FXGradeVector21)
    (firstLe : le firstLow firstHigh)
    (secondLe : le secondLow secondHigh) :
    le (compose firstLow secondLow) (compose firstHigh secondHigh) :=
  ⟨GradeVector.mul_mono
      firstLow.semiringGrades firstHigh.semiringGrades
      secondLow.semiringGrades secondHigh.semiringGrades
      firstLe.left secondLe.left,
   JoinGradeVector.join_mono
      firstLow.joinGrades firstHigh.joinGrades
      secondLow.joinGrades secondHigh.joinGrades
      firstLe.right secondLe.right⟩

end FXGradeVector21

/-! ## Smoke samples -/

example : allDimensionSlots.length = 21 := rfl
example : semiringDimensions21.length = 11 := rfl
example : joinDimensions21.length = 7 := rfl
example : structuralDimensionSlots21.length = 3 := rfl
example : DimensionSlot.usage.number = 3 := rfl
example : DimensionSlot.effect.algebraKind = .joinSemilattice := rfl
example : DimensionSlot.protocol.algebraKind = .structural := rfl

end LeanFX2.Graded
