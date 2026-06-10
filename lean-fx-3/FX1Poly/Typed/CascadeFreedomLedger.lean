import FX1Poly.Typed.HasTypeDescWeakening
import FX1Poly.Typed.HasTypeDescSubstitution
import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Typed.HasTypeDescPiSubstitution
import FX1Poly.Typed.WfContextDescUniqueness
import FX1Poly.Typed.GenericFormerTelescopeInversion
import FX1Poly.Typed.HasTypeDescSubjectReduction
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional
import FX1Poly.Typed.SubjectReductionAtFormerGeneric
import FX1Poly.Typed.HasTypeDescSubjectStronglyNormalizingNative
import FX1Poly.Typed.HasTypeDescPiContextConversionFlexibleUnderWf
import FX1Poly.Typed.GenFormerValidityContextConversion
import FX1Poly.Typed.TelescopeSubstitutedChildrenNormalization
import FX1Poly.Typed.ListCodeShape
import FX1Poly.Typed.BoundedFormationArityDispatch
import FX1Poly.Typed.TelescopeArityDispatchNormalization

/-! # FX1Poly/Typed/CascadeFreedomLedger — the per-row absorption-cost ledger
   (the logical-conclusion criterion for the table-generic metatheory program)

The table-generic program's goal: a NEW formation-table row (a new data type-code former)
costs ZERO new proof arms anywhere in the metatheory.  This ledger is the honest,
machine-anchored record of HOW FAR that goal is met — measured, not aspired: the listCode
landing demonstrated the zero-arm rows by absorption, and the bounded-dispatcher build
evidence located the residuals exactly.

## The honest absorption-cost picture (PARTIAL / LAYERED, not total)

| Metatheory row              | Absorption cost      | Evidence                                           |
| --------------------------- | -------------------- | -------------------------------------------------- |
| Weakening                   | ZERO arms            | `renameRespectingContext` (both engines)           |
| Substitution                | ZERO arms            | `substRespectingContext` (both engines)            |
| Uniqueness                  | ZERO arms            | `uniquenessNative` (generic over the table)        |
| Inversion                   | ZERO arms            | `invertFormerTelescopeWithConvGeneric`             |
| Subject reduction           | ZERO arms            | generic former arm + both master dispatchers       |
| Strong normalization        | ZERO arms            | `formerCellStronglyNormalizingOfChildren`          |
| Context conversion          | ZERO arms            | `convTelescopeFromChildIH` + `convContextUnderWf`  |
| Reducibility-FT dispatch    | ZERO arms            | generic non-Pi arm in all six dispatch files       |
| Canonical-forms shape       | BOUNDED bricks       | ~7 bricks per former (`eq_<former>Cell_of_...`)    |

  * **`zeroArm`** — a new row at an existing arity is absorbed with NO new line anywhere
    in that row's metatheory.  Seven of the nine rows are here; together they form the
    structural-metatheory layer (validity / subst / weaken / uniqueness / inversion /
    SR via the generic former arms / SN via the N-child accessibility assembly /
    context conversion via the table-generic telescope step).
  * **`thinLinearDispatch`** — RETIRED: this was the reducibility fundamental-theorem
    REASSEMBLY residual (~8 `by_cases` lines per new row in each of the six dispatch
    files).  The table-generic non-Pi dispatch arm landed in all six files
    (`dataFormationUnderSubst` / `dataFormationUnderSubstAtBounded` over the arity
    suppliers), so the dispatch row moved to `zeroArm`.  The constructor is kept so the
    ledger's history of the residual remains expressible; no row carries it.  The honest
    remaining per-row cost is NOT in the dispatch files: it is one defeq case in each of
    the four table-mirror facts co-located with `typingRuleDescOf`
    (`formationRowArityBound` / `formationRowIsNotFlat` / `formationRowNullaryIsUnit` /
    `formationRowOutputLevel`) — constant-size, single-file, the same edit locus as the
    row itself; the recorded follow-on (tag-bounded `decide` self-updating forms) erases
    even those.
  * **`boundedBricks`** — canonical-forms reconstruction: a new data former costs a
    BOUNDED per-former brick set (the `eq_<former>Cell_of_headGenerator` shape pin plus
    the head-disjunction extension across the closed-normal-form consumers, ~7 bricks
    measured on the list landing), shrinking for every subsequent former because the
    bricks are clones of the first.  Bounded and local, not table-generic.

## Kernel-anchored, non-vacuous

Each `zeroArm` claim is anchored `def cascadeAnchor_<row> := @<shippedDecl>` (the
cross-reference idiom): the file fails to compile if any anchored theorem is renamed or
deleted, and each anchor's audit gate re-certifies the underlying proof zero-axiom.  The
two SHIPPED kernel bricks of the dispatch-residual erasure are anchored the same way —
the ledger records the residual's path-to-zero by reference, not by promise.  The
completeness theorem at the bottom proves the cost function classifies EVERY row (full
enumeration), so no metatheory row is silently missing from the ledger.

## Zero-axiom verification

`MetatheoryRow` / `AbsorptionCost` are plain enums; `absorptionCost` is a
full-enumeration match; the ledger facts are `rfl`; the discriminations close by
`AbsorptionCost.noConfusion`; completeness is a bare `cases` enumeration.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The metatheory rows whose new-formation-row absorption cost this ledger records. -/
inductive MetatheoryRow where
  | weakening
  | substitution
  | uniqueness
  | inversion
  | subjectReduction
  | strongNormalization
  | contextConversion
  | reducibilityDispatch
  | canonicalForms

/-- The three honest absorption-cost classes for landing a new formation-table row. -/
inductive AbsorptionCost where
  /-- The row is absorbed table-generically: ZERO new proof arms for a new former at an
  existing arity. -/
  | zeroArm
  /-- RETIRED (no row carries this cost): the former ~8-dispatch-lines-per-row residual,
  erased by the table-generic non-Pi arm; kept so the ledger's history is expressible. -/
  | thinLinearDispatch
  /-- A bounded per-former brick set (~7 bricks, cloning-shrinkable): the canonical-forms
  shape pin and its head-disjunction consumers. -/
  | boundedBricks
  deriving DecidableEq

/-- The measured absorption cost of each metatheory row (full enumeration, no wildcard). -/
def MetatheoryRow.absorptionCost : MetatheoryRow → AbsorptionCost
  | .weakening => .zeroArm
  | .substitution => .zeroArm
  | .uniqueness => .zeroArm
  | .inversion => .zeroArm
  | .subjectReduction => .zeroArm
  | .strongNormalization => .zeroArm
  | .contextConversion => .zeroArm
  | .reducibilityDispatch => .zeroArm
  | .canonicalForms => .boundedBricks

/-! ## Zero-arm anchors (the teeth)

Each anchor binds the shipped table-generic theorem by reference; the file breaks if it is
renamed, and its audit gate re-certifies the proof zero-axiom. -/

/-- Weakening, formation engine — table-generic, no per-former arm. -/
def cascadeAnchor_weakening_formation := @HasTypeDesc.renameRespectingContext
/-- Weakening, grown engine. -/
def cascadeAnchor_weakening_grown := @HasTypeDescPi.renameRespectingContext
/-- Substitution, formation engine. -/
def cascadeAnchor_substitution_formation := @HasTypeDesc.substRespectingContext
/-- Substitution, grown engine. -/
def cascadeAnchor_substitution_grown := @HasTypeDescPi.substRespectingContext
/-- Uniqueness of typing — the native mutual twin, generic over the formation table. -/
def cascadeAnchor_uniqueness := @HasTypeDesc.uniquenessNative
/-- Generic former inversion — telescope extraction without per-former enumeration. -/
def cascadeAnchor_inversion := @HasTypeDescPi.invertFormerTelescopeWithConvGeneric
/-- Subject reduction, formation master — routes formers through the generic arm. -/
def cascadeAnchor_subjectReduction_formation := @HasTypeDesc.subjectReduction
/-- Subject reduction, grown master — unconditional. -/
def cascadeAnchor_subjectReduction_grown := @HasTypeDescPi.subjectReduction
/-- Subject reduction, the cascade-free generic former arm itself. -/
def cascadeAnchor_subjectReduction_genericArm := @HasTypeDescPi.subjectReductionAtFormerGeneric
/-- Strong normalization — the N-child accessibility assembly: a former cell is SN once
its children are, generator-symbolically. -/
def cascadeAnchor_strongNormalization := @formerCellStronglyNormalizingOfChildren
/-- Context conversion — the table-generic telescope step. -/
def cascadeAnchor_contextConversion_telescopeStep := @DescTelescopePi.convTelescopeFromChildIH
/-- Context conversion — the grown flexible master under a well-formed target context. -/
def cascadeAnchor_contextConversion_grownMaster := @HasTypeDescPi.convContextUnderWf

/-- Reducibility dispatch — the table-generic non-Pi membership arm (unbounded). -/
def cascadeAnchor_reducibilityDispatch_membership := @IsReducibleMemberAt.dataFormationUnderSubst
/-- Reducibility dispatch — the arity-dispatch child-SN supplier (unbounded). -/
def cascadeAnchor_reducibilityDispatch_supplier :=
  @TelescopeReducible.foldChildrenStronglyNormalizing
/-- Reducibility dispatch — the bounded membership arm. -/
def cascadeAnchor_reducibilityDispatch_boundedMembership :=
  @IsReducibleMemberAtBounded.dataFormationUnderSubstAtBounded
/-- Reducibility dispatch — the bounded combined supplier (SN + output bound). -/
def cascadeAnchor_reducibilityDispatch_boundedSupplier :=
  @TelescopeReducibleAtBounded.foldChildrenNormalizingAndOutputBelow
/-- Reducibility dispatch — the level-pinned row-output interface. -/
def cascadeAnchor_reducibilityDispatch_outputLevel := @formationRowOutputLevel

/-! ## Residual anchors — the canonical-forms bricks plus the dispatch's erased history -/

/-- Dispatch-residual kernel brick 1 (SHIPPED): the fresh-variable cons-closure
instantiation — lifted-open substituted binder-child SN from telescope tail closure. -/
def cascadeAnchor_dispatchBrick_liftedChild :=
  @IsStronglyNormalizing.liftedSubstOfConsClosureAtFreshVariable
/-- Dispatch-residual kernel brick 2 (SHIPPED): telescope reducibility yields the literal
substituted spine all-SN at the table's binary arity. -/
def cascadeAnchor_dispatchBrick_spineSN :=
  @TelescopeReducible.substitutedTwoChildSpineStronglyNormalizing
/-- Canonical-forms bounded-brick exemplar: the list-code shape pin (the first brick of
the ~7-brick per-former set; subsequent formers clone it). -/
def cascadeAnchor_canonicalFormsBrick := @eq_listCodeCell_of_headGenerator

/-! ## Ledger facts -/

/-- Weakening absorbs new rows with zero arms. -/
theorem weakening_isZeroArm :
    MetatheoryRow.weakening.absorptionCost = .zeroArm := rfl

/-- Substitution absorbs new rows with zero arms. -/
theorem substitution_isZeroArm :
    MetatheoryRow.substitution.absorptionCost = .zeroArm := rfl

/-- Uniqueness absorbs new rows with zero arms. -/
theorem uniqueness_isZeroArm :
    MetatheoryRow.uniqueness.absorptionCost = .zeroArm := rfl

/-- Inversion absorbs new rows with zero arms. -/
theorem inversion_isZeroArm :
    MetatheoryRow.inversion.absorptionCost = .zeroArm := rfl

/-- Subject reduction absorbs new rows with zero arms (generic former arm + masters). -/
theorem subjectReduction_isZeroArm :
    MetatheoryRow.subjectReduction.absorptionCost = .zeroArm := rfl

/-- Strong normalization absorbs new rows with zero arms (N-child assembly). -/
theorem strongNormalization_isZeroArm :
    MetatheoryRow.strongNormalization.absorptionCost = .zeroArm := rfl

/-- Context conversion absorbs new rows with zero arms (table-generic telescope step). -/
theorem contextConversion_isZeroArm :
    MetatheoryRow.contextConversion.absorptionCost = .zeroArm := rfl

/-- The reducibility-FT dispatch absorbs new rows with zero arms: the table-generic non-Pi
arm (anchored above) replaced the per-row `by_cases` branches in all six dispatch files. -/
theorem reducibilityDispatch_isZeroArm :
    MetatheoryRow.reducibilityDispatch.absorptionCost = .zeroArm := rfl

/-- Canonical-forms reconstruction is the BOUNDED-BRICKS residual: ~7 per-former bricks,
shrinking by cloning for each subsequent former. -/
theorem canonicalForms_isBoundedBricks :
    MetatheoryRow.canonicalForms.absorptionCost = .boundedBricks := rfl

/-! ## Non-vacuity and completeness -/

/-- The ledger genuinely discriminates: the structural layer's cost differs from the
canonical-forms residual's (the cost function is not constant). -/
theorem cost_discriminates_weakening_vs_canonicalForms :
    MetatheoryRow.weakening.absorptionCost ≠
      MetatheoryRow.canonicalForms.absorptionCost := by
  intro costEq
  rw [weakening_isZeroArm, canonicalForms_isBoundedBricks] at costEq
  exact AbsorptionCost.noConfusion costEq

/-- The now-zero-arm dispatch row is distinct from the bounded-bricks canonical-forms
residual — the ledger's one remaining residual class is genuinely non-trivial. -/
theorem cost_discriminates_dispatch_vs_canonicalForms :
    MetatheoryRow.reducibilityDispatch.absorptionCost ≠
      MetatheoryRow.canonicalForms.absorptionCost := by
  intro costEq
  rw [reducibilityDispatch_isZeroArm, canonicalForms_isBoundedBricks] at costEq
  exact AbsorptionCost.noConfusion costEq

/-- **The logical-conclusion criterion, complete over every row**: each metatheory row is
absorbed at zero arms except the ONE named residual — the bounded canonical-forms bricks.
Full enumeration; no row escapes classification, so cascade-freedom claims are exactly as
PARTIAL as this ledger states: total on the structural layer AND the reducibility dispatch,
residual on canonical forms (plus the constant four co-located table-mirror defeq cases
recorded in the `thinLinearDispatch` retirement note). -/
theorem absorptionCost_classifiesEveryRow (row : MetatheoryRow) :
    row.absorptionCost = .zeroArm ∨ row = .canonicalForms := by
  cases row with
  | weakening => exact Or.inl rfl
  | substitution => exact Or.inl rfl
  | uniqueness => exact Or.inl rfl
  | inversion => exact Or.inl rfl
  | subjectReduction => exact Or.inl rfl
  | strongNormalization => exact Or.inl rfl
  | contextConversion => exact Or.inl rfl
  | reducibilityDispatch => exact Or.inl rfl
  | canonicalForms => exact Or.inr rfl

end FX1Poly.Typed
