import FX1Poly.Typed.NormalizationTransferLedger

/-! # FX1Poly/Typed/ParametricityTransferLedger
    — the ParametricityExtraction record is LAWLESS; the honest type-indexed relational transfer (SN-095, #598)

The third interface verdict of the extraction family.  `InternalSconing.lean`'s
`ParametricityExtraction` carries a `Relation` family and a `fundamental` field whose closed-term
argument is an UNDERSCORE — the record states NO law at all (canonicity's record was refuted,
normalization's had one reduction-blind law, parametricity's has none).  Any constant family
inhabits it.  This file makes that a theorem and ships the honest content:

  * `punitParametricityExtraction` — the lawless record inhabited by the constant singleton family;
    `punitParametricityExtraction_ignoresTerm` (`rfl`) pins that its `fundamental` does not consult
    the term — a "relational interpretation" no term can fail.
  * ★ `GluedTypeCell.parametricityTransfer` — **the honest type-indexed relational transfer**: for
    a glued type, every well-typed term SATISFIES ITS TYPE'S relational interpretation (the scone,
    tied to the type by the model field `isModeled` — this is unary parametricity, the
    type-indexed logical relation) and is strongly normalizing by CR1.  The relation family here is
    not free-floating: `ReducibleType` assigns it per type cell, Π gets the dependent
    function-space relation, data formers get the model's neutral relation.
  * ★ `GluedTypeCell.piFreeTheorem` — **the Reynolds abstraction-theorem shape at Π**: through the
    SN-091 Π lift, a well-typed function maps RELATED arguments to RELATED results — the
    `IsDependentArrowReducible` membership unfolded into the free-theorem form (the unfolding is
    definitional: the SN-087/SN-091 packaging made the Π relation literally the
    related-arguments-to-related-results predicate).

## Honest scope boundary

This is UNARY parametricity (the type-indexed logical predicate, the BKS scone) — exactly what the
sconing thesis derives from one functor.  BINARY parametricity (relations between two
interpretations, full Reynolds free theorems for polymorphic terms) is NOT shipped; the
graded-layer projection (`DIM-FUNCTORIAL`: a multi-dimension graded derivation projects to each
factor) is the dimension-indexed analogue already in the tree, and the binary relational lift of
the glued model is the recorded follow-on.  The `fxSconingConstructionLevel` ledger advances to
`.parametricityTransferTheorem` on this package (see `InternalSconing.lean`); the BKS bundle
(SN-096) is the remaining level.

## Zero-axiom verification

The lawless-record instance is a structure literal; the transfers are direct applications of the
glued type's `fundamental` hypothesis, CR1 (`GluedTypeCell.isCandidate`), and the definitional
`piLift_computable` unfolding.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0
open StepStar

/-- **The lawless record inhabited by the constant singleton family.**  `ParametricityExtraction`
states no law (its `fundamental`'s term argument is an underscore in the record itself), so the
constant `PUnit` relation family inhabits it — a "relational interpretation" no term can fail. -/
def punitParametricityExtraction : ParametricityExtraction fxBaseSubstGlobalSections where
  Relation := fun _objectA => PUnit
  fundamental := fun _objectA _closedTerm => PUnit.unit

/-- **The diagnosis made a theorem**: the lawless instance's `fundamental` does not consult the
term — every two sections receive the SAME relational witness.  Inhabiting
`ParametricityExtraction` certifies no parametricity content. -/
theorem punitParametricityExtraction_ignoresTerm (objectA : Nat)
    (firstSection secondSection : fxBaseSubstGlobalSections.sections objectA) :
    punitParametricityExtraction.fundamental objectA firstSection
      = punitParametricityExtraction.fundamental objectA secondSection := rfl

/-- ★ **The honest type-indexed relational transfer** (unary parametricity over the glued model):
every well-typed term satisfies ITS TYPE'S relational interpretation — the scone `glued.computable`,
tied to the type cell by the model field — and is strongly normalizing by CR1.  The relation family
is not free-floating: `ReducibleType` assigns it per type (Π gets the dependent function-space
relation, the formers get the model's neutral relation). -/
theorem GluedTypeCell.parametricityTransfer {scope : Nat} (glued : GluedTypeCell (scope + 1))
    {isWellTyped : RawTerm (scope + 1) → Prop}
    (fundamental : ∀ term : RawTerm (scope + 1), isWellTyped term → glued.computable term)
    (term : RawTerm (scope + 1)) (typed : isWellTyped term) :
    glued.computable term ∧ IsStronglyNormalizing term :=
  have satisfiesInterpretation := fundamental term typed
  ⟨satisfiesInterpretation, glued.isCandidate.stronglyNormalizing satisfiesInterpretation⟩

/-- ★ **The Reynolds abstraction-theorem shape at Π** (the free-theorem form): through the SN-091
Π lift, a well-typed function maps RELATED arguments to RELATED results — the
`IsDependentArrowReducible` membership unfolded, which the SN-087/SN-091 packaging made
definitional. -/
theorem GluedTypeCell.piFreeTheorem {scope : Nat} (domainGlued : GluedTypeCell scope)
    (codomainCode : RawTerm (scope + 1))
    (codomainComputable : RawTerm scope → (RawTerm scope → Prop))
    (codomainModeled : ∀ argument : RawTerm scope, domainGlued.computable argument →
      ReducibleType (RawTerm.subst0 codomainCode argument) (codomainComputable argument))
    {isWellTyped : RawTerm scope → Prop}
    (fundamental : ∀ term : RawTerm scope, isWellTyped term →
      (domainGlued.piLift codomainCode codomainComputable codomainModeled).computable term)
    (functionTerm : RawTerm scope) (typed : isWellTyped functionTerm)
    (argument : RawTerm scope) (argumentRelated : domainGlued.computable argument) :
    codomainComputable argument
      (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))) :=
  fundamental functionTerm typed argument argumentRelated

end FX1Poly.Typed
