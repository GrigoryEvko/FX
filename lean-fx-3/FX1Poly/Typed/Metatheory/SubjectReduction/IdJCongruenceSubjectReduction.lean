import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction
import FX1Poly.Typed.Metatheory.SubjectReduction.ElimOutputTypeCongruence
import FX1Poly.Typed.Engine.Union.HasTypeUnionPathProjInversion
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/IdJCongruenceSubjectReduction
    — the `idJ` base-context congruence subject reductions (gate-2 arms, TYTAB-2-FT-SR #1740)

The base-context congruence arms of genuine Paulin-Mohring path induction (gate 2 of the consistency leg
#1697).  `idJ` has three children — the two-binder motive (at `scope + 2`), the base case, and the witness
(both at the ambient base `scope`) — with obligation order `[witness, rightEndpoint, baseCase, motive]`
(`idJElimRule`) and output `idJMotiveAt motive rightEndpoint witness`.

This file ships the two base-context child positions — the `witness` step (output drifts via
`idJOutputType_isConvStableUnderWitnessStep`, the witness being the `path` substituent of `idJMotiveAt`) and
the `baseCase` step (output unchanged — the base case does not occur in `idJMotiveAt motive rightEndpoint
witness`).  The right endpoint is a type-index PARAM, not a stepping child, so there is no right-endpoint
congruence arm here.  The motive step (the two-binder extended-context position, drifting the diagonal
base-case classifier and the output via `idJOutputType_isConvStableUnderMotiveStep`) is the harder sub-case
and is NOT YET SHIPPED: unlike `natElim`/`natRec`/`boolElim`, re-typing the base case at the drifted classifier
`idJMotiveAt motive' leftEndpoint (refl leftEndpoint)` needs that classifier FORMED FROM motive', but
`idJOutputFormed_ofMotiveEndpointWitness` (HasTypeUnionValidity) demands `leftEndpoint : typeCode` and a `refl
leftEndpoint` typing that `invertAtIdJHeadAllPremises` does NOT surface (it yields the RIGHT-endpoint typing and
the witness, not the left endpoint nor a diagonal refl), so the idJ motive arm needs either a strengthened
inversion exposing those two, or a dedicated "motive-step preserves `idJMotiveAt` formedness" stability lemma.
The table-driven SR-DSL-4 route (generic `premisesHoldAfter` over reified CellTemplates) supersedes this bespoke
arm anyway, so it is deferred to that route rather than hand-built.

Both arms use the `invertAtIdJHeadAllPremises` inversion (which surfaces the right-endpoint typing and the
2-extended-context motive obligation the plain `invertAtIdJHead` drops) to recover every premise the rebuild's
native `elim` arm requires.

## Zero-axiom verification

The shipped AllPremises inversion / validity `classifierIsType` / `reclassifyToType` / native `elim` arm /
witness-output congruence.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The `idJ` congruence subject reduction at the WITNESS position.**  When the witness steps, the reformed
cell re-types at the drifted output `idJMotiveAt motive rightEndpoint witnessReduct` (the witness is the `path`
substituent of the output); the stepped witness is re-typed by the IH and reclassified back to the general
identity code `idTypeCell typeCode leftEndpoint rightEndpoint`. -/
theorem HasTypeUnion.idJWitnessCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 2)} {baseCase witness witnessReduct classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context (idJCell motive baseCase witness) classifier)
    (witnessStep : Step witness witnessReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (idJCell motive baseCase witnessReduct) pinned ∧
      Conv classifier pinned := by
  obtain ⟨typeCode, leftEndpoint, rightEndpoint, witnessTyped, rightTyped, baseCaseTyped,
      ⟨motiveLevel, motiveFlag, motiveTyped⟩, classifierConv⟩ :=
    HasTypeUnion.invertAtIdJHeadAllPremises typed rfl
  obtain ⟨witnessReductType, witnessReductTyped, witnessTypeConv⟩ :=
    childSubjectReduction witnessTyped witnessStep
  have idIsType : UnionClassifierIsType profile context
      (idTypeCell typeCode leftEndpoint rightEndpoint) :=
    HasTypeUnion.classifierIsType witnessTyped wellFormed
  have witnessReductAtId :
      HasTypeUnion profile context witnessReduct (idTypeCell typeCode leftEndpoint rightEndpoint) :=
    HasTypeUnion.reclassifyToType witnessReductTyped witnessTypeConv.sym idIsType
  refine ⟨idJMotiveAt motive rightEndpoint witnessReduct, ?_,
    classifierConv.sym.trans
      (idJOutputType_isConvStableUnderWitnessStep motive rightEndpoint witnessStep)⟩
  refine HasTypeUnion.elim context .gen_idJ idJElimRule
    (.childCons motive (.childCons baseCase (.childCons witnessReduct .childNil)))
    (.childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
    motiveLevel motiveLevel motiveFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact witnessReductAtId
  | tail _ hmem => cases hmem with
    | head => exact rightTyped
    | tail _ hmem => cases hmem with
      | head => exact baseCaseTyped
      | tail _ hmem => cases hmem with
        | head => exact motiveTyped
        | tail _ hmem => cases hmem

/-- **The `idJ` congruence subject reduction at the BASE-CASE position.**  The base case (typed at the
diagonal motive instantiation `idJMotiveAt motive leftEndpoint (refl leftEndpoint)`) does not occur in the
output `idJMotiveAt motive rightEndpoint witness`, so the output `Conv` is the inversion's conversion leg
directly; the stepped base case is re-typed by the IH and reclassified back to the diagonal type. -/
theorem HasTypeUnion.idJBaseCaseCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 2)} {baseCase baseReduct witness classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context (idJCell motive baseCase witness) classifier)
    (baseStep : Step baseCase baseReduct)
    (childSubjectReduction : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {subterm reduct subtermType : RawTerm innerScope},
      HasTypeUnion profile innerContext subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm innerScope,
          HasTypeUnion profile innerContext reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (idJCell motive baseReduct witness) pinned ∧
      Conv classifier pinned := by
  obtain ⟨typeCode, leftEndpoint, rightEndpoint, witnessTyped, rightTyped, baseCaseTyped,
      ⟨motiveLevel, motiveFlag, motiveTyped⟩, classifierConv⟩ :=
    HasTypeUnion.invertAtIdJHeadAllPremises typed rfl
  obtain ⟨baseReductType, baseReductTyped, baseTypeConv⟩ :=
    childSubjectReduction baseCaseTyped baseStep
  have baseIsType : UnionClassifierIsType profile context
      (idJMotiveAt motive leftEndpoint (reflCell leftEndpoint)) :=
    HasTypeUnion.classifierIsType baseCaseTyped wellFormed
  have baseReductAtType :
      HasTypeUnion profile context baseReduct
        (idJMotiveAt motive leftEndpoint (reflCell leftEndpoint)) :=
    HasTypeUnion.reclassifyToType baseReductTyped baseTypeConv.sym baseIsType
  refine ⟨idJMotiveAt motive rightEndpoint witness, ?_, classifierConv.sym⟩
  refine HasTypeUnion.elim context .gen_idJ idJElimRule
    (.childCons motive (.childCons baseReduct (.childCons witness .childNil)))
    (.childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
    motiveLevel motiveLevel motiveFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact witnessTyped
  | tail _ hmem => cases hmem with
    | head => exact rightTyped
    | tail _ hmem => cases hmem with
      | head => exact baseReductAtType
      | tail _ hmem => cases hmem with
        | head => exact motiveTyped
        | tail _ hmem => cases hmem

end FX1Poly.Typed
