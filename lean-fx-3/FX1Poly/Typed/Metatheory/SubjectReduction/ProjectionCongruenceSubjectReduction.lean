import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction
import FX1Poly.Typed.Engine.Union.HasTypeUnionPathProjInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionPathAppInversion
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/ProjectionCongruenceSubjectReduction
    — the PARAM-OUTPUT eliminator congruence subject reductions (gate-2 arms, TYTAB-2-FT-SR #1740)

The eliminator-congruence subject reduction (gate 2 of the consistency leg #1697) re-types an eliminator
cell when a child steps.  This file ships the arms for the THREE eliminators whose output type reads only
the existential type-index PARAMS — `gen_fst` (→ `firstType`), `gen_snd` (→ `secondType`), `gen_pathApp`
(→ `carrierCode`) — so a child step leaves the output literally unchanged and the result `Conv` is the
head-inversion's conversion leg directly (no output drift, unlike `app`'s argument arm).

Each arm takes the context well-formedness `WfContextUnion` (threaded by the eventual congruence induction;
needed to reclassify the stepped child through validity) and the per-child single-step subject reduction
(the IH).  The proof is uniform:

  1. invert the eliminator cell (`invertAtFstHead` / `invertAtSndHead` / `invertAtPathAppHead`) to recover
     the scrutinee at its data/bridge code, the index params, and the classifier convertible to the param
     output;
  2. re-type the stepped child by the IH;
  3. reclassify it back to its original (convertible) code through validity (`classifierIsType` +
     `reclassifyToType`);
  4. recover the output-param formedness obligation from validity (`fstOutputFormed_ofValidity` /
     `sndOutputFormed_ofValidity` / `pathAppOutputFormed_ofValidity`) — the universe level/flag the rebuilt
     elim cell pins;
  5. rebuild via the native `elim` arm and land the output `Conv` (the param is unchanged, so it is the
     inversion's conversion leg).

`pathApp` has two children (path + interval argument), so it ships two arms — but both outputs are the
unchanged `carrierCode`, so neither drifts.

## Zero-axiom verification

The shipped inversions / validity component-formedness lemmas / `reclassifyToType` / native `elim` arm
composed with `Conv.sym`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The `fst` congruence subject reduction.**  When the pair scrutinee of a typed `fstCell` steps, the
reformed projection re-types at the SAME `firstType` output (a param, unchanged): the stepped scrutinee is
re-typed by the IH and reclassified back to the product code through validity, then the `fst` cell is
rebuilt with the validity-recovered `firstType` formedness obligation. -/
theorem HasTypeUnion.fstScrutineeCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {pairTerm pairReduct classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context (fstCell pairTerm) classifier)
    (scrutineeStep : Step pairTerm pairReduct)
    (childSubjectReduction : ∀ {subterm reduct subtermType : RawTerm scope},
      HasTypeUnion profile context subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm scope,
          HasTypeUnion profile context reduct reductType ∧ Conv subtermType reductType)
    -- ★ A1-CONJUNCT-WIRE: the rebuilt `fst`'s scrutinee-position obligation must be fibrantly usable (a precondition
    -- — the projected pair reduct stays usable); the `firstType` output param is universe-typed, so its usability
    -- is DERIVED from the recovered output formedness via `typedAtUniverseImpliesFibrantlyUsable`.
    :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (fstCell pairReduct) pinned ∧ Conv classifier pinned := by
  obtain ⟨secondType, firstType, pairTyped, classifierConv⟩ :=
    HasTypeUnion.invertAtFstHead typed rfl
  obtain ⟨pairReductType, pairReductTyped, pairTypeConv⟩ :=
    childSubjectReduction pairTyped scrutineeStep
  have productIsType : UnionClassifierIsType profile context (productTypeCell firstType secondType) :=
    HasTypeUnion.classifierIsType pairTyped wellFormed
  have pairReductAtProduct :
      HasTypeUnion profile context pairReduct (productTypeCell firstType secondType) :=
    HasTypeUnion.reclassifyToType pairReductTyped pairTypeConv.sym productIsType
  obtain ⟨firstLevel, firstFlag, firstTyped⟩ :=
    UnionClassifierIsType.fstOutputFormed_ofValidity context firstType secondType productIsType
  refine ⟨firstType, ?_, classifierConv.sym⟩
  refine HasTypeUnion.elim context .gen_fst fstElimRule
    (.childCons pairReduct .childNil)
    (.childCons firstType (.childCons secondType .childNil))
    firstLevel firstLevel firstFlag rfl ?_
  · intro obligation hmem
    cases hmem with
    | head => exact pairReductAtProduct
    | tail _ hmem => cases hmem with
      | head => exact firstTyped
      | tail _ hmem => cases hmem

/-- **The `snd` congruence subject reduction.**  The `fst` twin at the second projection: the output is the
unchanged `secondType` param, recovered formed via `sndOutputFormed_ofValidity`. -/
theorem HasTypeUnion.sndScrutineeCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {pairTerm pairReduct classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context (sndCell pairTerm) classifier)
    (scrutineeStep : Step pairTerm pairReduct)
    (childSubjectReduction : ∀ {subterm reduct subtermType : RawTerm scope},
      HasTypeUnion profile context subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm scope,
          HasTypeUnion profile context reduct reductType ∧ Conv subtermType reductType)
    -- ★ A1-CONJUNCT-WIRE: the rebuilt `snd`'s scrutinee-position obligation must be fibrantly usable (precondition);
    -- the `secondType` output param is universe-typed, so its usability is DERIVED via the universe bridge.
    :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (sndCell pairReduct) pinned ∧ Conv classifier pinned := by
  obtain ⟨firstType, secondType, pairTyped, classifierConv⟩ :=
    HasTypeUnion.invertAtSndHead typed rfl
  obtain ⟨pairReductType, pairReductTyped, pairTypeConv⟩ :=
    childSubjectReduction pairTyped scrutineeStep
  have productIsType : UnionClassifierIsType profile context (productTypeCell firstType secondType) :=
    HasTypeUnion.classifierIsType pairTyped wellFormed
  have pairReductAtProduct :
      HasTypeUnion profile context pairReduct (productTypeCell firstType secondType) :=
    HasTypeUnion.reclassifyToType pairReductTyped pairTypeConv.sym productIsType
  obtain ⟨secondLevel, secondFlag, secondTyped⟩ :=
    UnionClassifierIsType.sndOutputFormed_ofValidity context firstType secondType productIsType
  refine ⟨secondType, ?_, classifierConv.sym⟩
  refine HasTypeUnion.elim context .gen_snd sndElimRule
    (.childCons pairReduct .childNil)
    (.childCons firstType (.childCons secondType .childNil))
    secondLevel secondLevel secondFlag rfl ?_
  · intro obligation hmem
    cases hmem with
    | head => exact pairReductAtProduct
    | tail _ hmem => cases hmem with
      | head => exact secondTyped
      | tail _ hmem => cases hmem

/-- **The `pathApp` congruence subject reduction at the PATH position.**  When the path child of a typed
`pathAppCell` steps, the reformed cell re-types at the unchanged `carrierCode` output: the stepped path is
re-typed by the IH and reclassified back to the bridge code through validity, then the `pathApp` cell is
rebuilt with the validity-recovered `carrierCode` formedness obligation. -/
theorem HasTypeUnion.pathAppPathCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {path pathReduct argument classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context (pathAppCell path argument) classifier)
    (pathStep : Step path pathReduct)
    (childSubjectReduction : ∀ {subterm reduct subtermType : RawTerm scope},
      HasTypeUnion profile context subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm scope,
          HasTypeUnion profile context reduct reductType ∧ Conv subtermType reductType) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (pathAppCell pathReduct argument) pinned ∧ Conv classifier pinned := by
  obtain ⟨carrierCode, leftEndpoint, rightEndpoint, pathTyped, argumentTyped, classifierConv⟩ :=
    HasTypeUnion.invertAtPathAppHead typed rfl
  obtain ⟨pathReductType, pathReductTyped, pathTypeConv⟩ :=
    childSubjectReduction pathTyped pathStep
  have bridgeIsType :
      UnionClassifierIsType profile context
        (bridgeTypeCell carrierCode leftEndpoint rightEndpoint) :=
    HasTypeUnion.classifierIsType pathTyped wellFormed
  have pathReductAtBridge :
      HasTypeUnion profile context pathReduct
        (bridgeTypeCell carrierCode leftEndpoint rightEndpoint) :=
    HasTypeUnion.reclassifyToType pathReductTyped pathTypeConv.sym bridgeIsType
  obtain ⟨carrierLevel, carrierFlag, carrierTyped⟩ :=
    UnionClassifierIsType.pathAppOutputFormed_ofValidity context carrierCode leftEndpoint rightEndpoint
      bridgeIsType
  refine ⟨carrierCode, ?_, classifierConv⟩
  refine HasTypeUnion.elim context .gen_pathApp pathAppElimRule
    (.childCons pathReduct (.childCons argument .childNil))
    (.childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
    carrierLevel carrierLevel carrierFlag rfl ?_
  · intro obligation hmem
    cases hmem with
    | head => exact pathReductAtBridge
    | tail _ hmem => cases hmem with
      | head => exact argumentTyped
      | tail _ hmem => cases hmem with
        | head => exact carrierTyped
        | tail _ hmem => cases hmem

/-- **The `pathApp` congruence subject reduction at the ARGUMENT (interval) position.**  The interval
argument also leaves the `carrierCode` output unchanged; the stepped argument is re-typed by the IH and
reclassified back to `intervalTypeCell` through validity. -/
theorem HasTypeUnion.pathAppArgumentCongruenceSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {path argument argumentReduct classifier : RawTerm scope}
    (wellFormed : WfContextUnion context)
    (typed : HasTypeUnion profile context (pathAppCell path argument) classifier)
    (argumentStep : Step argument argumentReduct)
    (childSubjectReduction : ∀ {subterm reduct subtermType : RawTerm scope},
      HasTypeUnion profile context subterm subtermType → Step subterm reduct →
        ∃ reductType : RawTerm scope,
          HasTypeUnion profile context reduct reductType ∧ Conv subtermType reductType)
    -- ★ A1-CONJUNCT-WIRE: the rebuilt `pathApp`'s obligations are path@bridge (.fibrant), argumentReduct@interval
    -- (.dimensional), carrier@universe (.fibrant).  The unchanged path's fibrant usability and the stepped interval
    -- argument's reduct DIMENSIONAL usability are preconditions; the carrier param's usability is DERIVED via the
    -- universe bridge.
    :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context (pathAppCell path argumentReduct) pinned ∧ Conv classifier pinned := by
  obtain ⟨carrierCode, leftEndpoint, rightEndpoint, pathTyped, argumentTyped, classifierConv⟩ :=
    HasTypeUnion.invertAtPathAppHead typed rfl
  obtain ⟨argumentReductType, argumentReductTyped, argumentTypeConv⟩ :=
    childSubjectReduction argumentTyped argumentStep
  have intervalIsType : UnionClassifierIsType profile context intervalTypeCell :=
    HasTypeUnion.classifierIsType argumentTyped wellFormed
  have argumentReductAtInterval :
      HasTypeUnion profile context argumentReduct intervalTypeCell :=
    HasTypeUnion.reclassifyToType argumentReductTyped argumentTypeConv.sym intervalIsType
  have bridgeIsType :
      UnionClassifierIsType profile context
        (bridgeTypeCell carrierCode leftEndpoint rightEndpoint) :=
    HasTypeUnion.classifierIsType pathTyped wellFormed
  obtain ⟨carrierLevel, carrierFlag, carrierTyped⟩ :=
    UnionClassifierIsType.pathAppOutputFormed_ofValidity context carrierCode leftEndpoint rightEndpoint
      bridgeIsType
  refine ⟨carrierCode, ?_, classifierConv⟩
  refine HasTypeUnion.elim context .gen_pathApp pathAppElimRule
    (.childCons path (.childCons argumentReduct .childNil))
    (.childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
    carrierLevel carrierLevel carrierFlag rfl ?_
  · intro obligation hmem
    cases hmem with
    | head => exact pathTyped
    | tail _ hmem => cases hmem with
      | head => exact argumentReductAtInterval
      | tail _ hmem => cases hmem with
        | head => exact carrierTyped
        | tail _ hmem => cases hmem

end FX1Poly.Typed
