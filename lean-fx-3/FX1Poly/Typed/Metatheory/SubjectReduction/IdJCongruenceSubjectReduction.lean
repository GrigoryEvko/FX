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

/-- **The eliminator-head inversion surfacing the row's typed obligations with SHARED existentials.**  Reads the
typings straight off the native `elim` node, exposing `obligationsHold` over the SAME `args` / `params` / levels
that pin the subject — so a TYPE-INDEX-PARAM obligation subject (like `idJ`'s right endpoint, which is not pinned
by the subject's cell shape) is recovered through THIS single shared-existential projection rather than a fresh
re-run of the generic inversion (each fresh call would re-introduce independent existential `params`).  Zero-axiom:
one-pass `induction` over `toNativeOnly` (the EXACT refutation arms of `invertAtElimHeadGeneric`), the surviving
`elim` arm projecting `premisesHold.toUnion`, the `conv` arm threading it through the IH.  (The `Usable` in the
name is legacy from the retired use-site usability conjunct; the inversion now surfaces typings only.) -/
theorem HasTypeUnion.invertAtElimHeadTypedAndUsableGeneric {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {generator : Generator} {rule : ElimRule}
    (isElim : elimRuleOf generator = some rule)
    (derivation : HasTypeUnion profile context subject classifier)
    (headIsGenerator : RawTerm.rootGenerator subject = generator) :
    ∃ (args : RawTermChildren rule.argShifts scope)
      (params : RawTermChildren rule.paramShifts scope)
      (level0 level1 : LevelExpr) (flag : UniverseFlag),
      subject = rule.memberCell scope args ∧
      (∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
        HasTypeUnion profile obligation.context obligation.subject obligation.classifier) ∧
      Conv (rule.outputType scope args params) classifier := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _ctx index =>
      have headEq : Generator.gen_var = generator := headIsGenerator
      rw [← headEq, show elimRuleOf Generator.gen_var = none from rfl] at isElim
      cases isElim
  | universeFormation _ctx _levelExpr _flag =>
      have headEq : Generator.gen_universeCode = generator := headIsGenerator
      rw [← headEq, show elimRuleOf Generator.gen_universeCode = none from rfl] at isElim
      cases isElim
  | formationRule _ctx formGen _payload _children _formRule _levels _carrier _level _flag
      isFormationRule _premisesHold _ihPremises =>
      have headEq : formGen = generator := headIsGenerator
      subst headEq
      rw [formationRuleOf_eq_none_ofElim isElim] at isFormationRule
      cases isFormationRule
  | intro _ctx introGen introRule introArgs _params _level0 _level1 _flag isIntro _sideHolds
      _premisesHold _ihPremises =>
      have headEq : introGen = generator :=
        (introMemberCellRootGenerator isIntro introArgs).symm.trans headIsGenerator
      subst headEq
      rw [introRuleOf_eq_none_ofElim isElim] at isIntro
      cases isIntro
  | elim _ctx elimGen elimRule elimArgs elimParams elimLevel0 elimLevel1 elimFlag isElim' premisesHold
      _ihPremises =>
      have headEq : elimGen = generator :=
        (elimMemberCellRootGenerator isElim' elimArgs).symm.trans headIsGenerator
      subst headEq
      have ruleEq : rule = elimRule := Option.some.inj (isElim.symm.trans isElim')
      subst ruleEq
      exact ⟨elimArgs, elimParams, elimLevel0, elimLevel1, elimFlag, rfl,
        fun obligation hmem => (premisesHold obligation hmem).toUnion, Conv.refl _⟩
  | conv _levelExpr _flag _typed converts _reclassifierTyped typedIH _reclassifierIH =>
      obtain ⟨args, params, level0, level1, flag, subjectShape, obligationsHold,
          outputConv⟩ := typedIH headIsGenerator
      exact ⟨args, params, level0, level1, flag, subjectShape, obligationsHold,
        outputConv.trans converts⟩

/-- **The `idJ`-head inversion surfacing ALL four premises with SHARED existentials.**  The `idJ`-row
`right : A` obligation subject is an existential TYPE-INDEX PARAM (not a cell child), so its TYPING cannot be
pinned to the subject by the per-head inversion's `rcases ⟨⟩` (which only pins the cell ARGS).  This wrapper
runs the idJ-row `match` (the same the per-head typing inversion uses) over
`invertAtElimHeadTypedAndUsableGeneric`, so the surfaced right-endpoint TYPING shares the row's `rightEndpoint`
with the other three premises.  The combined twin of `invertAtIdJHeadAllPremises`.  (The `WithRightUsable` name
and the `…TypedAndUsableGeneric` helper are legacy from the retired use-site usability conjunct — the inversion
now surfaces TYPINGS only; the lock-accessibility discipline lives solely at the variable rule.) -/
theorem HasTypeUnion.invertAtIdJHeadAllPremisesWithRightUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 2)} {baseCase witness : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = idJCell motive baseCase witness) :
    ∃ typeCode leftEndpoint rightEndpoint : RawTerm scope,
      HasTypeUnion profile context witness (idTypeCell typeCode leftEndpoint rightEndpoint) ∧
      HasTypeUnion profile context rightEndpoint typeCode ∧
      HasTypeUnion profile context baseCase
        (idJMotiveAt motive leftEndpoint (reflCell leftEndpoint)) ∧
      (∃ (motiveLevel : LevelExpr) (motiveFlag : UniverseFlag),
        HasTypeUnion profile
          ((context.cons typeCode).cons (idJMotiveSecondBinderType typeCode leftEndpoint)) motive
          (universeCodeCell motiveLevel motiveFlag)) ∧
      Conv (idJMotiveAt motive rightEndpoint witness) classifier := by
  obtain ⟨args, params, level0, _level1, flag, subjectIsMember, obligationsHold,
      outputConv⟩ :=
    derivation.invertAtElimHeadTypedAndUsableGeneric (rule := idJElimRule)
      (show elimRuleOf Generator.gen_idJ = some idJElimRule from rfl) (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold, outputConv with
  | .childCons _argMotive (.childCons _argBase (.childCons _argWitness .childNil)),
    .childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)),
    subjectIsMember, obligationsHold, outputConv =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨typeCode, leftEndpoint, rightEndpoint,
      obligationsHold _ (List.Mem.head _),
      obligationsHold _ (List.Mem.tail _ (List.Mem.head _)),
      obligationsHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
      ⟨level0, flag, obligationsHold _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))⟩,
      outputConv⟩

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
    HasTypeUnion.invertAtIdJHeadAllPremisesWithRightUsable typed rfl
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
  · intro obligation hmem
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
    HasTypeUnion.invertAtIdJHeadAllPremisesWithRightUsable typed rfl
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
  · intro obligation hmem
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
