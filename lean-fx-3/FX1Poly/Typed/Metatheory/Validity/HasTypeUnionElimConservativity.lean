import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity

/-! # FX1Poly/Typed/Metatheory/Validity/HasTypeUnionElimConservativity — TYTAB-2 CONS

Conservativity of the Route-A elim-formedness hardening.  Route A (commit f5d99d0f) added a RESULT-type
formedness obligation as the LAST entry of every hardened eliminator row's `ElimRule.obligations`
(`{ subject := resultType, classifier := universeCodeCell level0 flag }`) and threaded `(level0 level1 flag)`
into the `elim` constructor of `HasTypeUnionOver`.  That STRENGTHENS the typing rules: in principle it could
reject an elimination the pre-Route-A kernel accepted.  We proved soundness + validity but NOT that
COMPLETENESS was preserved — the lone completeness asterisk on the whole arc.

This file discharges it as a per-row REFLECTION: for each hardened row, the elimination's GENUINE premises
(everything the pre-hardening relation required — scrutinee / branch / handler typings) PLUS `WfContextUnion`
yield the FULL hardened `elim`, with the result-formedness premise DISCHARGED — never assumed.  So the
hardening rejects no elimination whose genuine premises hold: old ⊆ new.  Equivalently, every pre-hardening
elim derivation embeds into the hardened one (the embedding is row-uniform; these theorems are its arms).

## The three regimes

  * **app — UNHARDENED.**  `appElimRule` carries NO formedness obligation (its output `subst0 codomain arg`
    is validated by the surrounding derivation's `classifierIsType`, not table-locally).  So app is
    conservative on the nose — no theorem needed, the relation is unchanged.

  * **The six branch-selecting rows (boolElim / natElim / natRec / optionMatch / idJ / listElim).**  The
    result type IS the classifier of a genuine BRANCH premise (then/else, base, base, none, base, nil).
    `classifierIsType` on that branch (now PARAMETER-FREE over `WfContextUnion`, Route A) supplies the
    result-formedness witness directly.  UNCONDITIONAL.

  * **The two projection rows + pathApp (fst / snd / pathApp).**  The result type is a COMPONENT / carrier of
    the scrutinee's data code, recovered by `classifierIsType` on the scrutinee + the shipped output helpers
    (`fstOutputFormed_ofValidity` / `sndOutputFormed_ofValidity` / `pathAppOutputFormed_ofValidity`).
    UNCONDITIONAL.

## The lone residual — eitherMatch

`eitherMatch` is the one row whose result type `C` is NOT a genuine-premise classifier: both branches are
handlers `A -> C` / `B -> C`, so `C` sits UNDER the handler binder as the weakened codomain `weaken C`.
Recovering `C`'s formedness from `A -> C`'s validity needs to STRENGTHEN `weaken C` (a type under `cons A`)
back to `C` in the base context — a codomain-strengthening lemma the union does not yet ship (and exactly the
fact Route A premised directly to retire the deleted `eitherMatchOutputFormed` oracle).  It IS conservative
(`A -> C` well-formed forces `C` well-formed), only the strengthening proof is missing; isolated as the named
`CodomainStrengthens` obligation, with `eitherMatchConservativeOfStrengthening` reducing eitherMatch
conservativity to it.

## Zero-axiom

Each arm is `classifierIsType` (or a shipped output helper) feeding the unified `elim` builder with a
`premisesHold` that dispatches the obligation list by `List.Mem` `cases`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditHasTypeUnionElimConservativity.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax FX1Poly.Modal

/-! ## (1) The six branch-selecting rows -/

/-- **boolElim conservativity.**  The genuine premises (scrutinee at `Bool`, both branches at `resultType`)
plus `WfContextUnion` build the hardened `boolElim`: `classifierIsType` on the then-branch supplies the
result-formedness premise.  The vestigial type params (unused by the row's obligations) are instantiated to
`boolTypeCell`. -/
theorem boolElimConservative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (motive : RawTerm (scope + 1)) (scrutinee thenBranch elseBranch resultType : RawTerm scope)
    (scrutineeTyped : HasTypeUnion profile context scrutinee boolTypeCell)
    (thenTyped : HasTypeUnion profile context thenBranch resultType)
    (elseTyped : HasTypeUnion profile context elseBranch resultType)
    (wellFormed : WfContextUnion context) :
    HasTypeUnion profile context (boolElimCell motive scrutinee thenBranch elseBranch) resultType := by
  obtain ⟨level0, flag, resultFormed⟩ := thenTyped.classifierIsType wellFormed
  refine HasTypeUnion.elim context .gen_boolElim boolElimRule
    (.childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil))))
    (.childCons boolTypeCell (.childCons boolTypeCell (.childCons resultType .childNil)))
    level0 level0 flag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact thenTyped
    | tail _ hmem => cases hmem with
      | head => exact elseTyped
      | tail _ hmem => cases hmem with
        | head => exact resultFormed
        | tail _ hmem => cases hmem

/-- **natElim conservativity.**  Genuine premises: scrutinee at `Nat`, base branch at `resultType`, step
branch at the twice-weakened result in the two-cell-extended context.  `classifierIsType` on the base branch
supplies result formedness. -/
theorem natElimConservative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (motive : RawTerm (scope + 1)) (baseBranch : RawTerm scope) (stepBranch : RawTerm (scope + 2))
    (scrutinee resultType : RawTerm scope)
    (scrutineeTyped : HasTypeUnion profile context scrutinee natTypeCell)
    (baseTyped : HasTypeUnion profile context baseBranch resultType)
    (stepTyped : HasTypeUnion profile ((context.cons natTypeCell).cons (RawTerm.weaken resultType))
      stepBranch (RawTerm.weaken (RawTerm.weaken resultType)))
    (wellFormed : WfContextUnion context) :
    HasTypeUnion profile context (natElimCell motive baseBranch stepBranch scrutinee) resultType := by
  obtain ⟨level0, flag, resultFormed⟩ := baseTyped.classifierIsType wellFormed
  refine HasTypeUnion.elim context .gen_natElim natElimRule
    (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))))
    (.childCons resultType .childNil) level0 level0 flag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact baseTyped
    | tail _ hmem => cases hmem with
      | head => exact stepTyped
      | tail _ hmem => cases hmem with
        | head => exact resultFormed
        | tail _ hmem => cases hmem

/-- **natRec conservativity.**  The dependent-recursor twin of `natElimConservative`. -/
theorem natRecConservative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (motive : RawTerm (scope + 1)) (baseBranch : RawTerm scope) (stepBranch : RawTerm (scope + 2))
    (scrutinee resultType : RawTerm scope)
    (scrutineeTyped : HasTypeUnion profile context scrutinee natTypeCell)
    (baseTyped : HasTypeUnion profile context baseBranch resultType)
    (stepTyped : HasTypeUnion profile ((context.cons natTypeCell).cons (RawTerm.weaken resultType))
      stepBranch (RawTerm.weaken (RawTerm.weaken resultType)))
    (wellFormed : WfContextUnion context) :
    HasTypeUnion profile context (natRecCell motive baseBranch stepBranch scrutinee) resultType := by
  obtain ⟨level0, flag, resultFormed⟩ := baseTyped.classifierIsType wellFormed
  refine HasTypeUnion.elim context .gen_natRec natRecElimRule
    (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))))
    (.childCons resultType .childNil) level0 level0 flag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact baseTyped
    | tail _ hmem => cases hmem with
      | head => exact stepTyped
      | tail _ hmem => cases hmem with
        | head => exact resultFormed
        | tail _ hmem => cases hmem

/-- **optionMatch conservativity.**  Genuine premises: scrutinee at `option(elementType)`, none branch at
`resultType`, some handler at `elementType -> resultType`.  `classifierIsType` on the none branch supplies
result formedness; the vestigial second type param is instantiated to `elementType`. -/
theorem optionMatchConservative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (motive : RawTerm (scope + 1)) (noneBranch someBranch scrutinee elementType resultType : RawTerm scope)
    (scrutineeTyped : HasTypeUnion profile context scrutinee (optionTypeCell elementType))
    (noneTyped : HasTypeUnion profile context noneBranch resultType)
    (someTyped : HasTypeUnion profile context someBranch
      (piTyCodeCell elementType (RawTerm.weaken resultType)))
    (wellFormed : WfContextUnion context) :
    HasTypeUnion profile context (optionMatchCell motive noneBranch someBranch scrutinee) resultType := by
  obtain ⟨level0, flag, resultFormed⟩ := noneTyped.classifierIsType wellFormed
  refine HasTypeUnion.elim context .gen_optionMatch optionMatchElimRule
    (.childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))))
    (.childCons elementType (.childCons elementType (.childCons resultType .childNil)))
    level0 level0 flag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact noneTyped
    | tail _ hmem => cases hmem with
      | head => exact someTyped
      | tail _ hmem => cases hmem with
        | head => exact resultFormed
        | tail _ hmem => cases hmem

/-- **idJ conservativity.**  Genuine premises: witness at the reflexive identity code, base case at
`resultType`.  `classifierIsType` on the base case supplies result formedness. -/
theorem idJConservative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (motive : RawTerm (scope + 2)) (baseCase witness typeCode endpoint resultType : RawTerm scope)
    (witnessTyped : HasTypeUnion profile context witness (idTypeCell typeCode endpoint endpoint))
    (baseTyped : HasTypeUnion profile context baseCase resultType)
    (wellFormed : WfContextUnion context) :
    HasTypeUnion profile context (idJCell motive baseCase witness) resultType := by
  obtain ⟨level0, flag, resultFormed⟩ := baseTyped.classifierIsType wellFormed
  refine HasTypeUnion.elim context .gen_idJ idJElimRule
    (.childCons motive (.childCons baseCase (.childCons witness .childNil)))
    (.childCons typeCode (.childCons endpoint (.childCons resultType .childNil)))
    level0 level0 flag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact witnessTyped
  | tail _ hmem => cases hmem with
    | head => exact baseTyped
    | tail _ hmem => cases hmem with
      | head => exact resultFormed
      | tail _ hmem => cases hmem

/-- **listElim conservativity.**  Genuine premises: scrutinee at `List(elementType)`, nil branch at
`resultType`, cons branch at the step-function type.  `classifierIsType` on the nil branch supplies result
formedness. -/
theorem listElimConservative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (motive : RawTerm (scope + 1)) (scrutinee nilBranch consBranch elementType resultType : RawTerm scope)
    (scrutineeTyped : HasTypeUnion profile context scrutinee (listTypeCell elementType))
    (nilTyped : HasTypeUnion profile context nilBranch resultType)
    (consTyped : HasTypeUnion profile context consBranch
      (listStepFunctionType elementType resultType))
    (wellFormed : WfContextUnion context) :
    HasTypeUnion profile context (listElimCell motive scrutinee nilBranch consBranch) resultType := by
  obtain ⟨level0, flag, resultFormed⟩ := nilTyped.classifierIsType wellFormed
  refine HasTypeUnion.elim context .gen_listElim listElimRule
    (.childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))))
    (.childCons elementType (.childCons resultType .childNil)) level0 level0 flag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact nilTyped
    | tail _ hmem => cases hmem with
      | head => exact consTyped
      | tail _ hmem => cases hmem with
        | head => exact resultFormed
        | tail _ hmem => cases hmem

/-! ## (2) The two projection rows + pathApp (output recovered from the scrutinee's data code) -/

/-- **fst conservativity.**  Genuine premise: the pair at `product(firstType, secondType)`.
`classifierIsType` on the pair + `fstOutputFormed_ofValidity` supply the first-component formedness. -/
theorem fstConservative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (pairTerm firstType secondType : RawTerm scope)
    (pairTyped : HasTypeUnion profile context pairTerm (productTypeCell firstType secondType))
    (wellFormed : WfContextUnion context) :
    HasTypeUnion profile context (fstCell pairTerm) firstType := by
  obtain ⟨level0, flag, firstFormed⟩ :=
    UnionClassifierIsType.fstOutputFormed_ofValidity context firstType secondType
      (pairTyped.classifierIsType wellFormed)
  refine HasTypeUnion.elim context .gen_fst fstElimRule
    (.childCons pairTerm .childNil)
    (.childCons firstType (.childCons secondType .childNil)) level0 level0 flag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact pairTyped
  | tail _ hmem => cases hmem with
    | head => exact firstFormed
    | tail _ hmem => cases hmem

/-- **snd conservativity.**  The `fst` twin, recovering the second component via
`sndOutputFormed_ofValidity`. -/
theorem sndConservative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (pairTerm firstType secondType : RawTerm scope)
    (pairTyped : HasTypeUnion profile context pairTerm (productTypeCell firstType secondType))
    (wellFormed : WfContextUnion context) :
    HasTypeUnion profile context (sndCell pairTerm) secondType := by
  obtain ⟨level0, flag, secondFormed⟩ :=
    UnionClassifierIsType.sndOutputFormed_ofValidity context firstType secondType
      (pairTyped.classifierIsType wellFormed)
  refine HasTypeUnion.elim context .gen_snd sndElimRule
    (.childCons pairTerm .childNil)
    (.childCons firstType (.childCons secondType .childNil)) level0 level0 flag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact pairTyped
  | tail _ hmem => cases hmem with
    | head => exact secondFormed
    | tail _ hmem => cases hmem

/-- **pathApp conservativity.**  Genuine premises: path at `bridge(carrier, left, right)`, argument at the
interval.  `classifierIsType` on the path + `pathAppOutputFormed_ofValidity` supply the carrier formedness. -/
theorem pathAppConservative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (path argument carrierCode leftEndpoint rightEndpoint : RawTerm scope)
    (pathTyped : HasTypeUnion profile context path
      (bridgeTypeCell carrierCode leftEndpoint rightEndpoint))
    (argTyped : HasTypeUnion profile context argument intervalTypeCell)
    (wellFormed : WfContextUnion context) :
    HasTypeUnion profile context (pathAppCell path argument) carrierCode := by
  obtain ⟨level0, flag, carrierFormed⟩ :=
    UnionClassifierIsType.pathAppOutputFormed_ofValidity context carrierCode leftEndpoint rightEndpoint
      (pathTyped.classifierIsType wellFormed)
  refine HasTypeUnion.elim context .gen_pathApp pathAppElimRule
    (.childCons path (.childCons argument .childNil))
    (.childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)))
    level0 level0 flag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact pathTyped
  | tail _ hmem => cases hmem with
    | head => exact argTyped
    | tail _ hmem => cases hmem with
      | head => exact carrierFormed
      | tail _ hmem => cases hmem

/-! ## (3) The lone residual — eitherMatch reduces to a codomain-strengthening lemma -/

/-- **The codomain-strengthening obligation.**  A weakened code that is a type under one extra binder is a
type in the base context — the inverse-weakening (strengthening) fact for a code with NO occurrence of the
fresh variable.  This is the SOLE ingredient missing from `eitherMatch` conservativity: the eitherMatch
result type `C` sits as the weakened handler codomain `weaken C` under the handler binder, and recovering
`C`'s formedness from `A -> C`'s validity strengthens `weaken C` back to `C`.  It IS true (a Pi code is
well-formed only if its codomain is), but the only shipped strengthening (`HasTypeUnion.strengthenAtUniverse`)
is HOST-flavored — it needs `WfContextDescPi` + `IsTypeDescPi bindingType` and discharges an
`UnionTableReflectionResidual` oracle, whereas here the binder `leftType` is a UNION type and only
`WfContextUnion` is in hand.  So the `WfContextUnion`-native strengthening is still open — it is the exact
fact Route A premised directly to retire the deleted `eitherMatchOutputFormed` oracle. -/
abbrev CodomainStrengthens (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) : Prop :=
  ∀ (binderType resultType : RawTerm scope),
    UnionClassifierIsType profile (context.cons binderType) (RawTerm.weaken resultType) →
      UnionClassifierIsType profile context resultType

/-- **eitherMatch conservativity, modulo codomain strengthening.**  Genuine premises: scrutinee at
`either(leftType, rightType)`, left handler at `leftType -> resultType`, right handler at
`rightType -> resultType`.  `classifierIsType` on the left handler gives `leftType -> resultType` is a type;
`invertAtPiCodeHeadCodomain` surfaces `weaken resultType` as a type under the `leftType` binder; the
`CodomainStrengthens` obligation descends it to `resultType`'s formedness, which builds the hardened
`eitherMatch`.  The ONLY non-self-contained conservativity arm — every other row is unconditional. -/
theorem eitherMatchConservativeOfStrengthening {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (strengthens : CodomainStrengthens profile context)
    (motive : RawTerm (scope + 1)) (leftBranch rightBranch scrutinee leftType rightType resultType : RawTerm scope)
    (scrutineeTyped : HasTypeUnion profile context scrutinee (eitherTypeCell leftType rightType))
    (leftTyped : HasTypeUnion profile context leftBranch
      (piTyCodeCell leftType (RawTerm.weaken resultType)))
    (rightTyped : HasTypeUnion profile context rightBranch
      (piTyCodeCell rightType (RawTerm.weaken resultType)))
    (wellFormed : WfContextUnion context) :
    HasTypeUnion profile context (eitherMatchCell motive leftBranch rightBranch scrutinee) resultType := by
  -- `leftType -> resultType` is a type; invert its codomain leg under the `leftType` binder.
  obtain ⟨_handlerLevel, _handlerFlag, handlerTyped⟩ := leftTyped.classifierIsType wellFormed
  have codomainUnderBinder : UnionClassifierIsType profile (context.cons leftType)
      (RawTerm.weaken resultType) :=
    HasTypeUnion.invertAtPiCodeHeadCodomain handlerTyped rfl
  obtain ⟨level0, flag, resultFormed⟩ := strengthens leftType resultType codomainUnderBinder
  refine HasTypeUnion.elim context .gen_eitherMatch eitherMatchElimRule
    (.childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))))
    (.childCons leftType (.childCons rightType (.childCons resultType .childNil)))
    level0 level0 flag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact scrutineeTyped
  | tail _ hmem => cases hmem with
    | head => exact leftTyped
    | tail _ hmem => cases hmem with
      | head => exact rightTyped
      | tail _ hmem => cases hmem with
        | head => exact resultFormed
        | tail _ hmem => cases hmem

/-! ## (4) Coverage record + witness

The hardening is conservative on every reducing-eliminator row: ten of the eleven rows UNCONDITIONALLY (app
is unhardened, the six branch-selecting + fst/snd/pathApp via `classifierIsType`), and `eitherMatch` modulo
the single `CodomainStrengthens` lemma.  An inhabitant certifies the conservativity arms are exercised. -/

/-- **The elim-hardening conservativity coverage record.**  Each field is a distinct per-row conservativity
arm: the genuine premises plus `WfContextUnion` build the hardened elim (its result-formedness obligation
discharged, never assumed).  `eitherMatch` carries the `CodomainStrengthens` hypothesis — the lone residual.
`app` is omitted: it was never hardened (its row has no formedness obligation), so it is conservative on the
nose. -/
structure ElimHardeningConservativeCoverage (profile : PolyProfile) : Prop where
  /-- boolElim conservativity. -/
  boolElim : ∀ {scope : Nat} {context : TypingContext profile scope}
    (motive : RawTerm (scope + 1)) (scrutinee thenBranch elseBranch resultType : RawTerm scope),
    HasTypeUnion profile context scrutinee boolTypeCell →
    HasTypeUnion profile context thenBranch resultType →
    HasTypeUnion profile context elseBranch resultType →
    WfContextUnion context →
    HasTypeUnion profile context (boolElimCell motive scrutinee thenBranch elseBranch) resultType
  /-- listElim conservativity. -/
  listElim : ∀ {scope : Nat} {context : TypingContext profile scope}
    (motive : RawTerm (scope + 1)) (scrutinee nilBranch consBranch elementType resultType : RawTerm scope),
    HasTypeUnion profile context scrutinee (listTypeCell elementType) →
    HasTypeUnion profile context nilBranch resultType →
    HasTypeUnion profile context consBranch (listStepFunctionType elementType resultType) →
    WfContextUnion context →
    HasTypeUnion profile context (listElimCell motive scrutinee nilBranch consBranch) resultType
  /-- fst conservativity. -/
  fst : ∀ {scope : Nat} {context : TypingContext profile scope}
    (pairTerm firstType secondType : RawTerm scope),
    HasTypeUnion profile context pairTerm (productTypeCell firstType secondType) →
    WfContextUnion context →
    HasTypeUnion profile context (fstCell pairTerm) firstType
  /-- pathApp conservativity. -/
  pathApp : ∀ {scope : Nat} {context : TypingContext profile scope}
    (path argument carrierCode leftEndpoint rightEndpoint : RawTerm scope),
    HasTypeUnion profile context path (bridgeTypeCell carrierCode leftEndpoint rightEndpoint) →
    HasTypeUnion profile context argument intervalTypeCell →
    WfContextUnion context →
    HasTypeUnion profile context (pathAppCell path argument) carrierCode
  /-- eitherMatch conservativity, modulo the codomain-strengthening residual. -/
  eitherMatchModuloStrengthening : ∀ {scope : Nat} {context : TypingContext profile scope},
    CodomainStrengthens profile context →
    ∀ (motive : RawTerm (scope + 1))
      (leftBranch rightBranch scrutinee leftType rightType resultType : RawTerm scope),
    HasTypeUnion profile context scrutinee (eitherTypeCell leftType rightType) →
    HasTypeUnion profile context leftBranch (piTyCodeCell leftType (RawTerm.weaken resultType)) →
    HasTypeUnion profile context rightBranch (piTyCodeCell rightType (RawTerm.weaken resultType)) →
    WfContextUnion context →
    HasTypeUnion profile context (eitherMatchCell motive leftBranch rightBranch scrutinee) resultType

/-- **The conservativity coverage witness** — inhabited by the shipped per-row arms, so the conservativity
guarantee cannot silently shrink. -/
theorem elimHardeningConservativeCoverageWitness {profile : PolyProfile} :
    ElimHardeningConservativeCoverage profile where
  boolElim := fun motive scrutinee thenBranch elseBranch resultType scrutineeTyped thenTyped elseTyped
      wellFormed =>
    boolElimConservative motive scrutinee thenBranch elseBranch resultType scrutineeTyped thenTyped
      elseTyped wellFormed
  listElim := fun motive scrutinee nilBranch consBranch elementType resultType scrutineeTyped nilTyped
      consTyped wellFormed =>
    listElimConservative motive scrutinee nilBranch consBranch elementType resultType scrutineeTyped
      nilTyped consTyped wellFormed
  fst := fun pairTerm firstType secondType pairTyped wellFormed =>
    fstConservative pairTerm firstType secondType pairTyped wellFormed
  pathApp := fun path argument carrierCode leftEndpoint rightEndpoint pathTyped argTyped wellFormed =>
    pathAppConservative path argument carrierCode leftEndpoint rightEndpoint pathTyped argTyped wellFormed
  eitherMatchModuloStrengthening := fun strengthens motive leftBranch rightBranch scrutinee leftType
      rightType resultType scrutineeTyped leftTyped rightTyped wellFormed =>
    eitherMatchConservativeOfStrengthening strengthens motive leftBranch rightBranch scrutinee leftType
      rightType resultType scrutineeTyped leftTyped rightTyped wellFormed

end FX1Poly.Typed
