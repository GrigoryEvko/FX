import FX1Poly.Typed.Engine.Classifier.TableTypingUnionDivergence
import FX1Poly.Typed.Engine.Union.HasTypeUnion

/-! # FX1Poly/Typed/UnionStaticTypingSoundness — the reserved-head refutation for the SINGLE union judgment

`StaticTypingSoundness.reservedHeadUntypedBySurvivingEngines` is the HON-5 honesty bundle for the
surviving standalone engines (grown + bridge): each disjunct says "a head the honesty classifier reports
reserved is untyped by THIS engine".  With the NATIVE-42/43 retirement collapsing the engine zoo into
`HasTypeUnion`, the honest statement collapses too: ONE lemma over the ONE judgment.  The classifier is `hasUnionEliminatorTypingRule` (`TableTypingUnionDivergence`) — the
full-union extension of the table classifier, which (unlike `hasSomeTypingRule`) tracks the three
union-only tables (`termIndexedFormerDescOf` / `nativeRecursiveElimRuleOf` / `listElimNativeRuleOf`).
Stating the refutation over the HONESTY classifier would be FALSE: the union types `natElim` / `natRec`
/ `listElim` / `idCode`-headed subjects, exactly the four strict-divergence witnesses — the pending
canonicity-collapse promotion decision stays untouched.

  * **`hasUnionEliminatorTypingRule_falsePeel`** — a union-reserved verdict forces all four disjuncts
    false (the propext-free `||`-peel, the union sibling of `hasTableTypingRule_falsePeel`).
  * **`hasSomeTypingRule_falseOfUnionReserved`** — union-reserved refines honesty-reserved (through the
    Leg-B equivalence), so the pre-union per-engine refutations remain applicable to the embeddings.
  * **`HasTypeUnion.reservedHeadUntyped`** (★) — the headline: a subject whose head the
    full-union classifier reports RESERVED is untyped by the union at EVERY context and classifier.
    Induction over the five union arms (`ofGrown · formationRule · intro · elim · conv`): the `ofGrown`
    embedding routes through the shipped per-engine refutation; the `formationRule` arm (base-type / flat /
    term-indexed) and the unified `intro` / `elim` arms each pin their generator by the table's `if`-chain,
    whereupon the subject's head computes LIVE, contradicting the verdict; the `conv` arm recurses (subject
    unchanged).
  * **`HasTypeUnion.headIsUnionLive`** (★) — the contrapositive consumer API: every union-typed
    subject's head is classifier-live.  This is the TRUTHFULNESS of `hasUnionEliminatorTypingRule`'s
    negative verdicts — `false` now means "the union types no such head", machine-checked, the exact
    property `hasSomeTypingRule` LOST when the union's recursive-eliminator arms landed.
  * Reserved-exemplar smoke: a `hilbertSpace`-headed subject is union-untypable.

## Zero-axiom

The peel reuses the propext-free `orEqFalse_leftFalse` / `orEqFalse_rightFalse`; the induction is
`by_cases` over decidable `Generator` equalities (instance-resolved, no `Classical`), `Option.some.inj`
on table hits, `if_neg` collapse on table misses, and `Bool.noConfusion` at the computed-live heads.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditUnionStaticTypingSoundness.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## The union-classifier false-peel -/

/-- **A union-reserved verdict forces every disjunct false.**  The four-way conjunction peeled off
`hasUnionEliminatorTypingRule generator = false` via the propext-free `||`-projections: the table
classifier and the three union-only tables are all empty at the head. -/
theorem hasUnionEliminatorTypingRule_falsePeel {generator : Generator}
    (reserved : hasUnionEliminatorTypingRule generator = false) :
    hasTableTypingRule generator = false ∧
    (termIndexedFormerDescOf generator).isSome = false ∧
    (nativeRecursiveElimRuleOf generator).isSome = false ∧
    (listElimNativeRuleOf generator).isSome = false := by
  unfold hasUnionEliminatorTypingRule at reserved
  have peelThree := reserved
  have peelTwo := orEqFalse_leftFalse peelThree
  have peelOne := orEqFalse_leftFalse peelTwo
  exact ⟨orEqFalse_leftFalse peelOne, orEqFalse_rightFalse peelOne,
    orEqFalse_rightFalse peelTwo, orEqFalse_rightFalse peelThree⟩

/-- **Union-reserved refines honesty-reserved.**  A head the full-union classifier reports reserved is
reserved for the honesty classifier too (through the Leg-B equivalence
`hasSomeTypingRule_eq_hasTableTypingRule`), so the shipped pre-union per-engine refutations apply to
the union's engine embeddings unchanged. -/
theorem hasSomeTypingRule_falseOfUnionReserved {generator : Generator}
    (reserved : hasUnionEliminatorTypingRule generator = false) :
    hasSomeTypingRule generator = false := by
  rw [hasSomeTypingRule_eq_hasTableTypingRule]
  exact (hasUnionEliminatorTypingRule_falsePeel reserved).1

/-! ## ★ The union reserved-head refutation -/

/-- **★ A head the full-union classifier reports RESERVED is untyped by the union** — at every
context and every classifier.  The single-lemma successor of the HON-5 bundle
`reservedHeadUntypedBySurvivingEngines`: one judgment, one refutation.  Induction over the nineteen union
arms; every table-driven arm pins its generator through the table's `if`-chain and dies at the
computed-live head, the embeddings route through the per-engine refutations, the conv arm recurses. -/
theorem HasTypeUnion.reservedHeadUntyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier)
    (reserved : hasUnionEliminatorTypingRule (RawTerm.headGenerator subject) = false) : False := by
  revert reserved
  induction typed with
  | ofGrown hostTyped =>
      intro reserved
      exact grownReservedUntyped (hasSomeTypingRule_falseOfUnionReserved reserved) hostTyped
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      intro reserved
      cases rule with
      | baseType baseRule =>
          have tableReserved := (hasUnionEliminatorTypingRule_falsePeel reserved).1
          have baseTableEmpty : (baseTypeRuleDescOf generator).isSome = false :=
            (hasTableTypingRule_falsePeel tableReserved).2.2.2.2.1
          rw [show baseTypeRuleDescOf generator = some baseRule from
            formationRuleOf_baseType_inv isFormationRule] at baseTableEmpty
          exact Bool.noConfusion baseTableEmpty
      | flat flatRule =>
          have tableReserved := (hasUnionEliminatorTypingRule_falsePeel reserved).1
          have flatTableEmpty : (flatTypingRuleDescOf generator).isSome = false :=
            (hasTableTypingRule_falsePeel tableReserved).2.2.2.1
          rw [show flatTypingRuleDescOf generator = some flatRule from
            formationRuleOf_flat_inv isFormationRule] at flatTableEmpty
          exact Bool.noConfusion flatTableEmpty
      | cumulative cumulativeRule =>
          -- UNREACHABLE: `formationRuleOf` never produces a `.cumulative` rule (TYTAB-2 wave U1 additive only).
          exact absurd isFormationRule formationRuleOf_ne_cumulative
      | termIndexed termRule =>
          have formerTableEmpty : (termIndexedFormerDescOf generator).isSome = false :=
            (hasUnionEliminatorTypingRule_falsePeel reserved).2.1
          rw [show termIndexedFormerDescOf generator = some termRule from
            formationRuleOf_termIndexed_inv isFormationRule] at formerTableEmpty
          exact Bool.noConfusion formerTableEmpty
  | intro context generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      intro reserved
      -- The unified INTRODUCER arm: one arm replacing the four old per-family intro arms.  The subject
      -- is `rule.memberCell scope args`, the introducer cell.  `introRuleOf_cases` pins the generator
      -- and rule to one of the seventeen concrete rows; once `args` is destructured to the row's child
      -- shape, the cell reduces to `.mkGen <generator> …`, so `RawTerm.headGenerator subject` computes
      -- to that generator.  Each introducer generator is classifier-LIVE
      -- (`hasUnionEliminatorTypingRule <gen> = true`), contradicting the reserved verdict via
      -- `Bool.noConfusion` — exactly the per-family deaths the old arms achieved, now table-driven.
      rcases introRuleOf_cases isIntro with
          ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
          | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
          | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · -- boolTrue
        match args with
        | .childNil => exact Bool.noConfusion reserved
      · -- boolFalse
        match args with
        | .childNil => exact Bool.noConfusion reserved
      · -- unit
        match args with
        | .childNil => exact Bool.noConfusion reserved
      · -- interval0
        match args with
        | .childNil => exact Bool.noConfusion reserved
      · -- interval1
        match args with
        | .childNil => exact Bool.noConfusion reserved
      · -- natZero
        match args with
        | .childNil => exact Bool.noConfusion reserved
      · -- lam
        match args with
        | .childCons _domainCode (.childCons _body .childNil) => exact Bool.noConfusion reserved
      · -- pathLam
        match args with
        | .childCons _body .childNil => exact Bool.noConfusion reserved
      · -- natSucc
        match args with
        | .childCons _child .childNil => exact Bool.noConfusion reserved
      · -- listCons
        match args with
        | .childCons _head (.childCons _tail .childNil) => exact Bool.noConfusion reserved
      · -- optionSome
        match args with
        | .childCons _value .childNil => exact Bool.noConfusion reserved
      · -- optionNone
        match args with
        | .childNil => exact Bool.noConfusion reserved
      · -- listNil
        match args with
        | .childNil => exact Bool.noConfusion reserved
      · -- eitherInl
        match args with
        | .childCons _value .childNil => exact Bool.noConfusion reserved
      · -- eitherInr
        match args with
        | .childCons _value .childNil => exact Bool.noConfusion reserved
      · -- pair
        match args with
        | .childCons _child0 (.childCons _child1 .childNil) => exact Bool.noConfusion reserved
      · -- refl
        match args with
        | .childCons _witness .childNil => exact Bool.noConfusion reserved
  | elim context generator rule args params isElim premisesHold =>
      intro reserved
      -- The unified ELIMINATOR arm: one arm replacing the six old per-family elim arms.  The subject
      -- is `rule.memberCell scope args`, the eliminator cell.  `elimRuleOf_cases` pins the generator
      -- and rule to one of the eleven concrete rows; once `args` is destructured to the row's child
      -- shape, the cell reduces to `.mkGen <generator> …`, so `RawTerm.headGenerator subject` computes
      -- to that generator.  Each eliminator generator is classifier-LIVE
      -- (`hasUnionEliminatorTypingRule <gen> = true`), contradicting the reserved verdict via
      -- `Bool.noConfusion` — exactly the per-family deaths the old arms achieved, now table-driven.
      rcases elimRuleOf_cases isElim with
          ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
          | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · -- app
        match args with
        | .childCons _function (.childCons _argument .childNil) => exact Bool.noConfusion reserved
      · -- pathApp
        match args with
        | .childCons _path (.childCons _argument .childNil) => exact Bool.noConfusion reserved
      · -- natElim
        match args with
        | .childCons _motive (.childCons _baseBranch (.childCons _stepBranch
            (.childCons _scrutinee .childNil))) => exact Bool.noConfusion reserved
      · -- natRec
        match args with
        | .childCons _motive (.childCons _baseBranch (.childCons _stepBranch
            (.childCons _scrutinee .childNil))) => exact Bool.noConfusion reserved
      · -- boolElim
        match args with
        | .childCons _motive (.childCons _scrutinee (.childCons _thenBranch
            (.childCons _elseBranch .childNil))) => exact Bool.noConfusion reserved
      · -- optionMatch
        match args with
        | .childCons _motive (.childCons _noneBranch (.childCons _someBranch
            (.childCons _scrutinee .childNil))) => exact Bool.noConfusion reserved
      · -- eitherMatch
        match args with
        | .childCons _motive (.childCons _leftBranch (.childCons _rightBranch
            (.childCons _scrutinee .childNil))) => exact Bool.noConfusion reserved
      · -- idJ
        match args with
        | .childCons _motive (.childCons _baseCase (.childCons _witness .childNil)) =>
          exact Bool.noConfusion reserved
      · -- fst
        match args with
        | .childCons _pairTerm .childNil => exact Bool.noConfusion reserved
      · -- snd
        match args with
        | .childCons _pairTerm .childNil => exact Bool.noConfusion reserved
      · -- listElim
        match args with
        | .childCons _motive (.childCons _scrutinee (.childCons _nilBranch
            (.childCons _consBranch .childNil))) => exact Bool.noConfusion reserved
  | conv levelExpr flag typed converts reclassifierTyped typedIH reclassifierIH =>
      exact typedIH

/-! ## ★ The contrapositive consumer API -/

/-- **★ Every union-typed subject's head is classifier-LIVE.**  The contrapositive of
`reservedHeadUntyped`: `hasUnionEliminatorTypingRule`'s negative verdicts are TRUTHFUL about the union
— `false` means "the union types no subject with this head", the exact property the honesty classifier
lost when the union's recursive-eliminator arms and the Id retrofit landed. -/
theorem HasTypeUnion.headIsUnionLive {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier) :
    hasUnionEliminatorTypingRule (RawTerm.headGenerator subject) = true := by
  cases liveVerdict : hasUnionEliminatorTypingRule (RawTerm.headGenerator subject) with
  | true => rfl
  | false => exact (typed.reservedHeadUntyped liveVerdict).elim

/-! ## Reserved-exemplar smoke -/

/-- The tier-★ extension name stays reserved under the FULL-union classifier (not just the honesty
classifier) — the union tables carry no `hilbertSpace` row. -/
theorem hasUnionEliminatorTypingRule_hilbertSpace :
    hasUnionEliminatorTypingRule .gen_hilbertSpace = false := rfl

/-- **A `hilbertSpace`-headed subject is union-untypable** — the reserved-exemplar instantiation of
the headline refutation. -/
theorem HasTypeUnion.hilbertSpaceHeadUntyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (headIsHilbert : RawTerm.headGenerator subject = .gen_hilbertSpace)
    (typed : HasTypeUnion profile context subject classifier) : False :=
  typed.reservedHeadUntyped
    (by rw [headIsHilbert]; exact hasUnionEliminatorTypingRule_hilbertSpace)

end FX1Poly.Typed
