import FX1Poly.Core.ReducibleType

/-! # Foundation/PolyCell/Core/StratifiedReducibleType
    — the level-indexed (Tarski-universe) reducibility relation

The pure-SN `ReducibleType` treats a universe code as NEUTRAL (its candidate is `IsStronglyNormalizing`).
That suffices to prove strong normalization, but it WALLS the fundamental theorem's conversion arm: a type
VARIABLE (a variable whose type is a universe) has, under a reducible substitution, only the SN witness of
its image — not a reducibility CANDIDATE — so `IsReducibleMember.castAlongConv` (which needs a
`ReducibleType` witness for the reclassifier) cannot fire.  Backward closure cannot recover the candidate
(only weak-head head-expansion exists; arbitrary-step backward closure is false).

The fix is the TARSKI UNIVERSE: a universe code denotes the candidate "is a reducible TYPE".  Then
`IsReducibleMember (universeCode) t = IsReducibleType t`, and a reducible environment AUTOMATICALLY carries
every type variable's candidate.  Stated naively as a self-referential `ReducibleType` arm
(`ReducibleType (universeCode) (fun t => ∃ c, ReducibleType t c)`) this is STRICT-POSITIVITY-REJECTED — the
inductive appears in its own stored constructor data.

This file resolves it by STRATIFICATION: a step-FUNCTOR `ReducibleTypeStep lowerReducible` parameterised by
the relation ONE LEVEL DOWN (a PARAMETER, so positivity holds — verified), with a `universe` arm denoting
`fun typeCode => IsStronglyNormalizing typeCode ∧ ∃ candidate, lowerReducible typeCode candidate`
("is a STRONGLY-NORMALIZING reducible type at the lower level").  The `IsStronglyNormalizing` conjunct is
load-bearing: the `neutral` arm admits non-SN reducible types (`app (var f) omega` is weak-head-normal yet
loops), so without it the universe candidate would contain non-SN members and FAIL CR1; conjoining SN
filters them out — see `universeReducibilityPredicate` and the `universeCode` arm.
The level-indexed relation `ReducibleTypeAt` ties the knot by recursion on a `Nat` fuel level: level `0`
has an empty lower relation; level `n+1` feeds level `n` as the lower relation.  A term using universe
nesting depth `k` is reducible at any level `≥ k`.

The three non-universe arms mirror `ReducibleType` verbatim (weak-head expansion / neutral / dependent
arrow); the `neutral` arm gains a second guard `root ≠ gen_universeCode` so universe codes route through the
`universe` arm rather than collapsing to SN.

NOTE (deferred refinement): the `universe` arm currently makes EVERY universe code denote reducibility at
the single lower level, i.e. the stratification is by the `Nat` fuel level, not yet matched to the cell's
`LevelExpr`.  That is a sound stratified model (the fuel bounds universe-nesting depth); per-`LevelExpr`
matching is a later refinement.

## Zero-axiom verification

A plain parametrised inductive `Prop` (positivity holds — `lowerReducible` is a parameter) + a structural
`Nat` recursion for the level family + a `deterministic` proof that mirrors `ReducibleType.deterministic`,
the new `universe` arm discharged by the root partition (`gen_universeCode` ≠ `gen_piTyCode`, the neutral
guard) and `Iff.rfl` (two universe arms share the candidate at a fixed lower relation).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **The Tarski-universe candidate predicate.**  A universe code's candidate: a type code is in the
universe when it is strongly normalizing AND denotes some candidate at the lower level (is a reducible type
there).  The SN conjunct is what makes this a Girard reducibility candidate — CR1 (members are SN) reads it
off the conjunct, where the bare "is a reducible type" predicate would fail it (the `neutral` arm admits
non-SN reducible types). -/
def universeReducibilityPredicate {scope : Nat}
    (lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop) :
    RawTerm scope → Prop :=
  fun typeCode => IsStronglyNormalizing typeCode ∧
    ∃ candidate : RawTerm scope → Prop, lowerReducible typeCode candidate

/-- **The stratified reducibility step-functor.**  `ReducibleTypeStep lowerReducible` assigns a candidate
to a type-code GIVEN the reducibility relation one level down (`lowerReducible`, a parameter).  Three arms
mirror `ReducibleType` (weak-head expansion / neutral / dependent arrow); the `universe` arm makes a
universe code denote "is a reducible type at the lower level". -/
inductive ReducibleTypeStep {scope : Nat}
    (lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop) :
    RawTerm scope → (RawTerm scope → Prop) → Prop where
  /-- A redex-type inherits its weak-head contractum's candidate (conversion-invariance under the complete
  weak-head reduction). -/
  | whnfExpand {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop} :
      WeakHeadStep typeCode reduct → ReducibleTypeStep lowerReducible reduct candidate →
      ReducibleTypeStep lowerReducible typeCode candidate
  /-- A weak-head-normal type that is neither Π-rooted NOR universe-rooted denotes the
  strong-normalization candidate. -/
  | neutral {typeCode : RawTerm scope} :
      (∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct) →
      typeCode.rootGenerator ≠ Generator.gen_piTyCode →
      typeCode.rootGenerator ≠ Generator.gen_universeCode →
      ReducibleTypeStep lowerReducible typeCode IsStronglyNormalizing
  /-- The dependent arrow: a Π-code denotes the dependent function-space candidate (the codomain candidate
  varying with the argument term). -/
  | piType {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
      {domainCandidate : RawTerm scope → Prop}
      (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)) :
      ReducibleTypeStep lowerReducible domainCode domainCandidate →
      (∀ argument : RawTerm scope, domainCandidate argument →
        ReducibleTypeStep lowerReducible (RawTerm.subst0 codomainCode argument)
          (codomainCandidate argument)) →
      ReducibleTypeStep lowerReducible
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
        (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
          codomainCandidate argument
            (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))))
  /-- The Tarski universe: a universe code denotes "is a STRONGLY-NORMALIZING reducible type at the lower
  level" (`universeReducibilityPredicate`).  The `IsStronglyNormalizing` conjunct is load-bearing for CR1:
  the `neutral` arm admits non-SN reducible types (e.g. `app (var f) omega`, weak-head-normal but looping),
  so the bare "is a reducible type" predicate would contain non-SN members and FAIL CR1.  Conjoining SN
  filters those out and — at a type variable — makes a reducible environment carry BOTH the variable's SN
  witness AND its candidate. -/
  | universeCode (levelExpr : FX1Poly.Universe.LevelExpr) (flag : FX1Poly.Universe.UniverseFlag) :
      ReducibleTypeStep lowerReducible
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (universeReducibilityPredicate lowerReducible)
  /-- **Congruence closure of the candidate.**  A type-code keeps its reducibility when its candidate is
  replaced by any pointwise-equivalent predicate.  This reifies candidate-congruence as a constructor —
  necessary because the `neutral` arm pins the candidate literally to `IsStronglyNormalizing`, so the
  relation is otherwise functional up to `PointwiseIff` but NOT closed under it.  Positivity holds: the
  recursive premise sits strictly positively, `canonical` is a non-uniform index, and `PointwiseIff` has no
  recursive occurrence.  This is the brick that lets the fundamental theorem feed the Π codomain the FIXED
  canonical member-predicate (`fun arg => memberCandidate (subst0 cod arg)`) without choice: the per-argument
  premise is discharged from per-argument EXISTENCE, then transported onto the fixed predicate here. -/
  | ofPointwiseIff {typeCode : RawTerm scope} {candidate canonical : RawTerm scope → Prop} :
      ReducibleTypeStep lowerReducible typeCode candidate →
      PointwiseIff candidate canonical →
      ReducibleTypeStep lowerReducible typeCode canonical

/-- **The level-indexed reducibility relation.**  By recursion on a `Nat` fuel level: at level `0` the
lower relation is empty (`fun _ _ => False`, so a universe denotes "is a reducible type at level −1" = the
empty candidate); at level `n+1` the lower relation is `ReducibleTypeAt n`.  A type using universe-nesting
depth `k` is reducible at every level `≥ k`. -/
def ReducibleTypeAt {scope : Nat} : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop
  | 0 => ReducibleTypeStep (fun _ _ => False)
  | Nat.succ predLevel => ReducibleTypeStep (ReducibleTypeAt predLevel)

/-- **Weak-head peel through `ofPointwiseIff`.**  A reducible type that weak-head-steps inherits the SAME
candidate at the contractum.  Induction on the derivation (subject generic): `whnfExpand` equates the two
reducts by `WeakHeadStep.deterministic`; `neutral` has no weak-head step; the Π / universe leaves are
weak-head normal (`rootIota` then `cases` on the impossible `IotaHeadStep`); the `ofPointwiseIff` arm
recurses by its IH and re-wraps the same pointwise equivalence. -/
theorem ReducibleTypeStep.candidateAtWhnfReduct {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStep lowerReducible typeCode candidate) :
    ∀ {reduct : RawTerm scope}, WeakHeadStep typeCode reduct →
      ReducibleTypeStep lowerReducible reduct candidate := by
  induction reducible with
  | whnfExpand weakHeadStep0 reductReducible0 _ =>
      intro reduct weakHeadStep
      have reductEquation := WeakHeadStep.deterministic weakHeadStep0 weakHeadStep
      subst reductEquation
      exact reductReducible0
  | neutral noWeakHeadStep _ _ =>
      intro reduct weakHeadStep
      exact absurd weakHeadStep (noWeakHeadStep reduct)
  | piType _ _ _ _ _ =>
      intro reduct weakHeadStep
      cases weakHeadStep with | rootIota iotaStep => cases iotaStep
  | universeCode _ _ =>
      intro reduct weakHeadStep
      cases weakHeadStep with | rootIota iotaStep => cases iotaStep
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro reduct weakHeadStep
      exact .ofPointwiseIff (innerHypothesis weakHeadStep) pointwiseIff

/-- **A weak-head-normal non-Π non-universe type has the strong-normalization candidate** (up to pointwise
iff).  Induction on the derivation: `whnfExpand` contradicts the weak-head-normal hypothesis; `neutral`
gives exactly `IsStronglyNormalizing`; the Π / universe leaves contradict the root guards; `ofPointwiseIff`
composes its stored equivalence with the IH. -/
theorem ReducibleTypeStep.candidateIffStronglyNormalizing {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStep lowerReducible typeCode candidate) :
    (∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct) →
    typeCode.rootGenerator ≠ Generator.gen_piTyCode →
    typeCode.rootGenerator ≠ Generator.gen_universeCode →
    PointwiseIff candidate IsStronglyNormalizing := by
  induction reducible with
  | whnfExpand weakHeadStep0 _ _ =>
      intro noWeakHeadStep _ _; exact absurd weakHeadStep0 (noWeakHeadStep _)
  | neutral _ _ _ => intro _ _ _ _term; exact Iff.rfl
  | piType _ _ _ _ _ => intro _ notPiType _; exact absurd rfl notPiType
  | universeCode _ _ => intro _ _ notUniverse; exact absurd rfl notUniverse
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro noWeakHeadStep notPiType notUniverse term
      exact (pointwiseIff term).symm.trans (innerHypothesis noWeakHeadStep notPiType notUniverse term)

/-- **Π-shape inversion (subject generic + equation).**  A reducible type whose code IS a Π-code came
through the `piType` arm: it recovers the domain / codomain candidates, their reducibility, and that the
candidate is the dependent-arrow predicate pointwise.  Stated with a generic subject plus an EQUATION so
induction supplies the `ofPointwiseIff` IH directly (a concrete-index recursion is rejected for both
structural and well-founded measures); `whnfExpand` substitutes the Π-cell and is then weak-head normal,
`neutral` / universe contradict the Π root. -/
theorem ReducibleTypeStep.candidatePiShape {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStep lowerReducible typeCode candidate) :
    ∀ {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)},
      typeCode = (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) →
      ∃ (domainCandidate : RawTerm scope → Prop)
        (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
        ReducibleTypeStep lowerReducible domainCode domainCandidate ∧
        (∀ argument : RawTerm scope, domainCandidate argument →
          ReducibleTypeStep lowerReducible (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument)) ∧
        PointwiseIff candidate
          (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
            codomainCandidate argument
              (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))) := by
  induction reducible with
  | whnfExpand weakHeadStep0 _ _ =>
      intro _domainCode _codomainCode hType; subst hType
      cases weakHeadStep0 with | rootIota iotaStep => cases iotaStep
  | neutral _ notPiType _ =>
      intro _domainCode _codomainCode hType; subst hType; exact absurd rfl notPiType
  | piType codomainCandidate domainReducible codomainReducible _ _ =>
      intro _domainCode _codomainCode hType; cases hType
      exact ⟨_, codomainCandidate, domainReducible, codomainReducible, fun _term => Iff.rfl⟩
  | universeCode _ _ =>
      intro _domainCode _codomainCode hType
      have rootMismatch : Generator.gen_universeCode = Generator.gen_piTyCode :=
        congrArg RawTerm.rootGenerator hType
      exact absurd rootMismatch (by decide)
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro _domainCode _codomainCode hType
      obtain ⟨domainCandidate, codomainCandidate, domainReducible, codomainReducible, pwi⟩ :=
        innerHypothesis hType
      exact ⟨domainCandidate, codomainCandidate, domainReducible, codomainReducible,
        fun term => (pointwiseIff term).symm.trans (pwi term)⟩

/-- **Universe-shape inversion (subject generic + equation).**  A reducible type whose code IS a universe
code has the Tarski-universe candidate (up to pointwise iff).  Same generic-subject + equation discipline as
`candidatePiShape`: `whnfExpand` substitutes the weak-head-normal universe cell, `neutral` / Π contradict the
universe root, `universeCode` gives it on the nose, `ofPointwiseIff` composes via the IH. -/
theorem ReducibleTypeStep.candidateIffUniverse {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStep lowerReducible typeCode candidate) :
    ∀ {levelExpr : FX1Poly.Universe.LevelExpr} {flag : FX1Poly.Universe.UniverseFlag},
      typeCode = (.mkGen .gen_universeCode (levelExpr, flag) .childNil) →
      PointwiseIff candidate (universeReducibilityPredicate lowerReducible) := by
  induction reducible with
  | whnfExpand weakHeadStep0 _ _ =>
      intro _levelExpr _flag hType; subst hType
      cases weakHeadStep0 with | rootIota iotaStep => cases iotaStep
  | neutral _ _ notUniverse =>
      intro _levelExpr _flag hType; subst hType; exact absurd rfl notUniverse
  | piType _ _ _ _ _ =>
      intro _levelExpr _flag hType
      have rootMismatch : Generator.gen_piTyCode = Generator.gen_universeCode :=
        congrArg RawTerm.rootGenerator hType
      exact absurd rootMismatch (by decide)
  | universeCode _ _ =>
      intro _levelExpr _flag _hType _term; exact Iff.rfl
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro _levelExpr _flag hType term
      exact (pointwiseIff term).symm.trans (innerHypothesis hType term)

/-- **The stratified reducibility step-functor is functional** (up to pointwise iff): at a fixed lower
relation, a type-code denotes at most one candidate.  Induction on the first derivation; each arm reads the
second derivation's candidate off the appropriate shape-inversion helper (`candidateAtWhnfReduct` for a
redex, `candidateIffStronglyNormalizing` for a neutral, `candidatePiShape` for a Π, `candidateIffUniverse`
for a universe), and the `ofPointwiseIff` arm composes its stored equivalence with the IH. -/
theorem ReducibleTypeStep.deterministic {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} {candidate1 : RawTerm scope → Prop}
    (reducible1 : ReducibleTypeStep lowerReducible typeCode candidate1) :
    ∀ {candidate2 : RawTerm scope → Prop},
      ReducibleTypeStep lowerReducible typeCode candidate2 → PointwiseIff candidate1 candidate2 := by
  induction reducible1 with
  | whnfExpand weakHeadStep1 _reductReducible1 reductInductiveHypothesis =>
      intro candidate2 reducible2
      exact reductInductiveHypothesis (reducible2.candidateAtWhnfReduct weakHeadStep1)
  | neutral noWeakHeadStep1 notPiType1 notUniverse1 =>
      intro candidate2 reducible2 term
      exact (reducible2.candidateIffStronglyNormalizing noWeakHeadStep1 notPiType1 notUniverse1 term).symm
  | piType codomainCandidate1 _domainReducible1 _codomainReducible1
      domainInductiveHypothesis codomainInductiveHypothesis =>
      intro candidate2 reducible2
      obtain ⟨domainCandidate2, codomainCandidate2, _domainReducible2, codomainReducible2, pointwiseIff2⟩ :=
        reducible2.candidatePiShape rfl
      refine fun functionTerm => Iff.trans ?_ (pointwiseIff2 functionTerm).symm
      constructor
      · intro membership1 argument domain2Argument
        have domain1Argument := (domainInductiveHypothesis _domainReducible2 argument).mpr domain2Argument
        have codomainEquivalence :=
          codomainInductiveHypothesis argument domain1Argument
            (codomainReducible2 argument domain2Argument)
        exact (codomainEquivalence _).mp (membership1 argument domain1Argument)
      · intro membership2 argument domain1Argument
        have domain2Argument := (domainInductiveHypothesis _domainReducible2 argument).mp domain1Argument
        have codomainEquivalence :=
          codomainInductiveHypothesis argument domain1Argument
            (codomainReducible2 argument domain2Argument)
        exact (codomainEquivalence _).mpr (membership2 argument domain2Argument)
  | universeCode _levelExpr1 _flag1 =>
      intro candidate2 reducible2 term
      exact (reducible2.candidateIffUniverse rfl term).symm
  | ofPointwiseIff _innerReducible1 pointwiseIff1 innerInductiveHypothesis1 =>
      intro candidate2 reducible2 term
      exact (pointwiseIff1 term).symm.trans (innerInductiveHypothesis1 reducible2 term)

/-- **The level-indexed relation is functional** at each level — the step-functor's determinism
specialized through the `Nat` recursion (level `0` over the empty lower relation, level `n+1` over
`ReducibleTypeAt n`). -/
theorem ReducibleTypeAt.deterministic {scope : Nat} {level : Nat}
    {typeCode : RawTerm scope} {candidate1 candidate2 : RawTerm scope → Prop}
    (reducible1 : ReducibleTypeAt level typeCode candidate1)
    (reducible2 : ReducibleTypeAt level typeCode candidate2) :
    PointwiseIff candidate1 candidate2 := by
  cases level with
  | zero => exact ReducibleTypeStep.deterministic reducible1 reducible2
  | succ predLevel => exact ReducibleTypeStep.deterministic reducible1 reducible2

end FX1Poly.Core
