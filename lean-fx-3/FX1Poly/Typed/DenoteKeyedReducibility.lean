import FX1Poly.Typed.ClassifierLevelMeasure
import FX1Poly.Typed.UniverseCodeShape
import FX1Poly.Core.StratifiedReducibleTypeConvInvariance
import FX1Poly.Core.StratifiedReducibleTypeReducibilityCandidate

/-! # FX1Poly/Typed/DenoteKeyedReducibility
    — the classifier-universe-level reducibility relation (SN-006 foundation toward #672)

The fuel-stratified relation `ReducibleTypeAt` (`StratifiedReducibleType`) walls type-level
level-irrelevance at the universe-domain Pi, for the precise structural reason pinned in `RouteAObstruction`
(SN-001): its universe arm uses `lowerReducible` UNIFORMLY (the relation one ambient-fuel level down,
`universeReducibilityPredicate lower = fun tc => IsSN tc ∧ ∃ c, lower tc c`), so at fuel 0 the universe
candidate is EMPTY and the obstruction propagates up every finite level.

This file lays the foundation stone of the fix diagnosed in SN-002/SN-005 and measured in SN-003
(`ClassifierLevelMeasure`): re-key the universe arm to the DECODED classifier level.  The universe arm at
`Type@levelExpr` now decodes to the lower relation AT `LevelExpr.denote levelExpr env` —
`universeDenotePredicate env lowerAt levelExpr = fun tc => IsSN tc ∧ ∃ c, lowerAt (denote levelExpr env) tc
c` — NOT at ambient-fuel-minus-one.  Because the decoded level is fixed by `levelExpr` (not by the ambient
fuel), `Type@levelExpr`'s candidate is the SAME at every ambient level above `denote levelExpr env`: the
fuel-0 vacuity simply does not arise, and universe-membership is level-irrelevant BY CONSTRUCTION
(`universeMembership_levelIrrelevant` below).  This is the denote-keyed shape the well-founded universe
recursion of the Adjedj-style derivation-indexed logical relation (SN-006) descends on via
`ClassifierLevelMeasure.denote_lt_lsucc`.

## Why STRUCTURAL, not well-founded recursion

Accessing the relation at the arbitrary lower level `denote levelExpr env` (which can be far below the
ambient level, not the immediate predecessor) is the genuine technical hurdle.  Well-founded recursion on
the level is the obvious tool, but its AUTO-GENERATED `.eq_def` equation lemma leaks `Quot.sound` (the WF
principle `WellFounded.fix_eq` itself is axiom-clean; the equation-compiler-generated unfolding is not),
which would break the zero-axiom discipline.  So the lower family is built by STRUCTURAL recursion on the
level (`denoteBelowFamily`): at `level + 1` it reuses `denoteBelowFamily level` for indices `< level`,
installs the step-functor over `denoteBelowFamily level` at exactly `level`, and is empty above.  EVERY
recursive call sits at the structural predecessor `level`, so the definition reduces definitionally — no WF,
no `Quot.sound` — yet arbitrary-lower-level access is recovered, and level-stability (`coherence`) becomes a
clean structural induction.

## What lands here (all zero-axiom)

  * `universeDenotePredicate` — the denote-keyed universe candidate.
  * `ReducibleTypeStepDenote` — the denote-keyed step functor (positivity holds; `lowerAt` is a parameter).
  * `denoteBelowFamily` — the structural lower family.
  * `ReducibleTypeAtDenote` / `IsReducibleTypeAtDenote` — the level-indexed relation + its semantic wrapper.
  * `denoteBelowFamily_eq_reducible` — coherence: the below-family at `lvl < level` is the relation at `lvl`.
  * `universeCode_isReducibleAtDenote` — anti-vacuity: a universe code is a reducible type at EVERY level
    (the direct refutation of SN-001's empty fuel-0 base).
  * `universeMembership_levelIrrelevant` — the HEADLINE: at every ambient level above `denote levelExpr
    env`, the candidate of `Type@levelExpr` is the fixed decode-at-`denote levelExpr env` set, INDEPENDENT
    of the ambient level — precisely the level-irrelevance the fuel model could not deliver.

The remaining SN-006 work (NOT in this file) is to thread this relation through the term/type fundamental
theorem with the universe-level well-founded recursion (`ClassifierLevelMeasure.denote_lt_lsucc`), porting
CR1/CR2/CR3 and the formation arms onto `ReducibleTypeAtDenote`, then discharging the universe-domain
`piArm` (`ReducibleTypeAtAllLevelsInduction`) from the now-level-irrelevant universe membership.

## Zero-axiom verification

A parametrised inductive (positivity: `lowerAt` is a parameter), one structural `Nat` recursion, a
structural-induction coherence lemma (`ite` split via `if_pos`/`if_neg`, boundary by `Nat.le_antisymm`), and
the universe arm reassembled through the relation's own `ofPointwiseIff` congruence (a pointwise iff —
introduced pointwise, NOT `funext`, which would itself pull `Quot.sound`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation FX1Poly.Universe
open StepStar

/-- **The denote-keyed universe candidate predicate.**  Unlike `universeReducibilityPredicate` (which uses a
single `lowerReducible`), this decodes `Type@levelExpr` to the lower relation AT `denote levelExpr env` —
the fixed classifier level, independent of the ambient level.  This is the surgical change that defeats the
fuel-0 vacuity. -/
def universeDenotePredicate {scope : Nat} (env : Nat → Nat)
    (lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop)
    (levelExpr : LevelExpr) : RawTerm scope → Prop :=
  fun typeCode => IsStronglyNormalizing typeCode ∧
    ∃ candidate : RawTerm scope → Prop, lowerAt (LevelExpr.denote levelExpr env) typeCode candidate

/-- **The denote-keyed reducibility step-functor.**  Identical to `ReducibleTypeStep` except the
`universeCode` arm reaches into `lowerAt (denote levelExpr env)` rather than a uniform `lower`.  The other
four arms (weak-head expansion / neutral / dependent arrow / pointwise-iff congruence) are verbatim. -/
inductive ReducibleTypeStepDenote {scope : Nat} (env : Nat → Nat)
    (lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop) :
    RawTerm scope → (RawTerm scope → Prop) → Prop where
  | whnfExpand {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop} :
      WeakHeadStep typeCode reduct → ReducibleTypeStepDenote env lowerAt reduct candidate →
      ReducibleTypeStepDenote env lowerAt typeCode candidate
  | neutral {typeCode : RawTerm scope} :
      (∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct) →
      typeCode.rootGenerator ≠ Generator.gen_piTyCode →
      typeCode.rootGenerator ≠ Generator.gen_universeCode →
      ReducibleTypeStepDenote env lowerAt typeCode IsStronglyNormalizing
  | piType {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
      {domainCandidate : RawTerm scope → Prop}
      (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)) :
      ReducibleTypeStepDenote env lowerAt domainCode domainCandidate →
      (∀ argument : RawTerm scope, domainCandidate argument →
        ReducibleTypeStepDenote env lowerAt (RawTerm.subst0 codomainCode argument)
          (codomainCandidate argument)) →
      ReducibleTypeStepDenote env lowerAt
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
        (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
          codomainCandidate argument
            (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))))
  | universeCode (levelExpr : LevelExpr) (flag : UniverseFlag) :
      ReducibleTypeStepDenote env lowerAt
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (universeDenotePredicate env lowerAt levelExpr)
  | ofPointwiseIff {typeCode : RawTerm scope} {candidate canonical : RawTerm scope → Prop} :
      ReducibleTypeStepDenote env lowerAt typeCode candidate →
      PointwiseIff candidate canonical →
      ReducibleTypeStepDenote env lowerAt typeCode canonical

/-- **The structural lower family below a level.**  `denoteBelowFamily (level + 1)` reuses
`denoteBelowFamily level` for indices `lvl < level`, installs the step-functor over `denoteBelowFamily
level` at exactly `lvl = level`, and is empty above.  Both recursive calls sit at the structural predecessor
`level`, so this avoids well-founded recursion (whose `.eq_def` would leak `Quot.sound`) while still
granting arbitrary-lower-level access. -/
def denoteBelowFamily {scope : Nat} (env : Nat → Nat) :
    Nat → Nat → RawTerm scope → (RawTerm scope → Prop) → Prop
  | 0, _lvl => fun _ _ => False
  | level + 1, lvl =>
      if lvl < level then denoteBelowFamily env level lvl
      else if lvl = level then ReducibleTypeStepDenote env (denoteBelowFamily env level)
      else fun _ _ => False

/-- **The denote-keyed level-indexed reducibility relation:** the step-functor over the structural
below-family. -/
def ReducibleTypeAtDenote {scope : Nat} (env : Nat → Nat) (level : Nat) :
    RawTerm scope → (RawTerm scope → Prop) → Prop :=
  ReducibleTypeStepDenote env (denoteBelowFamily env level)

/-- **Semantic well-formed type (denote-keyed).** -/
def IsReducibleTypeAtDenote {scope : Nat} (env : Nat → Nat) (level : Nat) (typeCode : RawTerm scope) :
    Prop :=
  ∃ candidate : RawTerm scope → Prop, ReducibleTypeAtDenote env level typeCode candidate

/-- **Coherence (level-stability of the below-family).**  For `lvl < level`, the below-family at `lvl`
agrees with the relation at `lvl` — the structural witness that the value at a fixed index is STABLE once
the ambient level passes it.  Structural induction on `level`; the `lvl = level` boundary uses
`Nat.le_antisymm`. -/
theorem denoteBelowFamily_eq_reducible {scope : Nat} (env : Nat → Nat) :
    ∀ (level lvl : Nat), lvl < level →
      denoteBelowFamily (scope := scope) env level lvl = ReducibleTypeAtDenote env lvl := by
  intro level
  induction level with
  | zero => intro lvl hlt; exact absurd hlt (Nat.not_lt_zero lvl)
  | succ predLevel ih =>
      intro lvl hlt
      show (if lvl < predLevel then denoteBelowFamily env predLevel lvl
            else if lvl = predLevel then ReducibleTypeStepDenote env (denoteBelowFamily env predLevel)
            else fun _ _ => False) = ReducibleTypeAtDenote env lvl
      by_cases hbelow : lvl < predLevel
      · rw [if_pos hbelow]; exact ih lvl hbelow
      · rw [if_neg hbelow]
        have heq : lvl = predLevel :=
          Nat.le_antisymm (Nat.le_of_lt_succ hlt) (Nat.not_lt.mp hbelow)
        rw [if_pos heq, heq]
        rfl

/-- **Anti-vacuity (the refutation of SN-001).**  A universe code `Type@levelExpr` is a reducible type at
EVERY ambient level — the universe arm fires unconditionally, with no fuel-0 emptiness.  Contrast
`RouteAObstruction.universeDomainPiVacuouslyReducibleAtZero`, where the fuel-0 universe candidate is the
empty predicate. -/
theorem universeCode_isReducibleAtDenote {scope : Nat} (env : Nat → Nat) (level : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsReducibleTypeAtDenote (scope := scope) env level
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) :=
  ⟨_, ReducibleTypeStepDenote.universeCode levelExpr flag⟩

/-- **The headline — universe-membership LEVEL-IRRELEVANCE.**  At any ambient level strictly above the
decoded level `denote levelExpr env`, the candidate of `Type@levelExpr` is `IsStronglyNormalizing ∧
IsReducibleTypeAtDenote env (denote levelExpr env)` — the SAME decode-at-`denote levelExpr env` set,
INDEPENDENT of the ambient level.  This is exactly the level-irrelevance the fuel model could not deliver
(SN-001): it holds HERE by construction, because the universe arm decodes at the fixed classifier level, and
coherence rewrites the below-family at `denote levelExpr env` to the relation there.  Reassembled through
the relation's own `ofPointwiseIff` (pointwise iff — no `funext`, hence no `Quot.sound`). -/
theorem universeMembership_levelIrrelevant {scope : Nat} (env : Nat → Nat) (level : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (habove : LevelExpr.denote levelExpr env < level) :
    ReducibleTypeAtDenote (scope := scope) env level
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (fun member : RawTerm scope => IsStronglyNormalizing member ∧
          IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) member) := by
  have key : denoteBelowFamily env level (LevelExpr.denote levelExpr env)
      = ReducibleTypeAtDenote (scope := scope) env (LevelExpr.denote levelExpr env) :=
    denoteBelowFamily_eq_reducible env level (LevelExpr.denote levelExpr env) habove
  refine ReducibleTypeStepDenote.ofPointwiseIff
    (ReducibleTypeStepDenote.universeCode levelExpr flag) (fun member => ?_)
  show (IsStronglyNormalizing member ∧
      ∃ candidate, denoteBelowFamily env level (LevelExpr.denote levelExpr env) member candidate)
    ↔ (IsStronglyNormalizing member ∧
      IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) member)
  rw [key]
  exact Iff.rfl

/-! ## CR machinery: shape inversions + determinism

Ported verbatim from `StratifiedReducibleType.*`, the only structural difference being the universe arm:
since the denote-keyed universe candidate depends on `levelExpr` (it decodes at `denote levelExpr env`),
`candidateIffUniverse` / `deterministic` align the `levelExpr` via `universeCodeCell_inj` (zero-axiom, a
plain `cases` on the cell equality), where the fuel versions could use bare `Iff.rfl`.  These feed the
universe-domain `piArm` of `typeLevelIrrelevance` (the remaining #672 obligation): `piTypeInversion`
decomposes a reducible `Π(Type@e)C`, `deterministic` aligns the domain/codomain candidates, and
`candidateIffStronglyNormalizing` is the neutral leaf the determinism induction consumes. -/

/-- **Weak-head peel through `ofPointwiseIff`.**  A reducible type that weak-head-steps inherits the same
candidate at the contractum. -/
theorem ReducibleTypeStepDenote.candidateAtWhnfReduct {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    ∀ {reduct : RawTerm scope}, WeakHeadStep typeCode reduct →
      ReducibleTypeStepDenote env lowerAt reduct candidate := by
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
iff). -/
theorem ReducibleTypeStepDenote.candidateIffStronglyNormalizing {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
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
candidate is the dependent-arrow predicate pointwise. -/
theorem ReducibleTypeStepDenote.candidatePiShape {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    ∀ {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)},
      typeCode = (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) →
      ∃ (domainCandidate : RawTerm scope → Prop)
        (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
        ReducibleTypeStepDenote env lowerAt domainCode domainCandidate ∧
        (∀ argument : RawTerm scope, domainCandidate argument →
          ReducibleTypeStepDenote env lowerAt (RawTerm.subst0 codomainCode argument)
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
code has the denote-keyed universe candidate (up to pointwise iff).  The `universeCode` arm aligns the
inducted-arm `levelExpr` with the equation's via `universeCodeCell_inj` (where the fuel version's
levelExpr-independent candidate allowed bare `Iff.rfl`). -/
theorem ReducibleTypeStepDenote.candidateIffUniverse {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    ∀ {levelExpr : LevelExpr} {flag : UniverseFlag},
      typeCode = (.mkGen .gen_universeCode (levelExpr, flag) .childNil) →
      PointwiseIff candidate (universeDenotePredicate env lowerAt levelExpr) := by
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
  | universeCode levelExpr flag =>
      intro _levelExpr _flag hType term
      obtain ⟨levelEq, _flagEq⟩ := universeCodeCell_inj hType
      subst levelEq
      exact Iff.rfl
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro _levelExpr _flag hType term
      exact (pointwiseIff term).symm.trans (innerHypothesis hType term)

/-- **The denote-keyed step functor is functional** (up to pointwise iff): at a fixed `env` / `lowerAt`, a
type-code denotes at most one candidate. -/
theorem ReducibleTypeStepDenote.deterministic {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} {candidate1 : RawTerm scope → Prop}
    (reducible1 : ReducibleTypeStepDenote env lowerAt typeCode candidate1) :
    ∀ {candidate2 : RawTerm scope → Prop},
      ReducibleTypeStepDenote env lowerAt typeCode candidate2 → PointwiseIff candidate1 candidate2 := by
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

/-- **The level-indexed relation is functional.**  Direct from `ReducibleTypeStepDenote.deterministic`
(unlike the fuel `ReducibleTypeAt`, no `Nat` recursion: `ReducibleTypeAtDenote env level` IS the step functor
over `denoteBelowFamily env level`). -/
theorem ReducibleTypeAtDenote.deterministic {scope : Nat} {env : Nat → Nat} {level : Nat}
    {typeCode : RawTerm scope} {candidate1 candidate2 : RawTerm scope → Prop}
    (reducible1 : ReducibleTypeAtDenote env level typeCode candidate1)
    (reducible2 : ReducibleTypeAtDenote env level typeCode candidate2) :
    PointwiseIff candidate1 candidate2 :=
  ReducibleTypeStepDenote.deterministic reducible1 reducible2

/-- **Π-code inversion (existential, level-indexed).**  A `gen_piTyCode`-rooted reducible type came through
the `piType` arm; recovers the domain/codomain candidates.  The decomposition the universe-domain `piArm`
consumes to take apart a reducible `Π(Type@e)C`. -/
theorem ReducibleTypeAtDenote.piTypeInversion {scope : Nat} {env : Nat → Nat} {level : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAtDenote env level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) candidate) :
    ∃ (domainCandidate : RawTerm scope → Prop)
      (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
      ReducibleTypeAtDenote env level domainCode domainCandidate ∧
      (∀ argument : RawTerm scope, domainCandidate argument →
        ReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)
          (codomainCandidate argument)) ∧
      PointwiseIff candidate
        (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
          codomainCandidate argument
            (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))) :=
  reducible.candidatePiShape rfl

/-! ## Forward closure + conversion-invariance

Ported from `StratifiedReducibleTypeForwardClosure` / `StratifiedReducibleTypeConvInvariance`.  The reduction
helpers (`WeakHeadStep.commuteWithStep`, `weakHeadNormalRootStableAlongStepStar`, `StepStar.piTyCode_decompose`,
`subst0Body`, `eq_of_noStep`, `noStep_universeCode`) are relation-agnostic and reused verbatim; only the
reducibility constructors change to the denote-keyed ones.  `convInvariant` carries each side's candidate down
to the `Conv` Join's common reduct (`forwardStepStar`), where `deterministic` equates them — no backward
closure.  `convTransfer` is the membership form the fundamental theorem's `conv` arm and the arrow CR3
argument-reduction case consume. -/

/-- **Forward closure of a denote-keyed `whnfExpand` code along `StepStar`.**  Each leading step is commuted
past the weak-head redex (`commuteWithStep`); the surviving-redex branch recurses with the catch-up chain. -/
theorem ReducibleTypeStepDenote.whnfExpandClosure {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {candidate : RawTerm scope → Prop} :
    ∀ {firstType finalType : RawTerm scope}, StepStar firstType finalType →
      ∀ {weakHeadReduct : RawTerm scope}, WeakHeadStep firstType weakHeadReduct →
        ReducibleTypeStepDenote env lowerAt weakHeadReduct candidate →
        (∀ furtherReduct : RawTerm scope, StepStar weakHeadReduct furtherReduct →
          ReducibleTypeStepDenote env lowerAt furtherReduct candidate) →
        ReducibleTypeStepDenote env lowerAt finalType candidate := by
  intro firstType finalType chain
  induction chain with
  | refl _ =>
      intro weakHeadReduct weakHeadStep reductReducible _laterClosure
      exact ReducibleTypeStepDenote.whnfExpand weakHeadStep reductReducible
  | trans firstStep _restChain restClosure =>
      intro weakHeadReduct weakHeadStep reductReducible laterClosure
      rcases weakHeadStep.commuteWithStep _ firstStep with
        midEquation | ⟨_laterReduct, laterWeakHeadStep, catchUpChain⟩
      · subst midEquation
        exact laterClosure _ _restChain
      · exact restClosure laterWeakHeadStep (laterClosure _ catchUpChain)
          (fun furtherReduct furtherChain =>
            laterClosure furtherReduct (StepStar.trans_compose catchUpChain furtherChain))

/-- **Forward closure of the denote-keyed reducibility relation under multi-step reduction.**  A reducible
type stays reducible at the SAME candidate along any `StepStar` — the keystone of conversion-invariance.
`universeCode` is a step normal form (`noStep_universeCode`), so the chain is reflexive and rebuilds. -/
theorem ReducibleTypeStepDenote.forwardStepStar {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {candidate : RawTerm scope → Prop} {typeCode : RawTerm scope}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    ∀ {finalType : RawTerm scope}, StepStar typeCode finalType →
      ReducibleTypeStepDenote env lowerAt finalType candidate := by
  induction reducible with
  | whnfExpand weakHeadStep reductReducible reductInductiveHypothesis =>
      intro finalType chain
      exact ReducibleTypeStepDenote.whnfExpandClosure chain weakHeadStep reductReducible
        (fun _furtherReduct furtherChain => reductInductiveHypothesis furtherChain)
  | neutral noWeakHeadStep notPiType notUniverse =>
      intro finalType chain
      obtain ⟨finalNoWeakHeadStep, rootEquation⟩ :=
        WeakHeadStep.weakHeadNormalRootStableAlongStepStar chain noWeakHeadStep
      exact ReducibleTypeStepDenote.neutral finalNoWeakHeadStep
        (fun rootIsPiType => notPiType (rootEquation.symm.trans rootIsPiType))
        (fun rootIsUniverse => notUniverse (rootEquation.symm.trans rootIsUniverse))
  | piType codomainCandidate _domainReducible _codomainReducible
      domainInductiveHypothesis codomainInductiveHypothesis =>
      intro finalType chain
      obtain ⟨_updatedDomain, _updatedCodomain, finalEquation, domainChain, codomainChain⟩ :=
        StepStar.piTyCode_decompose chain
      subst finalEquation
      exact ReducibleTypeStepDenote.piType codomainCandidate (domainInductiveHypothesis domainChain)
        (fun argument domainMember =>
          codomainInductiveHypothesis argument domainMember
            (StepStar.subst0Body argument codomainChain))
  | universeCode levelExpr flag =>
      intro finalType chain
      have finalEquation :=
        StepStar.eq_of_noStep (fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step)
          chain
      subst finalEquation
      exact ReducibleTypeStepDenote.universeCode levelExpr flag
  | ofPointwiseIff _innerReducible pointwiseIff innerHypothesis =>
      intro finalType chain
      exact (innerHypothesis chain).ofPointwiseIff pointwiseIff

/-- **Forward closure of the level-indexed relation** (direct — no `Nat` recursion). -/
theorem ReducibleTypeAtDenote.forwardStepStar {scope : Nat} {env : Nat → Nat} {level : Nat}
    {candidate : RawTerm scope → Prop} {typeCode finalType : RawTerm scope}
    (reducible : ReducibleTypeAtDenote env level typeCode candidate)
    (chain : StepStar typeCode finalType) :
    ReducibleTypeAtDenote env level finalType candidate :=
  ReducibleTypeStepDenote.forwardStepStar reducible chain

/-- **Conversion-invariance of the denote-keyed relation.**  Convertible reducible types denote the same
candidate: forward-close both to the `Conv` Join's common reduct, then `deterministic`. -/
theorem ReducibleTypeStepDenote.convInvariant {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeLeft typeRight : RawTerm scope}
    {candidateLeft candidateRight : RawTerm scope → Prop}
    (reducibleLeft : ReducibleTypeStepDenote env lowerAt typeLeft candidateLeft)
    (reducibleRight : ReducibleTypeStepDenote env lowerAt typeRight candidateRight)
    (conv : Conv typeLeft typeRight) :
    PointwiseIff candidateLeft candidateRight := by
  obtain ⟨_commonReduct, chainLeft, chainRight⟩ := conv
  exact ReducibleTypeStepDenote.deterministic
    (ReducibleTypeStepDenote.forwardStepStar reducibleLeft chainLeft)
    (ReducibleTypeStepDenote.forwardStepStar reducibleRight chainRight)

/-- **Reducibility transfers across conversion (denote-keyed).**  The membership form the `conv` typing arm
and the dependent-arrow CR3 argument-reduction case consume. -/
theorem ReducibleTypeStepDenote.convTransfer {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeLeft typeRight : RawTerm scope}
    {candidateLeft candidateRight : RawTerm scope → Prop}
    (reducibleLeft : ReducibleTypeStepDenote env lowerAt typeLeft candidateLeft)
    (reducibleRight : ReducibleTypeStepDenote env lowerAt typeRight candidateRight)
    (conv : Conv typeLeft typeRight)
    {term : RawTerm scope} (membership : candidateLeft term) :
    candidateRight term :=
  (ReducibleTypeStepDenote.convInvariant reducibleLeft reducibleRight conv term).mp membership

/-- **Conversion-transfer, level-indexed.** -/
theorem ReducibleTypeAtDenote.convTransfer {scope : Nat} {env : Nat → Nat} {level : Nat}
    {typeLeft typeRight : RawTerm scope}
    {candidateLeft candidateRight : RawTerm scope → Prop}
    (reducibleLeft : ReducibleTypeAtDenote env level typeLeft candidateLeft)
    (reducibleRight : ReducibleTypeAtDenote env level typeRight candidateRight)
    (conv : Conv typeLeft typeRight)
    {term : RawTerm scope} (membership : candidateLeft term) :
    candidateRight term :=
  ReducibleTypeStepDenote.convTransfer reducibleLeft reducibleRight conv membership

/-! ## Reducibility-candidate soundness (CR1/CR2/CR3)

Ported from `StratifiedReducibleTypeReducibilityCandidate`.  The dependent-arrow CR is verbatim except CR3's
argument-reduction case uses `ReducibleTypeStepDenote.convTransfer`.  The parametric
`isReducibilityCandidate` is the fuel proof with one change at the universe arm: the candidate
`universeDenotePredicate env lowerAt levelExpr` is DEFINITIONALLY `universeReducibilityPredicate (lowerAt
(denote levelExpr env))`, so it reuses the shipped fuel `ReducibleTypeStep.universeCandidateIsReducibilityCandidate`
at the decoded level — hence the interface legs are PER-LEVEL (`∀ lvl`), discharged at `denote levelExpr env`.

Note this is the PARAMETRIC form (legs as hypotheses).  The unconditional level-indexed discharge for
`denoteBelowFamily env level` carries the predicative level-bound subtlety — the universe candidate at a
decoded level `≥ level` is empty (fails CR3, the SN-001 degeneracy re-keyed to `denote`) — so it holds only
when every universe code's decoded level is `< level`; that bounded form is deferred to the universe-domain
`piArm` step, where the well-founded `denote_lt_lsucc` measure supplies the bound. -/

/-- **The dependent-arrow construction is a reducibility candidate (denote-keyed).**  Verbatim port of
`isDependentArrowReducibleStep_isReducibilityCandidate`; CR3's argument-reduction case carries membership
across the convertible reduced codomain codes via `ReducibleTypeStepDenote.convTransfer`. -/
theorem isDependentArrowReducibleStepDenote_isReducibilityCandidate {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {domainPredicate : RawTerm scope → Prop}
    {codomainCandidate : RawTerm scope → (RawTerm scope → Prop)}
    {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : IsReducibilityCandidate domainPredicate)
    (codomainCandidateHood : ∀ argument : RawTerm scope, domainPredicate argument →
      IsReducibilityCandidate (codomainCandidate argument))
    (codomainReducible : ∀ argument : RawTerm scope, domainPredicate argument →
      ReducibleTypeStepDenote env lowerAt (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument))
    (reducibleWitness : RawTerm scope)
    (witnessReducible : domainPredicate reducibleWitness) :
    IsReducibilityCandidate (IsDependentArrowReducible domainPredicate codomainCandidate) := by
  refine ⟨?stronglyNormalizing, ?closedUnderStep, ?neutralExpansion⟩
  case stronglyNormalizing =>
    intro function functionArrowReducible
    have applicationReducible :
        codomainCandidate reducibleWitness
          (.mkGen .gen_app ()
            (.childCons function (.childCons reducibleWitness .childNil))) :=
      functionArrowReducible reducibleWitness witnessReducible
    exact appHead_isStronglyNormalizing_of_app
      ((codomainCandidateHood reducibleWitness witnessReducible).stronglyNormalizing
        applicationReducible)
  case closedUnderStep =>
    intro function functionAfter functionArrowReducible functionStep argument argumentReducible
    have applicationStep :
        Step
          (.mkGen .gen_app () (.childCons function (.childCons argument .childNil)))
          (.mkGen .gen_app () (.childCons functionAfter (.childCons argument .childNil))) :=
      Step.cong .gen_app ()
        (StepChildren.here
          (.childCons argument .childNil : RawTermChildren [0] scope)
          functionStep)
    exact (codomainCandidateHood argument argumentReducible).closedUnderStep
      (functionArrowReducible argument argumentReducible) applicationStep
  case neutralExpansion =>
    intro function functionIsNeutral reductsArrowReducible
    suffices general :
        ∀ {currentArgument : RawTerm scope}, Acc StepSuccessor currentArgument →
          domainPredicate currentArgument →
            codomainCandidate currentArgument
              (.mkGen .gen_app ()
                (.childCons function (.childCons currentArgument .childNil))) from
      fun argument argumentReducible =>
        general (domainCandidate.stronglyNormalizing argumentReducible) argumentReducible
    intro currentArgument argumentAccessible
    induction argumentAccessible with
    | intro argumentFocus _argumentPredecessors argumentInductiveHypothesis =>
        intro argumentFocusReducible
        refine (codomainCandidateHood argumentFocus argumentFocusReducible).neutralExpansion
          (IsNeutral.app functionIsNeutral) ?_
        intro reduct reductionStep
        rcases Step.from_app reductionStep with
          ⟨_body, functionEqualsLam, _targetEq⟩ |
          ⟨functionAfter, reductEquals, functionStep⟩ |
          ⟨argumentAfter, reductEquals, argumentStep⟩
        · exact (IsNeutral.not_lam (functionEqualsLam ▸ functionIsNeutral)).elim
        · rw [reductEquals]
          exact reductsArrowReducible functionAfter functionStep
            argumentFocus argumentFocusReducible
        · rw [reductEquals]
          have argumentAfterReducible :=
            domainCandidate.closedUnderStep argumentFocusReducible argumentStep
          exact ReducibleTypeStepDenote.convTransfer
            (codomainReducible argumentAfter argumentAfterReducible)
            (codomainReducible argumentFocus argumentFocusReducible)
            ⟨_, StepStar.refl _, Step.subst0Argument codomainCode argumentStep⟩
            (argumentInductiveHypothesis argumentAfter argumentStep argumentAfterReducible)

/-- **Every denote-keyed reducibility candidate is a Girard reducibility candidate** (parametric, per-level
interface legs).  Induction on the derivation: `whnfExpand` reuses the IH, `neutral` is the SN candidate,
`piType` is the dependent function-space candidate (domain inhabitant = variable 0), `universeCode` reuses
the fuel `universeCandidateIsReducibilityCandidate` at the DECODED level `denote levelExpr env` (the
candidate is defeq to `universeReducibilityPredicate (lowerAt (denote levelExpr env))`).  Stated at
`scope + 1` so the arrow CR1 has variable 0 as the uniform domain inhabitant. -/
theorem ReducibleTypeStepDenote.isReducibilityCandidate {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm (scope + 1) → (RawTerm (scope + 1) → Prop) → Prop}
    (lowerForwardStep : ∀ (lvl : Nat) {typeCode reduct : RawTerm (scope + 1)}
        {candidate : RawTerm (scope + 1) → Prop},
      lowerAt lvl typeCode candidate → Step typeCode reduct → lowerAt lvl reduct candidate)
    (lowerNeutralInclusion : ∀ (lvl : Nat) {typeCode : RawTerm (scope + 1)}, IsNeutral typeCode →
      (∀ reduct : RawTerm (scope + 1), Step typeCode reduct →
        ∃ candidate : RawTerm (scope + 1) → Prop, lowerAt lvl reduct candidate) →
      ∃ candidate : RawTerm (scope + 1) → Prop, lowerAt lvl typeCode candidate)
    {typeCode : RawTerm (scope + 1)} {candidate : RawTerm (scope + 1) → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) :
    IsReducibilityCandidate candidate := by
  induction reducible with
  | whnfExpand _weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact reductInductiveHypothesis
  | neutral _noWeakHeadStep _notPiType _notUniverse =>
      exact isStronglyNormalizing_isReducibilityCandidate
  | piType codomainCandidate _domainReducible codomainReducible
      domainInductiveHypothesis codomainInductiveHypothesis =>
      exact isDependentArrowReducibleStepDenote_isReducibilityCandidate
        domainInductiveHypothesis codomainInductiveHypothesis codomainReducible
        (.mkGen .gen_var ⟨0, Nat.succ_pos scope⟩ .childNil)
        (domainInductiveHypothesis.containsVariable ⟨0, Nat.succ_pos scope⟩)
  | universeCode levelExpr _flag =>
      exact ReducibleTypeStep.universeCandidateIsReducibilityCandidate
        (lowerForwardStep (LevelExpr.denote levelExpr env))
        (lowerNeutralInclusion (LevelExpr.denote levelExpr env))
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      exact innerInductiveHypothesis.respectsPointwiseIff (fun term => pointwiseIff term)

/-! ## Interface-leg discharge for `denoteBelowFamily`

The parametric `isReducibilityCandidate` consumes two per-level interface legs on the lower family
(`lowerForwardStep`, `lowerNeutralInclusion`).  This section discharges them for `denoteBelowFamily env
level`: `forwardStep` UNCONDITIONALLY (below the level coherence reduces to the real relation's forward
closure; at/above it the family is empty, vacuous), and `neutralInclusion` for `lvl < level` ONLY.

The bound is essential and precise: at a decoded level `≥ level` the below-family is the EMPTY relation
(`denoteBelowFamily_eq_empty_of_ge`), and neutral-inclusion of the empty relation is FALSE — a variable is
neutral with no reducts, yet the empty relation has no members (the SN-001 fuel-0 degeneracy re-keyed to
`denote`).  The universe-domain `piArm` discharges this side-condition: it instantiates at the Π's own level
`≥ denote e + 1 > denote e` (via `ClassifierLevelMeasure.denote_lt_lsucc`), so the universe arm's decoded
level `denote e env` is strictly below the ambient level and the bound holds. -/

/-- **Single-step forward closure (denote-keyed).** -/
theorem ReducibleTypeStepDenote.forwardStep {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepDenote env lowerAt typeCode candidate) (step : Step typeCode reduct) :
    ReducibleTypeStepDenote env lowerAt reduct candidate :=
  ReducibleTypeStepDenote.forwardStepStar reducible (StepStar.single step)

/-- **A neutral type is reducible (denote-keyed)** — the SN candidate via the `neutral` arm (a neutral term
is weak-head-normal and neither Π- nor universe-rooted). -/
theorem ReducibleTypeStepDenote.reducibleOfNeutral {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop}
    {typeCode : RawTerm scope} (neutral : IsNeutral typeCode) :
    ∃ candidate : RawTerm scope → Prop, ReducibleTypeStepDenote env lowerAt typeCode candidate := by
  refine ⟨IsStronglyNormalizing, ReducibleTypeStepDenote.neutral
    (fun reduct => neutral.noWeakHeadStep reduct) ?_ ?_⟩
  · cases neutral <;> exact fun rootEquation => nomatch rootEquation
  · cases neutral <;> exact fun rootEquation => nomatch rootEquation

/-- **The below-family is the EMPTY relation at or above the level.**  Structural induction on `level`; at
`level + 1` with `level + 1 ≤ lvl` both the `lvl < level` and `lvl = level` guards fail, leaving the empty
arm. -/
theorem denoteBelowFamily_eq_empty_of_ge {scope : Nat} (env : Nat → Nat) :
    ∀ (level lvl : Nat), level ≤ lvl →
      denoteBelowFamily (scope := scope) env level lvl = (fun _ _ => False) := by
  intro level
  induction level with
  | zero => intro lvl _; rfl
  | succ predLevel _ih =>
      intro lvl hle
      have predLessThan : predLevel < lvl := Nat.lt_of_lt_of_le (Nat.lt_succ_self predLevel) hle
      show (if lvl < predLevel then denoteBelowFamily env predLevel lvl
            else if lvl = predLevel then ReducibleTypeStepDenote env (denoteBelowFamily env predLevel)
            else fun _ _ => False) = fun _ _ => False
      rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt predLessThan)),
        if_neg (Ne.symm (Nat.ne_of_lt predLessThan))]

/-- **Interface leg 1 (unconditional): `denoteBelowFamily env level` is forward-closed under `Step` at every
level.**  Below the bound, coherence reduces to the real relation's forward closure; at/above it the family
is empty (the `member` hypothesis is `False`). -/
theorem denoteBelowFamily_forwardStep {scope : Nat} (env : Nat → Nat) (level : Nat) (lvl : Nat)
    {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop}
    (member : denoteBelowFamily env level lvl typeCode candidate) (step : Step typeCode reduct) :
    denoteBelowFamily env level lvl reduct candidate := by
  by_cases hlt : lvl < level
  · rw [denoteBelowFamily_eq_reducible env level lvl hlt] at member ⊢
    exact ReducibleTypeStepDenote.forwardStep member step
  · rw [denoteBelowFamily_eq_empty_of_ge env level lvl (Nat.not_lt.mp hlt)] at member
    exact member.elim

/-- **Interface leg 2 (bounded by `lvl < level`): neutral-inclusion of `denoteBelowFamily env level`.**
Below the bound, coherence reduces to the real relation, where a neutral type is reducible
(`reducibleOfNeutral`).  The premise (reducts reducible) is not needed.  At/above the bound this FAILS (the
empty relation has no neutral members) — the level-bound the `piArm` satisfies via `denote e < level`. -/
theorem denoteBelowFamily_neutralInclusion_of_lt {scope : Nat} (env : Nat → Nat) (level : Nat) (lvl : Nat)
    (hlt : lvl < level) {typeCode : RawTerm scope} (neutral : IsNeutral typeCode)
    (_reductsReducible : ∀ reduct : RawTerm scope, Step typeCode reduct →
      ∃ candidate : RawTerm scope → Prop, denoteBelowFamily env level lvl reduct candidate) :
    ∃ candidate : RawTerm scope → Prop, denoteBelowFamily env level lvl typeCode candidate := by
  rw [denoteBelowFamily_eq_reducible env level lvl hlt]
  exact ReducibleTypeStepDenote.reducibleOfNeutral neutral

end FX1Poly.Typed
