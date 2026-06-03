import FX1Poly.Typed.ClassifierLevelMeasure

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

end FX1Poly.Typed
