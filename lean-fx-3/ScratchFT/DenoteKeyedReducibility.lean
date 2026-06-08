import FX1Poly.Typed.ClassifierLevelMeasure

/-! Scratch probe: the DENOTE-KEYED reducibility relation toward #672 — STRUCTURAL formulation.

The fuel relation walls level-irrelevance at the universe-domain Pi because its universe arm uses
`lowerReducible` UNIFORMLY (ambient fuel minus one), so `Type@e` membership at fuel 0 is empty.

The fix: the universe arm at `Type@e` decodes to the lower relation AT THE DECODED LEVEL
`LevelExpr.denote levelExpr env`.  To access arbitrary lower levels WITHOUT well-founded recursion (whose
auto-generated `.eq_def` leaks `Quot.sound`), the lower family is built by STRUCTURAL recursion on the
level: `belowFamily (level+1)` reuses `belowFamily level` below `level`, installs `Step (belowFamily level)`
at exactly `level`, empty above.  Every recursive call is at the structural predecessor.

Probe goals: (1) positivity of the step functor; (2) the structural family is zero-axiom (no WF, no
Quot.sound); (3) coherence `belowFamily level lvl = ReducibleTypeAtDenote lvl` for `lvl < level`;
(4) anti-vacuity: a universe code is a reducible type at EVERY level (refuting SN-001's empty base);
(5) the headline — universe-membership LEVEL-IRRELEVANCE: `Type@e`'s candidate is the same decode-at-
`denote e` set at every level `> denote e`. -/

namespace FX1Poly.Core
open FX1Poly.Foundation FX1Poly.Universe
open StepStar

/-- The denote-keyed universe candidate predicate.  Unlike `universeReducibilityPredicate` (which uses a
single `lowerReducible`), this decodes `Type@levelExpr` to the lower relation AT `denote levelExpr env`. -/
def universeDenotePredicate {scope : Nat} (env : Nat → Nat)
    (lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop)
    (levelExpr : LevelExpr) : RawTerm scope → Prop :=
  fun typeCode => IsStronglyNormalizing typeCode ∧
    ∃ candidate : RawTerm scope → Prop, lowerAt (LevelExpr.denote levelExpr env) typeCode candidate

/-- The denote-keyed reducibility step-functor.  Identical to `ReducibleTypeStep` except the `universeCode`
arm reaches into `lowerAt (denote levelExpr env)` rather than a uniform `lower`. -/
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

/-- The lower family below a level, built by STRUCTURAL recursion: `belowFamily (level+1)` reuses
`belowFamily level` for `lvl < level`, installs the step-functor over `belowFamily level` at exactly
`lvl = level`, and is empty above.  Both recursive calls are at the structural predecessor `level`. -/
def belowFamily {scope : Nat} (env : Nat → Nat) :
    Nat → Nat → RawTerm scope → (RawTerm scope → Prop) → Prop
  | 0, _lvl => fun _ _ => False
  | level + 1, lvl =>
      if lvl < level then belowFamily env level lvl
      else if lvl = level then ReducibleTypeStepDenote env (belowFamily env level)
      else fun _ _ => False

/-- The denote-keyed level-indexed reducibility relation: the step-functor over the structural
below-family. -/
def ReducibleTypeAtDenote {scope : Nat} (env : Nat → Nat) (level : Nat) :
    RawTerm scope → (RawTerm scope → Prop) → Prop :=
  ReducibleTypeStepDenote env (belowFamily env level)

/-- Existential (semantic well-formed type) wrapper. -/
def IsReducibleTypeAtDenote {scope : Nat} (env : Nat → Nat) (level : Nat) (typeCode : RawTerm scope) :
    Prop :=
  ∃ candidate : RawTerm scope → Prop, ReducibleTypeAtDenote env level typeCode candidate

/-- **Coherence (level-stability of the below-family).**  For `lvl < level`, the below-family at `lvl`
agrees with the relation at `lvl`.  Structural induction on `level`; the `lvl = level` boundary uses
`Nat.le_antisymm`.  No axioms (structural, `ite` split via `if_pos`/`if_neg`). -/
theorem belowFamily_eq_reducible {scope : Nat} (env : Nat → Nat) :
    ∀ (level lvl : Nat), lvl < level →
      belowFamily (scope := scope) env level lvl = ReducibleTypeAtDenote env lvl := by
  intro level
  induction level with
  | zero => intro lvl hlt; exact absurd hlt (Nat.not_lt_zero lvl)
  | succ predLevel ih =>
      intro lvl hlt
      show (if lvl < predLevel then belowFamily env predLevel lvl
            else if lvl = predLevel then ReducibleTypeStepDenote env (belowFamily env predLevel)
            else fun _ _ => False) = ReducibleTypeAtDenote env lvl
      by_cases hbelow : lvl < predLevel
      · rw [if_pos hbelow]; exact ih lvl hbelow
      · rw [if_neg hbelow]
        have heq : lvl = predLevel :=
          Nat.le_antisymm (Nat.le_of_lt_succ hlt) (Nat.not_lt.mp hbelow)
        rw [if_pos heq, heq]
        rfl

/-- **Anti-vacuity (the refutation of SN-001).**  A universe code `Type@e` is a reducible type at EVERY
ambient level — the universe arm fires unconditionally (no fuel-0 emptiness). -/
theorem universeCode_isReducibleAtDenote {scope : Nat} (env : Nat → Nat) (level : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsReducibleTypeAtDenote (scope := scope) env level
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) :=
  ⟨_, ReducibleTypeStepDenote.universeCode levelExpr flag⟩

/-- **The headline — universe-membership LEVEL-IRRELEVANCE.**  At any ambient level strictly above the
decoded level `denote levelExpr env`, the candidate of `Type@levelExpr` is `IsStronglyNormalizing ∧
IsReducibleTypeAtDenote env (denote levelExpr env)` — the SAME decode-at-`denote e` set, INDEPENDENT of
the ambient level.  This is precisely the level-irrelevance the fuel model could not deliver: it is true
HERE by construction (coherence rewrites the below-family at `denote e` to the relation at `denote e`). -/
theorem universeMembership_levelIrrelevant {scope : Nat} (env : Nat → Nat) (level : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (habove : LevelExpr.denote levelExpr env < level) :
    ReducibleTypeAtDenote (scope := scope) env level
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (fun member : RawTerm scope => IsStronglyNormalizing member ∧
          IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) member) := by
  have key : belowFamily env level (LevelExpr.denote levelExpr env)
      = ReducibleTypeAtDenote (scope := scope) env (LevelExpr.denote levelExpr env) :=
    belowFamily_eq_reducible env level (LevelExpr.denote levelExpr env) habove
  refine ReducibleTypeStepDenote.ofPointwiseIff
    (ReducibleTypeStepDenote.universeCode levelExpr flag) (fun member => ?_)
  show (IsStronglyNormalizing member ∧
      ∃ candidate, belowFamily env level (LevelExpr.denote levelExpr env) member candidate)
    ↔ (IsStronglyNormalizing member ∧
      IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) member)
  rw [key]
  exact Iff.rfl

end FX1Poly.Core

#print axioms FX1Poly.Core.ReducibleTypeStepDenote
#print axioms FX1Poly.Core.belowFamily
#print axioms FX1Poly.Core.ReducibleTypeAtDenote
#print axioms FX1Poly.Core.belowFamily_eq_reducible
#print axioms FX1Poly.Core.universeCode_isReducibleAtDenote
#print axioms FX1Poly.Core.universeMembership_levelIrrelevant
