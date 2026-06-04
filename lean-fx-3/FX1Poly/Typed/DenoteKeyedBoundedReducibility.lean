import FX1Poly.Typed.DenoteKeyedReducibility

/-! # FX1Poly/Typed/DenoteKeyedBoundedReducibility
    — the bound-carrying (universe-gated) denote reducibility relation, with FREE cumulativity (SN-D5e/#753)

This is the foundational brick of the #753 / SN-D5e bound-carrying refactor — the genuine resolution of the
universe-domain-Π obstruction (#672 / denote #752) that every SN-043 route bottoms out at.

## Why the existing denote model is stuck (the label-blindness diagnosis)

`ReducibleTypeStepDenote` (`DenoteKeyedReducibility.lean`) is **universe-label-blind**: its `universeCode` arm
fires for `Type@levelExpr` at EVERY ambient level (anti-vacuity), so a type code's reducibility-as-type does NOT
bound its universe content.  Concretely `Type@huge → Type@huge` is a reducible TYPE at every level and hence a
"member" of `Type@0` (via the decode-set candidate) even though its universe content is `huge`.  Membership
therefore fails to bound universe content, and cumulativity (lift a universe member's reducibility-as-type from
its decoded level up to a higher level) is genuinely UNPROVABLE in that model — the documented
`DenoteKeyedCumulativityObstruction`.  The shortcut "member of `Type@k` ⟹ content `< denote k`" is FALSE here.

## The fix: GATE the universeCode arm on `denote levelExpr env < bound`

`ReducibleTypeStepBounded env lowerAt bound` is `ReducibleTypeStepDenote` with ONE change: the `universeCode` arm
carries `belowBound : denote levelExpr env < bound`.  A `Type@e` is then reducible-as-type at bound `b` ONLY when
`denote e < b`, so high-universe type codes are EXCLUDED from low bounds BY CONSTRUCTION — the model becomes
universe-label-AWARE.  The below-family `denoteBelowFamilyBounded` is the SAME structural (non-well-founded)
recursion as `denoteBelowFamily`, so it inherits the propext-clean / `Quot.sound`-free discipline (well-founded
recursion's `.eq_def` would leak `Quot.sound`).

## The payoff: cumulativity is FREE (`stepBounded_cumulative`)

In the gated relation, a member of `Type@e` carries the bound `denote e`, and `denote e < b ≤ b'` is GUARANTEED,
so the `universeCode` arm re-fires at every higher bound with a candidate that the coherence lemma
(`denoteBelowFamilyBounded_eq_reducible`) shows is unchanged.  A clean five-arm induction lifts any
bounded-reducibility derivation from `bound` to any `higherBound` with the SAME candidate — the universeCode arm
via `ofPointwiseIff` (avoiding any function-`Eq`, hence no `funext`/`Quot.sound`), every other arm by the inductive
hypothesis.  This is exactly the property the label-blind model could not prove; it is the keystone the
genFormationPi piArm needs (a universe member lifts to the former's output level for free).

## What lands here (all zero-axiom)

  * `ReducibleTypeStepBounded` — the gated step functor (universeCode arm + `belowBound`).
  * `denoteBelowFamilyBounded` / `ReducibleTypeAtBounded` / `IsReducibleTypeAtBounded` — the structural
    below-family, the level-indexed relation, and its inhabitation wrapper.
  * `denoteBelowFamilyBounded_eq_reducible` — coherence (below-family at `lvl < bound` equals the relation at `lvl`).
  * `stepBounded_cumulative` — **the payoff**: same-candidate cumulativity at the step level.
  * `isReducibleBounded_cumulative` — the `IsReducibleTypeAtBounded` corollary.

## Remaining for #753 (next bricks)

CR1/CR2/CR3 over the gated relation (port from the existing proofs), the bounded FT motive + arms (the
genFormationPi piArm now closes because cumulativity is free), and the bridge `bounded-reducible → SN` wiring
SN-D6/#745.  This file is the de-risking foundation: the gated relation is propext-clean and its defining
advantage — free cumulativity — is proven.

## Zero-axiom verification

The gated inductive (same shape as the shipped `ReducibleTypeStepDenote`), the structural below-family + its
coherence (`rfl` at the boundary), and the cumulativity induction (five arms; universeCode via `ofPointwiseIff` +
one `rw` of the coherence-derived function equality).  No `funext`, no well-founded recursion.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The bound-carrying (universe-gated) denote step functor.**  Identical to `ReducibleTypeStepDenote` except
the `universeCode` arm carries `belowBound : denote levelExpr env < bound`, so a universe code is reducible-as-type
at a bound only strictly below that bound — making the model universe-label-AWARE (high-universe codes excluded
from low bounds by construction). -/
inductive ReducibleTypeStepBounded {scope : Nat} (env : Nat → Nat)
    (lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop) (bound : Nat) :
    RawTerm scope → (RawTerm scope → Prop) → Prop where
  | whnfExpand {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop} :
      WeakHeadStep typeCode reduct → ReducibleTypeStepBounded env lowerAt bound reduct candidate →
      ReducibleTypeStepBounded env lowerAt bound typeCode candidate
  | neutral {typeCode : RawTerm scope} :
      (∀ reduct : RawTerm scope, ¬ WeakHeadStep typeCode reduct) →
      typeCode.rootGenerator ≠ Generator.gen_piTyCode →
      typeCode.rootGenerator ≠ Generator.gen_universeCode →
      ReducibleTypeStepBounded env lowerAt bound typeCode IsStronglyNormalizing
  | piType {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
      {domainCandidate : RawTerm scope → Prop}
      (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)) :
      ReducibleTypeStepBounded env lowerAt bound domainCode domainCandidate →
      (∀ argument : RawTerm scope, domainCandidate argument →
        ReducibleTypeStepBounded env lowerAt bound (RawTerm.subst0 codomainCode argument)
          (codomainCandidate argument)) →
      ReducibleTypeStepBounded env lowerAt bound
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
        (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
          codomainCandidate argument
            (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))))
  | universeCode (levelExpr : LevelExpr) (flag : UniverseFlag)
      (belowBound : LevelExpr.denote levelExpr env < bound) :
      ReducibleTypeStepBounded env lowerAt bound
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (universeDenotePredicate env lowerAt levelExpr)
  | ofPointwiseIff {typeCode : RawTerm scope} {candidate canonical : RawTerm scope → Prop} :
      ReducibleTypeStepBounded env lowerAt bound typeCode candidate →
      PointwiseIff candidate canonical →
      ReducibleTypeStepBounded env lowerAt bound typeCode canonical

/-- **The structural below-family for the gated relation.**  The SAME structural-recursion shape as
`denoteBelowFamily` (recursive calls at the predecessor `level`, NOT well-founded), so it avoids the `Quot.sound`
leak that well-founded recursion's `.eq_def` would introduce. -/
def denoteBelowFamilyBounded {scope : Nat} (env : Nat → Nat) :
    Nat → Nat → RawTerm scope → (RawTerm scope → Prop) → Prop
  | 0, _lvl => fun _ _ => False
  | level + 1, lvl =>
      if lvl < level then denoteBelowFamilyBounded env level lvl
      else if lvl = level then ReducibleTypeStepBounded env (denoteBelowFamilyBounded env level) level
      else fun _ _ => False

/-- **The bound-carrying level-indexed reducibility relation:** the gated step functor over the structural
below-family at the same bound. -/
def ReducibleTypeAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat) :
    RawTerm scope → (RawTerm scope → Prop) → Prop :=
  ReducibleTypeStepBounded env (denoteBelowFamilyBounded env bound) bound

/-- **Semantic well-formed type (bound-carrying).** -/
def IsReducibleTypeAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat) (typeCode : RawTerm scope) : Prop :=
  ∃ candidate : RawTerm scope → Prop, ReducibleTypeAtBounded env bound typeCode candidate

/-- **Coherence (level-stability of the bounded below-family).**  For `lvl < bound`, the below-family at `lvl`
agrees with the relation at `lvl`.  Structural induction on `bound`; the boundary `lvl = predBound` closes by
`rfl` (the relation's own definition).  The exact analogue of `denoteBelowFamily_eq_reducible`. -/
theorem denoteBelowFamilyBounded_eq_reducible {scope : Nat} (env : Nat → Nat) :
    ∀ (bound lvl : Nat), lvl < bound →
      denoteBelowFamilyBounded (scope := scope) env bound lvl = ReducibleTypeAtBounded env lvl := by
  intro bound
  induction bound with
  | zero => intro lvl hlt; exact absurd hlt (Nat.not_lt_zero lvl)
  | succ predBound ih =>
      intro lvl hlt
      show (if lvl < predBound then denoteBelowFamilyBounded env predBound lvl
            else if lvl = predBound then ReducibleTypeStepBounded env (denoteBelowFamilyBounded env predBound) predBound
            else fun _ _ => False) = ReducibleTypeAtBounded env lvl
      by_cases hbelow : lvl < predBound
      · rw [if_pos hbelow]; exact ih lvl hbelow
      · rw [if_neg hbelow]
        have heq : lvl = predBound := Nat.le_antisymm (Nat.le_of_lt_succ hlt) (Nat.not_lt.mp hbelow)
        rw [if_pos heq, heq]
        rfl

/-- **The payoff: cumulativity is FREE in the gated relation (step level, same candidate).**  A bounded-reducibility
derivation at `bound` re-fires at any `higherBound ≥ bound` with the SAME candidate.  The four non-universe arms
lift by the inductive hypothesis; the `universeCode` arm re-fires at `higherBound` (its gate `denote e < higherBound`
is GUARANTEED by `denote e < bound ≤ higherBound`) and reconciles the two candidates via `ofPointwiseIff` — the
two `universeDenotePredicate`s agree pointwise because the below-family at the fixed index `denote e` is the same
relation at both bounds (`denoteBelowFamilyBounded_eq_reducible`).  Using `ofPointwiseIff` (a pointwise iff) rather
than a function `Eq` keeps the proof `funext`-free, hence `Quot.sound`-free.  This is precisely the property the
label-blind `ReducibleTypeStepDenote` could NOT prove: a universe member lifts to a higher bound for free. -/
theorem stepBounded_cumulative {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepBounded env (denoteBelowFamilyBounded env bound) bound typeCode candidate) :
    ∀ higherBound : Nat, bound ≤ higherBound →
      ReducibleTypeStepBounded env (denoteBelowFamilyBounded env higherBound) higherBound typeCode candidate := by
  induction reducible with
  | whnfExpand weakHeadStep _reductReducible ih =>
      intro higherBound hle; exact ReducibleTypeStepBounded.whnfExpand weakHeadStep (ih higherBound hle)
  | neutral noStep notPi notUniverse =>
      intro higherBound _hle; exact ReducibleTypeStepBounded.neutral noStep notPi notUniverse
  | @piType domainCode codomainCode domainCandidate codomainCandidate _domainReducible _codomainReducible
      ihDomain ihCodomain =>
      intro higherBound hle
      exact ReducibleTypeStepBounded.piType codomainCandidate (ihDomain higherBound hle)
        (fun argument argumentInDomain => ihCodomain argument argumentInDomain higherBound hle)
  | universeCode levelExpr flag belowBound =>
      intro higherBound hle
      have belowHigher : LevelExpr.denote levelExpr env < higherBound := Nat.lt_of_lt_of_le belowBound hle
      have lowEq := denoteBelowFamilyBounded_eq_reducible (scope := scope) env bound
        (LevelExpr.denote levelExpr env) belowBound
      have highEq := denoteBelowFamilyBounded_eq_reducible (scope := scope) env higherBound
        (LevelExpr.denote levelExpr env) belowHigher
      have funcEq : denoteBelowFamilyBounded env bound (LevelExpr.denote levelExpr env)
                  = denoteBelowFamilyBounded env higherBound (LevelExpr.denote levelExpr env) := lowEq.trans highEq.symm
      refine ReducibleTypeStepBounded.ofPointwiseIff
        (ReducibleTypeStepBounded.universeCode levelExpr flag belowHigher)
        (fun term => ?_)
      show (IsStronglyNormalizing term ∧
              ∃ c, denoteBelowFamilyBounded env higherBound (LevelExpr.denote levelExpr env) term c)
         ↔ (IsStronglyNormalizing term ∧
              ∃ c, denoteBelowFamilyBounded env bound (LevelExpr.denote levelExpr env) term c)
      rw [funcEq]
  | ofPointwiseIff _innerReducible pointwiseIff ih =>
      intro higherBound hle; exact ReducibleTypeStepBounded.ofPointwiseIff (ih higherBound hle) pointwiseIff

/-- **Cumulativity for the inhabitation wrapper.**  `IsReducibleTypeAtBounded` is monotone in the bound — the
`∃`-candidate corollary of `stepBounded_cumulative`. -/
theorem isReducibleBounded_cumulative {scope : Nat} {env : Nat → Nat} {bound higherBound : Nat}
    {typeCode : RawTerm scope}
    (reducible : IsReducibleTypeAtBounded env bound typeCode) (hle : bound ≤ higherBound) :
    IsReducibleTypeAtBounded env higherBound typeCode :=
  let ⟨candidate, candidateReducible⟩ := reducible
  ⟨candidate, stepBounded_cumulative candidateReducible higherBound hle⟩

end FX1Poly.Typed
