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
from low bounds by construction).  It also carries the candidate-bridge edit verbatim from
`ReducibleTypeStepDenote`: the data-type code `emptyTypeCell` is pinned via the dedicated `dataEmpty` arm to its
head-expansion-closed empty Tait candidate `emptyTaitCandidate`, and `neutral` is gated with
`rootGenerator ≠ gen_emptyCode` so it no longer over-fires on the empty type code. -/
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
      typeCode.rootGenerator ≠ Generator.gen_emptyCode →
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
  | dataEmpty :
      ReducibleTypeStepBounded env lowerAt bound (emptyTypeCell (scope := scope)) emptyTaitCandidate
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
  | neutral noStep notPi notUniverse notEmpty =>
      intro higherBound _hle; exact ReducibleTypeStepBounded.neutral noStep notPi notUniverse notEmpty
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
  | dataEmpty =>
      intro higherBound _hle; exact ReducibleTypeStepBounded.dataEmpty
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

/-! ## The forget bridge: bounded ⊆ denote (all denote metatheory transfers for free)

The gated relation is the denote relation with a strictly-stronger universeCode arm, so a bounded-reducibility
derivation IS a denote-reducibility derivation (drop the `belowBound` gate).  This single bridge makes the ENTIRE
`ReducibleTypeStepDenote` metatheory — determinism, candidate-shape inversions, forward-step closure,
Conv-invariance/transfer, and the CR1/CR2/CR3 reducibility-candidate bundle — apply to bounded derivations WITHOUT
re-porting any of it.  The gate only RESTRICTS which derivations exist (excluding the label-blind universe members);
it never changes a candidate, so everything the denote relation proves about a candidate holds verbatim. -/

/-- **The forget bridge.**  A bounded-reducibility derivation forgets its universe gate to a denote-reducibility
derivation at the same `lowerAt` and candidate.  Five-arm induction, each arm mapping to its denote twin; the
`universeCode` arm drops `belowBound` (the candidate `universeDenotePredicate env lowerAt levelExpr` is identical).
The leverage lemma: bounded ⊆ denote, so denote metatheory is inherited. -/
theorem ReducibleTypeStepBounded.toReducibleTypeStepDenote {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop} {bound : Nat}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepBounded env lowerAt bound typeCode candidate) :
    ReducibleTypeStepDenote env lowerAt typeCode candidate := by
  induction reducible with
  | whnfExpand weakHeadStep _reductReducible ih =>
      exact ReducibleTypeStepDenote.whnfExpand weakHeadStep ih
  | neutral noStep notPi notUniverse notEmpty =>
      exact ReducibleTypeStepDenote.neutral noStep notPi notUniverse notEmpty
  | @piType _domainCode _codomainCode _domainCandidate codomainCandidate _domainReducible _codomainReducible
      ihDomain ihCodomain =>
      exact ReducibleTypeStepDenote.piType codomainCandidate ihDomain ihCodomain
  | universeCode levelExpr flag _belowBound =>
      exact ReducibleTypeStepDenote.universeCode levelExpr flag
  | dataEmpty =>
      exact ReducibleTypeStepDenote.dataEmpty
  | ofPointwiseIff _innerReducible pointwiseIff ih =>
      exact ReducibleTypeStepDenote.ofPointwiseIff ih pointwiseIff

/-- **The gated step relation is functional** — transferred from `ReducibleTypeStepDenote.deterministic` through
the forget bridge.  Two candidates of the same type code at the same bound are pointwise-equivalent. -/
theorem ReducibleTypeStepBounded.deterministic {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop} {bound : Nat}
    {typeCode : RawTerm scope} {candidate1 candidate2 : RawTerm scope → Prop}
    (reducible1 : ReducibleTypeStepBounded env lowerAt bound typeCode candidate1)
    (reducible2 : ReducibleTypeStepBounded env lowerAt bound typeCode candidate2) :
    PointwiseIff candidate1 candidate2 :=
  ReducibleTypeStepDenote.deterministic reducible1.toReducibleTypeStepDenote
    reducible2.toReducibleTypeStepDenote

/-- **The bound-carrying level-indexed relation is functional** — the family-level determinism, the canonical-
candidate reconciliation the bounded FT consumes (it lets a per-level existential candidate be replaced by the
canonical one).  Direct from `ReducibleTypeStepBounded.deterministic`. -/
theorem ReducibleTypeAtBounded.deterministic {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {typeCode : RawTerm scope} {candidate1 candidate2 : RawTerm scope → Prop}
    (reducible1 : ReducibleTypeAtBounded env bound typeCode candidate1)
    (reducible2 : ReducibleTypeAtBounded env bound typeCode candidate2) :
    PointwiseIff candidate1 candidate2 :=
  ReducibleTypeStepBounded.deterministic reducible1 reducible2

/-! ## Reduction-closure infrastructure + the UNCONDITIONAL CR1/CR2/CR3 bundle

Forward-closure must PRODUCE a bounded derivation (preserve the gate), so it does NOT transfer through the forget
bridge — it is a direct port of the denote proof (`universeCode` is a step normal form, so the gate is carried
through vacuously).  CR1/CR2/CR3 (`isReducibilityCandidate`) is also a direct induction, but here the gate PAYS
OFF: at the `universeCode` arm `belowBound : denote e < bound` supplies the level bound the neutral-inclusion leg
needs, so the FAMILY-level `ReducibleTypeAtBounded.isReducibilityCandidate` is UNCONDITIONAL — no deferred
predicative caveat (contrast the label-blind `ReducibleTypeStepDenote`, whose `denoteBelowFamily` discharge fails
neutral-inclusion at decoded levels ≥ the ambient level). -/

/-- Multi-step weak-head-expansion closure (port of `ReducibleTypeStepDenote.whnfExpandClosure`). -/
theorem ReducibleTypeStepBounded.whnfExpandClosure {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop} {bound : Nat}
    {candidate : RawTerm scope → Prop} :
    ∀ {firstType finalType : RawTerm scope}, StepStar firstType finalType →
      ∀ {weakHeadReduct : RawTerm scope}, WeakHeadStep firstType weakHeadReduct →
        ReducibleTypeStepBounded env lowerAt bound weakHeadReduct candidate →
        (∀ furtherReduct : RawTerm scope, StepStar weakHeadReduct furtherReduct →
          ReducibleTypeStepBounded env lowerAt bound furtherReduct candidate) →
        ReducibleTypeStepBounded env lowerAt bound finalType candidate := by
  intro firstType finalType chain
  induction chain with
  | refl _ =>
      intro weakHeadReduct weakHeadStep reductReducible _laterClosure
      exact ReducibleTypeStepBounded.whnfExpand weakHeadStep reductReducible
  | trans firstStep _restChain restClosure =>
      intro weakHeadReduct weakHeadStep reductReducible laterClosure
      rcases weakHeadStep.commuteWithStep _ firstStep with
        midEquation | ⟨_laterReduct, laterWeakHeadStep, catchUpChain⟩
      · subst midEquation
        exact laterClosure _ _restChain
      · exact restClosure laterWeakHeadStep (laterClosure _ catchUpChain)
          (fun furtherReduct furtherChain =>
            laterClosure furtherReduct (StepStar.trans_compose catchUpChain furtherChain))

/-- **Forward closure under multi-step reduction (bounded).**  A bounded-reducible type stays bounded-reducible at
the SAME candidate along any `StepStar`; the `universeCode` arm re-fires with its carried `belowBound` (a universe
code is a step normal form, so the chain is reflexive there).  Direct port of `ReducibleTypeStepDenote.forwardStepStar`
— it cannot transfer through the forget bridge because it must produce a BOUNDED (gate-preserving) derivation. -/
theorem ReducibleTypeStepBounded.forwardStepStar {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop} {bound : Nat}
    {candidate : RawTerm scope → Prop} {typeCode : RawTerm scope}
    (reducible : ReducibleTypeStepBounded env lowerAt bound typeCode candidate) :
    ∀ {finalType : RawTerm scope}, StepStar typeCode finalType →
      ReducibleTypeStepBounded env lowerAt bound finalType candidate := by
  induction reducible with
  | whnfExpand weakHeadStep reductReducible reductInductiveHypothesis =>
      intro finalType chain
      exact ReducibleTypeStepBounded.whnfExpandClosure chain weakHeadStep reductReducible
        (fun _furtherReduct furtherChain => reductInductiveHypothesis furtherChain)
  | neutral noWeakHeadStep notPiType notUniverse notEmpty =>
      intro finalType chain
      obtain ⟨finalNoWeakHeadStep, rootEquation⟩ :=
        WeakHeadStep.weakHeadNormalRootStableAlongStepStar chain noWeakHeadStep
      exact ReducibleTypeStepBounded.neutral finalNoWeakHeadStep
        (fun rootIsPiType => notPiType (rootEquation.symm.trans rootIsPiType))
        (fun rootIsUniverse => notUniverse (rootEquation.symm.trans rootIsUniverse))
        (fun rootIsEmpty => notEmpty (rootEquation.symm.trans rootIsEmpty))
  | piType codomainCandidate _domainReducible _codomainReducible
      domainInductiveHypothesis codomainInductiveHypothesis =>
      intro finalType chain
      obtain ⟨_updatedDomain, _updatedCodomain, finalEquation, domainChain, codomainChain⟩ :=
        StepStar.piTyCode_decompose chain
      subst finalEquation
      exact ReducibleTypeStepBounded.piType codomainCandidate (domainInductiveHypothesis domainChain)
        (fun argument domainMember =>
          codomainInductiveHypothesis argument domainMember
            (StepStar.subst0Body argument codomainChain))
  | universeCode levelExpr flag belowBound =>
      intro finalType chain
      have finalEquation :=
        StepStar.eq_of_noStep (fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step)
          chain
      subst finalEquation
      exact ReducibleTypeStepBounded.universeCode levelExpr flag belowBound
  | dataEmpty =>
      intro finalType chain
      have finalEquation :=
        StepStar.eq_of_noStep (fun reduct step => emptyTypeCell_noStep reduct step) chain
      subst finalEquation
      exact ReducibleTypeStepBounded.dataEmpty
  | ofPointwiseIff _innerReducible pointwiseIff innerHypothesis =>
      intro finalType chain
      exact (innerHypothesis chain).ofPointwiseIff pointwiseIff

/-- Single-step forward closure (bounded). -/
theorem ReducibleTypeStepBounded.forwardStep {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop} {bound : Nat}
    {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepBounded env lowerAt bound typeCode candidate) (step : Step typeCode reduct) :
    ReducibleTypeStepBounded env lowerAt bound reduct candidate :=
  ReducibleTypeStepBounded.forwardStepStar reducible (StepStar.single step)

/-- A neutral type is bounded-reducible (SN candidate via the `neutral` arm). -/
theorem ReducibleTypeStepBounded.reducibleOfNeutral {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop} {bound : Nat}
    {typeCode : RawTerm scope} (neutral : IsNeutral typeCode) :
    ∃ candidate : RawTerm scope → Prop, ReducibleTypeStepBounded env lowerAt bound typeCode candidate := by
  refine ⟨IsStronglyNormalizing, ReducibleTypeStepBounded.neutral
    (fun reduct => neutral.noWeakHeadStep reduct) ?_ ?_ ?_⟩
  · cases neutral <;> exact fun rootEquation => nomatch rootEquation
  · cases neutral <;> exact fun rootEquation => nomatch rootEquation
  · cases neutral <;> exact fun rootEquation => nomatch rootEquation

/-- The bounded below-family is the empty relation at or above the bound (port of `denoteBelowFamily_eq_empty_of_ge`). -/
theorem denoteBelowFamilyBounded_eq_empty_of_ge {scope : Nat} (env : Nat → Nat) :
    ∀ (bound lvl : Nat), bound ≤ lvl →
      denoteBelowFamilyBounded (scope := scope) env bound lvl = (fun _ _ => False) := by
  intro bound
  induction bound with
  | zero => intro lvl _; rfl
  | succ predBound _ih =>
      intro lvl hle
      have predLessThan : predBound < lvl := Nat.lt_of_lt_of_le (Nat.lt_succ_self predBound) hle
      show (if lvl < predBound then denoteBelowFamilyBounded env predBound lvl
            else if lvl = predBound then ReducibleTypeStepBounded env (denoteBelowFamilyBounded env predBound) predBound
            else fun _ _ => False) = fun _ _ => False
      rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt predLessThan)),
        if_neg (Ne.symm (Nat.ne_of_lt predLessThan))]

/-- **Interface leg 1 (forward-closed, unconditional):** the bounded below-family is forward-`Step`-closed at every
level (below the bound via the relation's forward closure; at/above it the empty-relation premise is `False`). -/
theorem denoteBelowFamilyBounded_forwardStep {scope : Nat} (env : Nat → Nat) (bound lvl : Nat)
    {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop}
    (member : denoteBelowFamilyBounded env bound lvl typeCode candidate) (step : Step typeCode reduct) :
    denoteBelowFamilyBounded env bound lvl reduct candidate := by
  by_cases hlt : lvl < bound
  · rw [denoteBelowFamilyBounded_eq_reducible env bound lvl hlt] at member ⊢
    exact ReducibleTypeStepBounded.forwardStep member step
  · rw [denoteBelowFamilyBounded_eq_empty_of_ge env bound lvl (Nat.not_lt.mp hlt)] at member
    exact member.elim

/-- **Interface leg 2 (neutral-inclusion, below the bound):** a neutral type is in the bounded below-family at any
`lvl < bound` (coherence to the relation, where `reducibleOfNeutral` applies).  The `lvl < bound` bound is exactly
what the gate supplies at every universe arm — which is why the family CR1/2/3 is unconditional. -/
theorem denoteBelowFamilyBounded_neutralInclusion_of_lt {scope : Nat} (env : Nat → Nat) (bound lvl : Nat)
    (hlt : lvl < bound) {typeCode : RawTerm scope} (neutral : IsNeutral typeCode)
    (_reductsReducible : ∀ reduct : RawTerm scope, Step typeCode reduct →
      ∃ candidate : RawTerm scope → Prop, denoteBelowFamilyBounded env bound lvl reduct candidate) :
    ∃ candidate : RawTerm scope → Prop, denoteBelowFamilyBounded env bound lvl typeCode candidate := by
  rw [denoteBelowFamilyBounded_eq_reducible env bound lvl hlt]
  exact ReducibleTypeStepBounded.reducibleOfNeutral neutral

/-- **CR1/CR2/CR3 for the bounded step relation (parametric).**  Every bounded-reducible candidate is a Girard
reducibility candidate.  Induction: `whnfExpand`/`ofPointwiseIff` by IH, `neutral` is the SN candidate, `piType`
the dependent-arrow candidate (bridging the codomain to denote to reuse `isDependentArrowReducibleStepDenote_is\
ReducibilityCandidate`, var-0 domain inhabitant), `universeCode` discharges its legs LOCALLY via `belowBound` —
hence neutral-inclusion is needed only BELOW the bound.  At `scope + 1` for the arrow CR1's var-0 inhabitant. -/
theorem ReducibleTypeStepBounded.isReducibilityCandidate {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {lowerAt : Nat → RawTerm (scope + 1) → (RawTerm (scope + 1) → Prop) → Prop}
    (lowerForwardStep : ∀ (lvl : Nat) {typeCode reduct : RawTerm (scope + 1)}
        {candidate : RawTerm (scope + 1) → Prop},
      lowerAt lvl typeCode candidate → Step typeCode reduct → lowerAt lvl reduct candidate)
    (lowerNeutralInclusionBelowBound : ∀ (lvl : Nat), lvl < bound →
        ∀ {typeCode : RawTerm (scope + 1)}, IsNeutral typeCode →
      (∀ reduct : RawTerm (scope + 1), Step typeCode reduct →
        ∃ candidate : RawTerm (scope + 1) → Prop, lowerAt lvl reduct candidate) →
      ∃ candidate : RawTerm (scope + 1) → Prop, lowerAt lvl typeCode candidate)
    {typeCode : RawTerm (scope + 1)} {candidate : RawTerm (scope + 1) → Prop}
    (reducible : ReducibleTypeStepBounded env lowerAt bound typeCode candidate) :
    IsReducibilityCandidate candidate := by
  induction reducible with
  | whnfExpand _weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact reductInductiveHypothesis
  | neutral _noWeakHeadStep _notPiType _notUniverse _notEmpty =>
      exact isStronglyNormalizing_isReducibilityCandidate
  | piType codomainCandidate _domainReducible codomainReducible
      domainInductiveHypothesis codomainInductiveHypothesis =>
      exact isDependentArrowReducibleStepDenote_isReducibilityCandidate
        domainInductiveHypothesis codomainInductiveHypothesis
        (fun argument argumentMember => (codomainReducible argument argumentMember).toReducibleTypeStepDenote)
        (.mkGen .gen_var ⟨0, Nat.succ_pos scope⟩ .childNil)
        (domainInductiveHypothesis.containsVariable ⟨0, Nat.succ_pos scope⟩)
  | universeCode levelExpr _flag belowBound =>
      exact ReducibleTypeStep.universeCandidateIsReducibilityCandidate
        (lowerForwardStep (LevelExpr.denote levelExpr env))
        (lowerNeutralInclusionBelowBound (LevelExpr.denote levelExpr env) belowBound)
  | dataEmpty =>
      exact emptyTaitCandidate_isReducibilityCandidate
  | ofPointwiseIff _innerReducible pointwiseIff innerInductiveHypothesis =>
      exact innerInductiveHypothesis.respectsPointwiseIff (fun term => pointwiseIff term)

/-- **★ The bounded level-indexed relation has UNCONDITIONAL CR1/CR2/CR3.**  The family-level reducibility-candidate
bundle, discharged with NO predicative caveat: the two `denoteBelowFamilyBounded` legs (forward-closed everywhere;
neutral-inclusion below the bound) feed `ReducibleTypeStepBounded.isReducibilityCandidate`, whose universe arm only
ever asks neutral-inclusion below the bound (the gate).  This is the property the label-blind `ReducibleTypeAtDenote`
could not get unconditionally — members of a bounded-reducible type are strongly normalizing (CR1), the relation is
forward-closed (CR2) and neutral-backward-closed (CR3), for the FULL relation, zero side conditions. -/
theorem ReducibleTypeAtBounded.isReducibilityCandidate {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {typeCode : RawTerm (scope + 1)} {candidate : RawTerm (scope + 1) → Prop}
    (reducible : ReducibleTypeAtBounded env bound typeCode candidate) :
    IsReducibilityCandidate candidate :=
  ReducibleTypeStepBounded.isReducibilityCandidate (lowerAt := denoteBelowFamilyBounded env bound)
    (fun lvl => denoteBelowFamilyBounded_forwardStep env bound lvl)
    (fun lvl hlt => denoteBelowFamilyBounded_neutralInclusion_of_lt env bound lvl hlt)
    reducible

end FX1Poly.Typed
