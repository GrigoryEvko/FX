import FX1Poly.Typed.HigherOrderSimplyTypedReducibility
import FX1Poly.Typed.ReducibleSemanticRules
import FX1Poly.Core.SubstPreservationProbes

/-! # FX1Poly/Typed/SimplyTypedTermReducibility
    — the term-formation reducibility rules of the simply-typed fragment, made concrete

The simply-typed reducibility arc (`FirstOrderSimplyTypedReducibility` → `HigherOrderSimplyTypedReducibility`)
proved that simply-typed TYPES are reducible at all levels and admit member-extension.  This file turns to
the TERMS: it specializes the shipped semantic typing rules (`IsReducibleMemberAt.abstractionNonDependent` /
`.application`) to the simply-typed fragment, giving the two term-formation rules in candidate-free form, and
exercises them on concrete terms — culminating in the strong normalization of a genuinely REDUCING term (a
β-redex), the real Tait payoff (CR1 on a non-normal term, not a trivially-SN normal form).

These are the membership-construction counterparts of the type-level reducibility lemmas: where the type side
proves `A → B` is a reducible TYPE, the term side proves λ-abstractions are reducible MEMBERS of it and that
application eliminates membership.  They are the non-substitution (concrete-term) specializations of the
fundamental theorem's `piIntro` / `piElim` arms (`abstractionNonDependentUnderSubst` / `applicationUnderSubst`
in `ReducibleSemanticRules`); the universe/dependent obstruction is absent in the simply-typed fragment.

## Contents

  * `IsReducibleMemberAt.lambdaNeutralArrow` — ABSTRACTION: `λ.body : A → B` is a reducible member when A, B
    are neutral and the body preserves strong normalization under single substitution.  The neutral
    domain/codomain make their candidate `IsStronglyNormalizing`, collapsing `abstractionNonDependent`'s
    candidate-indexed premises to a pure SN-preservation condition on the body.
  * `IsReducibleMemberAt.applicationNonDependentArrow` — APPLICATION: a reducible member of `A → B` applied to
    a reducible member of A is a reducible member of B (the weakening cancels the dependent output).
  * `IsReducibleMemberAt.polymorphicIdentity` — `λx.x : A → A` is a reducible member for any variable type A
    (`subst0 (var 0) arg = arg`, so the body condition is the identity).
  * `polymorphicIdentityRedexStronglyNormalizing` — `(λx.x) y` (a β-REDEX) is strongly normalizing: the
    identity (reducible member of `A → A`) applied to a variable (reducible member of A) is a reducible member
    of A, hence SN by CR1 at the neutral classifier.  SN of an actually-reducing term.
  * `IsReducibleMemberAt.lambdaNeutralDomain` — ABSTRACTION over ANY reducible codomain (generalizes
    `lambdaNeutralArrow`): the codomain candidate is its own member-predicate, so the body condition is "the
    body lands as a reducible MEMBER of the codomain" — the form HIGHER-ORDER terms (functions returning
    functions) and the fundamental theorem's λ arm need.
  * `IsReducibleMemberAt.constantIdentity` — `λx.(λy.y) : A → (B → B)` is a reducible member: a higher-order
    function (ARROW codomain) returning the polymorphic identity, demonstrating `lambdaNeutralDomain` on a
    non-neutral codomain.
  * `subst0_lamCellVarOne_eq_lamWeaken` — the binder-crossing substitution `subst0 (λy.var 1) arg = λy.weaken
    arg`, proven fold-`rfl`-free (no `propext`/`Quot.sound`) with a `Nat`-arithmetic `Fin` bound (no `omega`).
  * `IsReducibleMemberAt.kCombinator` — `λx.λy.x : A → (B → A)` is a reducible member: the hardest concrete
    term, where the inner body CAPTURES the outer bound variable, exercising variable-capture-avoiding
    substitution under nested binders.
  * `IsReducibleMemberAt.lambdaLeafDomain` — the MAXIMALLY-GENERAL abstraction rule: a LEAF domain
    (weak-head-normal, non-Π, non-universe — covering DATA FORMERS, not only neutrals) + any reducible
    codomain.  Subsumes `lambdaNeutralArrow` and `lambdaNeutralDomain`, matching the `IsSimplyTyped.leaf` class.
  * `IsReducibleMemberAt.sigmaIdentity` — `λx.x : (Σ A. B) → (Σ A. B)` is a reducible member: the identity over
    a Σ-code (data-former) base type, reachable only via `lambdaLeafDomain` (a Σ-code is a leaf but NOT
    neutral).

## Zero-axiom verification

Each lemma composes shipped raw rules (`abstractionNonDependent` / `application` / `atNeutralClassifier` /
`IsReducibleMemberAt.variable`) with the neutral SN candidate (`ReducibleTypeStep.neutral`) and the
weaken/var substitution equations (`weaken_subst_singleton` / `subst0_var_zero`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Abstraction for a neutral-domain non-dependent arrow.**  `λ.body` is a reducible member of `A → B`
(code `piTyCodeCell domainCode (weaken codomainBase)`) when A, B are neutral and the body preserves strong
normalization under single substitution.  A neutral type's reducibility candidate is `IsStronglyNormalizing`
(`ReducibleTypeStep.neutral`), so the domain-CR1 premise of `abstractionNonDependent` is the identity and its
codomain-membership premise is exactly the SN-preservation condition stated here. -/
theorem IsReducibleMemberAt.lambdaNeutralArrow {scope : Nat} {level : Nat}
    {domainCode codomainBase : RawTerm scope} {body : RawTerm (scope + 1)}
    (domainNeutral : IsNeutral domainCode) (codomainNeutral : IsNeutral codomainBase)
    (bodyPreservesSN : ∀ argument : RawTerm scope,
      IsStronglyNormalizing argument → IsStronglyNormalizing (RawTerm.subst0 body argument)) :
    IsReducibleMemberAt level
      (piTyCodeCell domainCode (RawTerm.weaken codomainBase)) (lamCell body) := by
  have neutralReducible : ∀ {typeCode : RawTerm scope}, IsNeutral typeCode →
      ReducibleTypeAt level typeCode IsStronglyNormalizing := by
    intro typeCode neutral
    have noStep := neutral.noWeakHeadStep
    have notPi := neutral.rootGenerator_ne_piTyCode
    have notUniv := neutral.rootGenerator_ne_universeCode
    cases level with
    | zero => exact ReducibleTypeStep.neutral noStep notPi notUniv
    | succ predLevel => exact ReducibleTypeStep.neutral noStep notPi notUniv
  exact IsReducibleMemberAt.abstractionNonDependent (neutralReducible domainNeutral)
    (fun _argument argumentSN => argumentSN) (neutralReducible codomainNeutral) bodyPreservesSN

/-- **Application for a non-dependent arrow.**  A reducible member of `A → B` (code
`piTyCodeCell domainCode (weaken codomainBase)`) applied to a reducible member of A yields a reducible member
of B.  The shipped `IsReducibleMemberAt.application` lands at `subst0 (weaken codomainBase) argument`, which
the weakening cancels to `codomainBase` (`weaken_subst_singleton`). -/
theorem IsReducibleMemberAt.applicationNonDependentArrow {scope : Nat} {level : Nat}
    {domainCode codomainBase functionTerm argument : RawTerm scope}
    (functionMember : IsReducibleMemberAt level
      (piTyCodeCell domainCode (RawTerm.weaken codomainBase)) functionTerm)
    (argumentMember : IsReducibleMemberAt level domainCode argument) :
    IsReducibleMemberAt level codomainBase (appCell functionTerm argument) := by
  have applied := IsReducibleMemberAt.application functionMember argumentMember
  rwa [show RawTerm.subst0 (RawTerm.weaken codomainBase) argument = codomainBase from
    RawTerm.weaken_subst_singleton codomainBase argument] at applied

/-- **The polymorphic identity is a reducible member of `A → A`.**  For a variable type A, `λx.x`
(`lamCell (var 0)`) is a reducible member of `A → A`: the body `var 0` substitutes to the argument itself
(`subst0_var_zero`), so the SN-preservation condition of `lambdaNeutralArrow` is the identity.  The canonical
first concrete reducible TERM inhabitant of a simply-typed function type. -/
theorem IsReducibleMemberAt.polymorphicIdentity {scope : Nat} {level : Nat} {index : Fin scope} :
    IsReducibleMemberAt level
      (piTyCodeCell (variableCell index) (RawTerm.weaken (variableCell index)))
      (lamCell (variableCell ⟨0, Nat.zero_lt_succ scope⟩)) := by
  refine IsReducibleMemberAt.lambdaNeutralArrow (IsNeutral.var index) (IsNeutral.var index) ?_
  intro argument argumentSN
  rw [show RawTerm.subst0 (variableCell ⟨0, Nat.zero_lt_succ scope⟩) argument = argument from
    RawTerm.subst0_var_zero argument]
  exact argumentSN

/-- **The β-redex `(λx.x) y` is strongly normalizing.**  The polymorphic identity (a reducible member of
`A → A`) applied to a variable `y` (a reducible member of the variable type A, by
`IsReducibleMemberAt.variable`) is a reducible member of A, hence strongly normalizing by CR1 at the neutral
classifier (`atNeutralClassifier`).  This is strong normalization of an actually-REDUCING term — the genuine
Tait payoff, not a trivially-SN normal form: `(λx.x) y` β-reduces to `y`, and the reducibility machinery
proves the whole redex terminates. -/
theorem polymorphicIdentityRedexStronglyNormalizing {scope : Nat} {predLevel : Nat}
    {typeIndex argumentIndex : Fin (scope + 1)} :
    IsStronglyNormalizing
      (appCell (lamCell (variableCell ⟨0, Nat.zero_lt_succ (scope + 1)⟩))
        (variableCell argumentIndex)) := by
  have typeReducible : ReducibleTypeAt (predLevel + 1) (variableCell typeIndex) IsStronglyNormalizing :=
    ReducibleTypeStep.neutral (IsNeutral.var typeIndex).noWeakHeadStep
      (IsNeutral.var typeIndex).rootGenerator_ne_piTyCode
      (IsNeutral.var typeIndex).rootGenerator_ne_universeCode
  have argumentMember : IsReducibleMemberAt (predLevel + 1) (variableCell typeIndex)
      (variableCell argumentIndex) :=
    IsReducibleMemberAt.variable typeReducible argumentIndex
  have applicationMember : IsReducibleMemberAt (predLevel + 1) (variableCell typeIndex)
      (appCell (lamCell (variableCell ⟨0, Nat.zero_lt_succ (scope + 1)⟩))
        (variableCell argumentIndex)) :=
    IsReducibleMemberAt.applicationNonDependentArrow IsReducibleMemberAt.polymorphicIdentity argumentMember
  exact (IsReducibleMemberAt.atNeutralClassifier (IsNeutral.var typeIndex).noWeakHeadStep
    (IsNeutral.var typeIndex).rootGenerator_ne_piTyCode
    (IsNeutral.var typeIndex).rootGenerator_ne_universeCode).mp applicationMember

/-- **Abstraction for a neutral domain over ANY reducible codomain.**  Generalizes `lambdaNeutralArrow`
(which required the codomain to be neutral too) to an arbitrary reducible codomain — the form needed for
HIGHER-ORDER terms (functions returning functions).  The codomain candidate is its own member-predicate
(`IsReducibleTypeAt.reducibleMemberCandidate`, supplied by mere existence of a candidate), so the body
condition is the clean "the body lands as a reducible MEMBER of the codomain" — exactly the shape the
fundamental theorem's λ arm threads.  `lambdaNeutralArrow` is the special case where the codomain is neutral
(its member-predicate coincides with `IsStronglyNormalizing`). -/
theorem IsReducibleMemberAt.lambdaNeutralDomain {scope : Nat} {level : Nat}
    {domainCode codomainBase : RawTerm scope} {body : RawTerm (scope + 1)}
    (domainNeutral : IsNeutral domainCode)
    (codomainReducibleType : IsReducibleTypeAt level codomainBase)
    (bodyMember : ∀ argument : RawTerm scope, IsStronglyNormalizing argument →
      IsReducibleMemberAt level codomainBase (RawTerm.subst0 body argument)) :
    IsReducibleMemberAt level
      (piTyCodeCell domainCode (RawTerm.weaken codomainBase)) (lamCell body) := by
  have domainReducible : ReducibleTypeAt level domainCode IsStronglyNormalizing := by
    have noStep := domainNeutral.noWeakHeadStep
    have notPi := domainNeutral.rootGenerator_ne_piTyCode
    have notUniv := domainNeutral.rootGenerator_ne_universeCode
    cases level with
    | zero => exact ReducibleTypeStep.neutral noStep notPi notUniv
    | succ predLevel => exact ReducibleTypeStep.neutral noStep notPi notUniv
  exact IsReducibleMemberAt.abstractionNonDependent domainReducible
    (fun _argument argumentSN => argumentSN)
    (IsReducibleTypeAt.reducibleMemberCandidate codomainReducibleType) bodyMember

/-- **A higher-order term: `λx.(λy.y) : A → (B → B)` is a reducible member.**  The function that ignores its
argument and returns the polymorphic B-identity — a reducible member at an ARROW codomain, demonstrating
`lambdaNeutralDomain` on a non-neutral codomain.  The codomain `B → B` is reducible
(`IsSimplyTyped.reducibleAndMemberExtension`); the body `weaken (λy.y)` cancels under single substitution
(`weaken_subst_singleton`) to the B-identity, which is a reducible member by `polymorphicIdentity`. -/
theorem IsReducibleMemberAt.constantIdentity {scope : Nat} {level : Nat}
    {domainIndex codomainIndex : Fin scope} :
    IsReducibleMemberAt level
      (piTyCodeCell (variableCell domainIndex)
        (RawTerm.weaken (piTyCodeCell (variableCell codomainIndex)
          (RawTerm.weaken (variableCell codomainIndex)))))
      (lamCell (RawTerm.weaken (lamCell (variableCell ⟨0, Nat.zero_lt_succ scope⟩)))) := by
  have codomainReducibleType : IsReducibleTypeAt level
      (piTyCodeCell (variableCell codomainIndex) (RawTerm.weaken (variableCell codomainIndex))) :=
    (IsSimplyTyped.arrow (IsSimplyTyped.ofNeutral (IsNeutral.var codomainIndex))
      (IsSimplyTyped.ofNeutral (IsNeutral.var codomainIndex))).reducibleAndMemberExtension.1 level
  refine IsReducibleMemberAt.lambdaNeutralDomain (IsNeutral.var domainIndex) codomainReducibleType ?_
  intro argument _argumentSN
  rw [show RawTerm.subst0
      (RawTerm.weaken (lamCell (variableCell ⟨0, Nat.zero_lt_succ scope⟩))) argument
      = lamCell (variableCell ⟨0, Nat.zero_lt_succ scope⟩) from
    RawTerm.weaken_subst_singleton (lamCell (variableCell ⟨0, Nat.zero_lt_succ scope⟩)) argument]
  exact IsReducibleMemberAt.polymorphicIdentity

/-- **Substituting into `λy.x` (the captured outer variable) yields the constant function `λy.(weaken x)`.**
The binder-crossing substitution computation behind the K combinator: `subst0 (λy. var 1) arg = λy. weaken arg`.
`subst_lamCell` pushes the substitution under the λ (lifting it); `RawTerm.subst_var_reduces` evaluates the
lifted substitution at the captured variable `var 1`, which `RawTermSubst.lift`'s successor case sends to
`weaken (singleton arg at var 0) = weaken arg` (`singleton_var_zero`).  Proven WITHOUT a fold-level `rfl` (which
would leak `propext`/`Quot.sound`) and with a `Nat`-arithmetic `Fin` bound (avoiding the `omega` leak). -/
theorem subst0_lamCellVarOne_eq_lamWeaken {scope : Nat} (argument : RawTerm scope) :
    RawTerm.subst0
        (lamCell (variableCell ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ scope)⟩)) argument
      = lamCell (RawTerm.weaken argument) := by
  show RawTerm.subst (RawTermSubst.singleton argument)
      (lamCell (.mkGen .gen_var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ scope)⟩ .childNil))
      = lamCell (RawTerm.weaken argument)
  rw [subst_lamCell]
  refine congrArg lamCell ?_
  rw [RawTerm.subst_var_reduces]
  show RawTerm.weaken (RawTermSubst.singleton argument ⟨0, Nat.zero_lt_succ scope⟩)
      = RawTerm.weaken argument
  rw [RawTermSubst.singleton_var_zero]

/-- **The K combinator `λx.λy.x : A → (B → A)` is a reducible member** (for variable types A, B).  The hardest
concrete simply-typed term: the inner body captures the OUTER bound variable `x`, so the outer abstraction's
body substitution crosses the inner binder (`subst0_lamCellVarOne_eq_lamWeaken`: `subst0 (λy.var 1) arg = λy.
weaken arg`).  The resulting constant function `λy.(weaken arg)` is a reducible member of `B → A` by
`lambdaNeutralArrow` (its body cancels under substitution to `arg`, which is strongly normalizing).  Exercises
the variable-capture-avoiding substitution under nested binders end-to-end. -/
theorem IsReducibleMemberAt.kCombinator {scope : Nat} {level : Nat}
    {domainIndex codomainIndex : Fin scope} :
    IsReducibleMemberAt level
      (piTyCodeCell (variableCell domainIndex)
        (RawTerm.weaken (piTyCodeCell (variableCell codomainIndex)
          (RawTerm.weaken (variableCell domainIndex)))))
      (lamCell (lamCell (variableCell ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ scope)⟩))) := by
  have codomainReducibleType : IsReducibleTypeAt level
      (piTyCodeCell (variableCell codomainIndex) (RawTerm.weaken (variableCell domainIndex))) :=
    (IsSimplyTyped.arrow (IsSimplyTyped.ofNeutral (IsNeutral.var codomainIndex))
      (IsSimplyTyped.ofNeutral (IsNeutral.var domainIndex))).reducibleAndMemberExtension.1 level
  refine IsReducibleMemberAt.lambdaNeutralDomain (IsNeutral.var domainIndex) codomainReducibleType ?_
  intro argument argumentSN
  rw [subst0_lamCellVarOne_eq_lamWeaken argument]
  refine IsReducibleMemberAt.lambdaNeutralArrow (IsNeutral.var codomainIndex)
    (IsNeutral.var domainIndex) ?_
  intro innerArgument _innerArgumentSN
  rw [show RawTerm.subst0 (RawTerm.weaken argument) innerArgument = argument from
    RawTerm.weaken_subst_singleton argument innerArgument]
  exact argumentSN

/-- **Abstraction over a LEAF domain — the maximally-general form.**  `λ.body : A → B` is a reducible member
when the domain A is a leaf (weak-head-normal, neither Π- nor universe-rooted — covering DATA FORMERS such as
Σ-codes, not only neutrals) and the codomain B is any reducible type (candidate = its member-predicate, so the
body condition is "the body lands as a member of B").  Generalizes both `lambdaNeutralArrow` (neutral domain +
neutral codomain) and `lambdaNeutralDomain` (neutral domain + arbitrary codomain) by replacing `IsNeutral` with
the raw leaf conditions — matching the leaf class of `IsSimplyTyped.leaf` at the type level.  The leaf
conditions fire `ReducibleTypeStep.neutral` directly (giving the SN candidate), so the proof is identical to
the neutral case. -/
theorem IsReducibleMemberAt.lambdaLeafDomain {scope : Nat} {level : Nat}
    {domainCode codomainBase : RawTerm scope} {body : RawTerm (scope + 1)}
    (domainWeakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep domainCode reduct)
    (domainNotPiType : domainCode.rootGenerator ≠ Generator.gen_piTyCode)
    (domainNotUniverse : domainCode.rootGenerator ≠ Generator.gen_universeCode)
    (codomainReducibleType : IsReducibleTypeAt level codomainBase)
    (bodyMember : ∀ argument : RawTerm scope, IsStronglyNormalizing argument →
      IsReducibleMemberAt level codomainBase (RawTerm.subst0 body argument)) :
    IsReducibleMemberAt level
      (piTyCodeCell domainCode (RawTerm.weaken codomainBase)) (lamCell body) := by
  have domainReducible : ReducibleTypeAt level domainCode IsStronglyNormalizing := by
    cases level with
    | zero => exact ReducibleTypeStep.neutral domainWeakHeadNormal domainNotPiType domainNotUniverse
    | succ predLevel =>
        exact ReducibleTypeStep.neutral domainWeakHeadNormal domainNotPiType domainNotUniverse
  exact IsReducibleMemberAt.abstractionNonDependent domainReducible
    (fun _argument argumentSN => argumentSN)
    (IsReducibleTypeAt.reducibleMemberCandidate codomainReducibleType) bodyMember

/-- **The identity over a Σ-code base type: `λx.x : (Σ A. B) → (Σ A. B)` is a reducible member.**  A Σ-code is a
DATA FORMER — a leaf that is NOT neutral — so this inhabitant lies strictly outside what the neutral abstraction
rules (`lambdaNeutralArrow` / `polymorphicIdentity`) can express; it is reachable only via `lambdaLeafDomain`.
Witnesses that the term-formation reducibility rules cover data-former base types, the term-level companion to
the type-level `IsSimplyTyped` Σ-leaf treatment. -/
theorem IsReducibleMemberAt.sigmaIdentity {scope : Nat} {level : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)} :
    IsReducibleMemberAt level
      (piTyCodeCell (sigmaTyCodeCell domainCode codomainCode)
        (RawTerm.weaken (sigmaTyCodeCell domainCode codomainCode)))
      (lamCell (variableCell ⟨0, Nat.zero_lt_succ scope⟩)) := by
  have sigmaWeakHeadNormal :
      ∀ reduct : RawTerm scope, ¬ WeakHeadStep (sigmaTyCodeCell domainCode codomainCode) reduct :=
    fun _reduct => WeakHeadStep.not_from_sigmaTyCode
  have sigmaNotPiType :
      (sigmaTyCodeCell domainCode codomainCode).rootGenerator ≠ Generator.gen_piTyCode :=
    show Generator.gen_sigmaTyCode ≠ Generator.gen_piTyCode by decide
  have sigmaNotUniverse :
      (sigmaTyCodeCell domainCode codomainCode).rootGenerator ≠ Generator.gen_universeCode :=
    show Generator.gen_sigmaTyCode ≠ Generator.gen_universeCode by decide
  have codomainReducibleType : IsReducibleTypeAt level (sigmaTyCodeCell domainCode codomainCode) :=
    (IsSimplyTyped.leaf sigmaWeakHeadNormal sigmaNotPiType
      sigmaNotUniverse).reducibleAndMemberExtension.1 level
  refine IsReducibleMemberAt.lambdaLeafDomain sigmaWeakHeadNormal sigmaNotPiType sigmaNotUniverse
    codomainReducibleType ?_
  intro argument argumentSN
  rw [show RawTerm.subst0 (variableCell ⟨0, Nat.zero_lt_succ scope⟩) argument = argument from
    RawTerm.subst0_var_zero argument]
  exact (IsReducibleMemberAt.atNeutralClassifier sigmaWeakHeadNormal sigmaNotPiType
    sigmaNotUniverse).mpr argumentSN

end FX1Poly.Typed
