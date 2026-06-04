import FX1Poly.Typed.DenoteKeyedBoundedPiElimArm
import FX1Poly.Typed.DenoteKeyedHeadExpansion
import FX1Poly.Core.ReducibleTypeAbstraction
import FX1Poly.Core.RawTermSubstConsCommute

/-! # FX1Poly/Typed/DenoteKeyedBoundedPiIntroArm
    — the bounded fundamental theorem's Π-INTRODUCTION (λ) member arm + FT arm — THE BINDER CRUX (#753 → SN-043)

The bound-carrying analogue of `DenoteKeyedCanonicalMemberCandidate` + `DenoteKeyedHeadExpansion` (SN-D1) +
`DenoteKeyedAbstractionMember` (SN-D2) + `DenoteKeyedAbstractionUnderSubst` (SN-D3) +
`DenoteKeyedFundamentalPiIntro` (SN-D5c), assembled in one file: `λ body` is a bound-reducible member of
`Π domainCode codomainCode`, the classical hard Tait case.

## The forget-bridge economy at the binder crux

The headline: `ReducibleTypeAtBounded.headExpansionClosed` is a FORGET-BRIDGE TRANSFER.  `HeadExpansionClosed
candidate` is a FACT about the candidate (not a bounded derivation), and `ReducibleTypeStepDenote.headExpansionClosed`
is parametric on `lowerAt`, so a bounded derivation forgets to denote (at `lowerAt = denoteBelowFamilyBounded env
bound`) and the denote closure applies — supplied the bounded `lowerHeadExpand` leg
(`denoteBelowFamilyBounded_backwardWeakHeadStep`, the verbatim by-cases port: coherence + `whnfExpand` below the
bound, vacuous above).  So even the binder crux's deepest piece (SN-D1) is a ~5-line bridge transfer.

The rest are verbatim ports:
  * `reducibleMemberCandidate` (the choice-free canonical member predicate, #490) — `ofPointwiseIff` +
    `ReducibleTypeAtBounded.deterministic` (both shipped); this is what makes the binder env-cons coordination
    direct (the domain candidate IS `IsReducibleMemberAtBounded …`, exactly `ReducibleEnvAtBounded.cons`'s premise).
  * `abstractionMemberAtBounded` (SN-D2) — the `piType` constructor's candidate is defeq to
    `DependentArrowCandidate` (relation-agnostic Core), and `DependentArrowCandidate.abstraction` consumes the
    head-expansion closure; one anonymous constructor.
  * `abstractionMemberUnderClosingSubstitutionBounded` (SN-D3) — `subst` distributes over Π/λ definitionally; the
    IH-shaped premises bridge via `RawTerm.subst_cons_eq_subst0_lift`.
  * `fundamentalPiIntroAtBounded` (SN-D5c) — pins both candidates to the canonical member predicate, threads the
    binder environment via `ReducibleEnvAtBounded.cons`; premise-isolating (the A2-bridge reducibilities + CR1 SN
    are caller premises the FT assembly supplies).

## Zero-axiom verification

`headExpansionClosed` is the bridge composition; the rest are `ofPointwiseIff`/`deterministic`, the anonymous
`piType`+`DependentArrowCandidate.abstraction` constructor, definitional Π/λ distribution + substitution-pointwise
rewrites, and `ReducibleEnvAtBounded.cons` threading.  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega` (checked: depends on no axioms).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **The canonical member-predicate is the type's own candidate (bound-carrying, #490 analogue).**  For a
bound-reducible type, `IsReducibleMemberAtBounded env bound typeCode` is itself a candidate the type denotes —
built from any existing candidate by the `ofPointwiseIff` congruence arm, the pointwise equivalence from
`ReducibleTypeAtBounded.deterministic` (forward picks the given candidate; backward collapses an arbitrary witness
candidate onto it).  The choice-free engine the bounded piIntro arm threads through the binder. -/
theorem ReducibleTypeAtBounded.reducibleMemberCandidate {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAtBounded env bound typeCode candidate) :
    ReducibleTypeAtBounded env bound typeCode (IsReducibleMemberAtBounded env bound typeCode) := by
  refine ReducibleTypeStepBounded.ofPointwiseIff reducible (fun term => ?_)
  constructor
  · intro candidateTerm
    exact ⟨candidate, reducible, candidateTerm⟩
  · intro member
    obtain ⟨otherCandidate, otherReducible, otherMembership⟩ := member
    exact (ReducibleTypeAtBounded.deterministic otherReducible reducible term).mp otherMembership

/-- **Existence of a candidate suffices for the canonical member-predicate (bound-carrying).**  The
`IsReducibleTypeAtBounded` (`∃ candidate, …`) repackaging — the form the piIntro arm consumes (it has existence,
not a chosen candidate). -/
theorem IsReducibleTypeAtBounded.reducibleMemberCandidate {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {typeCode : RawTerm scope} (reducibleType : IsReducibleTypeAtBounded env bound typeCode) :
    ReducibleTypeAtBounded env bound typeCode (IsReducibleMemberAtBounded env bound typeCode) :=
  let ⟨_candidate, reducible⟩ := reducibleType
  reducible.reducibleMemberCandidate

/-- **Backward weak-head step for the bounded below-family.**  Verbatim by-cases port of
`denoteBelowFamily_backwardWeakHeadStep`: below the bound (coherence `denoteBelowFamilyBounded_eq_reducible` +
`whnfExpand`), at/above the bound the membership is vacuous (`denoteBelowFamilyBounded_eq_empty_of_ge`).  The
`lowerHeadExpand` leg the bounded head-expansion closure feeds to the parametric denote engine. -/
theorem denoteBelowFamilyBounded_backwardWeakHeadStep {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (lvl : Nat) {typeCode reduct : RawTerm scope} {candidate : RawTerm scope → Prop}
    (member : denoteBelowFamilyBounded env bound lvl reduct candidate)
    (weakHeadStep : WeakHeadStep typeCode reduct) :
    denoteBelowFamilyBounded env bound lvl typeCode candidate := by
  by_cases hlt : lvl < bound
  · rw [denoteBelowFamilyBounded_eq_reducible env bound lvl hlt] at member ⊢
    exact ReducibleTypeStepBounded.whnfExpand weakHeadStep member
  · rw [denoteBelowFamilyBounded_eq_empty_of_ge env bound lvl (Nat.not_lt.mp hlt)] at member
    exact member.elim

/-- **Every bound-reducible candidate is head-expansion-closed (via the forget bridge).**  `HeadExpansionClosed
candidate` is a FACT about the candidate, and `ReducibleTypeStepDenote.headExpansionClosed` is `lowerAt`-parametric,
so the bounded derivation forgets to denote (at `lowerAt = denoteBelowFamilyBounded env bound`) and the denote
closure applies with the bounded leg `denoteBelowFamilyBounded_backwardWeakHeadStep` on `WeakHeadStep.betaSpine`.
The bounded SN-D1; the codomain head-expansion closure `DependentArrowCandidate.abstraction` needs. -/
theorem ReducibleTypeAtBounded.headExpansionClosed {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAtBounded env bound typeCode candidate) :
    HeadExpansionClosed candidate := by
  refine ReducibleTypeStepDenote.headExpansionClosed ?leg reducible.toReducibleTypeStepDenote
  intro lvl _body _argument _spine _lowerCandidate contractumMember
  exact denoteBelowFamilyBounded_backwardWeakHeadStep env bound lvl contractumMember WeakHeadStep.betaSpine

/-- **The bounded Π-introduction (λ) member arm (the bounded SN-D2 — the classical hard Tait case).**  `λ body`
is a bound-reducible member of `Π domainCode codomainCode`, given the domain reducible with `domainCandidate`, the
substituted codomain reducible per reducible argument, the domain candidate's members SN (CR1, explicit premise),
and each body instance in the codomain candidate (the body IH).  The Π type is reducible with the dependent-arrow
candidate via `ReducibleTypeStepBounded.piType` (its candidate defeq to `DependentArrowCandidate`); membership of
`λ body` is `DependentArrowCandidate.abstraction`, its codomain head-expansion-closure premise the bounded
`headExpansionClosed`. -/
theorem abstractionMemberAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainCandidate : RawTerm scope → Prop}
    {codomainCandidate : RawTerm scope → (RawTerm scope → Prop)}
    {body : RawTerm (scope + 1)}
    (domainReducible : ReducibleTypeAtBounded env bound domainCode domainCandidate)
    (codomainReducible : ∀ argument : RawTerm scope, domainCandidate argument →
        ReducibleTypeAtBounded env bound (RawTerm.subst0 codomainCode argument)
          (codomainCandidate argument))
    (domainArgumentsSN : ∀ argument : RawTerm scope, domainCandidate argument →
        IsStronglyNormalizing argument)
    (bodyReducible : ∀ argument : RawTerm scope, domainCandidate argument →
        codomainCandidate argument (RawTerm.subst0 body argument)) :
    IsReducibleMemberAtBounded env bound
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      (.mkGen .gen_lam () (.childCons body .childNil)) :=
  ⟨DependentArrowCandidate domainCandidate codomainCandidate,
    ReducibleTypeStepBounded.piType codomainCandidate domainReducible codomainReducible,
    DependentArrowCandidate.abstraction domainArgumentsSN
      (fun argument argumentReducible =>
        (codomainReducible argument argumentReducible).headExpansionClosed)
      bodyReducible⟩

/-- **The bounded Π-introduction member arm under a closing substitution (the bounded SN-D3).**  `subst`
distributes over Π/λ definitionally; the two IH-shaped premises bridge to `abstractionMemberAtBounded`'s
`subst0 … (lift σ)` shape via `RawTerm.subst_cons_eq_subst0_lift`. -/
theorem abstractionMemberUnderClosingSubstitutionBounded {scope targetScope : Nat} (env : Nat → Nat)
    (bound : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {body : RawTerm (scope + 1)} {substitution : RawTermSubst scope targetScope}
    {domainCandidate : RawTerm targetScope → Prop}
    {codomainCandidate : RawTerm targetScope → (RawTerm targetScope → Prop)}
    (domainReducible :
      ReducibleTypeAtBounded env bound (RawTerm.subst substitution domainCode) domainCandidate)
    (codomainReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      ReducibleTypeAtBounded env bound
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode)
        (codomainCandidate argument))
    (domainArgumentsSN : ∀ argument : RawTerm targetScope, domainCandidate argument →
      IsStronglyNormalizing argument)
    (bodyReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      codomainCandidate argument
        (RawTerm.subst (RawTermSubst.cons argument substitution) body)) :
    IsReducibleMemberAtBounded env bound
      (RawTerm.subst substitution
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
      (RawTerm.subst substitution
        (.mkGen .gen_lam () (.childCons body .childNil))) := by
  show IsReducibleMemberAtBounded env bound
    (.mkGen .gen_piTyCode ()
      (.childCons (RawTerm.subst substitution domainCode)
        (.childCons (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) .childNil)))
    (.mkGen .gen_lam ()
      (.childCons (RawTerm.subst (RawTermSubst.lift substitution) body) .childNil))
  refine abstractionMemberAtBounded (codomainCandidate := codomainCandidate) env bound domainReducible
    (fun argument argumentInDomain => ?_) domainArgumentsSN
    (fun argument argumentInDomain => ?_)
  · rw [← RawTerm.subst_cons_eq_subst0_lift codomainCode argument substitution]
    exact codomainReducible argument argumentInDomain
  · rw [← RawTerm.subst_cons_eq_subst0_lift body argument substitution]
    exact bodyReducible argument argumentInDomain

/-- **The bounded `piIntro` (λ) fundamental-theorem arm — the binder crux (bounded SN-D5c).**  Pins both the domain
and per-argument codomain candidates to the canonical member predicate (`reducibleMemberCandidate`), making the
binder environment threading (`ReducibleEnvAtBounded.cons`) and the body membership both DIRECT; the assembly is
`abstractionMemberUnderClosingSubstitutionBounded`.  Premise-isolating: the domain/codomain reducibilities at the
ambient bound and the domain CR1 SN are caller premises (the FT assembly supplies them from the A2-bridge IHs);
the body conclusion is the direct body IH under the `cons`-extended environment. -/
theorem fundamentalPiIntroAtBounded {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope)
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    (domainReducibleAtBound : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        IsReducibleTypeAtBounded env bound (RawTerm.subst substitution domainCode))
    (domainArgumentsSN : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ argument : RawTerm targetScope,
          IsReducibleMemberAtBounded env bound (RawTerm.subst substitution domainCode) argument →
          IsStronglyNormalizing argument)
    (codomainReducibleAtBound : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ argument : RawTerm targetScope,
          IsReducibleMemberAtBounded env bound (RawTerm.subst substitution domainCode) argument →
          IsReducibleTypeAtBounded env bound
            (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    (bodyConclusion :
        FundamentalConclusionAtBounded env bound (context.cons domainCode) body codomainCode) :
    FundamentalConclusionAtBounded env bound context (lamCell body)
      (piTyCodeCell domainCode codomainCode) := by
  intro _targetScope substitution envReducible
  exact abstractionMemberUnderClosingSubstitutionBounded
    (domainCandidate := IsReducibleMemberAtBounded env bound (RawTerm.subst substitution domainCode))
    (codomainCandidate := fun argument =>
      IsReducibleMemberAtBounded env bound
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode))
    env bound
    (domainReducibleAtBound substitution envReducible).reducibleMemberCandidate
    (fun argument argumentMember =>
      (codomainReducibleAtBound substitution envReducible argument argumentMember).reducibleMemberCandidate)
    (domainArgumentsSN substitution envReducible)
    (fun argument argumentMember =>
      bodyConclusion (RawTermSubst.cons argument substitution)
        (ReducibleEnvAtBounded.cons envReducible argumentMember))

end FX1Poly.Typed
