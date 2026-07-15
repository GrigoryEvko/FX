import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedPiElimArm
import FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleTypeAbstraction
import FX1Poly.Axis.Term.Subst.RawTermSubstConsCommute

/-! # FX1Poly/Typed/DenoteKeyedBoundedPiIntroArm
    — the bounded fundamental theorem's Π-INTRODUCTION (λ) member arm + FT arm — THE BINDER CRUX (#753 → SN-043)

The bound-carrying analogue of `DenoteKeyedCanonicalMemberCandidate` + `DenoteKeyedHeadExpansion` (SN-D1) +
`DenoteKeyedAbstractionMember` (SN-D2) + `DenoteKeyedAbstractionUnderSubst` (SN-D3) +
`DenoteKeyedFundamentalPiIntro` (SN-D5c), assembled in one file: `λ body` is a bound-reducible member of
`Π domainCode codomainCode`, the classical hard Tait case.

## Head-expansion is a CALLER-SUPPLIED premise (bounded-native, the Sigma-projection model swap)

The binder arm's deepest piece (SN-D1, the codomain head-expansion closure `DependentArrowCandidate.abstraction`
needs) is now a PARAMETRIC PREMISE on `abstractionMemberAtBounded` / `abstractionMemberUnderClosingSubstitutionBounded`
(`codomainHeadExpansionClosed`), supplied by the +1-closing caller (`fundamentalPiIntroAtBoundedSucc`) from the
BOUNDED-NATIVE `ReducibleTypeAtBounded.headExpansionClosed` (`BoundedMemberWeakHeadExpansion`).  The bounded-native
proof is the one that WORKS for the projection-based Sigma candidate `projectionPairCandidate` (whose head-expansion
needs the two component carriers' member-weak-head-expansion, available only at the bounded family at `scope + 1`,
where the universe gate makes CR1/MWHE unconditional) — the pure-denote head-expansion fails there because denote
neutral-inclusion is vacuous above the bound.  Threading head-expansion as a premise keeps these abstraction lemmas
scope-generic; only the +1-closing caller, where the bounded-native head-expansion applies, supplies it.

The supporting leg `denoteBelowFamilyBounded_backwardWeakHeadStep` (the verbatim by-cases port: coherence +
`whnfExpand` below the bound, vacuous above) stays here — it is the `lowerHeadExpand` leg the bounded-native
head-expansion downstream feeds to the parametric universe arm.

The rest are verbatim ports:
  * `reducibleMemberCandidate` (the choice-free canonical member predicate, #490) — `ofPointwiseIff` +
    `ReducibleTypeAtBounded.deterministic` (both shipped); this is what makes the binder env-cons coordination
    direct (the domain candidate IS `IsReducibleMemberAtBounded …`, exactly `ReducibleEnvAtBounded.cons`'s premise).
  * `abstractionMemberAtBounded` (SN-D2) — the `piType` constructor's candidate is defeq to
    `DependentArrowCandidate` (relation-agnostic Core), and `DependentArrowCandidate.abstraction` consumes the
    head-expansion closure supplied as the `codomainHeadExpansionClosed` premise; one anonymous constructor.
  * `abstractionMemberUnderClosingSubstitutionBounded` (SN-D3) — `subst` distributes over Π/λ definitionally; the
    IH-shaped premises bridge via `RawTerm.subst_cons_eq_subst0_lift` (the head-expansion premise threaded through
    unchanged).

## Zero-axiom verification

The abstraction lemmas are the anonymous `piType`+`DependentArrowCandidate.abstraction` constructor (head-expansion
arriving as a premise), `ofPointwiseIff`/`deterministic` for `reducibleMemberCandidate`, definitional Π/λ
distribution + substitution-pointwise rewrites, and `ReducibleEnvAtBounded.cons` threading.  No `funext`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (checked: depends on no axioms).
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax
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

/-- **The bounded Π-introduction (λ) member arm (the bounded SN-D2 — the classical hard Tait case).**  `λ body`
is a bound-reducible member of `Π domainCode codomainCode`, given the domain reducible with `domainCandidate`, the
substituted codomain reducible per reducible argument, the domain candidate's members SN (CR1, explicit premise),
each body instance in the codomain candidate (the body IH), and the codomain candidate head-expansion-closed per
reducible argument (the `codomainHeadExpansionClosed` premise — supplied by the +1-closing caller from the
bounded-native `ReducibleTypeAtBounded.headExpansionClosed`, the head-expansion that works for the
projection-based Sigma candidate).  The Π type is reducible with the dependent-arrow candidate via
`ReducibleTypeStepBounded.piType` (its candidate defeq to `DependentArrowCandidate`); membership of `λ body` is
`DependentArrowCandidate.abstraction`. -/
theorem abstractionMemberAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {domainAnn domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainCandidate : RawTerm scope → Prop}
    {codomainCandidate : RawTerm scope → (RawTerm scope → Prop)}
    {body : RawTerm (scope + 1)}
    (domainReducible : ReducibleTypeAtBounded env bound domainCode domainCandidate)
    (domainAnnSN : IsStronglyNormalizing domainAnn)
    (codomainReducible : ∀ argument : RawTerm scope, domainCandidate argument →
        ReducibleTypeAtBounded env bound (RawTerm.subst0 codomainCode argument)
          (codomainCandidate argument))
    (domainArgumentsSN : ∀ argument : RawTerm scope, domainCandidate argument →
        IsStronglyNormalizing argument)
    (codomainHeadExpansionClosed : ∀ argument : RawTerm scope, domainCandidate argument →
        HeadExpansionClosed (codomainCandidate argument))
    (bodyReducible : ∀ argument : RawTerm scope, domainCandidate argument →
        codomainCandidate argument (RawTerm.subst0 body argument)) :
    IsReducibleMemberAtBounded env bound
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil))) :=
  ⟨DependentArrowCandidate domainCandidate codomainCandidate,
    ReducibleTypeStepBounded.piType codomainCandidate domainReducible codomainReducible,
    DependentArrowCandidate.abstraction domainAnnSN domainArgumentsSN
      codomainHeadExpansionClosed
      bodyReducible⟩

/-- **The bounded Π-introduction member arm under a closing substitution (the bounded SN-D3).**  `subst`
distributes over Π/λ definitionally; the two IH-shaped premises bridge to `abstractionMemberAtBounded`'s
`subst0 … (lift σ)` shape via `RawTerm.subst_cons_eq_subst0_lift`.  The `codomainHeadExpansionClosed` premise
(the codomain head-expansion-closure per reducible argument) is threaded through unchanged to
`abstractionMemberAtBounded` — supplied by the +1-closing caller from the bounded-native head-expansion. -/
theorem abstractionMemberUnderClosingSubstitutionBounded {scope targetScope : Nat} (env : Nat → Nat)
    (bound : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {body : RawTerm (scope + 1)} {substitution : RawTermSubst scope targetScope}
    {domainCandidate : RawTerm targetScope → Prop}
    {codomainCandidate : RawTerm targetScope → (RawTerm targetScope → Prop)}
    (domainReducible :
      ReducibleTypeAtBounded env bound (RawTerm.subst substitution domainCode) domainCandidate)
    (domainAnnSN : IsStronglyNormalizing (RawTerm.subst substitution domainCode))
    (codomainReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      ReducibleTypeAtBounded env bound
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode)
        (codomainCandidate argument))
    (domainArgumentsSN : ∀ argument : RawTerm targetScope, domainCandidate argument →
      IsStronglyNormalizing argument)
    (codomainHeadExpansionClosed : ∀ argument : RawTerm targetScope, domainCandidate argument →
      HeadExpansionClosed (codomainCandidate argument))
    (bodyReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      codomainCandidate argument
        (RawTerm.subst (RawTermSubst.cons argument substitution) body)) :
    IsReducibleMemberAtBounded env bound
      (RawTerm.subst substitution
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
      (RawTerm.subst substitution
        (.mkGen .gen_lam () (.childCons domainCode (.childCons body .childNil)))) := by
  show IsReducibleMemberAtBounded env bound
    (.mkGen .gen_piTyCode ()
      (.childCons (RawTerm.subst substitution domainCode)
        (.childCons (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) .childNil)))
    (.mkGen .gen_lam ()
      (.childCons (RawTerm.subst substitution domainCode)
        (.childCons (RawTerm.subst (RawTermSubst.lift substitution) body) .childNil)))
  refine abstractionMemberAtBounded (codomainCandidate := codomainCandidate) env bound
    domainReducible domainAnnSN
    (fun argument argumentInDomain => ?_) domainArgumentsSN
    codomainHeadExpansionClosed
    (fun argument argumentInDomain => ?_)
  · rw [← RawTerm.subst_cons_eq_subst0_lift codomainCode argument substitution]
    exact codomainReducible argument argumentInDomain
  · rw [← RawTerm.subst_cons_eq_subst0_lift body argument substitution]
    exact bodyReducible argument argumentInDomain

end FX1Poly.Typed
