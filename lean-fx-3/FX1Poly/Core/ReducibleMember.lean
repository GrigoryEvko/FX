import FX1Poly.Core.ReducibleTypeAbstraction
import FX1Poly.Core.ReducibleTypeHeadExpansion
import FX1Poly.Core.ReducibleTypeConvInvariance
import FX1Poly.Core.ReducibleTypeReducibilityCandidate
import FX1Poly.Core.ConvSubstRename
import FX1Poly.Core.CandidateInterpretationSubst
import FX1Poly.Core.CompoundSubstPreservation
import FX1Poly.Core.RawTermSubst0Commute

/-! # Foundation/PolyCell/Core/ReducibleMember
    — semantic membership: the fundamental theorem's conclusion shape + its Π/conv/SN rules

`ReducibleType typeCode candidate` is a RELATION ("the type denotes this candidate").  The fundamental
theorem concludes in the MEMBERSHIP form — "the term lies in its type's candidate" — which packages the
candidate existentially:

  `IsReducibleMember typeCode term := ∃ candidate, ReducibleType typeCode candidate ∧ candidate term`.

This is exactly `HasType Γ t T → IsReducibleMember (T.subst γ) (t.subst γ)` under a reducible closing
substitution `γ` (the #425 environment, built next).  This file ships the term-level reasoning the
fundamental theorem's structural cases consume DIRECTLY, lifted from the candidate-level lemmas to the
existentially-packaged membership form:

  * **`ReducibleType.piTypeInversion`** — a `gen_piTyCode`-rooted type is reducible ONLY through the
    `piType` arm (it is weak-head normal, so `whnfExpand` is impossible; its root IS `gen_piTyCode`, so
    `neutral` is impossible).  Recovers the domain/codomain candidates with their reducibility witnesses.
  * **`IsReducibleMember.application`** (`piElim`) — a member of a Π-type applied to a reducible
    argument is a member of the instantiated codomain.  The candidate alignment between the argument's
    own candidate and the Π's domain candidate is bridged by `ReducibleType.deterministic`.
  * **`IsReducibleMember.abstraction`** (`piIntro`) — `lam body` is a member of the Π-type when every
    reducible argument sends the body's instance into the codomain candidate; the β-redex head-expansion
    is discharged by `DependentArrowCandidate.abstraction` (codomain closure from
    `ReducibleType.headExpansionClosed`, domain SN supplied at the call site).
  * **`IsReducibleMember.castAlongConv`** (`conv`) — membership transfers to any convertible type that
    is itself reducible, via `ReducibleType.convTransfer`.
  * **`IsReducibleMember.stronglyNormalizing`** (CR1) — at a non-empty scope (where the arrow CR1 has a
    domain inhabitant, §`ReducibleType.isReducibilityCandidate`), every member strongly normalizes.  This
    is the candidate→SN direction the SN-for-closed corollary (#426) consumes.

## Zero-axiom verification

`piTypeInversion` delegates to `ReducibleType.candidatePiShape` (the generic-index Π-shape inversion that
inducts on the derivation and absorbs the `ofPointwiseIff` congruence arm), re-exposing it at the concrete
`gen_piTyCode` index; the four rules destructure the existential and apply the shipped candidate-level
lemma.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per
declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Semantic membership.**  `term` is a reducible member of the type `typeCode` when the type denotes
some reducibility candidate containing the term.  This is the CONCLUSION shape of the fundamental
theorem (`HasType Γ t T → IsReducibleMember (T.subst γ) (t.subst γ)` under a reducible environment). -/
def IsReducibleMember {scope : Nat} (typeCode term : RawTerm scope) : Prop :=
  ∃ candidate : RawTerm scope → Prop, ReducibleType typeCode candidate ∧ candidate term

/-- **Π-code inversion.**  A `gen_piTyCode`-rooted reducible type's candidate is pointwise the
dependent-arrow candidate: inverting recovers the domain candidate, the codomain candidate family, their
reducibility witnesses, and the pointwise equivalence.  A Π-code is weak-head normal with root
`gen_piTyCode`, so the only derivations are `piType` (which reads the data off directly) and
`ofPointwiseIff` (which composes a stored equivalence) — both handled by `candidatePiShape`. -/
theorem ReducibleType.piTypeInversion {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {candidate : RawTerm scope → Prop}
    (reducible : ReducibleType
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      candidate) :
    ∃ (domainCandidate : RawTerm scope → Prop)
      (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
      ReducibleType domainCode domainCandidate ∧
      (∀ argument : RawTerm scope, domainCandidate argument →
        ReducibleType (RawTerm.subst0 codomainCode argument) (codomainCandidate argument)) ∧
      PointwiseIff candidate (DependentArrowCandidate domainCandidate codomainCandidate) := by
  obtain ⟨domainCandidate, codomainCandidate, domainReducible, codomainReducible,
    candidateEquivalence⟩ := reducible.candidatePiShape rfl
  exact ⟨domainCandidate, codomainCandidate, domainReducible, codomainReducible,
    candidateEquivalence⟩

/-- **Semantic Π elimination (`piElim` / app).**  Applying a reducible member of a Π-type to a reducible
argument yields a reducible member of the instantiated codomain.  Inversion supplies the Π's domain and
codomain candidates; `ReducibleType.deterministic` aligns the argument's own candidate with the Π's
domain candidate so the dependent-arrow membership fires at the argument. -/
theorem IsReducibleMember.application {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {functionTerm argument : RawTerm scope}
    (functionMember : IsReducibleMember
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      functionTerm)
    (argumentMember : IsReducibleMember domainCode argument) :
    IsReducibleMember (RawTerm.subst0 codomainCode argument)
      (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))) := by
  obtain ⟨_piCandidate, piReducible, functionInPi⟩ := functionMember
  obtain ⟨_domainCandidate, codomainCandidate, domainReducible, codomainReducible,
    candidateEquivalence⟩ := piReducible.piTypeInversion
  obtain ⟨_argumentCandidate, argumentReducible, argumentInCandidate⟩ := argumentMember
  have argumentInDomain :=
    (ReducibleType.deterministic argumentReducible domainReducible argument).mp argumentInCandidate
  have functionArrow := (candidateEquivalence functionTerm).mp functionInPi
  exact ⟨codomainCandidate argument,
    codomainReducible argument argumentInDomain,
    functionArrow argument argumentInDomain⟩

/-- **Semantic Π introduction (`piIntro` / λ).**  `lam body` is a reducible member of the Π-type when,
for every reducible argument, the body's substitution instance lies in that argument's codomain
candidate.  The codomain candidate family and its reducibility are supplied as data (the fundamental
theorem's body induction hypothesis provides them); the domain arguments' strong normalization comes
from the domain candidate's CR1 at the call site.  The β-redex `app (lam body) argument` head-expands to
`subst0 body argument`, discharged by `DependentArrowCandidate.abstraction` threading
`ReducibleType.headExpansionClosed`. -/
theorem IsReducibleMember.abstraction {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainCandidate : RawTerm scope → Prop}
    {codomainCandidate : RawTerm scope → (RawTerm scope → Prop)}
    (domainReducible : ReducibleType domainCode domainCandidate)
    (domainArgumentsSN : ∀ argument : RawTerm scope, domainCandidate argument →
      IsStronglyNormalizing argument)
    (codomainReducible : ∀ argument : RawTerm scope, domainCandidate argument →
      ReducibleType (RawTerm.subst0 codomainCode argument) (codomainCandidate argument))
    (bodyReducible : ∀ argument : RawTerm scope, domainCandidate argument →
      codomainCandidate argument (RawTerm.subst0 body argument)) :
    IsReducibleMember
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      (.mkGen .gen_lam () (.childCons body .childNil)) :=
  ⟨DependentArrowCandidate domainCandidate codomainCandidate,
   ReducibleType.piType codomainCandidate domainReducible codomainReducible,
   DependentArrowCandidate.abstraction domainArgumentsSN
     (fun argument argumentInDomain => (codomainReducible argument argumentInDomain).headExpansionClosed)
     bodyReducible⟩

/-- **Semantic conversion (`conv`).**  A reducible member transfers to any convertible type that is
itself reducible — the fundamental theorem's `conv` arm.  `ReducibleType.convTransfer` ports membership
from the source candidate to the (independently supplied) target candidate. -/
theorem IsReducibleMember.castAlongConv {scope : Nat}
    {typeLeft typeRight term : RawTerm scope}
    {candidateRight : RawTerm scope → Prop}
    (member : IsReducibleMember typeLeft term)
    (targetReducible : ReducibleType typeRight candidateRight)
    (conv : Conv typeLeft typeRight) :
    IsReducibleMember typeRight term := by
  obtain ⟨_candidateLeft, reducibleLeft, membership⟩ := member
  exact ⟨candidateRight, targetReducible,
    ReducibleType.convTransfer reducibleLeft targetReducible conv membership⟩

/-- **Members are strongly normalizing (CR1).**  At a non-empty scope — where the candidate machinery's
arrow CR1 has a uniform domain inhabitant (variable 0, via `ReducibleType.isReducibilityCandidate`) —
every reducible member of a type strongly normalizes.  This is the candidate→SN direction the
SN-for-closed corollary consumes (the closed apex is reached by weakening to `scope + 1`). -/
theorem IsReducibleMember.stronglyNormalizing {scope : Nat}
    {typeCode term : RawTerm (scope + 1)} (member : IsReducibleMember typeCode term) :
    IsStronglyNormalizing term := by
  obtain ⟨_candidate, reducible, membership⟩ := member
  exact reducible.isReducibilityCandidate.stronglyNormalizing membership

/-- **Semantic conversion under a closing substitution (the fundamental theorem's `conv` arm).**  The
under-substitution form `IsReducibleMember.castAlongConv` consumes at the fundamental-theorem induction
site: a closing `substitution` sends `subject` to a reducible member of the closed `typeLeft` (the
subject's induction hypothesis) and the closed `typeRight` is itself reducible (the reclassifier's
type-formation induction hypothesis); since `typeLeft` and `typeRight` are convertible, the SUBSTITUTED
conversion `Conv.subst substitution conv` transports membership to the closed `typeRight`.  The level-free
counterpart of the stratified `IsReducibleMemberAt.castAlongConvUnderSubst` — and the arm the choice-free
`InterpretsType` interpretation cannot supply (it is not forward-closed; conversion-invariance lives on the
weak-head-normal `ReducibleType` relation underlying `IsReducibleMember`). -/
theorem IsReducibleMember.castAlongConvUnderSubst {scope targetScope : Nat}
    {typeLeft typeRight subject : RawTerm scope}
    {candidateRight : RawTerm targetScope → Prop}
    (substitution : RawTermSubst scope targetScope)
    (subjectMember : IsReducibleMember
      (RawTerm.subst substitution typeLeft) (RawTerm.subst substitution subject))
    (targetReducible : ReducibleType (RawTerm.subst substitution typeRight) candidateRight)
    (conv : Conv typeLeft typeRight) :
    IsReducibleMember
      (RawTerm.subst substitution typeRight) (RawTerm.subst substitution subject) :=
  IsReducibleMember.castAlongConv subjectMember targetReducible (Conv.subst substitution conv)

/-- **Semantic Π elimination under a closing substitution (the fundamental theorem's `piElim` arm).**  The
under-substitution form `IsReducibleMember.application` consumes at the induction site: a closing
`substitution` sends the function to a member of the closed Π-type and the argument to a member of the
closed domain (the function's and argument's induction hypotheses), so the closed application is a member
of the closed instantiated codomain.  The substitution distributes over the Π cell (`subst_piTyCode`,
`rfl` — domain by the substitution, codomain by the lift), over the application cell (`subst_app_reduces`,
`rfl`), and the dependent output classifier `subst γ (subst0 codomainCode argument)` re-expresses as
`subst0 (subst (lift γ) codomainCode) (subst γ argument)` by the β-commutation `subst0_subst_commute` —
exactly the shape `IsReducibleMember.application` produces.  The level-free counterpart of the stratified
`IsReducibleMemberAt.applicationUnderSubst`; CHOICE-FREE (the argument's candidate aligns with the Π domain
by `ReducibleType.deterministic` inside `application`, no uniform codomain candidate needed — the piElim arm
does not hit the piIntro choice obstruction). -/
theorem IsReducibleMember.applicationUnderSubst {scope targetScope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {functionTerm argument : RawTerm scope}
    (substitution : RawTermSubst scope targetScope)
    (functionReducible : IsReducibleMember
      (RawTerm.subst substitution
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
      (RawTerm.subst substitution functionTerm))
    (argumentReducible : IsReducibleMember
      (RawTerm.subst substitution domainCode) (RawTerm.subst substitution argument)) :
    IsReducibleMember
      (RawTerm.subst substitution (RawTerm.subst0 codomainCode argument))
      (RawTerm.subst substitution
        (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))) := by
  rw [RawTerm.subst_piTyCode] at functionReducible
  rw [RawTerm.subst_app_reduces, RawTerm.subst0_subst_commute]
  exact IsReducibleMember.application functionReducible argumentReducible

end FX1Poly.Core
