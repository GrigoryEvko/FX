import FX1Poly.Core.StratifiedReducibleTypeReducibilityCandidate

/-! # Foundation/PolyCell/Core/StratifiedReducibleMember
    — semantic membership over the stratified (Tarski-universe) reducibility relation

The stratified port of `IsReducibleType` (`ReducibleTypeWellFormed`) and the membership engine
(`ReducibleMember`): the fundamental-theorem conclusion shape over `ReducibleTypeAt`, packaging the
candidate existentially.  Where the pure-SN `IsReducibleMember` walls the conv arm at type variables (the
environment supplies only SN, never a candidate), the level-indexed version's universe arm carries each
type variable's candidate AND SN witness — the whole point of the Tarski universe.

  * `IsReducibleTypeAt level T := ∃ cand, ReducibleTypeAt level T cand` — semantic well-formed type.
  * `IsReducibleMemberAt level T t := ∃ cand, ReducibleTypeAt level T cand ∧ cand t` — membership.

Ships the term-level rules the fundamental theorem's structural cases consume directly, lifted from the
shipped `ReducibleTypeAt.*` metatheory to the existentially-packaged form:

  * `ReducibleTypeStep/At.piTypeInversion` — a Π-rooted reducible type came through the `piType` arm (the
    `whnfExpand` head-step is impossible, the `neutral`/`universeCode` arms are root-refuted), recovering
    the domain/codomain candidates.
  * `IsReducibleMemberAt.application` (`piElim`) — `ReducibleTypeAt.deterministic` aligns the argument
    candidate with the Π domain, then the dependent-arrow membership fires.
  * `IsReducibleMemberAt.castAlongConv` (`conv`) — `ReducibleTypeAt.convTransfer` ports membership to a
    convertible reducible type.
  * `IsReducibleMemberAt.stronglyNormalizing` (CR1, at `predLevel + 1`) — every member SNs, via the CR
    bundle (`ReducibleTypeAt.isReducibilityCandidate`).
  * `IsReducibleMemberAt.isReducibleType` / `IsReducibleTypeAt.forwardStepStar` — the type-level bridges.

The `piIntro` (`abstraction`) rule is DEFERRED: it needs the stratified head-expansion closure
(`ReducibleTypeStep.headExpansionClosed`), a separate prerequisite brick.

## Zero-axiom verification

`piTypeInversion` is `cases` on the derivation (the impossible arms root-refuted, mirroring
`ReducibleType.piTypeInversion`); the rules destructure the existential and apply the shipped
`ReducibleTypeAt.*` lemma.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Semantic well-formed type (level-indexed).**  A code is a reducible type at `level` when it denotes
some candidate there.  The type-level analogue of `IsReducibleMemberAt`. -/
def IsReducibleTypeAt {scope : Nat} (level : Nat) (typeCode : RawTerm scope) : Prop :=
  ∃ candidate : RawTerm scope → Prop, ReducibleTypeAt level typeCode candidate

/-- **Semantic membership (level-indexed).**  `term` is a reducible member of `typeCode` at `level` when
the type denotes some candidate at that level containing the term.  The CONCLUSION shape of the
fundamental theorem over the stratified relation. -/
def IsReducibleMemberAt {scope : Nat} (level : Nat) (typeCode term : RawTerm scope) : Prop :=
  ∃ candidate : RawTerm scope → Prop, ReducibleTypeAt level typeCode candidate ∧ candidate term

/-- **Π-code inversion (parametric).**  A `gen_piTyCode`-rooted type reducible at the step-functor came
through the `piType` arm: `whnfExpand` cannot fire (a Π-code is weak-head normal), and the `neutral` /
`universeCode` arms are refuted by the root (`neutral`'s non-Π guard by `rfl`; `universeCode` auto-dropped
by the `gen_universeCode ≠ gen_piTyCode` subject mismatch).  Recovers the domain/codomain candidates, their
reducibility, and that the candidate is the dependent-arrow candidate pointwise. -/
theorem ReducibleTypeStep.piTypeInversion {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStep lowerReducible
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      candidate) :
    ∃ (domainCandidate : RawTerm scope → Prop)
      (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
      ReducibleTypeStep lowerReducible domainCode domainCandidate ∧
      (∀ argument : RawTerm scope, domainCandidate argument →
        ReducibleTypeStep lowerReducible (RawTerm.subst0 codomainCode argument)
          (codomainCandidate argument)) ∧
      PointwiseIff candidate (IsDependentArrowReducible domainCandidate codomainCandidate) :=
  reducible.candidatePiShape rfl

/-- **Π-code inversion (level-indexed).**  `ReducibleTypeStep.piTypeInversion` through the `Nat` recursion
of `ReducibleTypeAt` (both cases by defeq). -/
theorem ReducibleTypeAt.piTypeInversion {scope : Nat} {level : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAt level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      candidate) :
    ∃ (domainCandidate : RawTerm scope → Prop)
      (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
      ReducibleTypeAt level domainCode domainCandidate ∧
      (∀ argument : RawTerm scope, domainCandidate argument →
        ReducibleTypeAt level (RawTerm.subst0 codomainCode argument) (codomainCandidate argument)) ∧
      PointwiseIff candidate (IsDependentArrowReducible domainCandidate codomainCandidate) := by
  cases level with
  | zero => exact ReducibleTypeStep.piTypeInversion reducible
  | succ predLevel => exact ReducibleTypeStep.piTypeInversion reducible

/-- **An inhabited type is a reducible type.**  Forgetting the inhabitant — the bridge from
`IsReducibleMemberAt` down to `IsReducibleTypeAt`. -/
theorem IsReducibleMemberAt.isReducibleType {scope : Nat} {level : Nat}
    {typeCode term : RawTerm scope} (member : IsReducibleMemberAt level typeCode term) :
    IsReducibleTypeAt level typeCode :=
  let ⟨candidate, reducible, _membership⟩ := member
  ⟨candidate, reducible⟩

/-- **Reducible types are forward-closed under reduction.**  A reducible type stays reducible (at the same
candidate) along any multi-step reduction. -/
theorem IsReducibleTypeAt.forwardStepStar {scope : Nat} {level : Nat}
    {firstType finalType : RawTerm scope}
    (reducibleType : IsReducibleTypeAt level firstType) (reduction : StepStar firstType finalType) :
    IsReducibleTypeAt level finalType :=
  let ⟨candidate, reducible⟩ := reducibleType
  ⟨candidate, ReducibleTypeAt.forwardStepStar reducible reduction⟩

/-- **Semantic Π elimination (`piElim` / app).**  Applying a reducible member of a Π-type to a reducible
argument yields a reducible member of the instantiated codomain.  Inversion supplies the Π's
domain/codomain candidates; `ReducibleTypeAt.deterministic` aligns the argument's own candidate with the
domain candidate so the dependent-arrow membership fires. -/
theorem IsReducibleMemberAt.application {scope : Nat} {level : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {functionTerm argument : RawTerm scope}
    (functionMember : IsReducibleMemberAt level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      functionTerm)
    (argumentMember : IsReducibleMemberAt level domainCode argument) :
    IsReducibleMemberAt level (RawTerm.subst0 codomainCode argument)
      (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil))) := by
  obtain ⟨_piCandidate, piReducible, functionInPi⟩ := functionMember
  obtain ⟨_domainCandidate, codomainCandidate, domainReducible, codomainReducible,
    candidateEquivalence⟩ := piReducible.piTypeInversion
  obtain ⟨_argumentCandidate, argumentReducible, argumentInCandidate⟩ := argumentMember
  have argumentInDomain :=
    (ReducibleTypeAt.deterministic argumentReducible domainReducible argument).mp argumentInCandidate
  have functionArrow := (candidateEquivalence functionTerm).mp functionInPi
  exact ⟨codomainCandidate argument,
    codomainReducible argument argumentInDomain,
    functionArrow argument argumentInDomain⟩

/-- **Semantic conversion (`conv`).**  A reducible member transfers to any convertible type that is itself
reducible — the fundamental theorem's `conv` arm, now CLOSING at type variables (the universe arm supplies
the target candidate).  `ReducibleTypeAt.convTransfer` ports membership. -/
theorem IsReducibleMemberAt.castAlongConv {scope : Nat} {level : Nat}
    {typeLeft typeRight term : RawTerm scope}
    {candidateRight : RawTerm scope → Prop}
    (member : IsReducibleMemberAt level typeLeft term)
    (targetReducible : ReducibleTypeAt level typeRight candidateRight)
    (conv : Conv typeLeft typeRight) :
    IsReducibleMemberAt level typeRight term := by
  obtain ⟨_candidateLeft, reducibleLeft, membership⟩ := member
  exact ⟨candidateRight, targetReducible,
    ReducibleTypeAt.convTransfer reducibleLeft targetReducible conv membership⟩

/-- **Members are strongly normalizing (CR1).**  At `predLevel + 1` (where the candidate machinery's arrow
CR1 has a domain inhabitant and the universe candidate is a genuine CR) and at a non-empty scope, every
reducible member strongly normalizes — the candidate→SN direction the SN-for-closed corollary consumes. -/
theorem IsReducibleMemberAt.stronglyNormalizing {scope : Nat} {predLevel : Nat}
    {typeCode term : RawTerm (scope + 1)}
    (member : IsReducibleMemberAt (predLevel + 1) typeCode term) :
    IsStronglyNormalizing term := by
  obtain ⟨_candidate, reducible, membership⟩ := member
  exact reducible.isReducibilityCandidate.stronglyNormalizing membership

/-- **The canonical member-predicate is the type's own candidate.**  For a reducible type, the predicate
`IsReducibleMemberAt level typeCode` (`fun term => ∃ C, ReducibleTypeAt level typeCode C ∧ C term`) is
itself a candidate the type denotes: built from any existing candidate by the `ofPointwiseIff`
congruence-closure arm, with the pointwise equivalence supplied by `deterministic` (every candidate of
`typeCode` is pointwise-iff to the member-predicate — forward picks the given candidate, backward collapses
an arbitrary witness candidate onto it).

This is the choice-free ENGINE of the dependent fundamental theorem: the Π codomain can be fed the FIXED
function `fun argument => IsReducibleMemberAt level (subst0 codomainCode argument)` (no `∃ candidate`
extracted, hence no choice), and the `piType` premise `ReducibleTypeAt level (subst0 codomainCode argument)
(IsReducibleMemberAt level (subst0 codomainCode argument))` discharged per argument from mere EXISTENCE of a
candidate there via this lemma. -/
theorem ReducibleTypeAt.reducibleMemberCandidate {scope : Nat} {level : Nat}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAt level typeCode candidate) :
    ReducibleTypeAt level typeCode (IsReducibleMemberAt level typeCode) := by
  have pointwise : ∀ term : RawTerm scope,
      candidate term ↔ IsReducibleMemberAt level typeCode term := by
    intro term
    constructor
    · intro candidateTerm; exact ⟨candidate, reducible, candidateTerm⟩
    · intro member
      obtain ⟨_otherCandidate, otherReducible, otherMembership⟩ := member
      exact (ReducibleTypeAt.deterministic otherReducible reducible term).mp otherMembership
  cases level with
  | zero => exact ReducibleTypeStep.ofPointwiseIff reducible pointwise
  | succ predLevel => exact ReducibleTypeStep.ofPointwiseIff reducible pointwise

/-- **Existence of a candidate suffices for the canonical member-predicate.**  The `IsReducibleTypeAt`
(`∃ candidate, …`) repackaging of `reducibleMemberCandidate`: a semantically well-formed type denotes its
own member-predicate.  The form the dependent Π-formation arm consumes (it has existence, not a chosen
candidate). -/
theorem IsReducibleTypeAt.reducibleMemberCandidate {scope : Nat} {level : Nat}
    {typeCode : RawTerm scope} (reducibleType : IsReducibleTypeAt level typeCode) :
    ReducibleTypeAt level typeCode (IsReducibleMemberAt level typeCode) :=
  let ⟨_candidate, reducible⟩ := reducibleType
  reducible.reducibleMemberCandidate

end FX1Poly.Core
