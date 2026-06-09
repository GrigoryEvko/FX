import FX1Poly.Typed.DenoteKeyedBoundedFundamentalMotive
import FX1Poly.Core.RawTermSubst0Commute
import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/DenoteKeyedBoundedPiElimArm
    — the bounded fundamental theorem's Π-ELIMINATION (application) member arm + FT arm (#753 toward SN-043)

The bound-carrying analogue of `DenoteKeyedApplicationMember.lean` + `DenoteKeyedFundamentalPiElim.lean` (the
elimination rule at the reducibility-member level): a bound-reducible member of `Π domainCode codomainCode`
applied to a bound-reducible member of `domainCode` is a bound-reducible member of the substituted dependent
codomain `subst0 codomainCode argumentTerm`.

## Why this needs a direct inversion port (not a bridge transfer)

Unlike the conv arm — whose `convTransfer` transfers in 3 lines via the forget bridge because it produces only a
FACT-ABOUT-CANDIDATES — the application member's OUTPUT carries a BOUNDED codomain derivation
(`ReducibleTypeAtBounded env bound (subst0 …) (codomainCandidate …)`), which the forget bridge (bounded → denote)
cannot recover.  So `ReducibleTypeStepBounded.candidatePiShape` is a DIRECT induction port of the denote
`candidatePiShape` (5 arms: `whnfExpand` iota-impossible, `neutral` absurd, `piType` extract, `universeCode` root
mismatch, `ofPointwiseIff` compose — the only change is the `universeCode` arm's extra `belowBound` binder).  This
is the same dichotomy the forget bridge established: derivation-PRODUCING lemmas need direct ports;
fact-producing ones transfer.  `ReducibleTypeAtBounded.deterministic` (shipped via the bridge) supplies the
argument-candidate alignment, so no second port is needed.

## The arm

`fundamentalPiElimAtBounded` is a direct composition of `applicationMemberUnderClosingSubstitutionBounded` with the
two sub-conclusions at the same closing substitution, environment, and uniform `bound` — the LOWEST-RISK recursive
arm (no level-bridge, no universe-membership extraction), exactly as `fundamentalPiElimAtDenote`.

## Zero-axiom verification

`candidatePiShape` is a 5-arm structural induction; `piTypeInversion` is `candidatePiShape rfl`;
`applicationMember` is `obtain` + inversion + `deterministic` + anonymous constructor; the substitution form
commutes via `RawTerm.subst0_subst_commute`; the FT arm is one composition.  No `funext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (checked: depends on no axioms).
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Π-code shape inversion for the bounded relation (direct induction port).**  A `gen_piTyCode`-rooted
bound-reducible type came through the `piType` arm; recovers the domain/codomain candidates as BOUNDED
sub-derivations plus the application-form `PointwiseIff`.  Five-arm induction on `ReducibleTypeStepBounded`,
verbatim from the denote `candidatePiShape` except the `universeCode` arm carries its `belowBound` binder
(unused: the root-mismatch closes it). -/
theorem ReducibleTypeStepBounded.candidatePiShape {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → (RawTerm scope → Prop) → Prop} {bound : Nat}
    {typeCode : RawTerm scope} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStepBounded env lowerAt bound typeCode candidate) :
    ∀ {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)},
      typeCode = (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) →
      ∃ (domainCandidate : RawTerm scope → Prop)
        (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
        ReducibleTypeStepBounded env lowerAt bound domainCode domainCandidate ∧
        (∀ argument : RawTerm scope, domainCandidate argument →
          ReducibleTypeStepBounded env lowerAt bound (RawTerm.subst0 codomainCode argument)
            (codomainCandidate argument)) ∧
        PointwiseIff candidate
          (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
            codomainCandidate argument
              (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))) := by
  induction reducible with
  | whnfExpand weakHeadStep0 _ _ =>
      intro _domainCode _codomainCode hType; subst hType
      cases weakHeadStep0 with | rootIota iotaStep => cases iotaStep
  | neutral _ notPiType _ _ =>
      intro _domainCode _codomainCode hType; subst hType; exact absurd rfl notPiType
  | piType codomainCandidate domainReducible codomainReducible _ _ =>
      intro _domainCode _codomainCode hType; cases hType
      exact ⟨_, codomainCandidate, domainReducible, codomainReducible, fun _term => Iff.rfl⟩
  | universeCode _ _ _ =>
      intro _domainCode _codomainCode hType
      have rootMismatch : Generator.gen_universeCode = Generator.gen_piTyCode :=
        congrArg RawTerm.rootGenerator hType
      exact absurd rootMismatch (by decide)
  | dataEmpty =>
      intro _domainCode _codomainCode hType
      have rootMismatch : Generator.gen_emptyCode = Generator.gen_piTyCode :=
        congrArg RawTerm.rootGenerator hType
      exact absurd rootMismatch (by decide)
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro _domainCode _codomainCode hType
      obtain ⟨domainCandidate, codomainCandidate, domainReducible, codomainReducible, pwi⟩ :=
        innerHypothesis hType
      exact ⟨domainCandidate, codomainCandidate, domainReducible, codomainReducible,
        fun term => (pointwiseIff term).symm.trans (pwi term)⟩

/-- **Π-code inversion (existential, bound-indexed).**  A `gen_piTyCode`-rooted bound-reducible type recovers the
domain/codomain candidates (as bound-reducible sub-derivations) and the application-form `PointwiseIff`.  The
bounded twin of `ReducibleTypeAtDenote.piTypeInversion`. -/
theorem ReducibleTypeAtBounded.piTypeInversion {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeAtBounded env bound
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) candidate) :
    ∃ (domainCandidate : RawTerm scope → Prop)
      (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
      ReducibleTypeAtBounded env bound domainCode domainCandidate ∧
      (∀ argument : RawTerm scope, domainCandidate argument →
        ReducibleTypeAtBounded env bound (RawTerm.subst0 codomainCode argument)
          (codomainCandidate argument)) ∧
      PointwiseIff candidate
        (fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
          codomainCandidate argument
            (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))) :=
  reducible.candidatePiShape rfl

/-- **The bounded Π-elimination (application) member arm.**  A bound-reducible member of `Π domainCode
codomainCode` applied to a bound-reducible member of `domainCode` is a bound-reducible member of
`subst0 codomainCode argumentTerm`.  Direct from the bounded `piType` candidate via `piTypeInversion` (recovering
the domain/codomain candidates and the application-form `PointwiseIff`) and `ReducibleTypeAtBounded.deterministic`
(aligning the argument's candidate with the domain candidate). -/
theorem applicationMemberAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {functionTerm argumentTerm : RawTerm scope}
    (functionMember : IsReducibleMemberAtBounded env bound
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) functionTerm)
    (argumentMember : IsReducibleMemberAtBounded env bound domainCode argumentTerm) :
    IsReducibleMemberAtBounded env bound (RawTerm.subst0 codomainCode argumentTerm)
      (.mkGen .gen_app () (.childCons functionTerm (.childCons argumentTerm .childNil))) := by
  obtain ⟨_piCandidate, piReducible, functionInPi⟩ := functionMember
  obtain ⟨domainCandidate, codomainCandidate, domainReducible, codomainReducible, piCandidateIff⟩ :=
    piReducible.piTypeInversion
  have functionApplies := (piCandidateIff functionTerm).mp functionInPi
  obtain ⟨argumentCandidate, argumentReducible, argumentInCandidate⟩ := argumentMember
  have argumentInDomain : domainCandidate argumentTerm :=
    (ReducibleTypeAtBounded.deterministic argumentReducible domainReducible argumentTerm).mp
      argumentInCandidate
  exact ⟨codomainCandidate argumentTerm, codomainReducible argumentTerm argumentInDomain,
    functionApplies argumentTerm argumentInDomain⟩

/-- **The bounded Π-elimination member arm under a closing substitution (the fundamental-theorem shape).**  The
`subst` distributes over the app and Π cells definitionally; the dependent result type commutes by
`RawTerm.subst0_subst_commute` into exactly the shape `applicationMemberAtBounded` produces. -/
theorem applicationMemberUnderClosingSubstitutionBounded {scope targetScope : Nat} (env : Nat → Nat)
    (bound : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {functionTerm argumentTerm : RawTerm scope} {substitution : RawTermSubst scope targetScope}
    (functionMember : IsReducibleMemberAtBounded env bound
      (RawTerm.subst substitution
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
      (RawTerm.subst substitution functionTerm))
    (argumentMember : IsReducibleMemberAtBounded env bound
      (RawTerm.subst substitution domainCode) (RawTerm.subst substitution argumentTerm)) :
    IsReducibleMemberAtBounded env bound
      (RawTerm.subst substitution (RawTerm.subst0 codomainCode argumentTerm))
      (RawTerm.subst substitution
        (.mkGen .gen_app () (.childCons functionTerm (.childCons argumentTerm .childNil)))) := by
  rw [RawTerm.subst0_subst_commute codomainCode argumentTerm substitution]
  exact applicationMemberAtBounded env bound functionMember argumentMember

/-- **The bounded `piElim` (application) fundamental-theorem arm.**  Given the fundamental-theorem conclusions of
the function (a member of `Π domainCode codomainCode`) and the argument (a member of `domainCode`), the
application `appCell functionTerm argument` satisfies the fundamental-theorem conclusion at the substituted
dependent codomain `subst0 codomainCode argument`.  A direct composition of
`applicationMemberUnderClosingSubstitutionBounded` with both sub-conclusions at the same closing substitution,
environment, and uniform `bound` — no level-bridge needed (the lowest-risk recursive arm). -/
theorem fundamentalPiElimAtBounded {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope)
    {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (functionConclusion :
      FundamentalConclusionAtBounded env bound context functionTerm
        (piTyCodeCell domainCode codomainCode))
    (argumentConclusion :
      FundamentalConclusionAtBounded env bound context argument domainCode) :
    FundamentalConclusionAtBounded env bound context (appCell functionTerm argument)
      (RawTerm.subst0 codomainCode argument) := by
  intro _targetScope substitution envReducible
  exact applicationMemberUnderClosingSubstitutionBounded env bound
    (functionConclusion substitution envReducible)
    (argumentConclusion substitution envReducible)

end FX1Poly.Typed
