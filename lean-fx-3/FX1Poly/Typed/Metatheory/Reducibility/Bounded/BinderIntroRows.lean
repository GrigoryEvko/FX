import FX1Poly.Typed.Metatheory.Reducibility.Bounded.SNNeutralIntroRows
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedAssemblyBridge

/-! # FX1Poly/Typed/BinderIntroRows
    — the graded-binder intro FT members (TYTAB-4 step 4, the intro side's Tier-3 binder family: lam)

The two graded binders of `introRuleOf` — `lam` (the dependent function abstraction, output a `piTyCodeCell`)
and `pathLam` (the affine path abstraction, output a `bridgeTypeCell`) — are the only introducers that bind a
variable in a child.  `lam` is the one whose OUTPUT type takes the dependent-arrow reducibility arm
(`piType` → `DependentArrowCandidate`), so its member witness is exactly the shipped binder-crux engine
`fundamentalPiIntroAtBoundedSucc` (DenoteKeyedBoundedAssemblyBridge): that engine already discharges the binder
threading (`abstractionMemberUnderClosingSubstitutionBounded`, the body IH composed through
`ReducibleEnvAtBounded.cons`), and its conclusion `FundamentalConclusionAtBoundedSucc … (lamCell domainCode body)
(piTyCodeCell domainCode codomainCode)` is definitionally the lam row's goal (`memberCell`/`outputType` reduce to
`lamCell`/`piTyCodeCell`).

So the lam row is a pure wiring: extract the three obligation IHs (domain formation @ `Type@(level0,flag)`,
codomain formation @ `Type@(level1,flag)` under the domain-extended context, body @ codomain under the same),
then feed `fundamentalPiIntroAtBoundedSucc` its three closing-substitution-quantified premises built from the two
universe-membership IHs (the A2 bridge `reducibleTypeAtBoundFromUniverseMemberBounded`, its `belowBound` read off
the universe code's reducibility via `universeCodeReducibleAtBounded_belowBound`; the domain's SN directly via
`stronglyNormalizing_of_memberAtBoundedSucc` on the universe membership) and the body obligation IH as
`bodyConclusion`.  This is the same premise assembly the grown-engine piIntro recursor arm performs
(`BoundedGrownFundamental`), restated over the union obligation table.

## Zero-axiom verification

`fundamentalPiIntroAtBoundedSucc` (the binder-crux member engine) + the A2 bridge
`reducibleTypeAtBoundFromUniverseMemberBounded` + the gate `universeCodeReducibleAtBounded_belowBound` +
`stronglyNormalizing_of_memberAtBoundedSucc` (member CR1) + `subst_universeCodeCell` (the closed universe code
is substitution-stable) + the propext-clean `List.Mem` obligation-witness constructors.  No induction, no
`funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The `gen_lam` intro FT member: `λ(x : A). body` is a bound-reducible member of `Π(x : A). B` given the
domain `A` and codomain `B` are formed (at their universe levels) and the body is a member of `B` under the
domain-extended context.  Output type `piTyCodeCell domainCode codomainCode` takes the dependent-arrow
reducibility arm, so the member witness is the shipped `fundamentalPiIntroAtBoundedSucc` binder engine, fed its
three closing-substitution premises from the two universe-membership obligation IHs and the body IH — the same
assembly the grown-engine piIntro arm performs, restated over the union obligation table. -/
theorem fundamentalLamIntroRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren lamIntroRule.argShifts scope}
    {params : RawTermChildren lamIntroRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ lamIntroRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (lamIntroRule.memberCell scope args)
      (lamIntroRule.outputType scope args params) := by
  match args, params with
  | .childCons domainCode (.childCons body .childNil), .childCons codomainCode .childNil =>
    have domainFundamental :
        FundamentalConclusionAtBoundedSucc env bound context domainCode
          (universeCodeCell level0 flag) :=
      premisesFundamental
        { scope := scope, context := context, subject := domainCode,
          classifier := universeCodeCell level0 flag }
        (List.Mem.head _)
    have codomainFundamental :
        FundamentalConclusionAtBoundedSucc env bound (context.cons domainCode) codomainCode
          (universeCodeCell level1 flag) :=
      premisesFundamental
        { scope := scope + 1, context := context.cons domainCode, subject := codomainCode,
          classifier := universeCodeCell level1 flag }
        (List.Mem.tail _ (List.Mem.head _))
    have bodyFundamental :
        FundamentalConclusionAtBoundedSucc env bound (context.cons domainCode) body codomainCode :=
      premisesFundamental
        { scope := scope + 1, context := context.cons domainCode, subject := body,
          classifier := codomainCode }
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    -- Type-ascribe the binder engine's conclusion so the folded `FundamentalConclusionAtBoundedSucc` head is
    -- preserved (no eager leading-implicit insertion); `exact` then closes the goal, whose `memberCell` /
    -- `outputType` applications reduce to `lamCell` / `piTyCodeCell` by match-iota.
    have lamMember :
        FundamentalConclusionAtBoundedSucc env bound context (lamCell domainCode body)
          (piTyCodeCell domainCode codomainCode) :=
      fundamentalPiIntroAtBoundedSucc env bound context
        (fun substitution envReducible => by
          -- domainReducibleAtBound: the A2 bridge over the domain universe-membership IH
          have domainUniverseMember := domainFundamental substitution envReducible
          rw [subst_universeCodeCell] at domainUniverseMember
          obtain ⟨candidate, candidateReducible, candidateMember⟩ := domainUniverseMember
          exact reducibleTypeAtBoundFromUniverseMemberBounded env bound
            ⟨candidate, candidateReducible, candidateMember⟩
            (universeCodeReducibleAtBounded_belowBound candidateReducible))
        (fun substitution envReducible => by
          -- domainCodeStronglyNormalizing: the domain code is SN as a reducible member of its universe
          have domainUniverseMember := domainFundamental substitution envReducible
          rw [subst_universeCodeCell] at domainUniverseMember
          exact stronglyNormalizing_of_memberAtBoundedSucc domainUniverseMember)
        (fun substitution envReducible argument argumentMember => by
          -- codomainReducibleAtBound: the A2 bridge over the codomain universe-membership IH, the closing
          -- substitution extended with the argument (the domain-extended context's reducible env)
          have codomainUniverseMember := codomainFundamental (RawTermSubst.cons argument substitution)
            (ReducibleEnvAtBounded.cons envReducible argumentMember)
          rw [subst_universeCodeCell] at codomainUniverseMember
          obtain ⟨candidate, candidateReducible, candidateMember⟩ := codomainUniverseMember
          exact reducibleTypeAtBoundFromUniverseMemberBounded env bound
            ⟨candidate, candidateReducible, candidateMember⟩
            (universeCodeReducibleAtBounded_belowBound candidateReducible))
        bodyFundamental
    -- Close into the closing-substitution form so the goal's `memberCell` / `outputType` reduce to
    -- `lamCell` / `piTyCodeCell` (match-iota), then `lamMember` applies directly (no leading-implicit
    -- insertion, since it is now applied to the introduced substitution).
    intro _targetScope substitution envReducible
    exact lamMember substitution envReducible

end FX1Poly.Typed
