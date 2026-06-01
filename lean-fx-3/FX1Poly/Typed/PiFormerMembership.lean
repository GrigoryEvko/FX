import FX1Poly.Typed.ReducibleSemanticRules
import FX1Poly.Core.StrongNormalizationReflection

/-! # FX1Poly/Typed/PiFormerMembership
    — the Π-former universe-membership dispatch from its children's fundamental-theorem hypotheses

The fundamental theorem's `genFormationPi` arm, for the `gen_piTyCode` former, must show the substituted
Π code is a reducible member of its universe.  This lemma is that dispatch, factored to take the children's
fundamental-theorem RESULTS as hypotheses (so it carries no recursion and no termination obligation): the
domain's universe membership (and a copy ONE LEVEL UP, used only to mine a variable inhabitant of the domain
candidate where the candidate is a genuine reducibility candidate), and the codomain's universe membership
under a `cons`-extended substitution for ANY reducible argument.  Everything else is the shipped Π-formation
machinery:

  * `tarskiDecode` drops each universe membership to a reducible TYPE (candidate + reducibility);
  * CR1 (`stronglyNormalizing`) gives the domain's strong normalization;
  * `containsVariable` on the level-`predLevel+1` candidate supplies a domain inhabitant (variable 0);
  * the cons-substitution codomain memberships give `codomainExists` (via the binder-split keystone
    `subst_cons_eq_subst0_lift`) and `codomainNormalizing` (via `openBodyOfConsSubstMember`);
  * `piFormationUnderSubst` assembles the Π former's universe membership;
  * `subst_universeCodeCell` normalises the substituted universe classifier.

This is the membership half of `genFormationPi` for the Π former; the only remaining ingredient at the
induction site is a `DescTelescopePi` companion to PRODUCE the three hypotheses structurally from the premise
telescope.

## Zero-axiom verification

Composition of the shipped reducibility / strong-normalization lemmas; no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The Π former is a reducible universe member, from its children's fundamental-theorem memberships.**
Takes the domain's universe membership at `predLevel+1` and `predLevel+2` (the latter only to extract a
variable inhabitant of the domain candidate) and the codomain's universe membership under `cons argument
substitution` for every reducible argument, and produces the Π code's membership in `universeCodeCell
formerLevel flag` at `predLevel+1`.  No recursion — the children IHs are hypotheses. -/
theorem IsReducibleMemberAt.piFormerOfChildMemberships {scope targetScope : Nat} {predLevel : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    {substitution : RawTermSubst scope (targetScope + 1)}
    (domainMember : IsReducibleMemberAt (predLevel + 1)
      (universeCodeCell domainLevel flag) (RawTerm.subst substitution domainCode))
    (domainMemberAbove : IsReducibleMemberAt (predLevel + 2)
      (universeCodeCell domainLevel flag) (RawTerm.subst substitution domainCode))
    (codomainMember : ∀ {memberLevel : Nat} (argument : RawTerm (targetScope + 1)),
      IsReducibleMemberAt memberLevel (RawTerm.subst substitution domainCode) argument →
      IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode)) :
    IsReducibleMemberAt (predLevel + 1)
      (universeCodeCell formerLevel flag)
      (RawTerm.subst substitution (piTyCodeCell domainCode codomainCode)) := by
  have domainNormalizing := domainMember.stronglyNormalizing
  obtain ⟨domainCandidate, domainReducible⟩ := domainMember.tarskiDecode
  obtain ⟨domainCandidateAbove, domainReducibleAbove⟩ := domainMemberAbove.tarskiDecode
  have freshVarInDomain :
      domainCandidateAbove (.mkGen .gen_var ⟨0, Nat.succ_pos _⟩ .childNil) :=
    domainReducibleAbove.isReducibilityCandidate.containsVariable ⟨0, Nat.succ_pos _⟩
  have codomainExists :
      ∀ argument : RawTerm (targetScope + 1), domainCandidate argument →
        IsReducibleTypeAt predLevel
          (RawTerm.subst0
            (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) argument) := by
    intro argument argumentInDomain
    have member := codomainMember argument ⟨domainCandidate, domainReducible, argumentInDomain⟩
    have asType := member.tarskiDecode
    rwa [RawTerm.subst_cons_eq_subst0_lift] at asType
  have codomainNormalizing :
      IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) :=
    IsStronglyNormalizing.openBodyOfConsSubstMember
      (codomainMember (.mkGen .gen_var ⟨0, Nat.succ_pos _⟩ .childNil)
        ⟨domainCandidateAbove, domainReducibleAbove, freshVarInDomain⟩)
  have result := IsReducibleMemberAt.piFormationUnderSubst formerLevel flag substitution
    domainReducible domainNormalizing codomainNormalizing codomainExists
  rwa [subst_universeCodeCell] at result

/-- **The Σ former is a reducible universe member, from its children's fundamental-theorem memberships.**
The Σ / data-former twin of `piFormerOfChildMemberships`: a Σ code is classified in its universe by STRONG
NORMALIZATION alone (`sigmaFormationUnderSubst`, the `dataFormerInUniverse` route), so it needs only the
domain's and codomain's strong normalization — no `codomainExists`, no domain candidate.  Domain SN is CR1 on
`domainMember`; codomain SN is `openBodyOfConsSubstMember` of the codomain's membership at variable 0 (the
inhabitant mined from the level-`predLevel+1` candidate via `containsVariable`).  Together with
`piFormerOfChildMemberships` this completes the `genFormationPi` arm's membership dispatch for BOTH
`typingRuleDescOf` formers; the only remaining ingredient is the `DescTelescopePi` companion feeding the child
memberships. -/
theorem IsReducibleMemberAt.sigmaFormerOfChildMemberships {scope targetScope : Nat} {predLevel : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainLevel codomainLevel formerLevel : LevelExpr} {flag : UniverseFlag}
    {substitution : RawTermSubst scope (targetScope + 1)}
    (domainMember : IsReducibleMemberAt (predLevel + 1)
      (universeCodeCell domainLevel flag) (RawTerm.subst substitution domainCode))
    (domainMemberAbove : IsReducibleMemberAt (predLevel + 2)
      (universeCodeCell domainLevel flag) (RawTerm.subst substitution domainCode))
    (codomainMember : ∀ {memberLevel : Nat} (argument : RawTerm (targetScope + 1)),
      IsReducibleMemberAt memberLevel (RawTerm.subst substitution domainCode) argument →
      IsReducibleMemberAt (predLevel + 1) (universeCodeCell codomainLevel flag)
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode)) :
    IsReducibleMemberAt (predLevel + 1)
      (universeCodeCell formerLevel flag)
      (RawTerm.subst substitution
        (.mkGen .gen_sigmaTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))) := by
  have domainNormalizing := domainMember.stronglyNormalizing
  obtain ⟨domainCandidateAbove, domainReducibleAbove⟩ := domainMemberAbove.tarskiDecode
  have freshVarInDomain :
      domainCandidateAbove (.mkGen .gen_var ⟨0, Nat.succ_pos _⟩ .childNil) :=
    domainReducibleAbove.isReducibilityCandidate.containsVariable ⟨0, Nat.succ_pos _⟩
  have codomainNormalizing :
      IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) :=
    IsStronglyNormalizing.openBodyOfConsSubstMember
      (codomainMember (.mkGen .gen_var ⟨0, Nat.succ_pos _⟩ .childNil)
        ⟨domainCandidateAbove, domainReducibleAbove, freshVarInDomain⟩)
  have result := IsReducibleMemberAt.sigmaFormationUnderSubst (predLevel := predLevel)
    formerLevel flag substitution domainNormalizing codomainNormalizing
  rwa [subst_universeCodeCell] at result

end FX1Poly.Typed
