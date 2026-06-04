import FX1Poly.Typed.DenoteKeyedReducibility
import FX1Poly.Typed.DenoteKeyedSigmaFormation
import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Core.StrongNormalizationReflection

/-! # FX1Poly/Typed/DenoteKeyedSigmaFromChildMembers
    — denote universe-member CR1 + the Σ-from-child-members assembly (SN-D5d; toward SN-043/#750)

The denote `genFormationPi` arm's Σ case (`sigmaFormationMemberAtDenote`,
`DenoteKeyedSigmaFormation.lean`) consumes the children's STRONG NORMALIZATION (`domainNormalizing` /
`codomainNormalizing`).  In the fundamental-theorem assembly those arrive as the children's denote-reducibility
MEMBERSHIPS in their universe codes (from the telescope companion's IH); this file bridges membership → SN and
assembles, the denote analogue of the fuel `IsReducibleMemberAt.sigmaFormerOfChildMembershipsAtRequiredLevel`
(`PiFormerMembership.lean:124`).

## The two declarations

  * `stronglyNormalizing_of_universeMemberAtDenote` — **denote universe-member CR1**: a denote-reducible member
    of a universe code `Type@levelExpr` at an ambient `level` strictly ABOVE its decoded level is strongly
    normalizing.  `universeMembership_levelIrrelevant` pins the universe candidate to the level-irrelevant
    decode set `fun m => SN m ∧ reducible-type m`; `ReducibleTypeAtDenote.deterministic` identifies the member's
    own (existential) candidate with it pointwise; the first conjunct is the SN.  The threshold `denote
    levelExpr env < level` is FUNDAMENTAL — below it the universe candidate's member set goes vacuous (the
    #672/#752 caveat), so this CR1 holds only above threshold (the FT runs at a large-enough ambient level).
  * `sigmaFormationFromChildMembersAtDenote` — the **Σ-from-child-members assembly**: under a closing
    substitution (taken at the binder-WEAKENED `RawTermSubst scope (targetScope+1)`), from the domain's
    universe membership and the codomain's universe membership AT THE FRESH VARIABLE (`var 0`, the
    `cons`-instantiation the telescope tail supplies), the Σ code `Σ domain. codomain` is a denote-reducible
    member of its universe `Type@(lmaxAll [domainLevel, codomainLevel])`.  Domain SN is CR1 on the domain
    member; codomain-under-binder SN is CR1 on the fresh-variable codomain member then `openBodyOfConsSubst`
    (the relation-agnostic binder reconciliation, `cons (var 0) σ` ↦ `lift σ`); `sigmaFormationMemberAtDenote`
    closes, `subst_universeCodeCell` fixing the closed classifier.

This completes the Σ branch's child-members → membership step; the remaining genFormationPi work is the
weakened-env telescope production of these child memberships (the `fundamentalPiIntroAtDenote` #749 pattern)
and the 2-case dispatch / mutual recursor, plus the Π branch's #752 threshold residual.

## Zero-axiom verification

CR1 is one `obtain` + `universeMembership_levelIrrelevant` + `ReducibleTypeAtDenote.deterministic` +
projection.  The assembly is two CR1 applications (the codomain composed with `openBodyOfConsSubst`) feeding
`sigmaFormationMemberAtDenote`, then `rwa [subst_universeCodeCell]`.  No induction, no `funext` (the pointwise
determinism avoids it).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`
(checked: neither depends on any axioms).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Denote universe-member CR1.**  A denote-reducible member of a universe code `Type@levelExpr` at an ambient
`level` strictly above the decoded level `denote levelExpr env` is strongly normalizing.  The universe
candidate is the level-irrelevant `SN ∧ reducible-type` set (`universeMembership_levelIrrelevant`); the member's
own existential candidate matches it pointwise (`ReducibleTypeAtDenote.deterministic`); the SN is the first
conjunct.  The threshold is fundamental (below it the candidate's member set is empty — the #672 caveat). -/
theorem stronglyNormalizing_of_universeMemberAtDenote {scope : Nat} (env : Nat → Nat) (level : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) (term : RawTerm scope)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (member : IsReducibleMemberAtDenote env level (universeCodeCell levelExpr flag) term) :
    IsStronglyNormalizing term := by
  obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
  have universeCandidateReducible :
      ReducibleTypeAtDenote env level (universeCodeCell levelExpr flag)
        (fun member : RawTerm scope => IsStronglyNormalizing member ∧
          IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) member) :=
    universeMembership_levelIrrelevant env level levelExpr flag levelAbove
  have pointwise := ReducibleTypeAtDenote.deterministic candidateReducible universeCandidateReducible
  exact ((pointwise term).mp termInCandidate).1

/-- **The Σ-from-child-members assembly (denote-keyed).**  Under a closing `substitution` at the binder-weakened
target scope, from the domain's universe membership and the codomain's universe membership at the fresh variable
`var 0` (the `cons`-instantiation the telescope tail supplies), the Σ code is a denote-reducible member of its
universe `Type@(lmaxAll [domainLevel, codomainLevel])`.  Domain SN by CR1; codomain-under-binder SN by CR1 then
`openBodyOfConsSubst`; `sigmaFormationMemberAtDenote` closes.  The denote analogue of the fuel
`IsReducibleMemberAt.sigmaFormerOfChildMembershipsAtRequiredLevel`. -/
theorem sigmaFormationFromChildMembersAtDenote {scope targetScope : Nat} (env : Nat → Nat) (level : Nat)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (substitution : RawTermSubst scope (targetScope + 1))
    (outputAbove : LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env < level)
    (domainAbove : LevelExpr.denote domainLevel env < level)
    (codomainAbove : LevelExpr.denote codomainLevel env < level)
    (domainMember : IsReducibleMemberAtDenote env level
      (universeCodeCell domainLevel flag) (RawTerm.subst substitution domain))
    (codomainMemberAtFreshVar : IsReducibleMemberAtDenote env level
      (universeCodeCell codomainLevel flag)
      (RawTerm.subst (RawTermSubst.cons (.mkGen .gen_var ⟨0, Nat.succ_pos targetScope⟩ .childNil)
        substitution) codomain)) :
    IsReducibleMemberAtDenote env level
      (universeCodeCell (lmaxAll [domainLevel, codomainLevel]) flag)
      (RawTerm.subst substitution
        (.mkGen .gen_sigmaTyCode () (.childCons domain (.childCons codomain .childNil)))) := by
  have domainNormalizing : IsStronglyNormalizing (RawTerm.subst substitution domain) :=
    stronglyNormalizing_of_universeMemberAtDenote env level domainLevel flag _ domainAbove domainMember
  have codomainNormalizing :
      IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) codomain) :=
    IsStronglyNormalizing.openBodyOfConsSubst
      (stronglyNormalizing_of_universeMemberAtDenote env level codomainLevel flag _ codomainAbove
        codomainMemberAtFreshVar)
  have result := sigmaFormationMemberAtDenote env level (lmaxAll [domainLevel, codomainLevel]) flag
    substitution outputAbove domainNormalizing codomainNormalizing
  rwa [subst_universeCodeCell] at result

end FX1Poly.Typed
