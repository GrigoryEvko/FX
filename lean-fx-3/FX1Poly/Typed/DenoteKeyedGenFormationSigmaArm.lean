import FX1Poly.Typed.DenoteKeyedSigmaFormation
import FX1Poly.Typed.DenoteKeyedSigmaFromChildMembers
import FX1Poly.Typed.DenoteKeyedFundamentalMotive
import FX1Poly.Typed.HasTypeDesc

/-! # FX1Poly/Typed/DenoteKeyedGenFormationSigmaArm
    — the genFormationPi Σ fundamental-theorem arm (premise-isolating; SN-D5d toward SN-043/#750)

The Σ case of the denote fundamental theorem's `genFormationPi` arm, in the premise-isolating shape the
shipped binder arm `fundamentalPiIntroAtDenote` (`DenoteKeyedFundamentalPiIntro.lean`) established: the
children's fundamental-theorem data arrive as universal premises (the FT induction's IHs supply them), and the
arm assembles the conclusion `FundamentalConclusionAtDenote`.

`typingRuleDescOf` is `some` only for `gen_piTyCode`/`gen_sigmaTyCode`, so the `genFormationPi` arm is the
2-case split {Π, Σ}.  The Σ case routes its reducible-as-type half through the FREE neutral arm
(`sigmaFormationMemberAtDenote`, `DenoteKeyedSigmaFormation.lean`), so — unlike Π, whose reducible-as-type is the
#752 threshold residual — the Σ arm reduces ENTIRELY to its children's strong normalization.

The asymmetry of the two child premises is the genuine structural content:
  * **domain** — supplied as its universe MEMBERSHIP (the telescope IH's natural output); its strong
    normalization is FREE by denote CR1 (`stronglyNormalizing_of_universeMemberAtDenote`, no binder).
  * **codomain** — supplied as its under-binder strong normalization `subst (lift σ) codomain` DIRECTLY.  Its
    production is genuinely harder: the only universal domain inhabitant for discharging the codomain's binder
    is `var 0` at the binder-WEAKENED target scope, and weakening the reducible environment needs the denote
    reducibility relation's renaming-closure (SN-040), which is Kripke-obstructed.  So the codomain SN is the
    correctly-DEFERRED premise — the same isolation `fundamentalPiIntroAtDenote` applies to its own codomain
    reducibility (`codomainReducibleAtLevel`, a universal premise).

## The declaration

`fundamentalGenFormationSigmaAtDenote` — from the domain's universe membership under every closing substitution
(discharging domain SN by CR1) and the codomain's under-binder SN under every closing substitution, `Σ domain.
codomain` satisfies `FundamentalConclusionAtDenote` at its universe classifier `Type@levelExpr`.  The genuinely
NEW content over `sigmaFormationMemberAtDenote` (which works at a fixed substitution) is the FT-motive threading
(`∀ substitution, reducible-env → …`) plus the CR1 discharge of the domain half — making the Σ arm the direct
analogue of `fundamentalPiIntroAtDenote`.

## Zero-axiom verification

`intro` the substitution / environment, then `sigmaFormationMemberAtDenote` on the domain SN (denote CR1 of the
domain membership) and the codomain SN premise — both applied to the closing substitution.  No induction, no
`funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (checked:
depends on no axioms).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The genFormationPi Σ fundamental-theorem arm (premise-isolating).**  From the domain's universe membership
under every closing substitution (the telescope IH, discharging domain SN by CR1) and the codomain's
under-binder strong normalization under every closing substitution, `Σ domain. codomain` satisfies the
fundamental-theorem conclusion at `Type@levelExpr`.  The direct analogue of `fundamentalPiIntroAtDenote`; the Σ
case's reducible-as-type is the free neutral arm, so the arm reduces to the children's strong normalization (the
codomain SN deferred as a premise, its production blocked on the Kripke-obstructed SN-040). -/
theorem fundamentalGenFormationSigmaAtDenote {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainLevel levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (domainAbove : LevelExpr.denote domainLevel env < level)
    (domainMember : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleMemberAtDenote env level
          (universeCodeCell domainLevel flag) (RawTerm.subst substitution domain))
    (codomainSN : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) codomain)) :
    FundamentalConclusionAtDenote env level context
      (.mkGen .gen_sigmaTyCode () (.childCons domain (.childCons codomain .childNil)))
      (universeCodeCell levelExpr flag) := by
  intro _targetScope substitution envReducible
  exact sigmaFormationMemberAtDenote env level levelExpr flag substitution levelAbove
    (stronglyNormalizing_of_universeMemberAtDenote env level domainLevel flag _ domainAbove
      (domainMember substitution envReducible))
    (codomainSN substitution envReducible)

end FX1Poly.Typed
