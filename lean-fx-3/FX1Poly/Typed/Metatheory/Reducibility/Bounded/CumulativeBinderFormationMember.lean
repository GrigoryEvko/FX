import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedGenFormationPiFromTelescope
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedGenFormationSigmaFromTelescope
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedTelescopeConsSucc

/-! # FX1Poly/Typed/CumulativeBinderFormationMember
    — the binder-crossing telescope bridge + the Π/Σ cumulative formation FT members (TYTAB-4 step 4)

The two genuinely dependent cumulative type-formers (Π / Σ) carry a BINDER-CROSSING codomain obligation: the
codomain is typed at `scope + 1` in the domain-extended context `context.cons domain`.  The native
`formationFundamental` premise hands these as a FLAT obligation list, not the structured `DescTelescopePi` the grown
FT recursor consumes — so the per-obligation `FundamentalConclusionAtBoundedSucc` IHs must be re-assembled into the
`TelescopeReducibleAtBounded` the shipped `fundamentalGenFormation{Pi,Sigma}FromTelescopeAtBoundedSucc` arms expect.

## The binder-crossing telescope bridge

`twoChildFormationTelescopeAtBoundedSucc` is that re-assembly: from the domain obligation IH (at `context`) and the
codomain obligation IH (at `context.cons domain`), under any closing substitution it produces the two-child
telescope at the former's output level.  Its `.twoChild` shape needs, per bound-reducible argument, the codomain
member under the `cons`-extended substitution — which `ReducibleEnvAtBounded.cons` builds, BUT only from an
argument member at `bound`, while the telescope hands the argument at the lower `argLevel` (the output level).

## Breaking the circularity

Lifting the argument `argLevel → bound` (`IsReducibleMemberAtBounded.cumulative`) needs `argLevel ≤ bound`, i.e.
`denote (lmaxAll [domainLevel, codomainLevel]) env < bound` — which needs BOTH the domain and codomain level
bounds.  The domain bound is read off the domain member directly; the codomain bound would seem to need the
codomain member, which needs the `cons` environment, which needs the lifted argument — a cycle.  It is broken with a
CANONICAL inhabitant: `variableZeroMemberOfBoundedUniverseMember` gives variable 0 as a member of `subst σ domain`
AT `bound` (using only the domain bound, via `domainLevel ≤ bound`), which `cons`-extends the environment and lets
the codomain IH fire to extract `codomainBelowBound`.  With both bounds in hand, `levelMax_lt` gives `argLevel <
bound` and the real argument lifts.  This is the same variable-0-inhabitant device the grown Π arm uses internally,
here lifted to the flat-obligation re-assembly.

## The members

`fundamentalCumulativePiMemberAtBoundedSucc` / `…SigmaMemberAtBoundedSucc` compose the bridge with the shipped
Π / Σ from-telescope arms: from the two obligation IHs, `piTyCodeCell domain codomain` /
`sigmaTyCodeCell domain codomain` is a bound-reducible member of `Type@(lmaxAll [domainLevel, codomainLevel])`.
The genuinely dependent cumulative formers' formation FT — the hard binder-crossing cases of the native
`formationFundamental` premise (the non-dependent list/option cases route through `dataFormationUnderSubstAtBounded`).

## Zero-axiom verification

`subst_universeCodeCell` rewrites + the shipped inhabitant / cons / cumulative / `levelMax_lt` lemmas + two
`fundamentalTelescopeConsAtBoundedSucc` applications, then the from-telescope arms.  No induction, no `funext`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax
open StepStar

/-- **The binder-crossing two-child formation telescope bridge (TYTAB-4 step 4).**  From the domain obligation IH
(at `context`) and the codomain obligation IH (at `context.cons domain`), under any closing substitution the two
children form the Π/Σ telescope at the former's output level `denote (lmaxAll [domainLevel, codomainLevel]) env`.
The codomain level bound is extracted via a variable-0 inhabitant at `bound` (breaking the argument-lift
circularity), then the real argument lifts and `ReducibleEnvAtBounded.cons` builds the binder-crossing tail. -/
theorem twoChildFormationTelescopeAtBoundedSucc {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (domainFundamental :
      FundamentalConclusionAtBoundedSucc env bound context domain (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionAtBoundedSucc env bound (context.cons domain) codomain
        (universeCodeCell codomainLevel flag)) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        TelescopeReducibleAtBounded env bound
          (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env) flag 0 2 substitution
          [domainLevel, codomainLevel]
          (.childCons domain (.childCons codomain .childNil)) := by
  intro _targetScope substitution envReducible
  have domainMember := domainFundamental substitution envReducible
  rw [subst_universeCodeCell] at domainMember
  have domainBelowBound : LevelExpr.denote domainLevel env < bound := by
    obtain ⟨_domCand, domCandReducible, _domIn⟩ := domainMember
    exact universeCodeReducibleAtBounded_belowBound domCandReducible
  have variableZeroAtBound :=
    variableZeroMemberOfBoundedUniverseMember domainMember domainBelowBound (Nat.le_of_lt domainBelowBound)
  have codomainMember :=
    codomainFundamental _ (ReducibleEnvAtBounded.cons envReducible variableZeroAtBound)
  rw [subst_universeCodeCell] at codomainMember
  have codomainBelowBound : LevelExpr.denote codomainLevel env < bound := by
    obtain ⟨_codCand, codCandReducible, _codIn⟩ := codomainMember
    exact universeCodeReducibleAtBounded_belowBound codCandReducible
  have argLevelBelowBound : LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env < bound :=
    levelMax_lt domainBelowBound codomainBelowBound
  refine fundamentalTelescopeConsAtBoundedSucc env bound _ envReducible domainFundamental ?_
  intro argument argumentMember
  refine fundamentalTelescopeConsAtBoundedSucc env bound _
    (ReducibleEnvAtBounded.cons envReducible
      (IsReducibleMemberAtBounded.cumulative argumentMember (Nat.le_of_lt argLevelBelowBound)))
    codomainFundamental ?_
  intro _argument2 _argument2Member
  exact fundamentalTelescopeNilAtBounded env bound _

/-- **The Π cumulative formation FT member (TYTAB-4 step 4).**  From the domain and codomain obligation IHs,
`piTyCodeCell domain codomain` is a bound-reducible member of `Type@(lmaxAll [domainLevel, codomainLevel])` under
any closing substitution.  The binder-crossing dependent formation, assembled by feeding the telescope bridge to
the shipped Π from-telescope arm. -/
theorem fundamentalCumulativePiMemberAtBoundedSucc {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (domainFundamental :
      FundamentalConclusionAtBoundedSucc env bound context domain (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionAtBoundedSucc env bound (context.cons domain) codomain
        (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionAtBoundedSucc env bound context (piTyCodeCell domain codomain)
      (universeCodeCell (lmaxAll [domainLevel, codomainLevel]) flag) :=
  fundamentalGenFormationPiFromTelescopeAtBoundedSucc env bound context domainLevel codomainLevel flag
    (twoChildFormationTelescopeAtBoundedSucc env bound context domainLevel codomainLevel flag
      domainFundamental codomainFundamental)

/-- **The Σ cumulative formation FT member (TYTAB-4 step 4).**  From the domain and codomain obligation IHs,
`sigmaTyCodeCell domain codomain` is a bound-reducible member of `Type@(lmaxAll [domainLevel, codomainLevel])` under
any closing substitution.  The Σ twin of `fundamentalCumulativePiMemberAtBoundedSucc`, sharing the binder-crossing
telescope bridge and feeding the shipped Σ from-telescope arm. -/
theorem fundamentalCumulativeSigmaMemberAtBoundedSucc {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (domainFundamental :
      FundamentalConclusionAtBoundedSucc env bound context domain (universeCodeCell domainLevel flag))
    (codomainFundamental :
      FundamentalConclusionAtBoundedSucc env bound (context.cons domain) codomain
        (universeCodeCell codomainLevel flag)) :
    FundamentalConclusionAtBoundedSucc env bound context (sigmaTyCodeCell domain codomain)
      (universeCodeCell (lmaxAll [domainLevel, codomainLevel]) flag) :=
  fundamentalGenFormationSigmaFromTelescopeAtBoundedSucc env bound context domainLevel codomainLevel flag
    (twoChildFormationTelescopeAtBoundedSucc env bound context domainLevel codomainLevel flag
      domainFundamental codomainFundamental)

end FX1Poly.Typed
