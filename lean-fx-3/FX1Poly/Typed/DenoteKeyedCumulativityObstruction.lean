import FX1Poly.Typed.DenoteKeyedReducibility

/-! # FX1Poly/Typed/DenoteKeyedCumulativityObstruction
    — the committed witness that denote-keyed TYPE-reducibility does NOT lift across levels (the
      non-uniform genFormationPi residual is model-obstructed, not merely unproven)

## What blocks the non-uniform genFormationPi piReducibleAsType

`fundamentalGenFormationPiAtDenote`'s `piReducibleAsType` premise needs the Π reducible-as-type at the
former's decoded OUTPUT level `denote (lmaxAll [domainLevel, codomainLevel]) env`.  The denote fundamental
motive (`FundamentalConclusionAtDenote`) is SINGLE-ambient-level, and the Π-formation rule outputs at the
`lmax` of the children's levels, so a child classified BELOW the lmax (the non-uniform case —
`piReducibleAsTypeFromUniformLevelMember` already closes the fully-uniform case) arrives reducible at its OWN
decoded level and must lift UP to the decoded lmax: a TYPE-reducibility cumulativity
`IsReducibleTypeAtDenote env lowerLevel D → IsReducibleTypeAtDenote env higherLevel D` for `lowerLevel ≤
higherLevel`.

## Why that lift is OBSTRUCTED (not merely hard)

By induction on the `lowerLevel`-derivation, the `piType` arm's codomain sub-derivations quantify over
SEMANTIC domain-members (`argument`).  Those members are NOT universe-bounded: denote reducibility does NOT
bound universes — `universeCode_isReducibleAtDenote` fires the universe arm at EVERY ambient level, so
`Type@huge` (and `Π (Type@huge). C`) are reducible-as-type at any level, with empty member candidates below
the threshold.  A gap-universe member (decoded level in `[lowerLevel, higherLevel)`) substituted into a
codomain makes that codomain's own domain candidate JUMP from empty (at `lowerLevel`) to non-empty (at
`higherLevel`) — and the `lowerLevel`-derivation supplies NO codomain data for the freshly-appeared
`higherLevel` members.  The re-derivation has nothing to transport.

## The committed witness

`gapUniverseDomainPiVacuouslyReducibleAtLowLevel` is the concrete pin: at any `lowLevel ≤ denote gapLevel
env`, the universe `Type@gapLevel` has the EMPTY member candidate (the below-family is empty at index ≥
`lowLevel`, `denoteBelowFamily_eq_empty_of_ge`), so `Π (Type@gapLevel). codomain` is reducible-as-type at
`lowLevel` for ARBITRARY `codomain` (the `piType` codomain obligation is vacuous — no domain member to feed
it).  Low-level reducibility of a gap-universe-domain Π is therefore CODOMAIN-BLIND: it holds identically for
every codomain, so it cannot determine — hence cannot be lifted to — the higher-level reducibility where the
domain gains members and the codomain genuinely constrains the candidate.

## Strategic consequence (recorded, not silently worked around)

The non-uniform genFormationPi `piReducibleAsType` is NOT closable by a within-model cumulativity lemma over
the current denote relation.  Closing it needs either (a) a STRENGTHENED reducibility whose universe MEMBERS
carry a universe bound (so substituted args can't inject gap-universes) — a model-wide refactor re-proving
CR1/CR2/CR3 and every FT arm; or (b) an honest CONDITIONAL/fragment milestone: the fully-uniform Π fragment
is unconditional (`piReducibleAsTypeFromUniformLevelMember`), the non-uniform arm stays a carried premise of
`fundamentalGenFormationPiAtDenote` (which is premise-isolating by construction).  The uniform fragment plus
the neutral/universe/whnf domain arms already shipped cover the member-stable cases; this file marks the
exact boundary of what semantic reducibility alone can deliver.

## Zero-axiom verification

A single `piType` anonymous constructor whose codomain obligation is discharged by `absurd` on the empty
below-family (`denoteBelowFamily_eq_empty_of_ge` rewrite).  No induction, no `funext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The cumulativity-obstruction witness.**  At any `lowLevel` at or below the decoded universe level
`denote gapLevel env`, the universe code `Type@gapLevel` has an EMPTY member candidate, so `Π (Type@gapLevel).
codomain` is reducible-as-type at `lowLevel` for ANY `codomain` — the dependent-arrow codomain obligation is
vacuous (no domain member exists to feed it).  This codomain-blindness is exactly why such a Π's low-level
reducibility cannot be lifted to a higher level: it carries no codomain information to transport.  The
concrete pin (cf. `universeCodeNotAllLevelsMemberStable` for the member-stability obstruction) showing the
denote TYPE-reducibility cumulativity is model-obstructed for gap-universe-domain Π. -/
theorem gapUniverseDomainPiVacuouslyReducibleAtLowLevel {scope : Nat} (env : Nat → Nat)
    (lowLevel : Nat) (gapLevel : LevelExpr) (flag : UniverseFlag)
    (codomain : RawTerm (scope + 1))
    (gapAtOrAboveLow : lowLevel ≤ LevelExpr.denote gapLevel env) :
    IsReducibleTypeAtDenote env lowLevel
      (piTyCodeCell (universeCodeCell gapLevel flag) codomain) := by
  refine ⟨_, ReducibleTypeStepDenote.piType
    (fun _argument => IsStronglyNormalizing)
    (ReducibleTypeStepDenote.universeCode gapLevel flag)
    (fun argument argumentInDomain => ?_)⟩
  obtain ⟨_strongNormalizing, candidate, member⟩ := argumentInDomain
  rw [denoteBelowFamily_eq_empty_of_ge env lowLevel (LevelExpr.denote gapLevel env) gapAtOrAboveLow]
    at member
  exact absurd member id

end FX1Poly.Typed
