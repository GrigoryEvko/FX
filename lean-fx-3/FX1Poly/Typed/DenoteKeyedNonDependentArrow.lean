import FX1Poly.Typed.DenoteKeyedLevelIrrelevance

/-! # FX1Poly/Typed/DenoteKeyedNonDependentArrow
    — all-denote-level reducibility for a NON-DEPENDENT arrow (an unconditional slice of #752, toward SN-043)

The denote port of the fuel `IsReducibleTypeAtAllLevels.nonDependentArrowOfAllLevelsDomain`.  It closes a
genuine slice of the composite-domain level-irrelevance residual (#752 = the `ofReducibleTypeStepDenote` piArm
for composite dependent domains) WITHOUT that piArm: the NON-DEPENDENT-codomain case, for an ARBITRARY domain
(including composite Π/Σ domains and universe codes).

The mechanism (the type-side crack past the level-drift wall): a non-dependent arrow is
`piTyCodeCell domainCode (RawTerm.weaken codomainBase)` — the codomain crosses the binder as a pure weakening of
a base type `codomainBase`.  The `piType` constructor's per-argument codomain obligation is
`ReducibleTypeAtDenote env level (subst0 (weaken codomainBase) argument) (codomainCandidate argument)`, and the
weaken-cancellation `RawTerm.weaken_subst_singleton` (`subst0 (weaken codomainBase) argument = codomainBase`)
collapses it to the CONSTANT fact `ReducibleTypeAtDenote env level codomainBase _` — independent of `argument`.
So the per-argument domain-membership gate is NEVER consumed, and the domain candidate's per-level DRIFT (the
obstruction that makes the general composite-domain piArm hard) is IRRELEVANT.  Each level is assembled directly
from the domain's reducibility at that level and the base codomain's reducibility at that level.

The denote proof is even cleaner than the fuel original: no `cases level` split (the denote relation is
level-uniform via `denoteBelowFamily`, unlike the fuel relation's fuel-0 degeneracy).

`universeDomainNonDependentArrow` is the headline instance: `Type@levelExpr → codomainBase` is all-denote-levels
reducible whenever the base codomain is — a non-dependent arrow over a UNIVERSE domain, the case the
from-existence family's member-extension-requiring lemmas could not reach (a universe domain has no
member-extension).  Only the DEPENDENT composite-domain Π stays gated on #752.

## Zero-axiom verification

`intro level`, `obtain` the domain and base-codomain candidates at that level, `piType` with a constant codomain
candidate, and `rw` the weaken-cancellation to discharge the per-argument obligation.  No induction, no `funext`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **All-denote-level reducibility for a non-dependent arrow over an arbitrary domain.**  The simple arrow
`domainCode → codomainBase` (= `piTyCodeCell domainCode (RawTerm.weaken codomainBase)`) is reducible at every
denote level from the domain and base codomain being reducible at every denote level ALONE — no domain-candidate
uniformity, no member-extension, no piArm.  The weaken-cancellation collapses the `piType` codomain obligation to
the constant base-codomain fact, so the domain candidate's per-level drift is never consumed. -/
theorem IsReducibleTypeAtAllDenoteLevels.nonDependentArrowOfAllLevelsDomain {scope : Nat} (env : Nat → Nat)
    {domainCode codomainBase : RawTerm scope}
    (domainAllLevels : IsReducibleTypeAtAllDenoteLevels env domainCode)
    (codomainAllLevels : IsReducibleTypeAtAllDenoteLevels env codomainBase) :
    IsReducibleTypeAtAllDenoteLevels env (piTyCodeCell domainCode (RawTerm.weaken codomainBase)) := by
  intro level
  obtain ⟨_domainCandidate, domainReducible⟩ := domainAllLevels level
  obtain ⟨codomainCandidate, codomainReducible⟩ := codomainAllLevels level
  refine ⟨_, ReducibleTypeStepDenote.piType (fun _argument => codomainCandidate) domainReducible
    (fun argument _argumentInDomain => ?_)⟩
  rw [show RawTerm.subst0 (RawTerm.weaken codomainBase) argument = codomainBase from
    RawTerm.weaken_subst_singleton codomainBase argument]
  exact codomainReducible

/-- **A non-dependent arrow over a UNIVERSE domain is reducible at all denote levels.**  `Type@levelExpr →
codomainBase` is all-denote-levels reducible whenever the base codomain is — the denote witness reaching past
the universe-domain wall (a universe domain has no member-extension, so the member-extension-requiring lemmas
cannot produce this; the non-dependent codomain makes member-extension unnecessary).  Only the dependent
composite-domain Π remains gated on #752. -/
theorem IsReducibleTypeAtAllDenoteLevels.universeDomainNonDependentArrow {scope : Nat} (env : Nat → Nat)
    {levelExpr : LevelExpr} {flag : UniverseFlag} {codomainBase : RawTerm scope}
    (codomainAllLevels : IsReducibleTypeAtAllDenoteLevels env codomainBase) :
    IsReducibleTypeAtAllDenoteLevels env
      (piTyCodeCell (universeCodeCell levelExpr flag) (RawTerm.weaken codomainBase)) :=
  IsReducibleTypeAtAllDenoteLevels.nonDependentArrowOfAllLevelsDomain env
    (IsReducibleTypeAtAllDenoteLevels.ofUniverseCode env levelExpr flag) codomainAllLevels

end FX1Poly.Typed
