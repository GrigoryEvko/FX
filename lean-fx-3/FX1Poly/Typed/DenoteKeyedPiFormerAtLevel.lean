import FX1Poly.Typed.DenoteKeyedCanonicalMemberCandidate

/-! # FX1Poly/Typed/DenoteKeyedPiFormerAtLevel
    — the single-level piType assembly primitive (the genFormationPi arm's core; toward SN-043/#752)

The route correction recorded for #752: the FT's genFormationPi arm needs the former reducible at its DECODED
level — a SINGLE level (`fundamentalTypeFormerAtDenote` consumes `IsReducibleTypeAtDenote env (denote levelExpr
env) (subst σ former)`), NOT all levels.  The all-level backbone is genuinely unachievable for threshold-drift
composite-domain Π (the Π fails below threshold) and is not needed: a former's components live in universes
strictly below the former's own, so the former's decoded level sits above every component threshold.  This file
ships the foundational primitive of that single-level route.

`piFormerReducibleAtLevel`: `Π domainCode codomainCode` is reducible at level `level` from the domain reducible
at `level` and the codomain reducible at `level` for every domain member — CHOICE-FREELY, the canonical
member-predicate (`reducibleMemberCandidate`) supplying the `piType` candidates from mere existence.  No
all-level quantifier, no member-stability, no threshold-split: a single `piType` at one level.  This is exactly
the shape the genFormationPi arm has after lifting the telescope children to the former's decoded level.

`universeDomainPiFormerReducibleAtLevel`: the impredicative case `Π (X : Type@levelExpr). C[X]` becomes TRIVIAL
at a single level — the domain `Type@levelExpr` is reducible at EVERY level (`universeCode_isReducibleAtDenote`,
the anti-vacuity that defeats SN-001), so NO threshold-split is required (contrast the all-level
`universeDomainPi_reducibleFromCodomainExistence`, which must split on `Nat.lt_or_ge` to handle the empty
universe candidate below `denote levelExpr env`).  The single-level route sidesteps the impredicative obstruction
entirely.

## Zero-axiom verification

`piFormerReducibleAtLevel` is one `piType` constructor with `reducibleMemberCandidate` discharging both premises
from existence; `universeDomainPiFormerReducibleAtLevel` instantiates it with
`universeCode_isReducibleAtDenote`.  No tactic, no recursion, no `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The single-level piType assembly primitive.**  `Π domainCode codomainCode` is denote-reducible at `level`
given the domain reducible at `level` and the codomain reducible at `level` for every domain member.  The
canonical member-predicate is the candidate for both domain and codomain (`reducibleMemberCandidate`), so the
`piType` premises discharge from mere existence — no `Classical.choice`.  A single `piType` at one level: the
genFormationPi arm's core, after the telescope children are lifted to the former's decoded level. -/
theorem piFormerReducibleAtLevel {scope : Nat} (env : Nat → Nat) (level : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainReducible : IsReducibleTypeAtDenote env level domainCode)
    (codomainReducible : ∀ argument : RawTerm scope,
      IsReducibleMemberAtDenote env level domainCode argument →
      IsReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtDenote env level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  ⟨_, ReducibleTypeStepDenote.piType
    (fun argument => IsReducibleMemberAtDenote env level (RawTerm.subst0 codomainCode argument))
    domainReducible.reducibleMemberCandidate
    (fun argument argumentInDomain =>
      (codomainReducible argument argumentInDomain).reducibleMemberCandidate)⟩

/-- **The universe-domain Π former, reducible at a single level — TRIVIALLY.**  `Π (X : Type@levelExpr). C[X]`
is denote-reducible at `level` from the codomain reducible at `level` for every universe member, with NO
threshold-split: the domain `Type@levelExpr` is reducible at EVERY level (`universeCode_isReducibleAtDenote`),
so `piFormerReducibleAtLevel` applies directly.  This is the impredicative case the all-level route had to
threshold-split (`universeDomainPi_reducibleFromCodomainExistence`); at a single level the obstruction vanishes
— the single-level route's payoff for impredicative polymorphism. -/
theorem universeDomainPiFormerReducibleAtLevel {scope : Nat} (env : Nat → Nat) (level : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) {codomainCode : RawTerm (scope + 1)}
    (codomainReducible : ∀ argument : RawTerm scope,
      IsReducibleMemberAtDenote env level
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil) argument →
      IsReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtDenote env level
      (.mkGen .gen_piTyCode ()
        (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
          (.childCons codomainCode .childNil))) :=
  piFormerReducibleAtLevel env level
    (universeCode_isReducibleAtDenote env level levelExpr flag) codomainReducible

/-- **The neutral/type-variable-domain Π former, reducible at a single level.**  When the domain is neutral
(weak-head-normal non-Π non-universe — a context type variable or stuck application), it is reducible at the
level directly via the `neutral` constructor (with the strong-normalization candidate, which references neither
the lower family nor the level), so `piFormerReducibleAtLevel` applies.  This is the common fundamental-theorem
case `Π (x : X). C[x]` where `X` is a context type variable; together with
`universeDomainPiFormerReducibleAtLevel` it covers the FREE-LIFT domain shapes (universe / neutral — both
reducible at every level), completing the genFormationPi piArm ingredient set.  The remaining domain shape,
threshold-drift composites, lifts via the above-threshold uniform candidate (shipped) supplied as the
`piFormerReducibleAtLevel` domain premise — no separate lemma. -/
theorem neutralDomainPiFormerReducibleAtLevel {scope : Nat} (env : Nat → Nat) (level : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (noWeakHeadStep : ∀ reduct : RawTerm scope, ¬ WeakHeadStep domainCode reduct)
    (notPiType : domainCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : domainCode.rootGenerator ≠ Generator.gen_universeCode)
    (notEmpty : domainCode.rootGenerator ≠ Generator.gen_emptyCode)
    (codomainReducible : ∀ argument : RawTerm scope,
      IsReducibleMemberAtDenote env level domainCode argument →
      IsReducibleTypeAtDenote env level (RawTerm.subst0 codomainCode argument)) :
    IsReducibleTypeAtDenote env level
      (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))) :=
  piFormerReducibleAtLevel env level
    ⟨IsStronglyNormalizing, ReducibleTypeStepDenote.neutral noWeakHeadStep notPiType notUniverse notEmpty⟩
    codomainReducible

end FX1Poly.Typed
