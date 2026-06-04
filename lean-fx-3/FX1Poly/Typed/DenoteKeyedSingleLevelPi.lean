import FX1Poly.Typed.DenoteKeyedGeneralDomainPiArm

/-! # FX1Poly/Typed/DenoteKeyedSingleLevelPi
    — the drift-free SINGLE-LEVEL Π reducibility toolkit (reframe of the #752/#672 residual)

The all-levels piArm (`ofReducibleTypeStepDenote`, #752) over-generalizes a Π's reducibility to EVERY denote
level — including the LOW levels where a composite-universe domain `Π (Type@inner). C'` is vacuously inhabited.
`universeCodeNotAllLevelsMemberStable` (`DenoteKeyedUniverseDomainPiArm.lean`) proves that those low levels
genuinely break the member-stability route: a universe-code component is NOT all-levels member-stable.

This file is the reframe.  The fundamental-theorem arm `genFormationPi` actually needs the Π reducible-as-type at
ONE level — the DECODED output level `denote levelExpr env` (`fundamentalGenFormationPiAtDenote`'s
`piReducibleAsType` premise) — which is ABOVE all the internal thresholds, so the low-level vacuity never
arises.  At a single level, TYPE reducibility (∃ candidate) is direct (the `piType` arm with canonical
member-predicates), and a universe MEMBER decodes to a reducible TYPE at the decoded level with no lift at all.

Two clean, drift-free, zero-axiom building blocks:
  * `piReducibleAtLevelFromComponents` — `IsReducibleTypeAtDenote env L (Π D C)` from `D` reducible at `L` and
    `C` reducible at `L` per `D`-member-at-`L`.  The canonical member-predicate (`reducibleMemberCandidate`,
    #490) keys the codomain candidate on membership, choice-free.  Single level ⟹ NO drift, NO member-stability,
    NO all-levels.
  * `universeMemberReducibleAsTypeAtDecodedLevel` — a reducible MEMBER of `Type@levelExpr` is a reducible TYPE at
    the decoded level `denote levelExpr env`, directly.  This is exactly the first half of the A2 bridge
    `universeMemberReducibleAtLevel` BEFORE it over-generalizes to all levels via the piArm; isolating it shows
    the decoded-level reducibility needs no piArm.

Together: from a Π whose domain is a universe member (reducible-as-type at the decoded level by the second lemma)
and whose codomain is reducible at the decoded level, the Π is reducible-as-type at the decoded level (first
lemma) — the genFormationPi `piReducibleAsType` discharged WITHOUT the all-levels #752 piArm.  The remaining
all-levels need (the A2 bridge's lift to the AMBIENT level, for the conv/piIntro arms) is the genuine residual,
and the path there is a LEVEL-BOUNDED ("reducible at all levels ≥ K") backbone variant that stays above the
thresholds — NOT the full all-levels `ofReducibleTypeStepDenote`.

## Zero-axiom verification

`piReducibleAtLevelFromComponents` is a single `piType` anonymous constructor with `reducibleMemberCandidate`
projections.  `universeMemberReducibleAsTypeAtDecodedLevel` is `candidateIffUniverse` + `denoteBelowFamily_eq_
reducible` rewrite (the bridge's extraction prefix).  No induction, no `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Single-level Π type-reducibility from component reducibility.**  `Π domainCode codomainCode` is reducible
as a TYPE at level `level` given `domainCode` reducible there and `codomainCode` reducible there for every
reducible member of `domainCode` at `level`.  The codomain candidate is the canonical member-predicate
(`reducibleMemberCandidate`), keyed on membership — choice-free.  At ONE level, so no member-stability / no
all-levels drift: this is the genFormationPi `piReducibleAsType` shape at the decoded output level. -/
theorem piReducibleAtLevelFromComponents {scope : Nat} (env : Nat → Nat) (level : Nat)
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

/-- **A universe member is a reducible TYPE at the decoded level, directly.**  A reducible member `typeCode` of
`Type@levelExpr` at the ambient `level` (with the decoded level below the ambient) is a reducible TYPE at the
decoded level `denote levelExpr env` — no all-levels lift, no piArm.  This is the prefix of the A2 bridge
`universeMemberReducibleAtLevel` (which then over-generalizes to all levels); isolating it shows the
decoded-level reducibility is piArm-free, hence drift-free for ANY `typeCode` (including composite-universe Π). -/
theorem universeMemberReducibleAsTypeAtDecodedLevel {scope : Nat} {env : Nat → Nat} {level : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {typeCode : RawTerm scope}
    (memberOfUniverse : IsReducibleMemberAtDenote env level
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) typeCode)
    (levelAbove : LevelExpr.denote levelExpr env < level) :
    IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) typeCode := by
  obtain ⟨candidate, reducibleUniverse, candidateMember⟩ := memberOfUniverse
  have candidateIff := ReducibleTypeStepDenote.candidateIffUniverse reducibleUniverse
    (levelExpr := levelExpr) (flag := flag) rfl
  obtain ⟨_strongNormalizing, decodeCandidate, denoteReducible⟩ := (candidateIff typeCode).mp candidateMember
  rw [denoteBelowFamily_eq_reducible env level (LevelExpr.denote levelExpr env) levelAbove]
    at denoteReducible
  exact ⟨decodeCandidate, denoteReducible⟩

end FX1Poly.Typed
