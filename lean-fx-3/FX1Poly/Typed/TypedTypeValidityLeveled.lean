import FX1Poly.Typed.TypedTypeValidityBoxedRelation

/-! # FX1Poly/Typed/TypedTypeValidityLeveled
    — the UNIVERSE-TRACKING refined typed type-validity logical relation (GrownCtxConv-5 route B)

The unindexed `TypedTypeValidityBoxed` (`#1110`) carries the type code's validity as an EXISTENTIAL
`IsTypeDescPi context typeCode` (∃ level flag, …).  Firing 34's honest finding pinned the consequence: the
LR-transport route to discharge the GrownCtxConv-5 residual `ConvContextPreservesPiValidity` is BLOCKED at the
`piType` arm, because rebuilding `IsTypeDescPi tgt (Π D C)` from the transported domain + codomain via
`piFormationViaGenArm` needs the domain and codomain at the SAME universe FLAG — and `toIsTypeDescPi` hands back
INDEPENDENT existential flags (the SN candidate `snKripkeCand` tracks no universe).

This file ships the route-B refinement: carry the universe `(level, flag)` in the relation's INDEX.  The
`piType` arm then FORCES the domain at `(domainLevel, flag)` and the codomain at `(codomainLevel, flag)` to share
the flag BY CONSTRUCTION — and the `Π` code lands at `(lmax domainLevel codomainLevel, flag)`.  So the
flag-matching obstacle dissolves: a transport recursion preserves the index, hence the rebuilt domain/codomain
share the flag and `piFormationViaGenArm` applies.

`toHasTypeDescPi` is correspondingly UNIVERSE-PRESERVING — it returns the EXACT `universeCodeCell level flag`
typing, not an existential.  This is the soundness shape the transport's `piType` rebuild consumes.

## The refinement vs the unindexed relation

`TypedTypeValidityBoxed` (`#1110`) is RETAINED (refactor-by-addition); this leveled relation is the
universe-tracking sibling that route B needs.  Same three arms (`neutral` / `universeType` / `piType`), same
candidate boxes (`KripkeCandBox`, `snKripkeCand`, `kripkeArrowDep`), but each arm's validity field is the
SPECIFIC universe-code typing `HasTypeDescPi context typeCode (universeCodeCell level flag)` rather than the
existential `IsTypeDescPi`.

## What this unblocks (the next bricks of route B)

  * `toHasTypeDescPi` (here) — universe-preserving soundness.
  * NEXT: the leveled transport across context conversion (universe arm free, `piType` arm rebuilds validity via
    `piFormationViaGenArm` — now flag-matched, the firing-34 obstacle resolved — recursing on domain + codomain;
    `neutral` arm = the Abel-reflection reconstruction from `#1119`'s var-headed leaf extended under a
    `WfContextTypedLrValid` context).
  * THEN: completeness (`HasTypeDescPi context T (universe level flag) → TypedTypeValidityLeveled …`) by
    structural recursion, and the residual discharge `soundness ∘ transport ∘ completeness`.

## Zero-axiom verification

The relation is a plain indexed inductive; `toHasTypeDescPi` is a three-arm `cases` projecting the validity
field; the non-vacuity smoke is `universeType ∘ ofFormation ∘ universeFormation`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The universe-TRACKING typed type-validity logical relation.**  Indexed by `(context, typeCode, level, flag,
candidate-box)`: the universe `(level, flag)` the type code inhabits is now part of the index.  Each arm's
validity field is the SPECIFIC universe-code typing `HasTypeDescPi context typeCode (universeCodeCell level
flag)` (not the existential `IsTypeDescPi`), so the `piType` arm forces its domain and codomain to share the
flag — resolving the flag-matching obstacle (firing 34) that blocked the unindexed `#1110` from rebuilding
`Π`-validity via `piFormationViaGenArm`. -/
inductive TypedTypeValidityLeveled (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope →
      LevelExpr → UniverseFlag → KripkeCandBox scope → Prop where
  /-- A NEUTRAL type code is leveled-valid at the SN Kripke candidate, carrying its EXACT universe-code typing
  `HasTypeDescPi context typeCode (universeCodeCell level flag)` (the level/flag the neutral inhabits). -/
  | neutral {scope : Nat} {context : TypingContext profile scope} {typeCode : RawTerm scope}
      {level : LevelExpr} {flag : UniverseFlag}
      (neutralCode : IsNeutral typeCode)
      (validity : HasTypeDescPi profile context typeCode (universeCodeCell level flag)) :
      TypedTypeValidityLeveled profile context typeCode level flag (KripkeCandBox.mk snKripkeCand)
  /-- A UNIVERSE code `Type@levelExpr` inhabits `Type@(levelExpr.lsucc)`, so it is leveled-valid at
  `(levelExpr.lsucc, flag)` carrying `HasTypeDescPi context (Type@levelExpr) (Type@(levelExpr.lsucc))`. -/
  | universeType {scope : Nat} {context : TypingContext profile scope}
      {levelExpr : LevelExpr} {flag : UniverseFlag}
      (validity : HasTypeDescPi profile context (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr.lsucc flag)) :
      TypedTypeValidityLeveled profile context (universeCodeCell levelExpr flag)
        levelExpr.lsucc flag (KripkeCandBox.mk snKripkeCand)
  /-- A `Π` type code with domain at `(domainLevel, flag)` and codomain at `(codomainLevel, flag)` — SAME flag,
  forced by the index — is leveled-valid at `(lmax domainLevel codomainLevel, flag)` at the dependent-arrow
  candidate.  The shared `flag` is exactly what makes the transport's rebuild via `piFormationViaGenArm` apply. -/
  | piType {scope : Nat} {context : TypingContext profile scope}
      {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
      {domainLevel codomainLevel : LevelExpr} {flag : UniverseFlag}
      {domainBox : KripkeCandBox scope} {codomainBox : KripkeCandBox (scope + 1)}
      (codomainFamily : KripkeCodFamily scope)
      (domainValid :
        TypedTypeValidityLeveled profile context domainCode domainLevel flag domainBox)
      (codomainValid :
        TypedTypeValidityLeveled profile (context.cons domainCode) codomainCode
          codomainLevel flag codomainBox)
      (validity : HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode)
        (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag)) :
      TypedTypeValidityLeveled profile context (piTyCodeCell domainCode codomainCode)
        (LevelExpr.lmax domainLevel codomainLevel) flag
        (KripkeCandBox.mk (kripkeArrowDep domainBox.run codomainFamily))

/-- **★ Universe-PRESERVING soundness: the leveled relation carries the EXACT universe-code typing.**  Unlike the
unindexed `TypedTypeValidityBoxed.toIsTypeDescPi` (which returns an existential `IsTypeDescPi`), this returns the
SPECIFIC `HasTypeDescPi context typeCode (universeCodeCell level flag)`.  That specificity is what the transport's
`piType` arm needs: it makes the rebuilt domain and codomain share the flag, so `piFormationViaGenArm` applies
(the firing-34 flag-matching obstacle, resolved). -/
theorem TypedTypeValidityLeveled.toHasTypeDescPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag} {box : KripkeCandBox scope}
    (relation : TypedTypeValidityLeveled profile context typeCode level flag box) :
    HasTypeDescPi profile context typeCode (universeCodeCell level flag) := by
  cases relation with
  | neutral _ validity => exact validity
  | universeType validity => exact validity
  | piType _ _ _ validity => exact validity

/-- **The leveled relation's existential soundness** (bridge to the unindexed shape).  Forgetting the tracked
level/flag recovers the grown validity `IsTypeDescPi`, so the leveled relation refines the unindexed one. -/
theorem TypedTypeValidityLeveled.toIsTypeDescPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag} {box : KripkeCandBox scope}
    (relation : TypedTypeValidityLeveled profile context typeCode level flag box) :
    IsTypeDescPi profile context typeCode :=
  ⟨level, flag, relation.toHasTypeDescPi⟩

/-- **Non-vacuity: the closed universe code is leveled-valid** at `(levelExpr.lsucc, flag)` — the leveled
relation's first scope-0 inhabitant, the universe-tracking twin of `smoke_closedUniverseIsBoxedTypedValid`
(`#1114`). -/
theorem smoke_closedUniverseLeveled {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    TypedTypeValidityLeveled (profile := profile)
      (TypingContext.empty : TypingContext profile 0)
      (universeCodeCell levelExpr flag) levelExpr.lsucc flag (KripkeCandBox.mk snKripkeCand) :=
  TypedTypeValidityLeveled.universeType
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation (TypingContext.empty : TypingContext profile 0) levelExpr flag))

end FX1Poly.Typed
