import FX1Poly.Typed.FormerChildrenReducible
import FX1Poly.Typed.OptionCodeFormationUnderSubst

/-! # FX1Poly/Typed/OptionFormerMemberLevelIndexed
    — the `optionCode` data-former universe-membership from the level-indexed telescope (GTL-13 FT-arm wiring)

The level-indexed analogue of `fundamentalGenFormationOptionFromTelescopeAtBoundedSucc` (the bounded twin) and
the one-child data-former analogue of `IsReducibleMemberAt.listFormerFromTelescope`: from the one-child premise
telescope `TelescopeReducible flag 0 1 substitution [elementLevel] (childCons element childNil)`, the former
`Option element` is a reducible member of its universe `Type@elementLevel` at `predLevel + 1`.

This is the exact reducibility content the level-indexed `genFormation` arm (`fundamentalGenFormation-
FormerLevelIndexed`) and its vector twin (`HasTypeDescPiFundamentalVectorFromFormation`) need for the
`gen_optionCode` branch.  Like the list former it is non-dependent (a single element child), so it needs ONLY the
element's strong normalization — read off the telescope's all-level head member (`telescopeReducible.1
(predLevel + 1)`) via CR1 — and the shipped under-substitution membership
`IsReducibleMemberAt.optionCodeFormationUnderSubst` (the generic `dataFormerInUniverse` instance) closes it.
Row-independent — lands ahead of the formation row.

## Zero-axiom verification

A single term: `optionCodeFormationUnderSubst` fed the CR1 projection of the telescope head member.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **`optionCode` former universe-membership from the one-child level-indexed telescope.**  From the premise
telescope over `[elementLevel]` and the one-child spine, `Option element` is a reducible member of
`Type@elementLevel` at `predLevel + 1`.  The level-indexed twin of
`fundamentalGenFormationOptionFromTelescopeAtBoundedSucc`; the one-child data-former analogue of
`IsReducibleMemberAt.listFormerFromTelescope` (element SN via CR1 at `predLevel + 1`, then
`optionCodeFormationUnderSubst`). -/
theorem IsReducibleMemberAt.optionFormerFromTelescope {scope targetScope : Nat} (predLevel : Nat)
    {flag : UniverseFlag} {substitution : RawTermSubst scope (targetScope + 1)}
    {element : RawTerm scope} {elementLevel : LevelExpr}
    (telescopeReducible :
      TelescopeReducible flag 0 1 substitution [elementLevel] (.childCons element .childNil)) :
    IsReducibleMemberAt (predLevel + 1)
      (RawTerm.subst substitution (universeCodeCell elementLevel flag))
      (RawTerm.subst substitution (.mkGen .gen_optionCode () (.childCons element .childNil))) :=
  IsReducibleMemberAt.optionCodeFormationUnderSubst elementLevel flag substitution
    (telescopeReducible.1 (predLevel + 1)).stronglyNormalizing

end FX1Poly.Typed
