import FX1Poly.Typed.FormerChildrenReducible
import FX1Poly.Typed.ListCodeFormationUnderSubst

/-! # FX1Poly/Typed/ListFormerMemberLevelIndexed
    — the `listCode` data-former universe-membership from the level-indexed telescope (GTL-11 FT-arm wiring)

The level-indexed analogue of `fundamentalGenFormationListFromTelescopeAtBoundedSucc` (the bounded twin) and
the data-former analogue of `FormerChildrenReducible.ofTelescopeReducible ∘ toPiMember`: from the one-child
premise telescope `TelescopeReducible flag 0 1 substitution [elementLevel] (childCons element childNil)`, the
former `List element` is a reducible member of its universe `Type@elementLevel` at `predLevel + 1`.

This is the exact reducibility content the level-indexed `genFormation` arm (`fundamentalGenFormation-
FormerLevelIndexed`) and its vector twin (`HasTypeDescPiFundamentalVectorFromFormation`) need for the
`gen_listCode` branch.  It is far simpler than the Π/Σ `toPiMember`/`toSigmaMember` reassembly: the list
former is non-dependent (a single element child), so it needs ONLY the element's strong normalization — read
off the telescope's all-level head member (`telescopeReducible.1 (predLevel + 1)`) via CR1
(`IsReducibleMemberAt.stronglyNormalizing`, at the positive level `predLevel + 1`) — and the shipped
under-substitution membership `IsReducibleMemberAt.listCodeFormationUnderSubst` (the generic
`dataFormerInUniverse` instance) closes it.  No `FormerChildrenReducible` bundle, no per-component cumulative
lift, no codomain instantiation.

## Zero-axiom verification

A single term: `listCodeFormationUnderSubst` fed the CR1 projection of the telescope head member.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **`listCode` former universe-membership from the one-child level-indexed telescope.**  From the premise
telescope over `[elementLevel]` and the one-child spine, `List element` is a reducible member of
`Type@elementLevel` at `predLevel + 1`.  The level-indexed twin of
`fundamentalGenFormationListFromTelescopeAtBoundedSucc`; the data-former analogue of
`FormerChildrenReducible.ofTelescopeReducible ∘ toPiMember`, simplified to the non-dependent one-child case
(element SN via CR1 at `predLevel + 1`, then `listCodeFormationUnderSubst`). -/
theorem IsReducibleMemberAt.listFormerFromTelescope {scope targetScope : Nat} (predLevel : Nat)
    {flag : UniverseFlag} {substitution : RawTermSubst scope (targetScope + 1)}
    {element : RawTerm scope} {elementLevel : LevelExpr}
    (telescopeReducible :
      TelescopeReducible flag 0 1 substitution [elementLevel] (.childCons element .childNil)) :
    IsReducibleMemberAt (predLevel + 1)
      (RawTerm.subst substitution (universeCodeCell elementLevel flag))
      (RawTerm.subst substitution (.mkGen .gen_listCode () (.childCons element .childNil))) :=
  IsReducibleMemberAt.listCodeFormationUnderSubst elementLevel flag substitution
    (telescopeReducible.1 (predLevel + 1)).stronglyNormalizing

end FX1Poly.Typed
