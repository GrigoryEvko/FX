import FX1Poly.Typed.FundamentalAtAllVectorPremises
import FX1Poly.Typed.UniverseCodeShape

/-! # FX1Poly/Typed/FormationEngineFundamental
    — the formation-engine fundamental theorem, arm by arm (#674; the SN-027 Kripke residual)

The Kripke route reduces SN-027 (`HasTypeDescPi → reducible / SN`) to a SINGLE obligation
(`FormationEngineFundamentalReduction.lean`): the formation-engine fundamental theorem

```
formationFundamental :
  ∀ {scope context subject classifier},
    HasTypeDesc profile context subject classifier → IsFundamentalConclusionAtVector context subject classifier
```

`HasTypeDesc` is the four-constructor formation sub-engine — `var` / `conv` / `universeFormation` /
`genFormation` — with NO `piIntro` / `piElim`.  This file assembles `formationFundamental` arm by arm; each arm
is a standalone theorem so it can be gated and reviewed independently, and the final assembly is one `induction`.

Unlike the refined-motive-via-`ValidTyping` route (whose conjunct-2 is provably unsatisfiable for type variables,
`ValidTypingVariableLevelPinned.lean`), the conclusion here is the REDUCIBILITY-keyed
`IsFundamentalConclusionAtVector` (`IsReducibleMemberAt`), so the `var` arm reads the environment
(`ReducibleEnvVec.lookupReducible`) rather than pinning a `ValidTyping` level — no wall.

## What is proved (so far)

* `formationFundamentalUniverseFormationArm` — the `universeFormation` arm: `Type@e` is a reducible member of
  `Type@(lsucc e)` at every positive level.  The universe code is closed (no children, no binders), so `subst`
  is the identity and the arm is `IsReducibleMemberAt.universeFormation` under the substitution — independent of
  the environment-level vector.

## Zero-axiom verification

`subst_universeCodeCell` (a `rfl`-grade rewrite) plus `IsReducibleMemberAt.universeFormation` (the shipped
universe-candidate non-degeneracy, SN-037).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- **The `universeFormation` arm of the formation-engine FT.**  `universeCodeCell levelExpr flag`
(i.e. `Type@levelExpr[flag]`) is a reducible member of `universeCodeCell levelExpr.lsucc flag` at every requested
positive conclusion level `predLevel + 1`.  The universe code is closed, so the closing substitution acts as the
identity on both subject and classifier (`subst_universeCodeCell`), and the membership is exactly
`IsReducibleMemberAt.universeFormation` — independent of the environment-level vector, so it holds at the
arbitrary-vector conclusion shape. -/
theorem formationFundamentalUniverseFormationArm {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsFundamentalConclusionAtVector context
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag) := by
  intro _targetScope substitution _envLevels predLevel _env
  rw [subst_universeCodeCell, subst_universeCodeCell]
  exact IsReducibleMemberAt.universeFormation predLevel levelExpr flag

end FX1Poly.Typed
