import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Typed.CellConstructors

/-! # FX1Poly/Typed/IsTypeDesc — the intrinsic native "is-a-type" predicate

`IsTypeDesc Γ T` says the classifier `T` inhabits SOME universe code, AS SEEN BY THE
description engine `HasTypeDesc` (`∃ levelExpr flag, HasTypeDesc Γ T (universeCodeCell
levelExpr flag)`).  It is the binding-typehood witness that the native well-formedness
predicate `WfContextDesc` is layered over.

## Why this lives in its own file

The `IsTypeDesc` DEFINITION needs nothing but `HasTypeDesc` (and `universeCodeCell`).
Keeping it here lets `WfContextDesc.lean` import only THIS file, so the native
well-formedness predicate's dependency cone is exactly
`WfContextDesc -> IsTypeDesc -> HasTypeDesc`.

## Zero-axiom verification

A single `def` (an existential over a `HasTypeDesc` derivation).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- INTRINSIC "`classifier` inhabits some universe, per the description engine":
`∃ levelExpr flag, HasTypeDesc Γ T (universeCodeCell levelExpr flag)`.  Depends only
on `HasTypeDesc`. -/
def IsTypeDesc (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (classifier : RawTerm scope) :
    Prop :=
  ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
    HasTypeDesc profile context classifier (universeCodeCell levelExpr flag)

end FX1Poly.Typed
