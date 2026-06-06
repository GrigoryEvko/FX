import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Typed.CellConstructors

/-! # FX1Poly/Typed/IsTypeDesc — the intrinsic native "is-a-type" predicate

`IsTypeDesc Γ T` says the classifier `T` inhabits SOME universe code, AS SEEN BY THE
description engine `HasTypeDesc` (`∃ levelExpr flag, HasTypeDesc Γ T (universeCodeCell
levelExpr flag)`).  It is the `HasTypeDesc`-native analogue of the bespoke `IsType`
(`∃ levelExpr flag, HasType Γ T (Type@levelExpr,flag)`), and it is the binding-typehood
witness that the native well-formedness predicate `WfContextDesc` is layered over.

## Why this lives in its own file (HT-B/HT-C cycle-break)

`IsTypeDesc` was originally defined inside `HasTypeDescValidity.lean`, alongside the
OLD bridge-routed validity `HasTypeDesc.classifierIsTypeDesc` (whose `var` arm reads
`WfContext.lookupIsType` and lifts it through `HasType.toHasTypeDesc`).  That forced
`HasTypeDescValidity.lean` — and hence everything importing it, including the native
`WfContextDesc.lean` — to transitively pull the OLD engine
(`HasTypeValidity → WfContext → HasType`).  That transitive edge is the LONE remaining
obstruction to the `WfContext := WfContextDesc` rethread: the rethread makes
`WfContext.lean` import `WfContextDesc.lean`, which would close a cycle
`WfContext → WfContextDesc → HasTypeDescValidity → HasTypeValidity → WfContext`.

The `IsTypeDesc` DEFINITION needs nothing but `HasTypeDesc` (and `universeCodeCell`).
Splitting it out lets `WfContextDesc.lean` import only THIS file — so the native
well-formedness predicate's dependency cone is `WfContext`-free
(`WfContextDesc → IsTypeDesc → HasTypeDesc`, and `HasTypeDesc.lean` imports no
`WfContext`).  The bridge-routed `classifierIsTypeDesc` stays behind in
`HasTypeDescValidity.lean` with its `HasTypeValidity` coupling — it is a rethread/HT-C
target, not part of the native predicate's cone.

## Zero-axiom verification

A single `def` (an existential over a `HasTypeDesc` derivation).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- INTRINSIC "`classifier` inhabits some universe, per the description engine":
the `HasTypeDesc` analogue of the bespoke `IsType` (`∃ levelExpr flag, HasType Γ T
(Type@levelExpr,flag)`).  Decoupled from `HasType` — depends only on `HasTypeDesc`. -/
def IsTypeDesc (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (classifier : RawTerm scope) :
    Prop :=
  ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
    HasTypeDesc profile context classifier (universeCodeCell levelExpr flag)

end FX1Poly.Typed
