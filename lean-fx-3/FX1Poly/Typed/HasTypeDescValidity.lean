import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Typed.IsTypeDesc

/-! # FX1Poly/Typed/HasTypeDescValidity — INTRINSIC validity of the description engine

The description engine `HasTypeDesc` carries its OWN validity metatheorem (a.k.a.
regularity / type-correctness): the classifier of any well-typed cell is itself a
type, as seen by the engine — stated against the intrinsic `IsTypeDesc`
(`∃ levelExpr flag, HasTypeDesc Γ T (universeCodeCell levelExpr flag)`).

The canonical formation validity is

  `HasTypeDesc.classifierIsTypeDescNative` (`WfContextDescValidity.lean`)

over the native well-formedness `WfContextDesc`, whose `var` arm reads
`WfContextDesc.lookupIsTypeDesc` directly.  Consumers thread `WfContextDesc` and call
`classifierIsTypeDescNative`.

This file is the import anchor that brings the intrinsic `IsTypeDesc` predicate
(re-exported from `FX1Poly.Typed.IsTypeDesc`) into scope for the classifier-validity
consumers; the proof itself lives in `WfContextDescValidity.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

-- The intrinsic native type-predicate `IsTypeDesc` lives in `FX1Poly.Typed.IsTypeDesc`
-- (imported above).  The formation classifier-validity is `HasTypeDesc.classifierIsTypeDescNative`
-- (`WfContextDescValidity.lean`), over the native `WfContextDesc`.

end FX1Poly.Typed
