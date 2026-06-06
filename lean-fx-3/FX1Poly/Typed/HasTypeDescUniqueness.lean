import FX1Poly.Typed.HasTypeDescInversion
import FX1Poly.Typed.HasTypeDescFormerTelescopeInversion
import FX1Poly.Typed.UniverseCodeConversion

/-! # FX1Poly/Typed/HasTypeDescUniqueness — uniqueness of typing (P7) for the
    description engine

polycell.md §11.8.5 P7 ("uniqueness of typing"): any two classifiers a cell receives
are convertible.  P7 disciplines the design (it makes `infer` well-defined) and is
consumed by the typechecker's conv-check and by canonicity.

The canonical uniqueness is the mutual twin

  `HasTypeDesc.uniquenessNative` / `DescTelescope.uniquenessAgreeNative`
  (`WfContextDescUniqueness.lean`)

over the native well-formedness `WfContextDesc`: the head child recurses into
`uniquenessNative` itself, and the rest-telescope recursion extends via
`WfContextDesc.cons`, whose `IsTypeDesc` binding IS the head typing directly.

This file is the import anchor that brings the formation-engine inversions
(`HasTypeDescInversion`, `HasTypeDescFormerTelescopeInversion`) into scope for the
native uniqueness twin; the proof itself lives in `WfContextDescUniqueness.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

-- The canonical uniqueness twins are `HasTypeDesc.uniquenessNative` /
-- `DescTelescope.uniquenessAgreeNative` (`WfContextDescUniqueness.lean`), over the native
-- `WfContextDesc`.

end FX1Poly.Typed
