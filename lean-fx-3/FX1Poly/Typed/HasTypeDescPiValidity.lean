import FX1Poly.Typed.HasTypeDescPiApplication

/-! # FX1Poly/Typed/HasTypeDescPiValidity — grown classifier-validity import anchor

Grown classifier-validity (every classifier of a `HasTypeDescPi`-typed cell is itself a grown type
`IsTypeDescPi`) is `HasTypeDescPi.classifierIsTypeDescPi` (`HasTypeDescPiClassifierValidity.lean`), which
threads the GROWN well-formedness `WfContextDescPi` (extendable at a grown `piIntro` binder via
`WfContextDescPi.cons`).

This file is an import anchor: it re-exports the upstream engine output-validity lemma
`HasTypeDescPi.piCodeInstantiationIsType` (`HasTypeDescPiApplication.lean`) for downstream files that
import this module by name.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

end FX1Poly.Typed
