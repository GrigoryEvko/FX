import FX1PolyAudit.AuditGen
-- Sink files of the foundational term-substrate slice (importing these
-- transitively loads every migrated FX1Poly.Core declaration).
import FX1Poly.Core.AbstractTermSpine
import FX1Poly.Core.CheckResult
import FX1Poly.Core.ConsistencyStrength
import FX1Poly.Core.CoreFxProfile
import FX1Poly.Core.FoldShiftGreaterThanOne
import FX1Poly.Core.GenPayloadEvidence
import FX1Poly.Core.GeneratorChildSpecsDim0
import FX1Poly.Core.GeneratorTotalityClass
import FX1Poly.Core.HasEqualDim
import FX1Poly.Core.RawCellCascadeLaws
import FX1Poly.Core.RawCellCode
import FX1Poly.Core.RawTermSubstAction
import FX1Poly.Core.RuleSpec
import FX1Poly.Core.SiteOpenness
import FX1Poly.Core.SpikeDimTransport
import FX1Poly.Core.StepEta
import FX1Poly.Core.StepInversion

/-! # FX1PolyAudit/AuditCoreSubstrate — namespace zero-axiom sweep

Persistent zero-axiom gate for the foundational term-substrate slice
migrated out of lean-fx-2's `Foundation/PolyCell/Core`:

* Generator substrate: `GeneratorCore` / `GeneratorMetadata` /
  `GeneratorAdmission` / `GenPayloadEvidence` / `GeneratorTotalityClass` /
  `GeneratorChildSpecsDim0` / `AbstractTermSpine` / `CoreFxProfile`.
* Cell-shape vocabulary: `RuleSpec` / `CheckResult` /
  `ConsistencyStrength` / `SiteOpenness` / `SpikeDimTransport` /
  `HasEqualDim`.
* `RawTerm` + the full rename/subst commute ladder
  (`RawTermSubstDefs` / `GenAlgebra` / `Fold` / `LiftsRaw` /
  `RawTermRename*` / `RawTermSubst*` / `RawTermStrengthen` / …).
* `RawCell` + `RawSize` / `RawCellDecEq` / `RawCellCode` /
  `RawCellRenameSubst` / `RawCellCascadeLaws`.
* Reduction leaves: `Step` / `StepStar` / `StepInversion` / `StepEta`.

The `#audit_namespace` sweep walks EVERY loaded declaration under the
namespace and fails the build at the first axiom leak — so this single
gate auto-covers all ~430 migrated declarations and every future Core
slice without a hand-maintained per-decl list.  It also re-checks the
native infra under `FX1Poly.Foundation`.
-/

#audit_namespace FX1Poly.Core
#audit_namespace FX1Poly.Foundation
