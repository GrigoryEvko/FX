import LeanFX2.Tools.StrictHarness.Census.SchematicPayload
import LeanFX2.Tools.StrictHarness.Census.ModeDiscipline
import LeanFX2.Tools.StrictHarness.Census.SemanticSignature
import LeanFX2.Tools.StrictHarness.Census.BridgeCoverage
import LeanFX2.Tools.StrictHarness.Census.RichSchemaLinkage
import LeanFX2.Tools.StrictHarness.Census.ExactSnapshots
import LeanFX2.Tools.StrictHarness.Census.ValueTypeCodes

/-! # LeanFX2.Tools.StrictHarness.Census — declaration-shape census audit (shim)

| Sub-module          | Family                                                |
| ------------------- | ----------------------------------------------------- |
| SchematicPayload    | Explicit `RawTerm`/`Nat` ctor payload budget          |
| ModeDiscipline      | Strict/univalent mode-equality premise budget         |
| SemanticSignature   | Dependent-elim motive, unit placeholders, modal       |
|                     | no-op, session no-advance, equiv coherence            |
| BridgeCoverage      | `FX1Bridge.encodeTermSound_*` exact-shape ratchet     |
| RichSchemaLinkage   | Ty raw endpoints, unstructured Ty schemas, transport  |
|                     | linkage, Glue/effect/session/hcomp schema gates       |
| ExactSnapshots      | Pinned ctor-name snapshots for high-risk debt classes |
| ValueTypeCodes      | `Term.*Code` value-shaped ctor budget + snapshot      |

## Root status

Layer T audit aggregator.  Re-exports every census-style budget /
snapshot gate elaborator and helper from the sub-modules listed above.
The shim itself contains no declarations beyond imports. -/
