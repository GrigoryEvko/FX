import LeanFX2.Confluence.RawCd.ArrowFamily
import LeanFX2.Confluence.RawCd.ModalAndRefine
import LeanFX2.Confluence.RawCd.RecordAndCodata
import LeanFX2.Confluence.RawCd.SigmaArms
import LeanFX2.Confluence.RawCd.BoolNatArms
import LeanFX2.Confluence.RawCd.ListOptionEitherArms
import LeanFX2.Confluence.RawCd.IdentityArms
import LeanFX2.Confluence.RawCd.CubicalAndEquiv
import LeanFX2.Confluence.RawCd.Core

/-! # LeanFX2.Confluence.RawCd — parallel-reduction development (shim)

`RawTerm.cd : RawTerm scope → RawTerm scope` produces the maximal
parallel reduct of a raw term.  See sub-module docstrings for the
per-redex helper rationale.

Carved into nine sub-modules along the ctor-family axis:

| Sub-module                 | Helpers / contents                                                   |
| -------------------------- | -------------------------------------------------------------------- |
| `RawCd.ArrowFamily`        | `cdAppCase`, `cdPathAppCase`                                         |
| `RawCd.ModalAndRefine`     | `cdGlueElimCase`, `cdModElimCase`, `cdRefineElimCase`                |
| `RawCd.RecordAndCodata`    | `cdRecordProjCase`, `cdCodataDestCase`                               |
| `RawCd.SigmaArms`          | `cdFstCase`, `cdSndCase`                                             |
| `RawCd.BoolNatArms`        | `cdBoolElimCase`, `cdNatElimCase`, `cdNatRecCase`                    |
| `RawCd.ListOptionEitherArms` | `cdListElimCase`, `cdOptionMatchCase`, `cdEitherMatchCase`         |
| `RawCd.IdentityArms`       | `cdIdJCase`, `cdIdStrictRecCase`                                     |
| `RawCd.CubicalAndEquiv`    | `cdTranspCase`, `cdIdToEquivCase`, `cdUaToEquivApplyCase`, `cdEquivApplyCase` |
| `RawCd.Core`               | Main `RawTerm.cd` dispatcher                                         |

Every inner `match` in every sub-module enumerates all 55 `RawTerm`
constructors explicitly to satisfy AXIOMS.md Layer M strict-zero-axiom
policy.  Existing consumers (`Confluence.Cd`, `Confluence.RawCdLemma`,
`Confluence.RawCdRename`, `Confluence.RawCdDominates`,
`Smoke/Audit*RawCd*`) see the full set of definitions unchanged.

## Root status

Layer 2 confluence aggregator. -/
