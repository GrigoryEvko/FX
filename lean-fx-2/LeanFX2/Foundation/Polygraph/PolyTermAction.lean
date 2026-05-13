import LeanFX2.Foundation.Polygraph.PolyTermAction.RawPolyTermRename
import LeanFX2.Foundation.Polygraph.PolyTermAction.RawPolyTermSubst
import LeanFX2.Foundation.Polygraph.PolyTermAction.SubstCommute
import LeanFX2.Foundation.Polygraph.PolyTermAction.ToRawTermRename
import LeanFX2.Foundation.Polygraph.PolyTermAction.ToRawTermSubst

/-! # LeanFX2.Foundation.Polygraph.PolyTermAction — PolyTerm action framework (shim)

Carved into 5 sub-modules along the K11.13 phase axis:

| Sub-module | Family |
| --- | --- |
| `RawPolyTermRename` | Phase A: `RawPolyTerm.rename`, `weaken`, `RawTerm.rename_toRawPoly_commute` |
| `RawPolyTermSubst` | Phase B (defs): `RawPolyTermSubst`, `RawPolyTerm.subst` (73-case), `subst0` |
| `SubstCommute` | Phase B (proofs): pointwise lemmas, `RawTermSubst.toRawPolySubst`, `RawTerm.subst_toRawPoly_commute` |
| `ToRawTermRename` | Phase C-1: `RawPolyTerm.toRawTerm_rename_commute` (reverse) |
| `ToRawTermSubst` | Phase C-1S: `RawPolyTerm.toRawTerm_subst_commute` (reverse) |

## Root status

Zero-axiom. -/
