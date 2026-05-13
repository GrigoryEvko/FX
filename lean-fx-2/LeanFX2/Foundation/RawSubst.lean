import LeanFX2.Foundation.RawSubst.RenameDefs
import LeanFX2.Foundation.RawSubst.RenameLemmas
import LeanFX2.Foundation.RawSubst.SubstDefs
import LeanFX2.Foundation.RawSubst.SubstLemmas
import LeanFX2.Foundation.RawSubst.SubstIdentityAndBeta
import LeanFX2.Foundation.RawSubst.ActionInstances

/-! # LeanFX2.Foundation.RawSubst — raw substitution algebra (shim)

Function-typed raw renamings and substitutions plus the BHKM
four-lemma ladder (RcR / ScR / RcS / ScS). Carved into six
sub-modules along definition-vs-lemma vs renaming-vs-substitution
axes; each slice is independently buildable and re-exposed here.

| Sub-module                  | Family                                                  |
| --------------------------- | ------------------------------------------------------- |
| `RawSubst.RenameDefs`       | `RawRenaming` type + ops + `RawTerm.rename` + `weaken`  |
| `RawSubst.RenameLemmas`     | Pointwise / compose / weaken-lift commute (rename-only) |
| `RawSubst.SubstDefs`        | `RawTermSubst` type + ops + `RawTerm.subst` + `subst0`  |
| `RawSubst.SubstLemmas`      | Pointwise + cross-direction + `subst_compose` (BHKM)    |
| `RawSubst.SubstIdentityAndBeta` | singleton-β, identity-subst, weaken/subst commute   |
| `RawSubst.ActionInstances`  | `Action` / `ActsOnRawTermVar*` instances + smoke decls  |

## Root status

Strict zero-axiom. Layer 0 raw-syntax foundation; all downstream
intrinsic `Term` and `Ty` substitution machinery threads through
these definitions. -/
