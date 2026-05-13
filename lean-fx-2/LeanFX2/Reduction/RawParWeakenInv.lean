import LeanFX2.Reduction.RawParWeakenInv.Foundation
import LeanFX2.Reduction.RawParWeakenInv.AtomShape1
import LeanFX2.Reduction.RawParWeakenInv.AtomShape2
import LeanFX2.Reduction.RawParWeakenInv.BinderShape
import LeanFX2.Reduction.RawParWeakenInv.CubicalShape
import LeanFX2.Reduction.RawParWeakenInv.HeadlineRenameInjInv
import LeanFX2.Reduction.RawParWeakenInv.Weaken

/-! # LeanFX2.Reduction.RawParWeakenInv — par-step weaken-image preservation (shim)

The headline `RawStep.par.weaken_inv : par X.weaken Y → ∃ Y', Y = Y'.weaken`
is proved through the more general `rename_inj_inv` for any injective
renaming `rho`, then specialized via `RawRenaming.weaken_injective`.

Carved into 7 sub-modules along the rename-shape ctor families plus
the headline induction and its specialization:

| Sub-module | Family |
| --- | --- |
| `Foundation` | `weaken_injective` + `lift_injective` |
| `AtomShape1` | refl-only atom inversions (boolTrue ... interval1) |
| `AtomShape2` | refl-only atom inversions (natSucc ... refl) |
| `BinderShape` | compound/binder inversions (modIntro ... lam) |
| `CubicalShape` | D3.6 cubical inversions (uaToEquiv ... equivCompose) |
| `HeadlineRenameInjInv` | the headline `rename_inj_inv` induction |
| `Weaken` | `weaken_inv` specialization |

## Root status

Kernel `theorem`s with bodies, zero-axiom. -/
