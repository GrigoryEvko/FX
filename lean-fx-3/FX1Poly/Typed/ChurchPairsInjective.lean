import FX1Poly.Typed.ChurchPairs
import FX1Poly.Core.ConvCongruence

/-! # FX1Poly/Typed/ChurchPairsInjective — the Church pair is injective up to conversion

`ChurchPairs` (#1017) showed the Church pair RECOVERS both stored components (`fst (pair a b) ↝* a`,
`snd (pair a b) ↝* b`).  This file proves the complementary faithfulness fact — the pair INJECTIVELY DISTINGUISHES
its components:

  **`pair_conv_injective` (★)** — `Conv (pair a b) (pair c d) → Conv a c ∧ Conv b d`.  Convertible pairs have
  convertible components.  The argument is purely the projections plus `Conv`-congruence: applying `fst` to both
  sides of `Conv (pair a b) (pair c d)` (via `Conv.app_cong`) gives `Conv (fst (pair a b)) (fst (pair c d))`, and
  since `fst (pair a b) ↝* a` and `fst (pair c d) ↝* c`, transitivity yields `Conv a c`; `snd` gives `Conv b d`.

Together with `pairProjectionsRecover` (#1017), the Church pair is a FAITHFUL product encoding: it stores both
components, recovers each, and never conflates distinct (up to `Conv`) component data.  This is exactly the
universal-property content of a product realized syntactically in the pure Π-fragment.

Everything is the raw `Conv` relation; no typing derivation is consulted.

## Zero-axiom verification

Each direction is `Conv.trans`/`Conv.sym` over two `Conv.fromStepStar` reductions (the projections, #1017) and one
`Conv.app_cong` congruence (`ConvCongruence.lean`) with `Conv.refl` on the unchanged projector.  No `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-decl in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

/-- **First-component injectivity.**  Convertible pairs have convertible first components: applying `fst` to both
sides of `Conv (pair a b) (pair c d)` and reducing (`pairFst_reduces`) collapses to `Conv a c`. -/
theorem pairFst_conv_injective (a b c d : RawTerm 0)
    (hConv : Conv (pairTerm a b) (pairTerm c d)) : Conv a c :=
  Conv.trans (Conv.sym (Conv.fromStepStar (pairFst_reduces a b)))
    (Conv.trans (Conv.app_cong (Conv.refl churchFst) hConv)
      (Conv.fromStepStar (pairFst_reduces c d)))

/-- **Second-component injectivity.**  The `snd` dual of `pairFst_conv_injective`: convertible pairs have
convertible second components. -/
theorem pairSnd_conv_injective (a b c d : RawTerm 0)
    (hConv : Conv (pairTerm a b) (pairTerm c d)) : Conv b d :=
  Conv.trans (Conv.sym (Conv.fromStepStar (pairSnd_reduces a b)))
    (Conv.trans (Conv.app_cong (Conv.refl churchSnd) hConv)
      (Conv.fromStepStar (pairSnd_reduces c d)))

/-- ★ **The Church pair is injective up to conversion.**  `Conv (pair a b) (pair c d) → Conv a c ∧ Conv b d` —
convertible pairs have convertible components.  Together with `pairProjectionsRecover` (#1017), the Church pair is
a FAITHFUL product encoding: it stores both components, recovers each, and never conflates distinct component
data — the universal property of a product, realized syntactically in the pure Π-fragment. -/
theorem pair_conv_injective (a b c d : RawTerm 0)
    (hConv : Conv (pairTerm a b) (pairTerm c d)) : Conv a c ∧ Conv b d :=
  ⟨pairFst_conv_injective a b c d hConv, pairSnd_conv_injective a b c d hConv⟩

end FX1Poly.Typed
