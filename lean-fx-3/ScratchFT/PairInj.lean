import FX1Poly.Typed.ChurchPairs
import FX1Poly.Core.ConvCongruence

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

theorem pairFst_conv_injective (a b c d : RawTerm 0)
    (hConv : Conv (pairTerm a b) (pairTerm c d)) : Conv a c :=
  Conv.trans (Conv.sym (Conv.fromStepStar (pairFst_reduces a b)))
    (Conv.trans (Conv.app_cong (Conv.refl churchFst) hConv)
      (Conv.fromStepStar (pairFst_reduces c d)))

theorem pairSnd_conv_injective (a b c d : RawTerm 0)
    (hConv : Conv (pairTerm a b) (pairTerm c d)) : Conv b d :=
  Conv.trans (Conv.sym (Conv.fromStepStar (pairSnd_reduces a b)))
    (Conv.trans (Conv.app_cong (Conv.refl churchSnd) hConv)
      (Conv.fromStepStar (pairSnd_reduces c d)))

theorem pair_conv_injective (a b c d : RawTerm 0)
    (hConv : Conv (pairTerm a b) (pairTerm c d)) : Conv a c ∧ Conv b d :=
  ⟨pairFst_conv_injective a b c d hConv, pairSnd_conv_injective a b c d hConv⟩

end FX1Poly.Typed

#print axioms FX1Poly.Typed.pairFst_conv_injective
#print axioms FX1Poly.Typed.pairSnd_conv_injective
#print axioms FX1Poly.Typed.pair_conv_injective
