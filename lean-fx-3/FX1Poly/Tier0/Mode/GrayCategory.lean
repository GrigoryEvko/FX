import FX1Poly.Polygraph.TwoCategory.GrayCategory
import FX1Poly.Tier0.Mode.TwoCategoryCore

/-! # mode-5 — the free mode 1-category as a (strict) Gray-category (the dim-3 rung)

The GENERIC Gray-category / semistrict-3-category core — the two whisker-order 2-cells the interchanger mediates
(`RawTwoCategory.interchangeSource` / `interchangeTarget`), the `RawGrayCategory` interface with its invertible
INTERCHANGER 3-cell, the `locallyDiscreteGrayCategory` realizing instance, and the honesty markers — now lives in
`FX1Poly.Polygraph.TwoCategory.GrayCategory` (the kernel's zero-dependency pure-category-theory library).

This file is the mode-axis specialisation: the free mode 1-category (`mode-1`) exhibited as a (strict,
locally-discrete) Gray-category — the mode axis reaching dimension 3.

Zero external dependencies beyond the Gray-category core + the `mode-1` free category.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-- ★ The free mode 1-category, exhibited as a (strict, locally-discrete) Gray-category — the mode axis
reaching dimension 3. -/
def freeModeGrayCategory (graph : ModeGraph) : RawGrayCategory :=
  locallyDiscreteGrayCategory (freeModeCategory graph)

/-- Round-trip: the free mode Gray-category's base 2-category IS the free mode 2-category, definitionally. -/
theorem freeModeGrayCategory_twoCategory (graph : ModeGraph) :
    (freeModeGrayCategory graph).twoCategory = freeModeTwoCategory graph :=
  rfl

end FX1Poly.Tier0
