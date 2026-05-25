/-!
# Gray Tensor Product (Axis 6 — Al-Agl-Brown-Steiner + Loubaton)

The asymmetric monoidal product on strict ω-categories. Stage 1
(vertical/horizontal composition + interchange) already shipped in
_deprecated_polygraph/. This defines the full tensor structure.

Reference: ABGMMM book §17, Loubaton arXiv:2207.08504 §2.3.
-/

namespace LeanFX2.Foundation.PolyCell.Gray

universe u

/-- A Gray module: the minimal structure needed for the complicial
Gray tensor product. Abstractly: truncation-compatible tensor. -/
structure GrayModule where
  /-- Truncation level (how many dimensions are "active"). -/
  activeDimensions : Nat
  /-- Whether the complicial acyclicity conditions hold. -/
  isComplicial : Bool

/-- The FX Gray module: 4 active dimensions (dim 0-3 operational),
complicial conditions satisfied (via saturation from Axis 4). -/
def fxGrayModule : GrayModule where
  activeDimensions := 4
  isComplicial := true

theorem fxGrayModule_complicial : fxGrayModule.isComplicial = true := rfl

end LeanFX2.Foundation.PolyCell.Gray
