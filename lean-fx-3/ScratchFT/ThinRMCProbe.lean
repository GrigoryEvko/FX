import FX1Poly.Tier0.RepresentableMapCategory
import FX1Poly.Tier0.FxRenamingCategory

/-! Scratch: (A) confirm the funext wall over the renaming category; (B) escape via a thin
    (preorder) category where Prop-morphisms make every equality free by proof irrelevance. -/

namespace FX1Poly.Tier0
open FX1Poly.Foundation

-- ============ PROBE A: funext wall over function-morphism renamings ============
-- The swap renaming on Fin 2 is a bijection; build it as a categorical iso and see what it costs.
def swap2 : RawRenaming 2 2 := fun p => ⟨1 - p.val, by omega⟩

-- Its categorical inverse-law obligation is a FUNCTION equality (compose = identity).
example : IsIsomorphism fxRenamingCategory swap2 where
  inverse := swap2
  leftInverse := by
    funext p
    fin_cases p <;> rfl
  rightInverse := by
    funext p
    fin_cases p <;> rfl

#print axioms FX1Poly.Tier0.swap2

-- ============ PROBE B: thin meet-semilattice category over (Nat, le) ============
-- Morphisms are PLift of a Prop; proof irrelevance kills every equality obligation.

-- B0: is PLift-of-Prop equality definitional (rfl)?
example (h1 h2 : (1 : Nat) ≤ 2) : (PLift.up h1 : PLift ((1:Nat) ≤ 2)) = PLift.up h2 := rfl

-- B1: Nat.min lemmas available in Init?
#check @Nat.min_le_left
#check @Nat.min_le_right
#check @Nat.le_min

end FX1Poly.Tier0
