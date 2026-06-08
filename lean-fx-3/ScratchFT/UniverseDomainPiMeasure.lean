import FX1Poly.Typed.ClassifierLevelMeasure

/-! Scratch: the precise universe-level strict-decrease for the universe-domain-Π Adjedj recursion.
A member X : Type@e has universe level denote e; the dependent Pi Π(X:Type@e).C lives at
lmax (lsucc e) (levelC) ≥ lsucc e > e. So the domain member's level is STRICTLY below the Pi's level —
the well-founded descent the piArm recurses on. Composes denote_lt_lsucc + denote_le_lmax_left. -/

namespace FX1Poly.Typed
open FX1Poly.Universe

/-- **Universe-domain-Π member-level strict-decrease.**  The level `denote e env` of a member of `Type@e`
is strictly below the level `denote (lmax (lsucc e) levelC) env` of the dependent function type
`Π (X : Type@e). C` (whose level combines `lsucc e` for the universe domain with the codomain level
`levelC`).  This is the well-founded measure-decrease the universe-domain `piArm` descends on: the domain
members are strictly smaller by universe level, so their level-irrelevance is the induction hypothesis. -/
theorem denote_lt_lmax_lsucc_left (e levelC : LevelExpr) (env : Nat → Nat) :
    LevelExpr.denote e env < LevelExpr.denote (LevelExpr.lmax e.lsucc levelC) env :=
  Nat.lt_of_lt_of_le (denote_lt_lsucc e env) (denote_le_lmax_left e.lsucc levelC env)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.denote_lt_lmax_lsucc_left
