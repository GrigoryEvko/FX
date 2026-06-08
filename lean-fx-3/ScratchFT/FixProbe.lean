import FX1Poly.Typed.CurryFixpointDivergence

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

-- innerHalf at scope 1: λx. f (x x), with f = var 1 (outer), x = var 0 (inner).
def innerHalfProbe : RawTerm 1 :=
  lamCell (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
    (appCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)) (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))))

-- fix = λf. (λx. f(xx)) (λx. f(xx))
def fixCombinatorProbe : RawTerm 0 :=
  lamCell (appCell innerHalfProbe innerHalfProbe)

-- THE KEY DEFEQ TEST: does subst0 innerHalf g compute to curryHalf g by rfl?
example (g : RawTerm 0) : RawTerm.subst0 innerHalfProbe g = curryHalf g := by rfl

-- And the full body subst:
example (g : RawTerm 0) :
    RawTerm.subst0 (appCell innerHalfProbe innerHalfProbe) g = curryOmega g := by rfl

-- The β-step appCell fix g ↝ curryOmega g (if the above rfl holds):
example (g : RawTerm 0) : Step (appCell fixCombinatorProbe g) (curryOmega g) := by
  exact Step.beta

end FX1Poly.Typed
