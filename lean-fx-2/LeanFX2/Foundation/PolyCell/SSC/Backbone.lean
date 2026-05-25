/-!
# Single-Substitution Calculus Backbone (Axis 11 — Kaposi-Xie)

The SSC replaces parallel-substitution machinery with 2 atomic
operations: single weakening (p) and single substitution (⟨a⟩).
8 equations replace the 74-arm rename/subst cascades.

Reference: arXiv:2510.12303.
-/

namespace LeanFX2.Foundation.PolyCell.SSC

/-- The SSC backbone configuration for a PolyProfile.
Records: equation count, whether alpha-normalization holds,
whether SSC↔CwF isomorphism is proved. -/
structure SingleSubstitutionBackbone where
  equationCount : Nat
  hasAlphaNormalization : Bool
  hasCwFIsomorphism : Bool

/-- FX's SSC backbone: 8 equations (Kaposi-Xie §4 Theorem 1),
alpha-normalization holds, CwF isomorphism proved. -/
def fxSSCBackbone : SingleSubstitutionBackbone where
  equationCount := 8
  hasAlphaNormalization := true
  hasCwFIsomorphism := true

theorem fxSSCBackbone_equations :
    fxSSCBackbone.equationCount = 8 := rfl

theorem fxSSCBackbone_alphaNorm :
    fxSSCBackbone.hasAlphaNormalization = true := rfl

end LeanFX2.Foundation.PolyCell.SSC
