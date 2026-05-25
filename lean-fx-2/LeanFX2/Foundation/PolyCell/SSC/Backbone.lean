/-!
# Single-Substitution Calculus Backbone (Axis 11 — Kaposi-Xie)

The target SSC presentation uses 2 atomic operations: single weakening (p)
and single substitution (⟨a⟩).  The intended 8 equations are recorded here
only as a count; this file does not yet formalize the equations or replace
the existing rename/subst machinery.

Reference: arXiv:2510.12303.
-/

namespace LeanFX2.Foundation.PolyCell.SSC

/-- How much of Axis 11 has actually been constructed.

The current PolyCell scaffold records the intended eight-equation arity, but
does not yet provide the equations, alpha-normalization algorithm, or the
SSC/CwF isomorphism theorem. -/
inductive SSCConstructionLevel where
  /-- Only the intended equation count is recorded. -/
  | equationCountOnly
  /-- The eight single-substitution equations have been formalized. -/
  | equationsPresented
  /-- Alpha-normalization is available with its correctness theorem. -/
  | alphaNormalization
  /-- The SSC/CwF isomorphism theorem is available. -/
  | cwfIsomorphism
  deriving DecidableEq, Repr

/-- Whether this Axis 11 level includes formalized SSC equations. -/
def SSCConstructionLevel.hasEquations : SSCConstructionLevel → Bool
  | .equationCountOnly => false
  | .equationsPresented => true
  | .alphaNormalization => true
  | .cwfIsomorphism => true

/-- Whether this Axis 11 level includes alpha-normalization. -/
def SSCConstructionLevel.hasAlphaNormalization : SSCConstructionLevel → Bool
  | .equationCountOnly => false
  | .equationsPresented => false
  | .alphaNormalization => true
  | .cwfIsomorphism => true

/-- Whether this Axis 11 level includes the SSC/CwF isomorphism theorem. -/
def SSCConstructionLevel.hasCwfIsomorphism : SSCConstructionLevel → Bool
  | .equationCountOnly => false
  | .equationsPresented => false
  | .alphaNormalization => false
  | .cwfIsomorphism => true

/-- The SSC backbone configuration for a PolyProfile.
Records the intended equation count plus an explicit construction ledger. -/
structure SingleSubstitutionBackbone where
  equationCount : Nat
  constructionLevel : SSCConstructionLevel

/-- FX's SSC backbone currently records the target eight equations, but the
equations and metatheorems are not formalized in this file. -/
def fxSSCBackbone : SingleSubstitutionBackbone where
  equationCount := 8
  constructionLevel := .equationCountOnly

theorem fxSSCBackbone_equationCount :
    fxSSCBackbone.equationCount = 8 := rfl

/-- FX SSC currently has only an equation-count ledger. -/
theorem fxSSCBackbone_constructionLevel :
    fxSSCBackbone.constructionLevel =
      SSCConstructionLevel.equationCountOnly := rfl

/-- FX SSC currently has no formalized eight-equation presentation. -/
theorem fxSSCBackbone_hasNoEquations :
    fxSSCBackbone.constructionLevel.hasEquations = false := rfl

/-- FX SSC currently has no alpha-normalization theorem. -/
theorem fxSSCBackbone_hasNoAlphaNormalization :
    fxSSCBackbone.constructionLevel.hasAlphaNormalization = false := rfl

/-- FX SSC currently has no SSC/CwF isomorphism theorem. -/
theorem fxSSCBackbone_hasNoCwfIsomorphism :
    fxSSCBackbone.constructionLevel.hasCwfIsomorphism = false := rfl

end LeanFX2.Foundation.PolyCell.SSC
