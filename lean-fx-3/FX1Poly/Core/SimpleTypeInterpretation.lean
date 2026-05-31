import FX1Poly.Core.HeadExpansionClosure

/-! # Foundation/PolyCell/Core/SimpleTypeInterpretation
    — the simple-type reducibility interpretation `Red : SimpleType → candidate`

Strong normalization of the grown Π-fragment factors through the **simple-type skeleton**:
β-reduction ignores type dependency, so SN of a well-typed term follows from reducibility at the
*erased* simple type.  This file defines that skeleton and the Tait reducibility interpretation

  `Red base            = IsStronglyNormalizing`   (base/atomic types ↦ the SN candidate)
  `Red (arrow dom cod) = IsArrowReducible (Red dom) (Red cod)`   (Π ↦ the function-space candidate)

and proves the first of the two properties the fundamental theorem combines:

* `Red_headExpansionClosed` — every interpreted type is head-expansion-closed, by induction on the
  simple type (SN base case + the arrow former's preservation).

The companion property — every `Red T` is a reducibility candidate (which feeds the variable case
and the `Red ⟹ SN` corollary) — is the next brick; it needs a `Red`-reducible witness at every type
(the closed constant-function construction) and the `subst0 (weaken t) a = t` cancellation lemma.

## Zero-axiom verification

A plain inductive + a structural recursive `def` + a two-case induction discharging to the shipped
closure theorems.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- Simple types — the erasure skeleton of the grown Π-fragment: a base sort and arrows. -/
inductive SimpleType : Type where
  | base : SimpleType
  | arrow : SimpleType → SimpleType → SimpleType

/-- The Tait reducibility interpretation: base ↦ the SN candidate, arrow ↦ the function-space
candidate `IsArrowReducible`.  Structural recursion on the simple type. -/
def Red {scope : Nat} : SimpleType → RawTerm scope → Prop
  | .base => IsStronglyNormalizing
  | .arrow domain codomain => IsArrowReducible (Red domain) (Red codomain)

/-- Every interpreted type is head-expansion-closed.  Induction on the simple type: the base case is
the SN candidate's closure (`isStronglyNormalizing_headExpansionClosed`), the arrow case is the
former's preservation (`isArrowReducible_headExpansionClosed`).  One of the two ingredients the
fundamental theorem's λ case combines. -/
theorem Red_headExpansionClosed {scope : Nat} (simpleType : SimpleType) :
    HeadExpansionClosed (Red (scope := scope) simpleType) := by
  induction simpleType with
  | base => exact isStronglyNormalizing_headExpansionClosed
  | arrow domain codomain _domainClosed codomainClosed =>
      show HeadExpansionClosed (IsArrowReducible (Red domain) (Red codomain))
      exact isArrowReducible_headExpansionClosed codomainClosed

end FX1Poly.Core
