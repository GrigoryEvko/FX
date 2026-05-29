import FX1Poly.Core.RawTermStrengthen
import FX1Poly.Core.StructuralInductionPrimitives

/-! # Foundation/PolyCell/Core/RawTermFresh

Small freshness lemmas for the raw eta cascade.

`RawTerm.isFreshFor rho sigma term` means `sigma` drops some ambient
variable and `rho` injects the result back, reconstructing the original
term.  The concrete eta use case is `sigma = singleton unit` and
`rho = weaken`, while child positions use lifted variants of both.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- A raw term is fresh for a substitution/renaming retraction when
substituting and then renaming back reconstructs the original term.

The eta freshness specialization uses `rawSubstitution = singleton unit`
and `rawRenaming = weaken`, but keeping the predicate general lets the
step-preservation proof recurse uniformly under child binders by lifting
both operations. -/
def RawTerm.isFreshFor {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming targetScope sourceScope)
    (rawSubstitution : RawTermSubst sourceScope targetScope)
    (sourceTerm : RawTerm sourceScope) : Prop :=
  RawTerm.rename rawRenaming (RawTerm.subst rawSubstitution sourceTerm) =
    sourceTerm

/-- Children-spine sibling of `RawTerm.isFreshFor`. -/
def RawTermChildren.isFreshFor {sourceScope targetScope : Nat}
    {binderShifts : List Nat}
    (rawRenaming : RawRenaming targetScope sourceScope)
    (rawSubstitution : RawTermSubst sourceScope targetScope)
    (sourceChildren : RawTermChildren binderShifts sourceScope) : Prop :=
  RawTermChildren.rename rawRenaming
      (RawTermChildren.subst rawSubstitution sourceChildren) =
    sourceChildren

/-- The empty child spine is always fresh. -/
theorem RawTermChildren.childNil_isFreshFor
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming targetScope sourceScope)
    (rawSubstitution : RawTermSubst sourceScope targetScope) :
    RawTermChildren.isFreshFor rawRenaming rawSubstitution
      (.childNil : RawTermChildren [] sourceScope) := by
  rfl

/-- Extract child-spine freshness from a fresh non-variable term. -/
theorem RawTermChildren.isFreshFor_of_nonVarTerm_isFreshFor
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming targetScope sourceScope)
    (rawSubstitution : RawTermSubst sourceScope targetScope)
    {generator : Generator} (hNotVar : generator ≠ .gen_var)
    (payload : generator.payload sourceScope)
    (sourceChildren : RawTermChildren generator.binderShifts sourceScope)
    (termFresh :
      RawTerm.isFreshFor rawRenaming rawSubstitution
        (.mkGen generator payload sourceChildren)) :
    RawTermChildren.isFreshFor rawRenaming rawSubstitution
      sourceChildren := by
  unfold RawTerm.isFreshFor at termFresh
  unfold RawTermChildren.isFreshFor
  rw [RawTerm.subst_nonVar_reduces rawSubstitution hNotVar payload
    sourceChildren] at termFresh
  rw [RawTerm.rename_nonVar_reduces rawRenaming hNotVar] at termFresh
  rw [RawTermChildren.subst_eq_foldChildren rawSubstitution sourceChildren]
  rw [RawTermChildren.rename_eq_foldChildren rawRenaming
    (foldChildren GenAlgebra.canonical rawSubstitution sourceChildren)]
  injection termFresh

/-- Rebuild freshness for a non-variable term from freshness of its
children spine. -/
theorem RawTerm.isFreshFor_nonVar_of_children_isFreshFor
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming targetScope sourceScope)
    (rawSubstitution : RawTermSubst sourceScope targetScope)
    {generator : Generator} (hNotVar : generator ≠ .gen_var)
    (payload : generator.payload sourceScope)
    (sourceChildren : RawTermChildren generator.binderShifts sourceScope)
    (childrenFresh :
      RawTermChildren.isFreshFor rawRenaming rawSubstitution
        sourceChildren) :
    RawTerm.isFreshFor rawRenaming rawSubstitution
      (.mkGen generator payload sourceChildren) := by
  unfold RawTerm.isFreshFor
  unfold RawTermChildren.isFreshFor at childrenFresh
  rw [RawTerm.subst_nonVar_reduces rawSubstitution hNotVar payload
    sourceChildren]
  rw [RawTerm.rename_nonVar_reduces rawRenaming hNotVar]
  rw [RawTermChildren.subst_eq_foldChildren rawSubstitution sourceChildren]
    at childrenFresh
  rw [RawTermChildren.rename_eq_foldChildren rawRenaming
    (foldChildren GenAlgebra.canonical rawSubstitution sourceChildren)]
    at childrenFresh
  rw [childrenFresh]
  cases generator <;> try rfl
  exact absurd rfl hNotVar

/-- The head of a fresh child spine is fresh under the lifted
substitution/renaming pair for that child position. -/
theorem RawTermChildren.head_isFreshFor_of_childCons_isFreshFor
    {sourceScope targetScope headShift : Nat} {restShifts : List Nat}
    (rawRenaming : RawRenaming targetScope sourceScope)
    (rawSubstitution : RawTermSubst sourceScope targetScope)
    (headTerm : RawTerm (sourceScope + headShift))
    (tailChildren : RawTermChildren restShifts sourceScope)
    (childrenFresh :
      RawTermChildren.isFreshFor rawRenaming rawSubstitution
        (RawTermChildren.childCons headTerm tailChildren)) :
    RawTerm.isFreshFor (iterateLiftRaw rawRenaming headShift)
      (iterateLiftRaw rawSubstitution headShift) headTerm := by
  unfold RawTermChildren.isFreshFor at childrenFresh
  unfold RawTerm.isFreshFor
  show RawTerm.rename (iterateLiftRaw rawRenaming headShift)
        (RawTerm.subst (iterateLiftRaw rawSubstitution headShift)
          headTerm) = headTerm
  injection childrenFresh

/-- The tail of a fresh child spine is fresh for the original
substitution/renaming pair. -/
theorem RawTermChildren.tail_isFreshFor_of_childCons_isFreshFor
    {sourceScope targetScope headShift : Nat} {restShifts : List Nat}
    (rawRenaming : RawRenaming targetScope sourceScope)
    (rawSubstitution : RawTermSubst sourceScope targetScope)
    (headTerm : RawTerm (sourceScope + headShift))
    (tailChildren : RawTermChildren restShifts sourceScope)
    (childrenFresh :
      RawTermChildren.isFreshFor rawRenaming rawSubstitution
        (RawTermChildren.childCons headTerm tailChildren)) :
    RawTermChildren.isFreshFor rawRenaming rawSubstitution
      tailChildren := by
  unfold RawTermChildren.isFreshFor at childrenFresh
  unfold RawTermChildren.isFreshFor
  show RawTermChildren.rename rawRenaming
        (RawTermChildren.subst rawSubstitution tailChildren) =
      tailChildren
  injection childrenFresh

/-- Construct freshness for a child spine from freshness of the head and
tail. -/
theorem RawTermChildren.childCons_isFreshFor
    {sourceScope targetScope headShift : Nat} {restShifts : List Nat}
    (rawRenaming : RawRenaming targetScope sourceScope)
    (rawSubstitution : RawTermSubst sourceScope targetScope)
    (headTerm : RawTerm (sourceScope + headShift))
    (tailChildren : RawTermChildren restShifts sourceScope)
    (headFresh :
      RawTerm.isFreshFor (iterateLiftRaw rawRenaming headShift)
        (iterateLiftRaw rawSubstitution headShift) headTerm)
    (tailFresh :
      RawTermChildren.isFreshFor rawRenaming rawSubstitution
        tailChildren) :
    RawTermChildren.isFreshFor rawRenaming rawSubstitution
      (RawTermChildren.childCons headTerm tailChildren) := by
  unfold RawTerm.isFreshFor at headFresh
  unfold RawTermChildren.isFreshFor at tailFresh
  unfold RawTermChildren.isFreshFor
  show RawTermChildren.childCons
        (RawTerm.rename (iterateLiftRaw rawRenaming headShift)
          (RawTerm.subst (iterateLiftRaw rawSubstitution headShift)
            headTerm))
        (RawTermChildren.rename rawRenaming
          (RawTermChildren.subst rawSubstitution tailChildren)) =
      RawTermChildren.childCons headTerm tailChildren
  rw [headFresh, tailFresh]

/-- A one-child spine is fresh when its head is fresh under the lifted
substitution/renaming pair for that child position. -/
theorem RawTermChildren.single_isFreshFor
    {sourceScope targetScope headShift : Nat}
    (rawRenaming : RawRenaming targetScope sourceScope)
    (rawSubstitution : RawTermSubst sourceScope targetScope)
    (headTerm : RawTerm (sourceScope + headShift))
    (headFresh :
      RawTerm.isFreshFor (iterateLiftRaw rawRenaming headShift)
        (iterateLiftRaw rawSubstitution headShift) headTerm) :
    RawTermChildren.isFreshFor rawRenaming rawSubstitution
      (RawTermChildren.childCons headTerm .childNil) :=
  RawTermChildren.childCons_isFreshFor rawRenaming rawSubstitution
    headTerm .childNil headFresh
    (RawTermChildren.childNil_isFreshFor rawRenaming rawSubstitution)

/-- A two-child spine is fresh when both children are fresh under their
position-specific lifted substitution/renaming pairs. -/
theorem RawTermChildren.double_isFreshFor
    {sourceScope targetScope firstShift secondShift : Nat}
    (rawRenaming : RawRenaming targetScope sourceScope)
    (rawSubstitution : RawTermSubst sourceScope targetScope)
    (firstTerm : RawTerm (sourceScope + firstShift))
    (secondTerm : RawTerm (sourceScope + secondShift))
    (firstFresh :
      RawTerm.isFreshFor (iterateLiftRaw rawRenaming firstShift)
        (iterateLiftRaw rawSubstitution firstShift) firstTerm)
    (secondFresh :
      RawTerm.isFreshFor (iterateLiftRaw rawRenaming secondShift)
        (iterateLiftRaw rawSubstitution secondShift) secondTerm) :
    RawTermChildren.isFreshFor rawRenaming rawSubstitution
      (RawTermChildren.childCons firstTerm
        (RawTermChildren.childCons secondTerm .childNil)) :=
  RawTermChildren.childCons_isFreshFor rawRenaming rawSubstitution
    firstTerm (RawTermChildren.childCons secondTerm .childNil)
    firstFresh
    (RawTermChildren.single_isFreshFor rawRenaming rawSubstitution
      secondTerm secondFresh)

/-- A three-child spine is fresh when every child is fresh under its
position-specific lifted substitution/renaming pair. -/
theorem RawTermChildren.triple_isFreshFor
    {sourceScope targetScope firstShift secondShift thirdShift : Nat}
    (rawRenaming : RawRenaming targetScope sourceScope)
    (rawSubstitution : RawTermSubst sourceScope targetScope)
    (firstTerm : RawTerm (sourceScope + firstShift))
    (secondTerm : RawTerm (sourceScope + secondShift))
    (thirdTerm : RawTerm (sourceScope + thirdShift))
    (firstFresh :
      RawTerm.isFreshFor (iterateLiftRaw rawRenaming firstShift)
        (iterateLiftRaw rawSubstitution firstShift) firstTerm)
    (secondFresh :
      RawTerm.isFreshFor (iterateLiftRaw rawRenaming secondShift)
        (iterateLiftRaw rawSubstitution secondShift) secondTerm)
    (thirdFresh :
      RawTerm.isFreshFor (iterateLiftRaw rawRenaming thirdShift)
        (iterateLiftRaw rawSubstitution thirdShift) thirdTerm) :
    RawTermChildren.isFreshFor rawRenaming rawSubstitution
      (RawTermChildren.childCons firstTerm
        (RawTermChildren.childCons secondTerm
          (RawTermChildren.childCons thirdTerm .childNil))) :=
  RawTermChildren.childCons_isFreshFor rawRenaming rawSubstitution
    firstTerm
    (RawTermChildren.childCons secondTerm
      (RawTermChildren.childCons thirdTerm .childNil))
    firstFresh
    (RawTermChildren.double_isFreshFor rawRenaming rawSubstitution
      secondTerm thirdTerm secondFresh thirdFresh)

/-- Renaming distributes over single-variable beta substitution. -/
theorem RawTerm.rename_subst0_commute {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (body : RawTerm (sourceScope + 1)) (rawArg : RawTerm sourceScope) :
    RawTerm.rename rawRenaming (RawTerm.subst0 body rawArg) =
      RawTerm.subst0
        (RawTerm.rename (RawRenaming.lift rawRenaming) body)
        (RawTerm.rename rawRenaming rawArg) := by
  unfold RawTerm.subst0
  rw [RawTerm.subst_rename_commute]
  rw [RawTerm.rename_subst_commute]
  apply RawTerm.subst_pointwise
  intro position
  cases position with
  | mk positionValue positionBound =>
      cases positionValue with
      | zero => rfl
      | succ _priorPositionValue => rfl

/-- Freshness for the canonical newest-variable drop gives the concrete
strengthening result. -/
theorem RawTerm.strengthen_eq_subst_of_isFreshFor_singleton {scope : Nat}
    (rawArg : RawTerm scope) (sourceTerm : RawTerm (scope + 1))
    (termFresh :
      RawTerm.isFreshFor RawRenaming.weaken
        (RawTermSubst.singleton rawArg) sourceTerm) :
    RawTerm.strengthen sourceTerm =
      some (RawTerm.subst (RawTermSubst.singleton rawArg) sourceTerm) := by
  unfold RawTerm.isFreshFor at termFresh
  let extractedTerm := RawTerm.subst (RawTermSubst.singleton rawArg) sourceTerm
  have sourceEq : RawTerm.weaken extractedTerm = sourceTerm := by
    unfold extractedTerm
    rw [RawTerm.weaken_eq_rename]
    exact termFresh
  rw [← sourceEq]
  unfold extractedTerm
  rw [RawTerm.weaken_subst_singleton]
  exact RawTerm.strengthen_weaken
    (RawTerm.subst (RawTermSubst.singleton rawArg) sourceTerm)

end FX1Poly.Core
