import FX1Poly.Core.RawTermSubstPointwise
import FX1Poly.Core.RawTermWeaken
import FX1Poly.Core.StructuralInductionPrimitives

/-! # FX1Poly/Core/RawTermRenameAsSubst — rename IS subst at the variable injection

The classical sigma-calculus factoring: a renaming `rho` acts on terms
exactly like the substitution sending every position to the renamed
VARIABLE (`fun position => gen_var (rho position)`).  Mechanized
funext-free: the two Containers agree only POINTWISE through binder
lifts, so the bridge routes through the Allais extensionality theorem
(`RawTerm.subst_pointwise`) instead of rewriting one function into the
other.

Payoff: every substitution-closure theorem yields its rename-closure
sibling as a one-line corollary (`StepOverTable.rename` from
`StepOverTable.subst`) — no second fold induction per relation.

## Zero-axiom verification

Direct `⟨0, _⟩` / `⟨k + 1, h⟩` Fin matching (no `Fin.cases` — it pulls
`propext`), `rfl` on the fold engine's variable dispatch (concrete
`gen_var` head reduces the `DecidableEq` dite), and the shipped
pointwise machinery.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Gated per declaration in
`FX1PolyAudit/AuditIotaTableEquivariance.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- Inject a renaming into a substitution: every position maps to the
renamed variable, as a term. -/
@[reducible] def RawTermSubst.ofRenaming {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope) :
    RawTermSubst sourceScope targetScope :=
  fun position => .mkGen .gen_var (someRenaming position) .childNil

/-- One binder lift commutes with the injection, pointwise: position 0
maps to the fresh variable on both sides; position `k + 1` weakens a
variable term on the left and injects a lifted-renaming image on the
right — the same variable term, definitionally. -/
theorem RawTermSubst.ofRenaming_lift_pointwise
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope) :
    RawTermSubst.PointwiseEq
      (RawTermSubst.lift (RawTermSubst.ofRenaming someRenaming))
      (RawTermSubst.ofRenaming (RawRenaming.lift someRenaming)) := by
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨priorPositionValue + 1, hBound⟩ => rfl

/-- Iterated binder lifts commute with the injection, pointwise. -/
theorem RawTermSubst.ofRenaming_iterateLift_pointwise
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope) :
    (binderDepth : Nat) →
    RawTermSubst.PointwiseEq
      (iterateLiftRaw (RawTermSubst.ofRenaming someRenaming) binderDepth)
      (RawTermSubst.ofRenaming (iterateLiftRaw someRenaming binderDepth))
  | 0 => RawTermSubst.PointwiseEq.refl _
  | priorDepth + 1 => by
      intro position
      have liftedPrior := RawTermSubst.lift_pointwise
        (RawTermSubst.ofRenaming_iterateLift_pointwise someRenaming
          priorDepth)
      exact (liftedPrior position).trans
        (RawTermSubst.ofRenaming_lift_pointwise
          (iterateLiftRaw someRenaming priorDepth) position)

mutual

/-- ★ **Rename IS subst at the injection** — term level.  Variable
heads dispatch identically on both sides (the injected substituent IS
the renamed variable); non-variable heads recurse through the children
spine. -/
theorem RawTerm.rename_eq_subst_ofRenaming
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope) :
    (sourceTerm : RawTerm sourceScope) →
    RawTerm.rename someRenaming sourceTerm =
      RawTerm.subst (RawTermSubst.ofRenaming someRenaming) sourceTerm
  | .mkGen someGenerator somePayload someChildren => by
      by_cases isVarGen : someGenerator = .gen_var
      case pos =>
        subst isVarGen
        rfl
      case neg =>
        rw [RawTerm.rename_nonVar_reduces someRenaming isVarGen somePayload
          someChildren]
        rw [RawTerm.subst_nonVar_reduces
          (RawTermSubst.ofRenaming someRenaming) isVarGen somePayload
          someChildren]
        rw [show foldChildren GenAlgebra.canonical someRenaming someChildren
            = RawTermChildren.rename someRenaming someChildren from rfl,
          show foldChildren GenAlgebra.canonical
              (RawTermSubst.ofRenaming someRenaming) someChildren
            = RawTermChildren.subst
                (RawTermSubst.ofRenaming someRenaming) someChildren
            from rfl]
        rw [RawTermChildren.rename_eq_subst_ofRenaming someRenaming
          someChildren]

/-- Spine companion: each child bridges at its own binder depth, with
the pointwise lift-commutation transported through Allais
extensionality. -/
theorem RawTermChildren.rename_eq_subst_ofRenaming
    {parentSourceScope parentTargetScope : Nat}
    (someRenaming : RawRenaming parentSourceScope parentTargetScope) :
    {binderShifts : List Nat} →
    (someChildren : RawTermChildren binderShifts parentSourceScope) →
    RawTermChildren.rename someRenaming someChildren =
      RawTermChildren.subst (RawTermSubst.ofRenaming someRenaming)
        someChildren
  | [], .childNil => rfl
  | headShift :: _, .childCons childHead childTail => by
      show RawTermChildren.childCons
          (RawTerm.rename (iterateLiftRaw someRenaming headShift)
            childHead)
          (RawTermChildren.rename someRenaming childTail)
        = RawTermChildren.childCons
          (RawTerm.subst
            (iterateLiftRaw (RawTermSubst.ofRenaming someRenaming)
              headShift)
            childHead)
          (RawTermChildren.subst (RawTermSubst.ofRenaming someRenaming)
            childTail)
      rw [RawTerm.rename_eq_subst_ofRenaming
        (iterateLiftRaw someRenaming headShift) childHead]
      rw [RawTerm.subst_pointwise
        (RawTermSubst.ofRenaming_iterateLift_pointwise someRenaming
          headShift) childHead]
      rw [RawTermChildren.rename_eq_subst_ofRenaming someRenaming
        childTail]

end

end FX1Poly.Core
