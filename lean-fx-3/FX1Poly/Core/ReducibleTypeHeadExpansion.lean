import FX1Poly.Core.ReducibleType
import FX1Poly.Core.HeadExpansionClosure

/-! # Foundation/PolyCell/Core/ReducibleTypeHeadExpansion
    — every dependent-reducible type's candidate is head-expansion-closed

The fundamental theorem's Π-introduction case needs each interpreted candidate to be
**head-expansion-closed**: a λ is reducible at the dependent arrow because, for every reducible
argument, the β-redex `app (lam body) argument` inherits its codomain membership from the contractum
`subst0 body argument` (which the body's induction hypothesis supplies).  This file proves that every
`ReducibleType` candidate has that property.

Induction on the derivation discharges to the shipped closures: `headExpand` forwards its hypothesis
unchanged (the candidate is literally the contractum's); `neutral` is `IsStronglyNormalizing`, closed
by `isStronglyNormalizing_headExpansionClosed`; the dependent arrow mirrors
`isArrowReducible_headExpansionClosed` — applying the spined redex to one more argument absorbs into
the spine (`applySpineApp_append`), where the codomain candidate `codomainCandidate extraArgument` (a
fixed candidate for that reducible argument, head-expansion-closed by the induction hypothesis)
discharges the goal.  Only the FUNCTION position head-expands; the codomain candidate is indexed by a
fixed argument, so no argument-reduction enters — this property is independent of the candidate-hood
proof.

## Zero-axiom verification

Induction on `ReducibleType` + `applySpineApp_append` (`rw`) + the shipped SN / arrow closures.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per
declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Every dependent-reducible type's candidate is head-expansion-closed.**  By induction: a
weak-head redex forwards the contractum's candidate; a neutral type's SN candidate is closed; the
dependent arrow is closed because the spined redex applied to one more (reducible) argument lengthens
the spine, where the codomain candidate for that argument — itself head-expansion-closed by the
induction hypothesis — discharges the goal. -/
theorem ReducibleType.headExpansionClosed {scope : Nat} {typeCode : RawTerm scope}
    {candidate : RawTerm scope → Prop} (reducible : ReducibleType typeCode candidate) :
    HeadExpansionClosed candidate := by
  induction reducible with
  | whnfExpand _weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact reductInductiveHypothesis
  | neutral _noWeakHeadStep _notPiType =>
      exact isStronglyNormalizing_headExpansionClosed
  | piType codomainCandidate _domainReducible _codomainReducible
      _domainInductiveHypothesis codomainInductiveHypothesis =>
      intro body argument spine argumentSN contractumReducible
      intro extraArgument extraArgumentReducible
      have contractumAtExtendedSpine :
          codomainCandidate extraArgument
            (RawTerm.applySpineApp (RawTerm.subst0 body argument) (spine ++ [extraArgument])) := by
        rw [applySpineApp_append]
        exact contractumReducible extraArgument extraArgumentReducible
      have redexAtExtendedSpine :
          codomainCandidate extraArgument
            (RawTerm.applySpineApp
              (.mkGen .gen_app ()
                (.childCons (.mkGen .gen_lam () (.childCons body .childNil))
                  (.childCons argument .childNil)))
              (spine ++ [extraArgument])) :=
        (codomainInductiveHypothesis extraArgument extraArgumentReducible)
          argumentSN contractumAtExtendedSpine
      rw [applySpineApp_append] at redexAtExtendedSpine
      exact redexAtExtendedSpine

end FX1Poly.Core
