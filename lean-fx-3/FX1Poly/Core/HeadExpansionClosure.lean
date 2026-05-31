import FX1Poly.Core.StrongNormalizationSpineExpansion

/-! # Foundation/PolyCell/Core/HeadExpansionClosure
    — head-expansion closure as a candidate property, closed under SN and the arrow former

The Tait fundamental theorem's λ case needs each interpreted type's candidate to be
**head-expansion-closed** (so that a β-redex inherits membership from its contractum).  This file
makes that a first-class property and proves it closes under the two type-interpretation
constructors:

* `isStronglyNormalizing_headExpansionClosed` — the SN candidate (base types) is closed; this is
  exactly the general spine head-expansion `betaSpineHeadExpansion`.
* `isArrowReducible_headExpansionClosed` — the arrow construction PRESERVES the property: if the
  codomain candidate is head-expansion-closed, so is `IsArrowReducible domain codomain`.

Together (with `IsReducibilityCandidate` closure already shipped) every interpreted type is both a
reducibility candidate AND head-expansion-closed — the two ingredients the fundamental theorem
combines.  Both proofs are GENERIC (over the candidate predicates), so this is one composition
principle, not a per-type lemma.

## The arrow case in one line

`app (applySpineApp f spine) a = applySpineApp f (spine ++ [a])` (`applySpineApp_append`): applying
the redex to one more argument just lengthens the spine, so the codomain's head-expansion closure
at the longer spine discharges the goal.  No domain-candidate hypothesis is needed.

## Zero-axiom verification

`applySpineApp_append` (list induction) + `betaSpineHeadExpansion` + `rw`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core` in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- Applying a spined application to one more argument lengthens the spine:
`applySpineApp head (spine ++ [extraArgument]) = app (applySpineApp head spine) extraArgument`. -/
theorem applySpineApp_append {scope : Nat} :
    ∀ (spine : List (RawTerm scope)) (head extraArgument : RawTerm scope),
      RawTerm.applySpineApp head (spine ++ [extraArgument]) =
        .mkGen .gen_app ()
          (.childCons (RawTerm.applySpineApp head spine)
            (.childCons extraArgument .childNil)) := by
  intro spine
  induction spine with
  | nil => intro _head _extraArgument; rfl
  | cons spineElement restSpine restInductiveHypothesis =>
      intro head extraArgument
      exact restInductiveHypothesis
        (.mkGen .gen_app () (.childCons head (.childCons spineElement .childNil))) extraArgument

/-- A candidate is **head-expansion-closed** when, for any application spine, the spined β-redex
inherits membership from its spined contractum (given the argument is strongly normalizing).  The
spine-general formulation is what makes the property close under the arrow former. -/
def HeadExpansionClosed {scope : Nat} (candidate : RawTerm scope → Prop) : Prop :=
  ∀ {body : RawTerm (scope + 1)} {argument : RawTerm scope} {spine : List (RawTerm scope)},
    IsStronglyNormalizing argument →
    candidate (RawTerm.applySpineApp (RawTerm.subst0 body argument) spine) →
    candidate
      (RawTerm.applySpineApp
        (.mkGen .gen_app ()
          (.childCons (.mkGen .gen_lam () (.childCons body .childNil))
            (.childCons argument .childNil)))
        spine)

/-- The SN candidate is head-expansion-closed — the base-type case, which IS the general spine
head-expansion `betaSpineHeadExpansion`. -/
theorem isStronglyNormalizing_headExpansionClosed {scope : Nat} :
    HeadExpansionClosed (IsStronglyNormalizing (scope := scope)) :=
  fun argumentSN contractumSN => betaSpineHeadExpansion argumentSN contractumSN

/-- **The arrow former preserves head-expansion closure.**  If the codomain candidate is
head-expansion-closed, so is `IsArrowReducible domain codomain` — applying the redex to one more
argument absorbs into the spine (`applySpineApp_append`), where the codomain's closure discharges
it.  No reducibility-candidate hypothesis on the domain is needed. -/
theorem isArrowReducible_headExpansionClosed {scope : Nat}
    {domainPredicate codomainPredicate : RawTerm scope → Prop}
    (codomainClosed : HeadExpansionClosed codomainPredicate) :
    HeadExpansionClosed (IsArrowReducible domainPredicate codomainPredicate) := by
  intro body argument spine argumentSN contractumArrowReducible
  intro extraArgument extraArgumentReducible
  have contractumAtExtendedSpine :
      codomainPredicate
        (RawTerm.applySpineApp (RawTerm.subst0 body argument) (spine ++ [extraArgument])) := by
    rw [applySpineApp_append]
    exact contractumArrowReducible extraArgument extraArgumentReducible
  have redexAtExtendedSpine :
      codomainPredicate
        (RawTerm.applySpineApp
          (.mkGen .gen_app ()
            (.childCons (.mkGen .gen_lam () (.childCons body .childNil))
              (.childCons argument .childNil)))
          (spine ++ [extraArgument])) :=
    codomainClosed argumentSN contractumAtExtendedSpine
  rw [applySpineApp_append] at redexAtExtendedSpine
  exact redexAtExtendedSpine

end FX1Poly.Core
