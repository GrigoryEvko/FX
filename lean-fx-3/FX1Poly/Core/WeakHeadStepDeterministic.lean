import FX1Poly.Core.WeakHeadStep

/-! # Foundation/PolyCell/Core/WeakHeadStepDeterministic
    — weak-head reduction is a partial function

`WeakHeadStep` (`WeakHeadStep.lean`) has at most one reduct per term: the weak-head redex is unique.
This is the property a weak-head-normal dispatching reducibility relation needs to stay functional — the
`ReducibleType.deterministic` `whnfExpand` case equates the two weak-head reducts by it.

The three reduction "kinds" are mutually exclusive on a fixed term and each is internally deterministic:

  * β (`beta`/`appCongruence`) fires only on `gen_app`-rooted terms; root-ι (`rootIota`) and
    scrutinee-congruence only on eliminator-rooted ones — disjoint roots, dispatched by index
    unification (`cases` on the impossible `IotaHeadStep`/wrong-root steps);
  * within β: `beta` vs `appCongruence` is decided by whether the function is a λ (`not_from_lam`), and
    nested `appCongruence` by the induction hypothesis;
  * `rootIota` vs scrutinee-congruence at the same eliminator: the ι rule forces the scrutinee to be a
    *constructor*, which has no `WeakHeadStep` (so the scrutinee-congruence premise is impossible — refuted
    inline by `cases` reaching an `IotaHeadStep` on the constructor); within scrutinee-congruence the
    induction hypothesis equates the scrutinee reducts.

## Zero-axiom verification

Induction on the first step, inverting the second by `cases`; the same propext-clean `cases`-inversion
route used by `HeadStep.deterministic` / `IotaHeadStep.deterministic`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **Weak-head reduction is deterministic**: a term has at most one weak-head reduct. -/
theorem WeakHeadStep.deterministic {scope : Nat} {term firstReduct : RawTerm scope}
    (firstStep : WeakHeadStep term firstReduct) :
    ∀ {secondReduct : RawTerm scope}, WeakHeadStep term secondReduct → firstReduct = secondReduct := by
  induction firstStep with
  | beta =>
      intro secondReduct secondStep
      cases secondStep with
      | beta => rfl
      | appCongruence functionStep2 => exact absurd functionStep2 WeakHeadStep.not_from_lam
      | rootIota iotaStep2 => cases iotaStep2
  | appCongruence _functionStep1 functionInductiveHypothesis =>
      intro secondReduct secondStep
      cases secondStep with
      | beta => exact absurd _functionStep1 WeakHeadStep.not_from_lam
      | appCongruence functionStep2 => rw [functionInductiveHypothesis functionStep2]
      | rootIota iotaStep2 => cases iotaStep2
  | rootIota iotaStep1 =>
      intro secondReduct secondStep
      cases secondStep with
      | beta => cases iotaStep1
      | appCongruence _functionStep2 => cases iotaStep1
      | rootIota iotaStep2 => exact IotaHeadStep.deterministic iotaStep1 iotaStep2
      | scrutineeBoolElim scrutineeStep2 =>
          cases iotaStep1 <;> (cases scrutineeStep2 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeFst scrutineeStep2 =>
          cases iotaStep1 <;> (cases scrutineeStep2 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeSnd scrutineeStep2 =>
          cases iotaStep1 <;> (cases scrutineeStep2 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeNatElim scrutineeStep2 =>
          cases iotaStep1 <;> (cases scrutineeStep2 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeNatRec scrutineeStep2 =>
          cases iotaStep1 <;> (cases scrutineeStep2 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeListElim scrutineeStep2 =>
          cases iotaStep1 <;> (cases scrutineeStep2 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeOptionMatch scrutineeStep2 =>
          cases iotaStep1 <;> (cases scrutineeStep2 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeEitherMatch scrutineeStep2 =>
          cases iotaStep1 <;> (cases scrutineeStep2 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeIdJ scrutineeStep2 =>
          cases iotaStep1 <;> (cases scrutineeStep2 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeIdStrictRec scrutineeStep2 =>
          cases iotaStep1 <;> (cases scrutineeStep2 with | rootIota iotaStep3 => cases iotaStep3)
  | scrutineeBoolElim _scrutineeStep1 scrutineeInductiveHypothesis =>
      intro secondReduct secondStep
      cases secondStep with
      | rootIota iotaStep2 =>
          cases iotaStep2 <;> (cases _scrutineeStep1 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeBoolElim scrutineeStep2 => rw [scrutineeInductiveHypothesis scrutineeStep2]
  | scrutineeFst _scrutineeStep1 scrutineeInductiveHypothesis =>
      intro secondReduct secondStep
      cases secondStep with
      | rootIota iotaStep2 =>
          cases iotaStep2 <;> (cases _scrutineeStep1 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeFst scrutineeStep2 => rw [scrutineeInductiveHypothesis scrutineeStep2]
  | scrutineeSnd _scrutineeStep1 scrutineeInductiveHypothesis =>
      intro secondReduct secondStep
      cases secondStep with
      | rootIota iotaStep2 =>
          cases iotaStep2 <;> (cases _scrutineeStep1 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeSnd scrutineeStep2 => rw [scrutineeInductiveHypothesis scrutineeStep2]
  | scrutineeNatElim _scrutineeStep1 scrutineeInductiveHypothesis =>
      intro secondReduct secondStep
      cases secondStep with
      | rootIota iotaStep2 =>
          cases iotaStep2 <;> (cases _scrutineeStep1 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeNatElim scrutineeStep2 => rw [scrutineeInductiveHypothesis scrutineeStep2]
  | scrutineeNatRec _scrutineeStep1 scrutineeInductiveHypothesis =>
      intro secondReduct secondStep
      cases secondStep with
      | rootIota iotaStep2 =>
          cases iotaStep2 <;> (cases _scrutineeStep1 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeNatRec scrutineeStep2 => rw [scrutineeInductiveHypothesis scrutineeStep2]
  | scrutineeListElim _scrutineeStep1 scrutineeInductiveHypothesis =>
      intro secondReduct secondStep
      cases secondStep with
      | rootIota iotaStep2 =>
          cases iotaStep2 <;> (cases _scrutineeStep1 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeListElim scrutineeStep2 => rw [scrutineeInductiveHypothesis scrutineeStep2]
  | scrutineeOptionMatch _scrutineeStep1 scrutineeInductiveHypothesis =>
      intro secondReduct secondStep
      cases secondStep with
      | rootIota iotaStep2 =>
          cases iotaStep2 <;> (cases _scrutineeStep1 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeOptionMatch scrutineeStep2 => rw [scrutineeInductiveHypothesis scrutineeStep2]
  | scrutineeEitherMatch _scrutineeStep1 scrutineeInductiveHypothesis =>
      intro secondReduct secondStep
      cases secondStep with
      | rootIota iotaStep2 =>
          cases iotaStep2 <;> (cases _scrutineeStep1 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeEitherMatch scrutineeStep2 => rw [scrutineeInductiveHypothesis scrutineeStep2]
  | scrutineeIdJ _scrutineeStep1 scrutineeInductiveHypothesis =>
      intro secondReduct secondStep
      cases secondStep with
      | rootIota iotaStep2 =>
          cases iotaStep2 <;> (cases _scrutineeStep1 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeIdJ scrutineeStep2 => rw [scrutineeInductiveHypothesis scrutineeStep2]
  | scrutineeIdStrictRec _scrutineeStep1 scrutineeInductiveHypothesis =>
      intro secondReduct secondStep
      cases secondStep with
      | rootIota iotaStep2 =>
          cases iotaStep2 <;> (cases _scrutineeStep1 with | rootIota iotaStep3 => cases iotaStep3)
      | scrutineeIdStrictRec scrutineeStep2 => rw [scrutineeInductiveHypothesis scrutineeStep2]

end FX1Poly.Core
