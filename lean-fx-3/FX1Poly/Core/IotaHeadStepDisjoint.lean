import FX1Poly.Core.HeadStep
import FX1Poly.Core.IotaHeadStep

/-! # Foundation/PolyCell/Core/IotaHeadStepDisjoint
    — β-head and root-ι reduction are disjoint

`HeadStep` (β at the head / congruence into the function spine) fires ONLY on `gen_app`-rooted terms;
`IotaHeadStep` (eliminator-on-constructor at the root) fires ONLY on eliminator-rooted terms
(`gen_boolElim` / `gen_natRec` / `gen_fst` / …).  Those root generators are disjoint, so no term has
both a weak-head β reduct and a root-ι reduct.

This is the cornerstone of determinism for the COMBINED weak-head reduction `HeadStep ∪ IotaHeadStep`
(∪ scrutinee-congruence) that the large-elimination-ready reducibility relation will dispatch on: to
keep the combined relation a partial function, the β branch and the ι branch must never both apply.
Together with `HeadStep.deterministic` and `IotaHeadStep.deterministic` (each branch deterministic on
its own), this disjointness gives the cross-branch exclusion the combined-relation determinism needs.

## Zero-axiom verification

`cases` on the β-step pins a `gen_app` root; every `IotaHeadStep` constructor concludes an
eliminator-rooted subject, so all sixteen are impossible by index unification and `cases` on the ι-step
closes the `False` goal with no remaining cases — the propext-clean route shared with
`IotaHeadStep.deterministic`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **β-head and root-ι reduction are disjoint.**  No term has both a `HeadStep` reduct and an
`IotaHeadStep` reduct: `HeadStep` is `gen_app`-rooted, `IotaHeadStep` is eliminator-rooted. -/
theorem HeadStep.not_iotaHeadStep {scope : Nat} {term betaReduct iotaReduct : RawTerm scope}
    (betaStep : HeadStep term betaReduct) (iotaStep : IotaHeadStep term iotaReduct) : False := by
  cases betaStep <;> cases iotaStep

/-- Symmetric form of `HeadStep.not_iotaHeadStep` (ι-step first), for ergonomic discharge of the
cross-branch case in combined weak-head reduction proofs. -/
theorem IotaHeadStep.not_headStep {scope : Nat} {term iotaReduct betaReduct : RawTerm scope}
    (iotaStep : IotaHeadStep term iotaReduct) (betaStep : HeadStep term betaReduct) : False :=
  HeadStep.not_iotaHeadStep betaStep iotaStep

end FX1Poly.Core
