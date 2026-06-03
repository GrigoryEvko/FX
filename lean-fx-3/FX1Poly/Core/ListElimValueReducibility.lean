import FX1Poly.Core.ListCanonicalFormsCandidate
import FX1Poly.Core.WeakHeadStepSubsumes

/-! # FX1Poly/Core/ListElimValueReducibility
    — the VALUE-CASE of `listElim` recursor reducibility (the list analogue of `NatElimValueReducibility`)

The list counterpart of `NatElimValueReducibility` (the value-case of SN-061): `listElim v nilBranch consBranch`
on a LIST-VALUE scrutinee `v` lands in the result candidate, by structural induction on `IsListValue`.  This
is the computational core of SN-064 (list reducibility + `listElim`): where the two ι rules fire —
`listElim listNil n c ↝ n` (nil) and `listElim (listCons head tail) n c ↝ app (app (app c head) tail)
(listElim tail n c)` (cons) — and where the recursion descends on the tail (the `IsListValue` structural IH).
Each ι is a weak-head step (`IotaHeadStep`, `toWeakHeadStep`), so the recursor cell's membership follows from
the result candidate's weak-head-expansion applied to the contractum.

The conditional hypotheses are the honest interface the eventual full recursor proof supplies (the same
conditional-arm discipline as `natElimValueReducibility` / the dependent-Π fuel-stability arms):

* `headExpand` — the result candidate is closed under weak-head expansion (the deferred generic candidate
  property; holds for the universe / Π / data candidates).
* `nilBranchMember` — the nil branch is reducible.
* `consBranchApplication` — the cons branch applied to a normal head, a list-value tail, and a `C`-member
  result lands in `C` (the function-space membership of the cons branch, 3-argument).
* `redexStronglyNormalizing` — the `listElim` cell at a list value is strongly normalizing (shipped via the
  `listElim` cons-case ι-redex SN family).

The scrutinee-reduction / neutral outer regimes (the SN/neutral recursion) are the deferred remaining half,
shared with the Nat recursor case.

## Zero-axiom verification

Structural induction on `IsListValue`; the `nil` arm is one `headExpand` of `IotaHeadStep.iotaListElimNil`,
the `cons` arm one `headExpand` of `IotaHeadStep.iotaListElimCons` feeding the tail IH through
`consBranchApplication` (both ι lifted by `toWeakHeadStep`).  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **Value-case reducibility for `listElim`** (the recursor on a list-value scrutinee).  By structural
induction on `IsListValue`: the `nil` ι selects the nil branch (a `C`-member); the `cons` ι yields
`app (app (app consBranch head) tail) (listElim tail …)`, whose membership comes from `consBranchApplication`
fed the tail's inductive hypothesis — each lifted to the recursor cell by the candidate's weak-head expansion.
The list analogue of `natElimValueReducibility`; the scrutinee-reduction / neutral regimes are the deferred
outer recursion. -/
theorem listElimValueReducibility {scope : Nat}
    {nilBranch consBranch : RawTerm scope}
    (resultCandidate : RawTerm scope → Prop)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (nilBranchMember : resultCandidate nilBranch)
    (consBranchApplication : ∀ {head tail result : RawTerm scope},
        RawTerm.isStepNormalForm head → IsListValue tail → resultCandidate result →
        resultCandidate (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
                (.childCons tail .childNil)))
            (.childCons result .childNil))))
    (redexStronglyNormalizing : ∀ {value : RawTerm scope}, IsListValue value →
        IsStronglyNormalizing
          (.mkGen .gen_listElim ()
            (.childCons value (.childCons nilBranch (.childCons consBranch .childNil)))))
    {value : RawTerm scope} (valueIsList : IsListValue value) :
    resultCandidate (.mkGen .gen_listElim ()
        (.childCons value (.childCons nilBranch (.childCons consBranch .childNil)))) := by
  induction valueIsList with
  | nil =>
      exact headExpand IotaHeadStep.iotaListElimNil.toWeakHeadStep nilBranchMember
        (redexStronglyNormalizing IsListValue.nil)
  | @cons head tail headNormal tailIsValue tailIH =>
      exact headExpand IotaHeadStep.iotaListElimCons.toWeakHeadStep
        (consBranchApplication headNormal tailIsValue tailIH)
        (redexStronglyNormalizing (IsListValue.cons headNormal tailIsValue))

end FX1Poly.Core
