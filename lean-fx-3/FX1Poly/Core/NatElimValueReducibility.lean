import FX1Poly.Core.NatCanonicalFormsCandidate
import FX1Poly.Core.WeakHeadStepSubsumes

/-! # FX1Poly/Core/NatElimValueReducibility
    — the VALUE-CASE of non-dependent Nat-recursor reducibility (the computational heart of SN-061)

SN-061 is recursor reducibility: `natElim n z s` (and `natRec`) is a reducible member of the result type
whenever the scrutinee `n` and the branches are reducible.  The full theorem decomposes into three regimes of
the scrutinee — neutral (the recursor is itself neutral, CR3), reduces-to-a-numeral, and the numeral VALUE
itself — with the recursive descent on the numeral predecessor.  This file ships the VALUE case: the recursor
applied to a NUMERAL scrutinee lands in the result candidate, proved by structural induction on `IsNatValue`.

The value case is the genuine COMPUTATIONAL heart: it is where the two ι rules fire — `natElim natZero z s ↝ z`
(zero) and `natElim (natSucc m) z s ↝ app (app s m) (natElim m z s)` (succ) — and where the recursion on the
predecessor `m` happens (the `IsNatValue` structural IH).  Each ι is a weak-head step (`IotaHeadStep`,
`toWeakHeadStep`), so membership of the recursor cell follows from the result candidate's WEAK-HEAD-EXPANSION
closure applied to the contractum's membership (`z` for zero; `app (app s m) (natElim m z s)` for succ, via the
succ-branch application fed the predecessor's IH).

The conditional hypotheses are the honest interface the eventual full recursor proof supplies — the same
conditional-arm discipline as the dependent-Π fuel-stability arms (`IsReducibleTypeAtAllPositiveLevels.ofPiType`
etc.):

* `headExpand` — the result candidate `C` is closed under weak-head expansion (a member of the contractum, with
  the redex strongly normalizing, gives a member of the redex).  This is a genuine reducibility-candidate
  property (it holds for the universe / Π / data candidates — the ι contractum is the principal reduct); the
  GENERIC proof over the stratified candidate is the deferred load-bearing lemma.
* `zeroBranchMember` / `succBranchApplication` — the branches are reducible (the succ branch's application to a
  numeral and a `C`-member lands in `C`: the function-space membership of the successor branch).
* `redexStronglyNormalizing` — the recursor cell at a numeral is strongly normalizing (shipped: the
  `natElim`/`natRec` successor-case ι-redex SN, the `*_isStronglyNormalizing_of_normal_branches` family).

The general-member case (scrutinee neutral or reducing to a numeral) — the SN/neutral outer recursion — is the
remaining half of SN-061, deferred.

## Zero-axiom verification

Structural induction on `IsNatValue`; each arm is one `headExpand` applied to the corresponding `IotaHeadStep`
(`iotaNatElimZero` / `iotaNatElimSucc`, and the `natRec` twins) lifted by `toWeakHeadStep`, with the succ arm
feeding the predecessor IH through `succBranchApplication`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **Value-case reducibility for `natElim`** (the non-dependent recursor on a numeral scrutinee).  By
structural induction on the numeral: the `zero` ι selects the zero branch (a `C`-member); the `succ` ι yields
`app (app succBranch predecessor) (natElim predecessor …)`, whose membership comes from `succBranchApplication`
fed the predecessor's inductive hypothesis — each lifted to the recursor cell by the candidate's weak-head
expansion.  The computational core of SN-061; the scrutinee-reduction / neutral regimes are the deferred
outer recursion. -/
theorem natElimValueReducibility {scope : Nat}
    {zeroBranch succBranch : RawTerm scope}
    (resultCandidate : RawTerm scope → Prop)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (zeroBranchMember : resultCandidate zeroBranch)
    (succBranchApplication : ∀ {predecessor result : RawTerm scope},
        IsNatValue predecessor → resultCandidate result →
        resultCandidate (.mkGen .gen_app ()
            (.childCons (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
              (.childCons result .childNil))))
    (redexStronglyNormalizing : ∀ {value : RawTerm scope}, IsNatValue value →
        IsStronglyNormalizing
          (.mkGen .gen_natElim ()
            (.childCons value (.childCons zeroBranch (.childCons succBranch .childNil)))))
    {value : RawTerm scope} (valueIsNat : IsNatValue value) :
    resultCandidate (.mkGen .gen_natElim ()
        (.childCons value (.childCons zeroBranch (.childCons succBranch .childNil)))) := by
  induction valueIsNat with
  | zero =>
      exact headExpand IotaHeadStep.iotaNatElimZero.toWeakHeadStep zeroBranchMember
        (redexStronglyNormalizing IsNatValue.zero)
  | @succ predecessor predecessorIsValue predecessorIH =>
      exact headExpand IotaHeadStep.iotaNatElimSucc.toWeakHeadStep
        (succBranchApplication predecessorIsValue predecessorIH)
        (redexStronglyNormalizing (IsNatValue.succ predecessorIsValue))

/-- **Value-case reducibility for `natRec`** (the dependent-recursor twin).  Identical structure to
`natElimValueReducibility`: the `natRec` ι contractum at `natSucc predecessor` has the same nested-application
shape (`app (app succBranch predecessor) (natRec predecessor …)`), so the same weak-head-expansion + succ-branch
application + predecessor IH closes it. -/
theorem natRecValueReducibility {scope : Nat}
    {zeroBranch succBranch : RawTerm scope}
    (resultCandidate : RawTerm scope → Prop)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (zeroBranchMember : resultCandidate zeroBranch)
    (succBranchApplication : ∀ {predecessor result : RawTerm scope},
        IsNatValue predecessor → resultCandidate result →
        resultCandidate (.mkGen .gen_app ()
            (.childCons (.mkGen .gen_app () (.childCons succBranch (.childCons predecessor .childNil)))
              (.childCons result .childNil))))
    (redexStronglyNormalizing : ∀ {value : RawTerm scope}, IsNatValue value →
        IsStronglyNormalizing
          (.mkGen .gen_natRec ()
            (.childCons value (.childCons zeroBranch (.childCons succBranch .childNil)))))
    {value : RawTerm scope} (valueIsNat : IsNatValue value) :
    resultCandidate (.mkGen .gen_natRec ()
        (.childCons value (.childCons zeroBranch (.childCons succBranch .childNil)))) := by
  induction valueIsNat with
  | zero =>
      exact headExpand IotaHeadStep.iotaNatRecZero.toWeakHeadStep zeroBranchMember
        (redexStronglyNormalizing IsNatValue.zero)
  | @succ predecessor predecessorIsValue predecessorIH =>
      exact headExpand IotaHeadStep.iotaNatRecSucc.toWeakHeadStep
        (succBranchApplication predecessorIsValue predecessorIH)
        (redexStronglyNormalizing (IsNatValue.succ predecessorIsValue))

end FX1Poly.Core
