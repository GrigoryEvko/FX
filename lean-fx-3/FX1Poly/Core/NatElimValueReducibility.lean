import FX1Poly.Core.NatCanonicalFormsCandidate
import FX1Poly.Core.WeakHeadStepSubsumes

/-! # FX1Poly/Core/NatElimValueReducibility
    — the VALUE-CASE of non-dependent Nat-recursor reducibility (the computational heart of recursor reducibility)

Nat-recursor reducibility: `natElim motive zeroBranch succBranch scrutinee` (and `natRec`) is a reducible
member of the result type whenever the scrutinee `n` and the branches are reducible.  The full theorem
decomposes into three regimes of the scrutinee — neutral (the recursor is itself neutral, CR3),
reduces-to-a-numeral, and the numeral VALUE itself — with the recursive descent on the numeral predecessor.
This file ships the VALUE case: the recursor applied to a NUMERAL scrutinee lands in the result candidate,
proved by structural induction on `IsNatValue`.

The value case is the genuine COMPUTATIONAL heart: it is where the two ι rules fire — `natElim motive z s
natZero ↝ z` (zero) and the SUBSTITUTING successor rule

```
natElim motive z s (natSucc predecessor)
  ↝ s[var 0 := natElim motive z s predecessor, var 1 := predecessor]
```

(Phase-Z motive shape: arity 4, `binderShifts [1, 0, 2, 0]`, spine `(motive, zeroBranch, succBranch,
scrutinee)` with the scrutinee LAST; the succ-branch is a `RawTerm (scope + 2)` whose `var 0` is the inductive
hypothesis — the recursive call threading the SAME motive — and `var 1` is the predecessor).  The recursion on
the predecessor `m` happens via the `IsNatValue` structural IH.  Each ι is a weak-head step (`IotaHeadStep`,
`toWeakHeadStep`), so membership of the recursor cell follows from the result candidate's WEAK-HEAD-EXPANSION
closure applied to the contractum's membership (`z` for zero; the SUBSTITUTED succ reduct for succ — which the
caller's `succReductMember`, the 2-binder substitution-reduct membership, supplies for the predecessor).

The conditional hypotheses are the honest interface the eventual full recursor proof supplies — the same
conditional-arm discipline as the dependent-Π fuel-stability arms (`IsReducibleTypeAtAllPositiveLevels.ofPiType`
etc.):

* `headExpand` — the result candidate `C` is closed under weak-head expansion (a member of the contractum, with
  the redex strongly normalizing, gives a member of the redex).  This is a genuine reducibility-candidate
  property (it holds for the universe / Π / data candidates — the ι contractum is the principal reduct); the
  GENERIC proof over the stratified candidate is the deferred load-bearing lemma.
* `zeroBranchMember` / `succReductMember` — the branches are reducible (the succ ι reduct, the SUBSTITUTION
  `s[var 0 := natElim motive z s predecessor, var 1 := predecessor]`, applied to a numeral predecessor and a
  `C`-member recursive result lands in `C`: the 2-binder substitution membership of the successor branch).
* `redexStronglyNormalizing` — the recursor cell at a numeral is strongly normalizing (shipped: the
  `natElim`/`natRec` successor-case ι-redex SN, the `*_isStronglyNormalizing_of_normal_branches` family).
  Phase-Z motive shape: the cell carries a stored motive head child; the motive is fixed through the
  `IsNatValue` recursion, so the recursive `natElim` in the succ-ι reduct threads the SAME motive and the
  predecessor IH lands at it directly.

The general-member case (scrutinee neutral or reducing to a numeral) — the SN/neutral outer recursion — is the
remaining half, deferred.

## Zero-axiom verification

Structural induction on `IsNatValue`; each arm is one `headExpand` applied to the corresponding `IotaHeadStep`
(`iotaNatElimZero` / `iotaNatElimSucc`, and the `natRec` twins) lifted by `toWeakHeadStep`, with the succ arm
feeding the predecessor IH through `succReductMember`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- The natElim succ-iota SUBSTITUTED reduct
`subst (cons (natElim motive zeroBranch succBranch predecessor) (singleton predecessor)) succBranch`
(Phase-Z motive shape: the succ-branch under TWO binders, `var 0` the inductive hypothesis = recursive call,
`var 1` the predecessor; the succ-iota substitutes BOTH simultaneously). -/
private abbrev natElimSuccReduct {scope : Nat} (motive : RawTerm (scope + 1))
    (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope) :
    RawTerm scope :=
  RawTerm.subst
    (RawTermSubst.cons
      (.mkGen .gen_natElim ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons predecessor .childNil)))))
      (RawTermSubst.singleton predecessor))
    succBranch

/-- The natRec succ-iota SUBSTITUTED reduct — the `gen_natRec` mirror of `natElimSuccReduct`. -/
private abbrev natRecSuccReduct {scope : Nat} (motive : RawTerm (scope + 1))
    (zeroBranch : RawTerm scope) (succBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope) :
    RawTerm scope :=
  RawTerm.subst
    (RawTermSubst.cons
      (.mkGen .gen_natRec ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons predecessor .childNil)))))
      (RawTermSubst.singleton predecessor))
    succBranch

/-- **Value-case reducibility for `natElim`** (the non-dependent recursor on a numeral scrutinee).  Phase-Z
motive shape: arity 4, `binderShifts [1, 0, 2, 0]`, spine `(motive, zeroBranch, succBranch, scrutinee)` with
the scrutinee LAST.  By structural induction on the numeral: the `zero` ι selects the zero branch (a
`C`-member); the `succ` ι SUBSTITUTES the recursive call `natElim motive z s predecessor` (threading the same
motive) for `var 0` and the predecessor for `var 1`, whose membership comes from `succReductMember` fed the
predecessor's inductive hypothesis — each lifted to the recursor cell by the candidate's weak-head expansion.
The computational core of Nat-recursor reducibility; the scrutinee-reduction / neutral regimes are the deferred
outer recursion. -/
theorem natElimValueReducibility {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (resultCandidate : RawTerm scope → Prop)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (zeroBranchMember : resultCandidate zeroBranch)
    (succReductMember : ∀ {predecessor : RawTerm scope},
        IsNatValue predecessor → resultCandidate (natElimSuccReduct motive zeroBranch succBranch predecessor))
    (redexStronglyNormalizing : ∀ {value : RawTerm scope}, IsNatValue value →
        IsStronglyNormalizing
          (.mkGen .gen_natElim ()
            (.childCons motive
              (.childCons zeroBranch
                (.childCons succBranch
                  (.childCons value .childNil))))))
    {value : RawTerm scope} (valueIsNat : IsNatValue value) :
    resultCandidate (.mkGen .gen_natElim ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons value .childNil))))) := by
  induction valueIsNat with
  | zero =>
      exact headExpand IotaHeadStep.iotaNatElimZero.toWeakHeadStep zeroBranchMember
        (redexStronglyNormalizing IsNatValue.zero)
  | @succ predecessor predecessorIsValue _predecessorIH =>
      exact headExpand IotaHeadStep.iotaNatElimSucc.toWeakHeadStep
        (succReductMember predecessorIsValue)
        (redexStronglyNormalizing (IsNatValue.succ predecessorIsValue))

/-- **Value-case reducibility for `natRec`** (the dependent-recursor twin).  Identical structure to
`natElimValueReducibility`: the `natRec` ι contractum at `natSucc predecessor` has the same SUBSTITUTED shape
(`s[var 0 := natRec motive z s predecessor, var 1 := predecessor]`), so the same weak-head-expansion + succ
reduct membership + predecessor IH closes it. -/
theorem natRecValueReducibility {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    (resultCandidate : RawTerm scope → Prop)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (zeroBranchMember : resultCandidate zeroBranch)
    (succReductMember : ∀ {predecessor : RawTerm scope},
        IsNatValue predecessor → resultCandidate (natRecSuccReduct motive zeroBranch succBranch predecessor))
    (redexStronglyNormalizing : ∀ {value : RawTerm scope}, IsNatValue value →
        IsStronglyNormalizing
          (.mkGen .gen_natRec ()
            (.childCons motive
              (.childCons zeroBranch
                (.childCons succBranch
                  (.childCons value .childNil))))))
    {value : RawTerm scope} (valueIsNat : IsNatValue value) :
    resultCandidate (.mkGen .gen_natRec ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons value .childNil))))) := by
  induction valueIsNat with
  | zero =>
      exact headExpand IotaHeadStep.iotaNatRecZero.toWeakHeadStep zeroBranchMember
        (redexStronglyNormalizing IsNatValue.zero)
  | @succ predecessor predecessorIsValue _predecessorIH =>
      exact headExpand IotaHeadStep.iotaNatRecSucc.toWeakHeadStep
        (succReductMember predecessorIsValue)
        (redexStronglyNormalizing (IsNatValue.succ predecessorIsValue))

end FX1Poly.Core
