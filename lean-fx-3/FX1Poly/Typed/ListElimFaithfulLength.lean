import FX1Poly.Typed.ListElimComputingCanonicity
import FX1Poly.Typed.NatElimFaithfulArithmetic

/-! # FX1Poly/Typed/ListElimFaithfulLength — the native `listElim` recursor FAITHFULLY computes host `List.length` (HON-12)

`ListElimComputingCanonicity.listElimLengthComputesToNumeral` proved the length fold reaches *some* numeral
(`∃ out, StepStar … out ∧ IsNatNumeral out`).  That answers "does it terminate at a numeral?" but NOT the honesty
question the 197-generator audit asks: **does `gen_listElim` truthfully encode the host recursor — does it count
to the EXACT length?**  This file closes that: the native list recursor, run on the closed `n`-element list,
reduces to the numeral `n` — the exact image of host `List.length`.

This is the list analogue of `NatElimFaithfulArithmetic.natElimAddFaithful` (native `natElim` computes exact host
`Nat.add`): same upgrade from "reaches A value" to "reaches the RIGHT value."  The length step `lengthNatStep`
(`λ_.λ_.λr.natSucc r`) has a SIMPLE body (`natSucc` of the recursive result), so its three β-steps compute
definitionally — unlike a step that embeds another recursor (e.g. native `Nat.mul`, whose `subst0` does not
reduce definitionally; that is a separate, harder follow-on).

  * **`rawListReplicate : Nat → RawTerm 0`** — the closed `n`-element list (`n` copies of `natZero`), whose host
    length is exactly `n`, with `rawListReplicate_isListValue`.  (The element content is irrelevant to length, so
    `natZero` copies suffice to range the length over every `n`.)
  * **`lengthNatStepComputesExact`** — `(λ_.λ_.λr.natSucc r) h t rec ↝* natSucc rec`, the existential-free form
    of `lengthNatStepProduces` (faithfulness pins the EXACT output).
  * **`listElimLengthFaithful` (★ headline)** — `listElim(rawListReplicate n, natZero, lengthStep) ↝*
    natNumeral n` for ALL `n`, by induction on `n`: nil projects `natZero` (`iotaListElimNil`); cons fires
    `iotaListElimCons`, the IH reduces the inner recursor over the tail via `StepStar.appArgument`, and
    `lengthNatStepComputesExact` wraps one `natSucc` (`natSucc (natNumeral n) ≡ natNumeral (n+1)` definitionally).
  * **`listElimLengthFaithful.three`** — fully-concrete `listElim([_,_,_], natZero, lengthStep) ↝* numeral 3`.

The native recursor counting to the EXACT length — the honest "this cell truthfully encodes its mathematical
meaning" the generator-honesty arc (HON-1..6) set up to ask.

## Zero-axiom

`listElimLengthFaithful` is structural recursion on `n` composing `Step.iotaListElimNil`/`iotaListElimCons`
ι-steps, `StepStar.appArgument` congruence, and `lengthNatStepComputesExact` (three `Step.beta`); the numeral
bridge `natSucc (natNumeral n) ≡ natNumeral (n+1)` is definitional.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The closed `n`-element list — `n` copies of `natZero`.  Its host length is exactly `n`; the element content
is irrelevant to length, so `natZero` copies range the length over every `n`. -/
def rawListReplicate : Nat → RawTerm 0
  | 0 => listNilCell
  | n + 1 => listConsCell natZeroCell (rawListReplicate n)

/-- Every `rawListReplicate n` is a closed list value (`natZero` heads are normal, tail by IH). -/
theorem rawListReplicate_isListValue : ∀ n, IsListValue (rawListReplicate n)
  | 0 => IsListValue.nil
  | n + 1 => IsListValue.cons (by decide) (rawListReplicate_isListValue n)

/-- **Exact-reduct length step.**  `(λ_.λ_.λr.natSucc r) h t rec ↝* natSucc rec` — the existential-free form of
`lengthNatStepProduces` (faithfulness pins the EXACT output).  Three `Step.beta`: drop the unused head and tail
binders, substitute the recursive result for `r`. -/
theorem lengthNatStepComputesExact (headVal tailVal recResult : RawTerm 0) :
    StepStar (appCell (appCell (appCell lengthNatStep headVal) tailVal) recResult) (natSuccCell recResult) := by
  have firstBeta : Step (appCell lengthNatStep headVal)
      (lamCell natZeroCell (lamCell natZeroCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 2))))) := Step.beta
  have secondBeta :
      Step (appCell (lamCell natZeroCell (lamCell natZeroCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 2))))) tailVal)
        (lamCell natZeroCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 1)))) := Step.beta
  have thirdBeta : Step (appCell (lamCell natZeroCell (natSuccCell (variableCell (⟨0, by decide⟩ : Fin 1)))) recResult)
      (natSuccCell recResult) := Step.beta
  exact StepStar.trans_compose
    (StepStar.appFunction (StepStar.appFunction (StepStar.single firstBeta)))
    (StepStar.trans_compose (StepStar.appFunction (StepStar.single secondBeta)) (StepStar.single thirdBeta))

/-- **★ The native `gen_listElim` recursor computes host `List.length` faithfully.**  `listElim(rawListReplicate
n, natZero, lengthStep) ↝* natNumeral n` for ALL `n` — the de Bruijn list recursor, run on the closed
`n`-element list, reduces to the numeral of its host LENGTH.  Faithfulness made precise: not "reaches some
numeral" (the existing `listElimLengthComputesToNumeral`) but "reaches the RIGHT numeral", i.e. `gen_listElim`
truthfully encodes `List.length`. -/
theorem listElimLengthFaithful : ∀ n,
    StepStar (listElimCell (rawListReplicate n) natZeroCell lengthNatStep) (natNumeralCell n)
  | 0 => StepStar.single Step.iotaListElimNil
  | n + 1 =>
      StepStar.trans_compose (StepStar.single Step.iotaListElimCons)
        (StepStar.trans_compose
          (StepStar.appArgument (appCell (appCell lengthNatStep natZeroCell) (rawListReplicate n))
            (listElimLengthFaithful n))
          (lengthNatStepComputesExact natZeroCell (rawListReplicate n) (natNumeralCell n)))

/-- Fully-concrete faithfulness smoke: `listElim([natZero, natZero, natZero], natZero, lengthStep) ↝* 3` — the
3-element list counted to the numeral `3` by the native recursor. -/
theorem listElimLengthFaithful.three :
    StepStar (listElimCell (rawListReplicate 3) natZeroCell lengthNatStep) (natNumeralCell 3) :=
  listElimLengthFaithful 3

end FX1Poly.Typed
