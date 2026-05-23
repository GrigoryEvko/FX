import LeanFX2.Reduction.ConvRenameParJoin

/-! # Reduction/ConvRenameParJoinExtra — companions of the forward rename parallel-join

This file extends `ConvRenameParJoin.lean` with three additional parallel-join
flavors of the T6 forward rename equivariance, each composing ONLY the shipped
infrastructure (`Conv.toParJoin`, `Step.parStar.rename_compatible_typed` from
#2028, `Step.parStar.append`, and `Conv.sym`).  No new kernel ctor; no `StepStar`
single-step rename-compatibility (which remains the unshipped ~107-arm blocker
described in `ConvRenameParJoin.lean`).

## Why these and not the literal `Conv` form

The literal `Conv (rename source) (rename target)` still needs
`StepStar.rename_compatible_typed` (single-step), which is not shipped.  Every
theorem here therefore lands in the same typed **parallel join** shape as the
forward headline: `∃ mid, Step.parStar (rename _) mid ∧ Step.parStar (rename _)
mid`.  These are the orientation/extension variants that symmetric and
chain-extending consumers reach for without re-deriving the rename lift.

## What lives here

* `Conv.rename_equivariant_fwd_parJoin_sym` — symmetric orientation: the same
  parallel join with the two arms presented target-first.  Built by renaming the
  symmetrized `Conv` (so the source/target roles in the output join swap).
* `Conv.rename_equivariant_fwd_parJoin_extend` — common-reduct extension: lift
  the convertibility under the renaming, then advance BOTH arms of the resulting
  join along ANY further `Step.parStar` chain out of the common reduct via
  `Step.parStar.append`.  No Church-Rosser is needed — a single chain extends
  both already-converging arms at once, pushing the witnessed common reduct
  downstream while keeping both rename images joined.
* `Conv.weaken_equivariant_fwd_parJoin_sym` — canonical-weaken specialization of
  the symmetric form, mirroring `Conv.weaken_equivariant_fwd_parJoin`'s
  specialization of the forward headline.

Zero-axiom — `Conv.sym` and `Step.parStar.append` are zero-axiom, and the rename
arm reuses #2028 exactly as the forward headline does. -/

namespace LeanFX2

/-- **T6 forward rename equivariance — symmetric orientation.**  The same typed
parallel join as `Conv.rename_equivariant_fwd_parJoin`, but presented with the
roles of source and target swapped: the first arm reduces the rename-image of
`targetTerm`, the second reduces the rename-image of `sourceTerm`.

Built by symmetrizing the convertibility (`Conv.sym`) before applying the forward
headline, so the resulting join's two `Step.parStar` arms come out target-first.
Useful for consumers that already hold the convertibility target-first and would
otherwise re-apply `Conv.sym` at every call site. -/
theorem Conv.rename_equivariant_fwd_parJoin_sym
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term sourceCtx targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ (midType : Ty level targetScope) (midRaw : RawTerm targetScope)
      (midTerm : Term targetCtx midType midRaw),
      Step.parStar (Term.rename termRenaming targetTerm) midTerm ∧
      Step.parStar (Term.rename termRenaming sourceTerm) midTerm :=
  Conv.rename_equivariant_fwd_parJoin termRenaming (Conv.sym convertibility)

/-- **T6 forward rename equivariance — common-reduct extension.**  Lift a typed
`Conv source target` under the renaming `termRenaming` to its forward parallel
join (a common reduct reached by both renamed endpoints), then advance BOTH arms
along ANY further `Step.parStar` chain out of that reduct via
`Step.parStar.append`.  The result is a parallel join of the two rename images at
the chain's far end.

No Church-Rosser is needed: a single chain `extendChain` extends both
already-converging arms at once.  This is the honest trans-chain flavor of the
forward headline — it pushes the witnessed common reduct further downstream while
keeping both rename images joined.  The caller supplies `extendChain` as a
function of the join's existentially-quantified common reduct, so the extension
applies at exactly the reduct the rename lift produced. -/
theorem Conv.rename_equivariant_fwd_parJoin_extend
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term sourceCtx targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm)
    {furtherType : Ty level targetScope} {furtherRaw : RawTerm targetScope}
    {furtherTerm : Term targetCtx furtherType furtherRaw}
    (extendChain :
      ∀ {commonType : Ty level targetScope} {commonRaw : RawTerm targetScope}
        (commonReduct : Term targetCtx commonType commonRaw),
        Step.parStar (Term.rename termRenaming sourceTerm) commonReduct →
        Step.parStar (Term.rename termRenaming targetTerm) commonReduct →
        Step.parStar commonReduct furtherTerm) :
    Step.parStar (Term.rename termRenaming sourceTerm) furtherTerm ∧
    Step.parStar (Term.rename termRenaming targetTerm) furtherTerm := by
  obtain ⟨_, _, commonReduct, sourceArm, targetArm⟩ :=
    Conv.rename_equivariant_fwd_parJoin termRenaming convertibility
  exact ⟨Step.parStar.append sourceArm (extendChain commonReduct sourceArm targetArm),
         Step.parStar.append targetArm (extendChain commonReduct sourceArm targetArm)⟩

/-- Canonical-weaken specialization of `Conv.rename_equivariant_fwd_parJoin_sym`.

A typed `Conv source target` lifts to the **target-first** parallel join between
the one-binder weakenings of `target` and `source` in `context.cons newType`.
Instantiates the symmetric form at `termRenaming := TermRenaming.weakenStep
context newType`, mirroring how `Conv.weaken_equivariant_fwd_parJoin` specializes
the forward headline. -/
theorem Conv.weaken_equivariant_fwd_parJoin_sym
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (newType : Ty level scope)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ (midType : Ty level (scope + 1)) (midRaw : RawTerm (scope + 1))
      (midTerm : Term (context.cons newType) midType midRaw),
      Step.parStar
        (Term.rename (TermRenaming.weakenStep context newType) targetTerm) midTerm ∧
      Step.parStar
        (Term.rename (TermRenaming.weakenStep context newType) sourceTerm) midTerm :=
  Conv.rename_equivariant_fwd_parJoin_sym (TermRenaming.weakenStep context newType)
    convertibility

end LeanFX2
