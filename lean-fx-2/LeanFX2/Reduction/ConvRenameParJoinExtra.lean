import LeanFX2.Reduction.ConvRenameParJoin
import LeanFX2.Confluence.ParStarBridge

/-! # ConvRenameParJoinExtra — TODO POLYCELL: BODY DISABLED

Body depends on cd_lemma / Conv.canonical_form / parStar.confluence /
RawStep.parStar orchestration deleted in commit c2efaccf (cascade-fake
bulldoze).  Replacement: FXcdLemma / FXConv view defs per polycell.md §5.
Imports are preserved at top so downstream transitive imports still work.
-/

/- TODO POLYCELL: original body preserved as block comment


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
* `Conv.rename_equivariant_fwd_parJoin_toRaw` — raw projection: project both arms
  of the typed forward rename join down to `RawStep.parStar` on `RawTerm` via
  `Step.parStar.toRawBridge`, presenting the endpoints as `(toRaw _).rename rho`.
  This is the raw-join shape `RawStep.parStar.confluence` and the
  `Conv.renameRaw` consumers (Church-Rosser corollary) reach for.
* `Conv.weaken_equivariant_fwd_parJoin_extend` — canonical-weaken specialization
  of `_extend`.  Common-reduct chain extension at one-binder weakening, the shape
  β-redex consumers reach for under canonical weaken.
* `Conv.weaken_equivariant_fwd_parJoin_toRaw` — canonical-weaken specialization
  of `_toRaw`.  Raw projection at one-binder weakening, the raw-join shape Geuvers
  β-η critical-pair consumers reach for under canonical weaken.

Zero-axiom — `Conv.sym`, `Step.parStar.append`, and `Step.parStar.toRawBridge`
are zero-axiom, and the rename arm reuses #2028 exactly as the forward headline
does. -/

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

/-- **T6 forward rename equivariance — raw projection.**  Project both arms of the
typed forward rename parallel join down to a RAW parallel join on `RawTerm`.

The typed join (`Conv.rename_equivariant_fwd_parJoin`) gives two typed
`Step.parStar` arms reaching a typed common reduct.  Applying
`Step.parStar.toRawBridge` to each arm yields raw `RawStep.parStar` chains over
the underlying `RawTerm`s; rewriting the renamed endpoints with `Term.toRaw_rename`
presents the raw sources as `(toRaw source).rename rho` / `(toRaw target).rename
rho`.  This is the raw-join shape consumed by `RawStep.parStar.confluence` and the
`Conv.renameRaw` Church-Rosser corollary — the typed strengthening shipped in the
forward headline, projected back to the raw layer where confluence completes the
join. -/
theorem Conv.rename_equivariant_fwd_parJoin_toRaw
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
    ∃ midRaw : RawTerm targetScope,
      RawStep.parStar (sourceRaw.rename rho) midRaw ∧
      RawStep.parStar (targetRaw.rename rho) midRaw := by
  obtain ⟨_, midRaw, midTerm, sourceArm, targetArm⟩ :=
    Conv.rename_equivariant_fwd_parJoin termRenaming convertibility
  exact ⟨midRaw,
    Step.parStar.toRawBridge sourceArm,
    Step.parStar.toRawBridge targetArm⟩

/-- Canonical-weaken specialization of `Conv.rename_equivariant_fwd_parJoin_extend`.

A typed `Conv source target` lifts to a typed parallel join between the one-binder
weakenings of `source` and `target` in `context.cons newType`, with BOTH arms then
advanced along ANY further `Step.parStar` chain out of the common reduct.
Instantiates the general `_extend` at `termRenaming := TermRenaming.weakenStep
context newType`, mirroring how `Conv.weaken_equivariant_fwd_parJoin` /
`Conv.weaken_equivariant_fwd_parJoin_sym` specialize the headline and symmetric
forms.  This is the shape β-redex consumers under canonical weaken (e.g. Geuvers
β-η critical pair when the bound variable is weakened past one fresh binder)
reach for. -/
theorem Conv.weaken_equivariant_fwd_parJoin_extend
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (newType : Ty level scope)
    (convertibility : Conv sourceTerm targetTerm)
    {furtherType : Ty level (scope + 1)} {furtherRaw : RawTerm (scope + 1)}
    {furtherTerm : Term (context.cons newType) furtherType furtherRaw}
    (extendChain :
      ∀ {commonType : Ty level (scope + 1)} {commonRaw : RawTerm (scope + 1)}
        (commonReduct : Term (context.cons newType) commonType commonRaw),
        Step.parStar
          (Term.rename (TermRenaming.weakenStep context newType) sourceTerm)
          commonReduct →
        Step.parStar
          (Term.rename (TermRenaming.weakenStep context newType) targetTerm)
          commonReduct →
        Step.parStar commonReduct furtherTerm) :
    Step.parStar
      (Term.rename (TermRenaming.weakenStep context newType) sourceTerm)
      furtherTerm ∧
    Step.parStar
      (Term.rename (TermRenaming.weakenStep context newType) targetTerm)
      furtherTerm :=
  Conv.rename_equivariant_fwd_parJoin_extend
    (TermRenaming.weakenStep context newType) convertibility extendChain

/-- Canonical-weaken specialization of `Conv.rename_equivariant_fwd_parJoin_toRaw`.

A typed `Conv source target` projects to a RAW parallel join between the
one-binder-weakened raw forms `sourceRaw.rename RawRenaming.weaken` and
`targetRaw.rename RawRenaming.weaken`.  Instantiates the general `_toRaw` at
`termRenaming := TermRenaming.weakenStep context newType`; under
`TermRenaming.weakenStep`'s defining equation
`rho := RawRenaming.weaken` (Term/Rename.lean:89), the raw endpoints come out
exactly as `RawRenaming.weaken`-renamed.  This is the raw-join shape Geuvers β-η
critical-pair consumers under canonical weaken (e.g. `RawStep.parStar.confluence`
applied to the weakened arms) reach for. -/
theorem Conv.weaken_equivariant_fwd_parJoin_toRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (newType : Ty level scope)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ midRaw : RawTerm (scope + 1),
      RawStep.parStar (sourceRaw.rename RawRenaming.weaken) midRaw ∧
      RawStep.parStar (targetRaw.rename RawRenaming.weaken) midRaw :=
  Conv.rename_equivariant_fwd_parJoin_toRaw
    (TermRenaming.weakenStep context newType) convertibility

end LeanFX2

-/
