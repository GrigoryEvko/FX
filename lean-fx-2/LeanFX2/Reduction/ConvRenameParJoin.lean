import LeanFX2.Reduction.Conv
import LeanFX2.Reduction.StepStarToPar
import LeanFX2.Reduction.ParRed.RenameCompatibleTypedStar

/-! # Reduction/ConvRenameParJoin — typed Conv rename equivariance (forward, parallel-join flavor)

This file ships the **forward direction** of T6 (`Conv.rename_equivariant`,
#2029 unblock-C.t6.forward) in the strongest form the current kernel supports:
typed convertibility is preserved by renaming, witnessed by a **typed parallel
join**.

## Why a parallel join and not a literal `Conv`

`Conv source target` is `∃ midTerm, StepStar source midTerm ∧ StepStar target
midTerm` — a join over the SINGLE-step reflexive-transitive closure
(`StepStar`).  Producing a literal `Conv (Term.rename rho source)
(Term.rename rho target)` therefore requires `StepStar.rename_compatible_typed`,
which in turn needs single-step `Step.rename_compatible_typed` — a fresh
~107-arm structural induction over `Step` of the same magnitude as the
`Step.par` headline (#2027).  The parallel-closure rename-compatibility shipped
in #2028 (`Step.parStar.rename_compatible_typed`) does NOT discharge this,
because there is no `Step.par → StepStar` decomposition (`Step.par.toStepStar`):
lean-fx-2 currently proves only the easy inclusion `StepStar ⊆ Step.parStar`
(`StepStar.toParStar`), not the reverse `Step.parStar ⊆ StepStar` (each
parallel step splitting into a sequence of single steps).

So the maximal currently-provable typed statement lands in a parallel join:

```
Conv source target →
  ∃ mid, Step.parStar (rename source) mid ∧ Step.parStar (rename target) mid
```

This is the typed strengthening of `Conv.renameRaw`
(`Confluence/ChurchRosser.lean`), which drops all the way to a RAW join
(`RawStep.parStar` on `RawTerm`).  Here both arms stay TYPED — the witness is
`Term.rename rho midTerm`, a real `Term` in the target context — and the two
chains are typed `Step.parStar` reductions, supplied directly by #2028.

## What lives here

* `Conv.toParJoin` — every typed `Conv` IS a typed parallel join (lift both
  `StepStar` chains to `Step.parStar` via `StepStar.toParStar`).
* `Conv.rename_equivariant_fwd_parJoin` — the T6 forward direction: rename the
  parallel join through #2028.
* `Conv.weaken_equivariant_fwd_parJoin` — canonical-weaken specialization
  (`rho := RawRenaming.weaken`, `termRenaming := TermRenaming.weakenStep`),
  the shape #2032's weaken trio and downstream β-η consumers reach for.

## The remaining gap (literal `StepStar`-`Conv` form)

Closing #2029 to the literal `Conv (rename source) (rename target)` form is
unblocked by EITHER:

* `Step.par.toStepStar` (par → single-step chain decomposition, ~133-arm
  induction, NO renaming so NO cast machinery — cleaner than #2027), then
  `StepStar.rename_compatible_typed` via #2028 composed with it; OR
* single-step `Step.rename_compatible_typed` directly (~107-arm induction with
  cast machinery mirroring #2027).

Neither introduces a new kernel ctor; both are large proofs.  The parallel-join
form shipped here is what confluence (`RawStep.parStar.confluence`) and the
β-η critical-pair / Geuvers lift consumers actually use, so it carries the
practical weight of T6 forward today.

Zero-axiom — `Conv.toParJoin` adds only `StepStar.toParStar` (zero-axiom) per
chain; the rename arm cites #2028 (`Step.parStar.rename_compatible_typed`,
zero-axiom). -/

namespace LeanFX2

/-- Every typed `Conv` unpacks to a typed **parallel** join: lift each of the
two single-step `StepStar` chains to a `Step.parStar` chain via
`StepStar.toParStar`.  The common reduct `midTerm` is unchanged — it is the same
typed `Term`; only the closure flavor of the two chains widens from `StepStar`
to `Step.parStar`. -/
theorem Conv.toParJoin
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ (midType : Ty level scope) (midRaw : RawTerm scope)
      (midTerm : Term context midType midRaw),
      Step.parStar sourceTerm midTerm ∧ Step.parStar targetTerm midTerm := by
  obtain ⟨midType, midRaw, midTerm, chainSource, chainTarget⟩ := convertibility
  exact ⟨midType, midRaw, midTerm,
    chainSource.toParStar, chainTarget.toParStar⟩

/-- **T6 forward direction (parallel-join flavor).**  Renaming preserves typed
convertibility: a typed `Conv source target` lifts, under a typed renaming
`termRenaming`, to a typed parallel join between the rename-images of `source`
and `target`.

Pipeline: unpack the `Conv` into a typed parallel join (`Conv.toParJoin`), then
push each arm through the renaming with #2028
(`Step.parStar.rename_compatible_typed`).  The new common reduct is
`Term.rename termRenaming midTerm`. -/
theorem Conv.rename_equivariant_fwd_parJoin
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
      Step.parStar (Term.rename termRenaming sourceTerm) midTerm ∧
      Step.parStar (Term.rename termRenaming targetTerm) midTerm := by
  obtain ⟨midType, midRaw, midTerm, chainSource, chainTarget⟩ :=
    Conv.toParJoin convertibility
  exact ⟨_, _, Term.rename termRenaming midTerm,
    Step.parStar.rename_compatible_typed termRenaming chainSource,
    Step.parStar.rename_compatible_typed termRenaming chainTarget⟩

/-- Canonical-weaken specialization of `Conv.rename_equivariant_fwd_parJoin`.

A typed `Conv source target` in `context` lifts to a typed parallel join between
the one-binder weakenings of `source` and `target` in `context.cons newType`.
Instantiates the general renaming at `rho := RawRenaming.weaken` and
`termRenaming := TermRenaming.weakenStep context newType` (`fun _ => rfl`,
Term/Rename.lean:89).  This is the surface shape #2032's `Conv.weaken_equivariant`
trio and downstream β-redex consumers (Geuvers β-η critical pair under
canonical-weaken) reach for. -/
theorem Conv.weaken_equivariant_fwd_parJoin
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
        (Term.rename (TermRenaming.weakenStep context newType) sourceTerm) midTerm ∧
      Step.parStar
        (Term.rename (TermRenaming.weakenStep context newType) targetTerm) midTerm :=
  Conv.rename_equivariant_fwd_parJoin (TermRenaming.weakenStep context newType)
    convertibility

end LeanFX2
