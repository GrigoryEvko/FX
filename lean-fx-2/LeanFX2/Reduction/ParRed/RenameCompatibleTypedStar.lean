import LeanFX2.Reduction.ParRed.RenameCompatibleTyped
import LeanFX2.Reduction.ParStar

/-! # Reduction/ParRed/RenameCompatibleTypedStar

Chain version of typed rename-compatibility (#2028 unblock-C.t6.stepStarCompat).
Lifts the single-step headline `Step.par.rename_compatible_typed` (#2027) over the
reflexive-transitive closure `Step.parStar` by induction on the chain.

Unlike the single-step headline, no `generalizing` is needed: `Step.parStar` is
context-preserving (every node of the chain lives in the same `context`), so the
renaming stays fixed across the induction and the chain induction hypothesis is
directly usable.  Each `trans` link renames its leading single step through the
#2027 headline and prepends it to the renamed tail.

Zero-axiom — the single-step headline is, and the chain lift adds only
`Step.parStar.refl` / `Step.parStar.trans` constructor applications.  Typed
counterpart to the raw `RawStep.parStar` rename-compatibility chain. -/

namespace LeanFX2

namespace Step.parStar

/-- Typed multi-step parallel reduction is compatible with renaming: renaming both
endpoints of a `Step.parStar` chain yields a `Step.parStar` between the
rename-images.  Induct on the chain; the `refl` link maps to the renamed reflexive
chain, and each `trans` link renames its leading `Step.par` through the single-step
headline `Step.par.rename_compatible_typed` and prepends it to the renamed tail. -/
theorem rename_compatible_typed
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {beforeType : Ty level sourceScope} {beforeRaw : RawTerm sourceScope}
    {afterType : Ty level sourceScope} {afterRaw : RawTerm sourceScope}
    {beforeTerm : Term sourceCtx beforeType beforeRaw}
    {afterTerm : Term sourceCtx afterType afterRaw}
    (parallelChain : Step.parStar beforeTerm afterTerm) :
    Step.parStar (Term.rename termRenaming beforeTerm)
                 (Term.rename termRenaming afterTerm) := by
  induction parallelChain with
  | refl someTerm =>
      exact Step.parStar.refl (Term.rename termRenaming someTerm)
  | trans firstStep _restChain restIH =>
      exact Step.parStar.trans
        (Step.par.rename_compatible_typed termRenaming firstStep) restIH

end Step.parStar

end LeanFX2
