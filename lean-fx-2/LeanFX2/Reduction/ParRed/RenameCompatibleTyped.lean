import LeanFX2.Reduction.ParRed.ParInductive
import LeanFX2.Term.Rename

/-! # Reduction/ParRed/RenameCompatibleTyped

Phase A.0 of the typed `Step.par.rename_compatible_typed` headline
(#2027 unblock-C.t6.stepCompat, forward direction).  This file ships
exactly the reflexive arm; subsequent ralph-loop iterations extend the
cascade per Step.par constructor.

The full headline (target of #2027) is the typed counterpart to
`RawStep.par.rename_compatible` at
`Reduction/RawParCompatible/NamedCompatibility.lean:20`:

    theorem Step.par.rename_compatible_typed
        (termRenaming : TermRenaming sourceCtx targetCtx rho)
        (parallelStep : Step.par beforeTerm afterTerm) :
        Step.par (Term.rename termRenaming beforeTerm)
                 (Term.rename termRenaming afterTerm)

It proves by induction on `parallelStep` over Step.par's ~120
constructors.  The refl arm — `Step.par.refl beforeTerm` — collapses
to `Step.par.refl (Term.rename termRenaming beforeTerm)`, requiring
no induction hypothesis and no cast.  Ship this first as a sanity
fixture for the cascade architecture.

Architecture note: the typed headline is the residual "step 5" of the
five-step composition documented in the project memory file
`project_block_b_t5_blocker.md` (lines 217 through 234) under
the agent memory directory.  That composition unlocks the entire
Block C cascade (tickets 2027 through 2034) and downstream
Block D (Conv.trans, ticket 2035).  Each Step.par constructor case lives
as its own atomic theorem so successive ralph iterations can land them
without expensive tactics; the eventual universal headline composes
them via Step.par induction.
-/

namespace LeanFX2

namespace Step.par

/-- Reflexive arm of typed-Step.par rename equivariance.

Renaming preserves the trivial Step.par on a single term: if
`someTerm` parallel-reduces to itself by `Step.par.refl`, then so
does its rename-image.  Pure definitional — applies the renamed
`Step.par.refl` constructor directly with no induction hypothesis. -/
theorem rename_compatible_typed_refl
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {someType : Ty level sourceScope}
    {someRaw : RawTerm sourceScope}
    (someTerm : Term sourceCtx someType someRaw) :
    Step.par (Term.rename termRenaming someTerm)
             (Term.rename termRenaming someTerm) :=
  Step.par.refl (Term.rename termRenaming someTerm)

end Step.par

end LeanFX2
