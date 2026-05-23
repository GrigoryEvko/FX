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

/-- Cong arm `fst` of typed-Step.par rename equivariance.

If the renamed pair sub-step `Step.par (rename pairSource) (rename
pairTarget)` holds, then the renamed first-projection step holds too.
`Term.rename` on the `fst` ctor carries no type cast, so pushing the
rename through is definitional (`dsimp only [Term.rename]`); the
result is `Step.par.fst` applied to the supplied sub-step.  Single
sub-step premise, no induction hypothesis, no cast — the minimal
delta from the reflexive arm. -/
theorem rename_compatible_typed_fst
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRawSource pairRawTarget : RawTerm sourceScope}
    {pairTermSource :
      Term sourceCtx (Ty.sigmaTy firstType secondType) pairRawSource}
    {pairTermTarget :
      Term sourceCtx (Ty.sigmaTy firstType secondType) pairRawTarget}
    (pairStep :
      Step.par (Term.rename termRenaming pairTermSource)
               (Term.rename termRenaming pairTermTarget)) :
    Step.par
      (Term.rename termRenaming (Term.fst (secondType := secondType) pairTermSource))
      (Term.rename termRenaming (Term.fst (secondType := secondType) pairTermTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.fst pairStep

/-- Cong arm `app` of typed-Step.par rename equivariance.

Non-dependent application reduces in both the function and the
argument position.  `Term.rename` on the `app` ctor carries no type
cast (the `Ty.arrow` result renames automatically), so the rename
push is definitional and the result is `Step.par.app` applied to the
two renamed sub-steps.  Two sub-step premises, no cast. -/
theorem rename_compatible_typed_app
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType codomainType : Ty level sourceScope}
    {functionRawSource functionRawTarget
     argumentRawSource argumentRawTarget : RawTerm sourceScope}
    {functionTermSource :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRawSource}
    {functionTermTarget :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRawTarget}
    {argumentTermSource : Term sourceCtx domainType argumentRawSource}
    {argumentTermTarget : Term sourceCtx domainType argumentRawTarget}
    (functionStep :
      Step.par (Term.rename termRenaming functionTermSource)
               (Term.rename termRenaming functionTermTarget))
    (argumentStep :
      Step.par (Term.rename termRenaming argumentTermSource)
               (Term.rename termRenaming argumentTermTarget)) :
    Step.par
      (Term.rename termRenaming (Term.app functionTermSource argumentTermSource))
      (Term.rename termRenaming (Term.app functionTermTarget argumentTermTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.app functionStep argumentStep

/-- Cong arm `lamPi` of typed-Step.par rename equivariance.

Dependent Π lambda reduces in its body.  `Term.rename` on the `lamPi`
ctor carries no outer type cast — the body recurses under the lifted
renaming `termRenaming.lift domainType` (extending the renaming past
one binder), and the `Ty.piTy` result renames automatically.  So the
push is definitional and the result is `Step.par.lamPi` applied to the
body sub-step taken under the lifted renaming. -/
theorem rename_compatible_typed_lamPi
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRawSource bodyRawTarget : RawTerm (sourceScope + 1)}
    {bodySource :
      Term (sourceCtx.cons domainType) codomainType bodyRawSource}
    {bodyTarget :
      Term (sourceCtx.cons domainType) codomainType bodyRawTarget}
    (bodyStep :
      Step.par (Term.rename (termRenaming.lift domainType) bodySource)
               (Term.rename (termRenaming.lift domainType) bodyTarget)) :
    Step.par
      (Term.rename termRenaming (Term.lamPi (domainType := domainType) bodySource))
      (Term.rename termRenaming (Term.lamPi (domainType := domainType) bodyTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.lamPi bodyStep

/-- Cong arm `natSucc` of typed-Step.par rename equivariance.

Successor reduces in its predecessor.  `Ty.nat` is closed, so
`Term.rename` on `natSucc` carries no type cast and the push is
definitional. -/
theorem rename_compatible_typed_natSucc
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {predecessorRawSource predecessorRawTarget : RawTerm sourceScope}
    {predecessorSource : Term sourceCtx Ty.nat predecessorRawSource}
    {predecessorTarget : Term sourceCtx Ty.nat predecessorRawTarget}
    (predecessorStep :
      Step.par (Term.rename termRenaming predecessorSource)
               (Term.rename termRenaming predecessorTarget)) :
    Step.par
      (Term.rename termRenaming (Term.natSucc predecessorSource))
      (Term.rename termRenaming (Term.natSucc predecessorTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.natSucc predecessorStep

/-- Cong arm `listCons` of typed-Step.par rename equivariance.

Cons reduces in both head and tail.  `Ty.listType` renames
structurally (no `subst0`), so `Term.rename` carries no cast and the
push is definitional. -/
theorem rename_compatible_typed_listCons
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType : Ty level sourceScope}
    {headRawSource headRawTarget tailRawSource tailRawTarget : RawTerm sourceScope}
    {headSource : Term sourceCtx elementType headRawSource}
    {headTarget : Term sourceCtx elementType headRawTarget}
    {tailSource : Term sourceCtx (Ty.listType elementType) tailRawSource}
    {tailTarget : Term sourceCtx (Ty.listType elementType) tailRawTarget}
    (headStep :
      Step.par (Term.rename termRenaming headSource)
               (Term.rename termRenaming headTarget))
    (tailStep :
      Step.par (Term.rename termRenaming tailSource)
               (Term.rename termRenaming tailTarget)) :
    Step.par
      (Term.rename termRenaming (Term.listCons headSource tailSource))
      (Term.rename termRenaming (Term.listCons headTarget tailTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.listCons headStep tailStep

/-- Cong arm `optionSome` of typed-Step.par rename equivariance.

Some reduces in its payload.  `Ty.optionType` renames structurally,
so the push is definitional and cast-free. -/
theorem rename_compatible_typed_optionSome
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType : Ty level sourceScope}
    {valueRawSource valueRawTarget : RawTerm sourceScope}
    {valueSource : Term sourceCtx elementType valueRawSource}
    {valueTarget : Term sourceCtx elementType valueRawTarget}
    (valueStep :
      Step.par (Term.rename termRenaming valueSource)
               (Term.rename termRenaming valueTarget)) :
    Step.par
      (Term.rename termRenaming (Term.optionSome valueSource))
      (Term.rename termRenaming (Term.optionSome valueTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.optionSome valueStep

/-- Cong arm `eitherInl` of typed-Step.par rename equivariance.

Left injection reduces in its payload.  `Ty.eitherType` renames
structurally, so the push is definitional and cast-free. -/
theorem rename_compatible_typed_eitherInl
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftType rightType : Ty level sourceScope}
    {valueRawSource valueRawTarget : RawTerm sourceScope}
    {valueSource : Term sourceCtx leftType valueRawSource}
    {valueTarget : Term sourceCtx leftType valueRawTarget}
    (valueStep :
      Step.par (Term.rename termRenaming valueSource)
               (Term.rename termRenaming valueTarget)) :
    Step.par
      (Term.rename termRenaming (Term.eitherInl (rightType := rightType) valueSource))
      (Term.rename termRenaming (Term.eitherInl (rightType := rightType) valueTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.eitherInl valueStep

/-- Cong arm `eitherInr` of typed-Step.par rename equivariance.

Right injection reduces in its payload.  `Ty.eitherType` renames
structurally, so the push is definitional and cast-free. -/
theorem rename_compatible_typed_eitherInr
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftType rightType : Ty level sourceScope}
    {valueRawSource valueRawTarget : RawTerm sourceScope}
    {valueSource : Term sourceCtx rightType valueRawSource}
    {valueTarget : Term sourceCtx rightType valueRawTarget}
    (valueStep :
      Step.par (Term.rename termRenaming valueSource)
               (Term.rename termRenaming valueTarget)) :
    Step.par
      (Term.rename termRenaming (Term.eitherInr (leftType := leftType) valueSource))
      (Term.rename termRenaming (Term.eitherInr (leftType := leftType) valueTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.eitherInr valueStep

end Step.par

end LeanFX2
