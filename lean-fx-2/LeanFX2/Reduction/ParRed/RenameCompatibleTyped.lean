import LeanFX2.Reduction.ParRed.ParInductive
import LeanFX2.Reduction.ParRed.ParCasts
import LeanFX2.Term.Rename
import LeanFX2.Reduction.RawParCompatible.NamedCompatibility

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

/-- Cong arm `natElim` of typed-Step.par rename equivariance.

Nat elimination reduces in scrutinee, zero branch, and successor
branch.  The motive is non-dependent (`Ty level scope`), so the
result type is closed under renaming and `Term.rename` carries no
cast — definitional push. -/
theorem rename_compatible_typed_natElim
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level sourceScope}
    {scrutineeRawSource scrutineeRawTarget zeroRawSource zeroRawTarget
     succRawSource succRawTarget : RawTerm sourceScope}
    {scrutineeSource : Term sourceCtx Ty.nat scrutineeRawSource}
    {scrutineeTarget : Term sourceCtx Ty.nat scrutineeRawTarget}
    {zeroSource : Term sourceCtx motiveType zeroRawSource}
    {zeroTarget : Term sourceCtx motiveType zeroRawTarget}
    {succSource : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRawSource}
    {succTarget : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRawTarget}
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutineeSource)
               (Term.rename termRenaming scrutineeTarget))
    (zeroStep :
      Step.par (Term.rename termRenaming zeroSource)
               (Term.rename termRenaming zeroTarget))
    (succStep :
      Step.par (Term.rename termRenaming succSource)
               (Term.rename termRenaming succTarget)) :
    Step.par
      (Term.rename termRenaming (Term.natElim scrutineeSource zeroSource succSource))
      (Term.rename termRenaming (Term.natElim scrutineeTarget zeroTarget succTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.natElim scrutineeStep zeroStep succStep

/-- Cong arm `natRec` of typed-Step.par rename equivariance.

Nat recursion reduces in scrutinee, zero branch, and successor
branch.  Non-dependent motive, cast-free push. -/
theorem rename_compatible_typed_natRec
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level sourceScope}
    {scrutineeRawSource scrutineeRawTarget zeroRawSource zeroRawTarget
     succRawSource succRawTarget : RawTerm sourceScope}
    {scrutineeSource : Term sourceCtx Ty.nat scrutineeRawSource}
    {scrutineeTarget : Term sourceCtx Ty.nat scrutineeRawTarget}
    {zeroSource : Term sourceCtx motiveType zeroRawSource}
    {zeroTarget : Term sourceCtx motiveType zeroRawTarget}
    {succSource :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawSource}
    {succTarget :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawTarget}
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutineeSource)
               (Term.rename termRenaming scrutineeTarget))
    (zeroStep :
      Step.par (Term.rename termRenaming zeroSource)
               (Term.rename termRenaming zeroTarget))
    (succStep :
      Step.par (Term.rename termRenaming succSource)
               (Term.rename termRenaming succTarget)) :
    Step.par
      (Term.rename termRenaming (Term.natRec scrutineeSource zeroSource succSource))
      (Term.rename termRenaming (Term.natRec scrutineeTarget zeroTarget succTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.natRec scrutineeStep zeroStep succStep

/-- Cong arm `listElim` of typed-Step.par rename equivariance.

List elimination reduces in scrutinee, nil branch, and cons branch.
Non-dependent motive over structurally-renaming `Ty.listType`,
cast-free push. -/
theorem rename_compatible_typed_listElim
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRawSource scrutineeRawTarget nilRawSource nilRawTarget
     consRawSource consRawTarget : RawTerm sourceScope}
    {scrutineeSource : Term sourceCtx (Ty.listType elementType) scrutineeRawSource}
    {scrutineeTarget : Term sourceCtx (Ty.listType elementType) scrutineeRawTarget}
    {nilSource : Term sourceCtx motiveType nilRawSource}
    {nilTarget : Term sourceCtx motiveType nilRawTarget}
    {consSource :
      Term sourceCtx
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
        consRawSource}
    {consTarget :
      Term sourceCtx
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
        consRawTarget}
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutineeSource)
               (Term.rename termRenaming scrutineeTarget))
    (nilStep :
      Step.par (Term.rename termRenaming nilSource)
               (Term.rename termRenaming nilTarget))
    (consStep :
      Step.par (Term.rename termRenaming consSource)
               (Term.rename termRenaming consTarget)) :
    Step.par
      (Term.rename termRenaming (Term.listElim scrutineeSource nilSource consSource))
      (Term.rename termRenaming (Term.listElim scrutineeTarget nilTarget consTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.listElim scrutineeStep nilStep consStep

/-- Cong arm `optionMatch` of typed-Step.par rename equivariance.

Option matching reduces in scrutinee, none branch, and some branch.
Non-dependent motive over structurally-renaming `Ty.optionType`,
cast-free push. -/
theorem rename_compatible_typed_optionMatch
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRawSource scrutineeRawTarget noneRawSource noneRawTarget
     someRawSource someRawTarget : RawTerm sourceScope}
    {scrutineeSource : Term sourceCtx (Ty.optionType elementType) scrutineeRawSource}
    {scrutineeTarget : Term sourceCtx (Ty.optionType elementType) scrutineeRawTarget}
    {noneSource : Term sourceCtx motiveType noneRawSource}
    {noneTarget : Term sourceCtx motiveType noneRawTarget}
    {someSource : Term sourceCtx (Ty.arrow elementType motiveType) someRawSource}
    {someTarget : Term sourceCtx (Ty.arrow elementType motiveType) someRawTarget}
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutineeSource)
               (Term.rename termRenaming scrutineeTarget))
    (noneStep :
      Step.par (Term.rename termRenaming noneSource)
               (Term.rename termRenaming noneTarget))
    (someStep :
      Step.par (Term.rename termRenaming someSource)
               (Term.rename termRenaming someTarget)) :
    Step.par
      (Term.rename termRenaming (Term.optionMatch scrutineeSource noneSource someSource))
      (Term.rename termRenaming (Term.optionMatch scrutineeTarget noneTarget someTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.optionMatch scrutineeStep noneStep someStep

/-- Cong arm `eitherMatch` of typed-Step.par rename equivariance.

Either matching reduces in scrutinee, left branch, and right branch.
Non-dependent motive over structurally-renaming `Ty.eitherType`,
cast-free push. -/
theorem rename_compatible_typed_eitherMatch
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftType rightType motiveType : Ty level sourceScope}
    {scrutineeRawSource scrutineeRawTarget leftRawSource leftRawTarget
     rightRawSource rightRawTarget : RawTerm sourceScope}
    {scrutineeSource :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRawSource}
    {scrutineeTarget :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRawTarget}
    {leftSource : Term sourceCtx (Ty.arrow leftType motiveType) leftRawSource}
    {leftTarget : Term sourceCtx (Ty.arrow leftType motiveType) leftRawTarget}
    {rightSource : Term sourceCtx (Ty.arrow rightType motiveType) rightRawSource}
    {rightTarget : Term sourceCtx (Ty.arrow rightType motiveType) rightRawTarget}
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutineeSource)
               (Term.rename termRenaming scrutineeTarget))
    (leftStep :
      Step.par (Term.rename termRenaming leftSource)
               (Term.rename termRenaming leftTarget))
    (rightStep :
      Step.par (Term.rename termRenaming rightSource)
               (Term.rename termRenaming rightTarget)) :
    Step.par
      (Term.rename termRenaming (Term.eitherMatch scrutineeSource leftSource rightSource))
      (Term.rename termRenaming (Term.eitherMatch scrutineeTarget leftTarget rightTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.eitherMatch scrutineeStep leftStep rightStep

/-- Cong arm `modIntro` of typed-Step.par rename equivariance.

Modal introduction reduces in its payload.  `Term.rename` on
`modIntro` carries no cast (structural modal-type rename), so the
push is definitional. -/
theorem rename_compatible_typed_modIntro
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {innerType : Ty level sourceScope}
    {innerRawSource innerRawTarget : RawTerm sourceScope}
    {innerSource : Term sourceCtx innerType innerRawSource}
    {innerTarget : Term sourceCtx innerType innerRawTarget}
    (innerStep :
      Step.par (Term.rename termRenaming innerSource)
               (Term.rename termRenaming innerTarget)) :
    Step.par
      (Term.rename termRenaming (Term.modIntro innerSource))
      (Term.rename termRenaming (Term.modIntro innerTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.modIntro innerStep

/-- Cong arm `modElim` of typed-Step.par rename equivariance.

Modal elimination reduces in its payload.  Cast-free push. -/
theorem rename_compatible_typed_modElim
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {innerType : Ty level sourceScope}
    {innerRawSource innerRawTarget : RawTerm sourceScope}
    {innerSource : Term sourceCtx innerType innerRawSource}
    {innerTarget : Term sourceCtx innerType innerRawTarget}
    (innerStep :
      Step.par (Term.rename termRenaming innerSource)
               (Term.rename termRenaming innerTarget)) :
    Step.par
      (Term.rename termRenaming (Term.modElim innerSource))
      (Term.rename termRenaming (Term.modElim innerTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.modElim innerStep

/-- Cong arm `subsume` of typed-Step.par rename equivariance.

Cumulativity subsumption reduces in its payload.  Cast-free push. -/
theorem rename_compatible_typed_subsume
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {innerType : Ty level sourceScope}
    {innerRawSource innerRawTarget : RawTerm sourceScope}
    {innerSource : Term sourceCtx innerType innerRawSource}
    {innerTarget : Term sourceCtx innerType innerRawTarget}
    (innerStep :
      Step.par (Term.rename termRenaming innerSource)
               (Term.rename termRenaming innerTarget)) :
    Step.par
      (Term.rename termRenaming (Term.subsume innerSource))
      (Term.rename termRenaming (Term.subsume innerTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.subsume innerStep

/-- Cong arm `lam` of typed-Step.par rename equivariance (cast-bearing pilot).

Non-dependent arrow lambda reduces in its body.  Unlike the cast-free
arms, `Term.rename` on `lam` carries a `Ty.weaken_rename_commute`
cast: the renamed body lands at `codomainType.weaken.rename rho.lift`
but the `lam` ctor needs it at `(codomainType.rename rho).weaken`.

Because the cong rule keeps `codomainType` fixed across source and
target, the SAME cast applies to both endpoints, so the entire body
`Step.par` transports along one equality `h ▸ bodyStep` — `▸`
rewrites the shared `Ty` index in both positions simultaneously,
exploiting `Step.par`'s heterogeneous source/target indices.  This is
the reusable cast-transport pattern for the rest of the cast-bearing
cluster (appPi / snd / pair / boolElim / cubical). -/
theorem rename_compatible_typed_lam
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType codomainType : Ty level sourceScope}
    {bodyRawSource bodyRawTarget : RawTerm (sourceScope + 1)}
    {bodySource : Term (sourceCtx.cons domainType) codomainType.weaken bodyRawSource}
    {bodyTarget : Term (sourceCtx.cons domainType) codomainType.weaken bodyRawTarget}
    (bodyStep :
      Step.par (Term.rename (termRenaming.lift domainType) bodySource)
               (Term.rename (termRenaming.lift domainType) bodyTarget)) :
    Step.par
      (Term.rename termRenaming (Term.lam (codomainType := codomainType) bodySource))
      (Term.rename termRenaming (Term.lam (codomainType := codomainType) bodyTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.lam
    (Step.par.castTargetType (Ty.weaken_rename_commute rho codomainType)
      (Step.par.castSourceType (Ty.weaken_rename_commute rho codomainType) bodyStep))

/-- Cong arm `appPi` of typed-Step.par rename equivariance (cast-bearing).

Dependent Π application reduces in function and argument.  `Term.rename`
casts the whole `appPi` result by `(Ty.subst0_rename_commute …).symm`,
and crucially the source and target casts DIFFER (they depend on
`argumentRawSource` vs `argumentRawTarget`).  So the two endpoints are
transported separately: `castSourceType` with the source cast,
`castTargetType` with the target cast, around `Step.par.appPi`. -/
theorem rename_compatible_typed_appPi
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType : Ty level sourceScope} {codomainType : Ty level (sourceScope + 1)}
    {functionRawSource functionRawTarget
     argumentRawSource argumentRawTarget : RawTerm sourceScope}
    {functionTermSource :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRawSource}
    {functionTermTarget :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRawTarget}
    {argumentTermSource : Term sourceCtx domainType argumentRawSource}
    {argumentTermTarget : Term sourceCtx domainType argumentRawTarget}
    (functionStep :
      Step.par (Term.rename termRenaming functionTermSource)
               (Term.rename termRenaming functionTermTarget))
    (argumentStep :
      Step.par (Term.rename termRenaming argumentTermSource)
               (Term.rename termRenaming argumentTermTarget)) :
    Step.par
      (Term.rename termRenaming (Term.appPi functionTermSource argumentTermSource))
      (Term.rename termRenaming (Term.appPi functionTermTarget argumentTermTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.castTargetType
    (Ty.subst0_rename_commute codomainType domainType argumentRawTarget rho).symm
    (Step.par.castSourceType
      (Ty.subst0_rename_commute codomainType domainType argumentRawSource rho).symm
      (Step.par.appPi functionStep argumentStep))

/-- Cong arm `snd` of typed-Step.par rename equivariance (cast-bearing).

Second projection reduces in its pair.  `Term.rename` casts the `snd`
result by `(Ty.subst0_rename_commute … (RawTerm.fst pairRaw) …).symm`;
source and target casts differ (`RawTerm.fst pairRawSource` vs
`…Target`), so transport each endpoint separately. -/
theorem rename_compatible_typed_snd
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {firstType : Ty level sourceScope} {secondType : Ty level (sourceScope + 1)}
    {pairRawSource pairRawTarget : RawTerm sourceScope}
    {pairTermSource :
      Term sourceCtx (Ty.sigmaTy firstType secondType) pairRawSource}
    {pairTermTarget :
      Term sourceCtx (Ty.sigmaTy firstType secondType) pairRawTarget}
    (pairStep :
      Step.par (Term.rename termRenaming pairTermSource)
               (Term.rename termRenaming pairTermTarget)) :
    Step.par
      (Term.rename termRenaming (Term.snd (secondType := secondType) pairTermSource))
      (Term.rename termRenaming (Term.snd (secondType := secondType) pairTermTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.castTargetType
    (Ty.subst0_rename_commute secondType firstType (RawTerm.fst pairRawTarget) rho).symm
    (Step.par.castSourceType
      (Ty.subst0_rename_commute secondType firstType (RawTerm.fst pairRawSource) rho).symm
      (Step.par.snd pairStep))

/-- Cong arm `pair` of typed-Step.par rename equivariance (cast-bearing).

Pair reduces in both components.  Unlike appPi/snd the cast sits on the
SECOND component inside the pair (forward `Ty.subst0_rename_commute`,
not `.symm`), so the second-component step is transported (source and
target casts differ via `firstRawSource`/`firstRawTarget`) while the
first component is cast-free. -/
theorem rename_compatible_typed_pair
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {firstType : Ty level sourceScope} {secondType : Ty level (sourceScope + 1)}
    {firstRawSource firstRawTarget
     secondRawSource secondRawTarget : RawTerm sourceScope}
    {firstValueSource : Term sourceCtx firstType firstRawSource}
    {firstValueTarget : Term sourceCtx firstType firstRawTarget}
    {secondValueSource :
      Term sourceCtx (secondType.subst0 firstType firstRawSource) secondRawSource}
    {secondValueTarget :
      Term sourceCtx (secondType.subst0 firstType firstRawTarget) secondRawTarget}
    (firstStep :
      Step.par (Term.rename termRenaming firstValueSource)
               (Term.rename termRenaming firstValueTarget))
    (secondStep :
      Step.par (Term.rename termRenaming secondValueSource)
               (Term.rename termRenaming secondValueTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.pair (secondType := secondType) firstValueSource secondValueSource))
      (Term.rename termRenaming
        (Term.pair (secondType := secondType) firstValueTarget secondValueTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.pair firstStep
    (Step.par.castTargetType
      (Ty.subst0_rename_commute secondType firstType firstRawTarget rho)
      (Step.par.castSourceType
        (Ty.subst0_rename_commute secondType firstType firstRawSource rho)
        secondStep))

/-- Cong arm `boolElim` of typed-Step.par rename equivariance (cast-bearing, mixed).

Boolean elimination reduces in scrutinee and both branches.  This is the
first arm to combine BOTH cast directions in a single term.  `Term.rename`
on `boolElim` carries three `Ty.subst0_rename_commute` casts:

  * an OUTER `.symm` cast on the whole result, keyed on the scrutinee raw
    (`scrutineeRaw`), so the source and target casts DIFFER — transported
    separately, exactly the `appPi`/`snd` pattern; and
  * two INNER forward casts on the then/else branches, keyed on the CLOSED
    raw constants `RawTerm.boolTrue` / `RawTerm.boolFalse`.  Closed constants
    rename to themselves by `rfl`, so the SAME equality serves both endpoints
    of each branch step — the constant-keyed flavour of the `pair` cast.

Reconstruct inside-out: cast each branch step forward to the renamed motive
`(motiveType.rename rho.lift).subst0 Ty.bool <const>` (both endpoints via the
one constant-keyed equality), assemble `Step.par.boolElim` (its `motiveType`
implicit is inferred from the cast branch types), then transport the assembled
step's two endpoints by the differing scrutinee-keyed `.symm` casts. -/
theorem rename_compatible_typed_boolElim
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level (sourceScope + 1)}
    {scrutineeRawSource scrutineeRawTarget thenRawSource thenRawTarget
     elseRawSource elseRawTarget : RawTerm sourceScope}
    {scrutineeSource : Term sourceCtx Ty.bool scrutineeRawSource}
    {scrutineeTarget : Term sourceCtx Ty.bool scrutineeRawTarget}
    {thenSource :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRawSource}
    {thenTarget :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRawTarget}
    {elseSource :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRawSource}
    {elseTarget :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRawTarget}
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutineeSource)
               (Term.rename termRenaming scrutineeTarget))
    (thenStep :
      Step.par (Term.rename termRenaming thenSource)
               (Term.rename termRenaming thenTarget))
    (elseStep :
      Step.par (Term.rename termRenaming elseSource)
               (Term.rename termRenaming elseTarget)) :
    Step.par
      (Term.rename termRenaming (Term.boolElim scrutineeSource thenSource elseSource))
      (Term.rename termRenaming (Term.boolElim scrutineeTarget thenTarget elseTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.castTargetType
    (Ty.subst0_rename_commute motiveType Ty.bool scrutineeRawTarget rho).symm
    (Step.par.castSourceType
      (Ty.subst0_rename_commute motiveType Ty.bool scrutineeRawSource rho).symm
      (Step.par.boolElim
        scrutineeStep
        (Step.par.castTargetType
          (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho)
          (Step.par.castSourceType
            (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho)
            thenStep))
        (Step.par.castTargetType
          (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho)
          (Step.par.castSourceType
            (Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho)
            elseStep))))

/-- Cong arm `idJ` of typed-Step.par rename equivariance.

HoTT identity-elimination (J) reduces in its base case and its identity
witness.  `Term.rename` on `idJ` is cast-free — the witness sits at the
structurally-renaming `Ty.id carrier leftEndpoint rightEndpoint` and the
base at the non-dependent `motiveType`, so the rename push is definitional
(`dsimp only [Term.rename]`) and the result is `Step.par.idJ` on the two
renamed sub-steps. -/
theorem rename_compatible_typed_idJ
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRawSource baseRawTarget witnessRawSource witnessRawTarget : RawTerm sourceScope}
    {baseSource : Term sourceCtx motiveType baseRawSource}
    {baseTarget : Term sourceCtx motiveType baseRawTarget}
    {witnessSource :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRawSource}
    {witnessTarget :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRawTarget}
    (baseStep :
      Step.par (Term.rename termRenaming baseSource)
               (Term.rename termRenaming baseTarget))
    (witnessStep :
      Step.par (Term.rename termRenaming witnessSource)
               (Term.rename termRenaming witnessTarget)) :
    Step.par
      (Term.rename termRenaming (Term.idJ baseSource witnessSource))
      (Term.rename termRenaming (Term.idJ baseTarget witnessTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.idJ baseStep witnessStep

/-- Cong arm `oeqJCong` of typed-Step.par rename equivariance.

Observational-equality elimination (J) reduces in its base case and its
observational witness.  Cast-free: the witness sits at the structurally-
renaming `Ty.oeq carrier leftEndpoint rightEndpoint`, the base at the
non-dependent `motiveType` — definitional push, then `Step.par.oeqJCong`. -/
theorem rename_compatible_typed_oeqJCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRawSource baseRawTarget witnessRawSource witnessRawTarget : RawTerm sourceScope}
    {baseSource : Term sourceCtx motiveType baseRawSource}
    {baseTarget : Term sourceCtx motiveType baseRawTarget}
    {witnessSource :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRawSource}
    {witnessTarget :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRawTarget}
    (baseStep :
      Step.par (Term.rename termRenaming baseSource)
               (Term.rename termRenaming baseTarget))
    (witnessStep :
      Step.par (Term.rename termRenaming witnessSource)
               (Term.rename termRenaming witnessTarget)) :
    Step.par
      (Term.rename termRenaming (Term.oeqJ baseSource witnessSource))
      (Term.rename termRenaming (Term.oeqJ baseTarget witnessTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.oeqJCong baseStep witnessStep

/-- Cong arm `idStrictRecCong` of typed-Step.par rename equivariance.

Strict-identity recursion reduces in its base case and its strict-identity
witness.  Cast-free: the witness sits at the structurally-renaming
`Ty.idStrict carrier leftEndpoint rightEndpoint`, the base at the
non-dependent `motiveType`.  The mode-side condition `modeIsStrict :
mode = Mode.strict` threads through unchanged (renaming does not touch the
mode index), so the push is definitional and the result is
`Step.par.idStrictRecCong modeIsStrict` on the two renamed sub-steps. -/
theorem rename_compatible_typed_idStrictRecCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {motiveType : Ty level sourceScope}
    {baseRawSource baseRawTarget witnessRawSource witnessRawTarget : RawTerm sourceScope}
    {baseSource : Term sourceCtx motiveType baseRawSource}
    {baseTarget : Term sourceCtx motiveType baseRawTarget}
    {witnessSource :
      Term sourceCtx (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRawSource}
    {witnessTarget :
      Term sourceCtx (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRawTarget}
    (baseStep :
      Step.par (Term.rename termRenaming baseSource)
               (Term.rename termRenaming baseTarget))
    (witnessStep :
      Step.par (Term.rename termRenaming witnessSource)
               (Term.rename termRenaming witnessTarget)) :
    Step.par
      (Term.rename termRenaming (Term.idStrictRec modeIsStrict baseSource witnessSource))
      (Term.rename termRenaming (Term.idStrictRec modeIsStrict baseTarget witnessTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.idStrictRecCong modeIsStrict baseStep witnessStep

/-- Cong arm `intervalOppCong` of typed-Step.par rename equivariance.

Interval negation reduces in its operand.  `Ty.interval` is closed, so
`Term.rename` carries no cast and the push is definitional. -/
theorem rename_compatible_typed_intervalOppCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {innerRawSource innerRawTarget : RawTerm sourceScope}
    {innerSource : Term sourceCtx Ty.interval innerRawSource}
    {innerTarget : Term sourceCtx Ty.interval innerRawTarget}
    (innerStep :
      Step.par (Term.rename termRenaming innerSource)
               (Term.rename termRenaming innerTarget)) :
    Step.par
      (Term.rename termRenaming (Term.intervalOpp innerSource))
      (Term.rename termRenaming (Term.intervalOpp innerTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.intervalOppCong innerStep

/-- Cong arm `intervalMeetCong` of typed-Step.par rename equivariance.

Interval meet reduces in both arguments, each at the closed `Ty.interval`.
Cast-free definitional push, two sub-steps. -/
theorem rename_compatible_typed_intervalMeetCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftRawSource leftRawTarget rightRawSource rightRawTarget : RawTerm sourceScope}
    {leftSource : Term sourceCtx Ty.interval leftRawSource}
    {leftTarget : Term sourceCtx Ty.interval leftRawTarget}
    {rightSource : Term sourceCtx Ty.interval rightRawSource}
    {rightTarget : Term sourceCtx Ty.interval rightRawTarget}
    (leftStep :
      Step.par (Term.rename termRenaming leftSource)
               (Term.rename termRenaming leftTarget))
    (rightStep :
      Step.par (Term.rename termRenaming rightSource)
               (Term.rename termRenaming rightTarget)) :
    Step.par
      (Term.rename termRenaming (Term.intervalMeet leftSource rightSource))
      (Term.rename termRenaming (Term.intervalMeet leftTarget rightTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.intervalMeetCong leftStep rightStep

/-- Cong arm `intervalJoinCong` of typed-Step.par rename equivariance.

Interval join reduces in both arguments at the closed `Ty.interval`.
Cast-free definitional push, two sub-steps. -/
theorem rename_compatible_typed_intervalJoinCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftRawSource leftRawTarget rightRawSource rightRawTarget : RawTerm sourceScope}
    {leftSource : Term sourceCtx Ty.interval leftRawSource}
    {leftTarget : Term sourceCtx Ty.interval leftRawTarget}
    {rightSource : Term sourceCtx Ty.interval rightRawSource}
    {rightTarget : Term sourceCtx Ty.interval rightRawTarget}
    (leftStep :
      Step.par (Term.rename termRenaming leftSource)
               (Term.rename termRenaming leftTarget))
    (rightStep :
      Step.par (Term.rename termRenaming rightSource)
               (Term.rename termRenaming rightTarget)) :
    Step.par
      (Term.rename termRenaming (Term.intervalJoin leftSource rightSource))
      (Term.rename termRenaming (Term.intervalJoin leftTarget rightTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.intervalJoinCong leftStep rightStep

/-- Cong arm `recordIntroCong` of typed-Step.par rename equivariance.

Single-field record introduction reduces in its field.  The field sits at
the non-dependent `singleFieldType`, so `Term.rename` is cast-free —
definitional push, one sub-step. -/
theorem rename_compatible_typed_recordIntroCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {singleFieldType : Ty level sourceScope}
    {firstRawSource firstRawTarget : RawTerm sourceScope}
    {firstSource : Term sourceCtx singleFieldType firstRawSource}
    {firstTarget : Term sourceCtx singleFieldType firstRawTarget}
    (firstStep :
      Step.par (Term.rename termRenaming firstSource)
               (Term.rename termRenaming firstTarget)) :
    Step.par
      (Term.rename termRenaming (Term.recordIntro firstSource))
      (Term.rename termRenaming (Term.recordIntro firstTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.recordIntroCong firstStep

/-- Cong arm `recordProjCong` of typed-Step.par rename equivariance.

Single-field record projection reduces in its record, which sits at the
structurally-renaming `Ty.record singleFieldType`.  Cast-free definitional
push, one sub-step. -/
theorem rename_compatible_typed_recordProjCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {singleFieldType : Ty level sourceScope}
    {recordRawSource recordRawTarget : RawTerm sourceScope}
    {recordSource : Term sourceCtx (Ty.record singleFieldType) recordRawSource}
    {recordTarget : Term sourceCtx (Ty.record singleFieldType) recordRawTarget}
    (recordStep :
      Step.par (Term.rename termRenaming recordSource)
               (Term.rename termRenaming recordTarget)) :
    Step.par
      (Term.rename termRenaming (Term.recordProj recordSource))
      (Term.rename termRenaming (Term.recordProj recordTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.recordProjCong recordStep

/-- Cong arm `refineIntroCong` of typed-Step.par rename equivariance.

Refinement introduction reduces in its value and its (unit) proof.  The
refinement predicate is type-level data carried unchanged (renamed to
`predicate.rename rho.lift` by `Term.rename`, and `Step.par.refineIntroCong`
infers its own predicate implicit to match), the value sits at the
non-dependent `baseType`, the proof at the closed `Ty.unit` — so the push is
definitional and cast-free, two sub-steps. -/
theorem rename_compatible_typed_refineIntroCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {valueRawSource valueRawTarget proofRawSource proofRawTarget : RawTerm sourceScope}
    {valueSource : Term sourceCtx baseType valueRawSource}
    {valueTarget : Term sourceCtx baseType valueRawTarget}
    {proofSource : Term sourceCtx Ty.unit proofRawSource}
    {proofTarget : Term sourceCtx Ty.unit proofRawTarget}
    (valueStep :
      Step.par (Term.rename termRenaming valueSource)
               (Term.rename termRenaming valueTarget))
    (proofStep :
      Step.par (Term.rename termRenaming proofSource)
               (Term.rename termRenaming proofTarget)) :
    Step.par
      (Term.rename termRenaming (Term.refineIntro predicate valueSource proofSource))
      (Term.rename termRenaming (Term.refineIntro predicate valueTarget proofTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.refineIntroCong valueStep proofStep

/-- Cong arm `refineElimCong` of typed-Step.par rename equivariance.

Refinement elimination reduces in its refined value, which sits at the
structurally-renaming `Ty.refine baseType predicate`.  Cast-free
definitional push, one sub-step. -/
theorem rename_compatible_typed_refineElimCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRawSource refinedRawTarget : RawTerm sourceScope}
    {refinedSource : Term sourceCtx (Ty.refine baseType predicate) refinedRawSource}
    {refinedTarget : Term sourceCtx (Ty.refine baseType predicate) refinedRawTarget}
    (refinedStep :
      Step.par (Term.rename termRenaming refinedSource)
               (Term.rename termRenaming refinedTarget)) :
    Step.par
      (Term.rename termRenaming (Term.refineElim refinedSource))
      (Term.rename termRenaming (Term.refineElim refinedTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.refineElimCong refinedStep

/-- Cong arm `pathAppCong` of typed-Step.par rename equivariance.

Path application reduces in path and interval argument.  `Term.rename` on
`pathApp` is cast-free (path at structurally-renaming `Ty.path`, interval at
closed `Ty.interval`); the univalence side condition
`modeIsUnivalent : mode = Mode.univalent` rides through unchanged. -/
theorem rename_compatible_typed_pathAppCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRawSource pathRawTarget intervalRawSource intervalRawTarget : RawTerm sourceScope}
    {pathSource :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint) pathRawSource}
    {pathTarget :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint) pathRawTarget}
    {intervalSource : Term sourceCtx Ty.interval intervalRawSource}
    {intervalTarget : Term sourceCtx Ty.interval intervalRawTarget}
    (pathStep :
      Step.par (Term.rename termRenaming pathSource)
               (Term.rename termRenaming pathTarget))
    (intervalStep :
      Step.par (Term.rename termRenaming intervalSource)
               (Term.rename termRenaming intervalTarget)) :
    Step.par
      (Term.rename termRenaming (Term.pathApp modeIsUnivalent pathSource intervalSource))
      (Term.rename termRenaming (Term.pathApp modeIsUnivalent pathTarget intervalTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.pathAppCong modeIsUnivalent pathStep intervalStep

/-- Cong arm `glueIntroCong` of typed-Step.par rename equivariance.

Glue introduction reduces in base value and partial value, both at the
non-dependent `baseType`.  Cast-free; `baseType` / `boundaryWitness` /
`modeIsUnivalent` ride through unchanged (renamed in the node, the ctor
infers its implicits to match). -/
theorem rename_compatible_typed_glueIntroCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness : RawTerm sourceScope}
    {baseRawSource baseRawTarget partialRawSource partialRawTarget : RawTerm sourceScope}
    {baseSource : Term sourceCtx baseType baseRawSource}
    {baseTarget : Term sourceCtx baseType baseRawTarget}
    {partialSource : Term sourceCtx baseType partialRawSource}
    {partialTarget : Term sourceCtx baseType partialRawTarget}
    (baseStep :
      Step.par (Term.rename termRenaming baseSource)
               (Term.rename termRenaming baseTarget))
    (partialStep :
      Step.par (Term.rename termRenaming partialSource)
               (Term.rename termRenaming partialTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness baseSource partialSource))
      (Term.rename termRenaming
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness baseTarget partialTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.glueIntroCong modeIsUnivalent baseStep partialStep

/-- Cong arm `glueElimCong` of typed-Step.par rename equivariance.

Glue elimination reduces in its glued value, at the structurally-renaming
`Ty.glue baseType boundaryWitness`.  Cast-free, one sub-step. -/
theorem rename_compatible_typed_glueElimCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness : RawTerm sourceScope}
    {gluedRawSource gluedRawTarget : RawTerm sourceScope}
    {gluedSource : Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRawSource}
    {gluedTarget : Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRawTarget}
    (gluedStep :
      Step.par (Term.rename termRenaming gluedSource)
               (Term.rename termRenaming gluedTarget)) :
    Step.par
      (Term.rename termRenaming (Term.glueElim modeIsUnivalent gluedSource))
      (Term.rename termRenaming (Term.glueElim modeIsUnivalent gluedTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.glueElimCong modeIsUnivalent gluedStep

/-- Cong arm `transpCong` of typed-Step.par rename equivariance.

Transport reduces in its type-path and source value.  Despite the heavy
index list (univalence side condition, universe level + bound, source/target
types and their raw codes), `Term.rename` on `transp` is cast-free — every
`Ty`/`RawTerm` index renames structurally.  The four explicit type/raw-code
arguments of `Step.par.transpCong` are left as `_`: `exact` solves them by
unifying against the renamed goal (and the renamed sub-step types). -/
theorem rename_compatible_typed_transpCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    {sourceType targetType : Ty level sourceScope}
    {sourceTypeRaw targetTypeRaw : RawTerm sourceScope}
    {pathRawSource pathRawTarget sourceRawSource sourceRawTarget : RawTerm sourceScope}
    {typePathSource :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt) sourceTypeRaw targetTypeRaw)
        pathRawSource}
    {typePathTarget :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt) sourceTypeRaw targetTypeRaw)
        pathRawTarget}
    {sourceValueSource : Term sourceCtx sourceType sourceRawSource}
    {sourceValueTarget : Term sourceCtx sourceType sourceRawTarget}
    (typePathStep :
      Step.par (Term.rename termRenaming typePathSource)
               (Term.rename termRenaming typePathTarget))
    (sourceValueStep :
      Step.par (Term.rename termRenaming sourceValueSource)
               (Term.rename termRenaming sourceValueTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.transp modeIsUnivalent universeLevel universeLevelLt sourceType targetType
          sourceTypeRaw targetTypeRaw typePathSource sourceValueSource))
      (Term.rename termRenaming
        (Term.transp modeIsUnivalent universeLevel universeLevelLt sourceType targetType
          sourceTypeRaw targetTypeRaw typePathTarget sourceValueTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.transpCong modeIsUnivalent universeLevel universeLevelLt _ _ _ _
    typePathStep sourceValueStep

/-- Cong arm `hcompCong` of typed-Step.par rename equivariance.

Homogeneous composition reduces in sides and cap, both at the non-dependent
`carrierType`.  Cast-free, two sub-steps. -/
theorem rename_compatible_typed_hcompCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesRawSource sidesRawTarget capRawSource capRawTarget : RawTerm sourceScope}
    {sidesSource : Term sourceCtx carrierType sidesRawSource}
    {sidesTarget : Term sourceCtx carrierType sidesRawTarget}
    {capSource : Term sourceCtx carrierType capRawSource}
    {capTarget : Term sourceCtx carrierType capRawTarget}
    (sidesStep :
      Step.par (Term.rename termRenaming sidesSource)
               (Term.rename termRenaming sidesTarget))
    (capStep :
      Step.par (Term.rename termRenaming capSource)
               (Term.rename termRenaming capTarget)) :
    Step.par
      (Term.rename termRenaming (Term.hcomp modeIsUnivalent sidesSource capSource))
      (Term.rename termRenaming (Term.hcomp modeIsUnivalent sidesTarget capTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.hcompCong modeIsUnivalent sidesStep capStep

/-- Cong arm `hcompPathCong` of typed-Step.par rename equivariance.

Path-shaped homogeneous composition reduces in its path-typed sides and its
cap.  Cast-free; the explicit `leftEndpoint` / `rightEndpoint` raw codes of
`Step.par.hcompPathCong` are passed as `_` and solved by `exact` against the
renamed goal (and the renamed path sub-step type). -/
theorem rename_compatible_typed_hcompPathCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {sidesPathRawSource sidesPathRawTarget capRawSource capRawTarget : RawTerm sourceScope}
    {sidesPathSource :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint) sidesPathRawSource}
    {sidesPathTarget :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint) sidesPathRawTarget}
    {capSource : Term sourceCtx carrierType capRawSource}
    {capTarget : Term sourceCtx carrierType capRawTarget}
    (sidesPathStep :
      Step.par (Term.rename termRenaming sidesPathSource)
               (Term.rename termRenaming sidesPathTarget))
    (capStep :
      Step.par (Term.rename termRenaming capSource)
               (Term.rename termRenaming capTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.hcompPath modeIsUnivalent leftEndpoint rightEndpoint sidesPathSource capSource))
      (Term.rename termRenaming
        (Term.hcompPath modeIsUnivalent leftEndpoint rightEndpoint sidesPathTarget capTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.hcompPathCong modeIsUnivalent _ _ sidesPathStep capStep

/-- Cong arm `codataUnfoldCong` of typed-Step.par rename equivariance.

Codata unfold reduces in its seed state and its transition function.  State
at the non-dependent `stateType`, transition at the structurally-renaming
`Ty.arrow stateType outputType`.  Cast-free, two sub-steps. -/
theorem rename_compatible_typed_codataUnfoldCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {stateType outputType : Ty level sourceScope}
    {stateRawSource stateRawTarget transitionRawSource transitionRawTarget : RawTerm sourceScope}
    {stateSource : Term sourceCtx stateType stateRawSource}
    {stateTarget : Term sourceCtx stateType stateRawTarget}
    {transitionSource : Term sourceCtx (Ty.arrow stateType outputType) transitionRawSource}
    {transitionTarget : Term sourceCtx (Ty.arrow stateType outputType) transitionRawTarget}
    (stateStep :
      Step.par (Term.rename termRenaming stateSource)
               (Term.rename termRenaming stateTarget))
    (transitionStep :
      Step.par (Term.rename termRenaming transitionSource)
               (Term.rename termRenaming transitionTarget)) :
    Step.par
      (Term.rename termRenaming (Term.codataUnfold stateSource transitionSource))
      (Term.rename termRenaming (Term.codataUnfold stateTarget transitionTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.codataUnfoldCong stateStep transitionStep

/-- Cong arm `codataDestCong` of typed-Step.par rename equivariance.

Codata destruction reduces in its codata value, at the structurally-renaming
`Ty.codata stateType outputType`.  Cast-free, one sub-step. -/
theorem rename_compatible_typed_codataDestCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {stateType outputType : Ty level sourceScope}
    {codataRawSource codataRawTarget : RawTerm sourceScope}
    {codataSource : Term sourceCtx (Ty.codata stateType outputType) codataRawSource}
    {codataTarget : Term sourceCtx (Ty.codata stateType outputType) codataRawTarget}
    (codataStep :
      Step.par (Term.rename termRenaming codataSource)
               (Term.rename termRenaming codataTarget)) :
    Step.par
      (Term.rename termRenaming (Term.codataDest codataSource))
      (Term.rename termRenaming (Term.codataDest codataTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.codataDestCong codataStep

/-- Cong arm `sessionSendCong` of typed-Step.par rename equivariance.

Session send reduces in its channel and payload.  Channel at the
structurally-renaming `Ty.session protocolStep`, payload at the non-dependent
`payloadType`; the protocol-step raw rides through (renamed in the node, the
ctor infers its implicit to match).  Cast-free, two sub-steps. -/
theorem rename_compatible_typed_sessionSendCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {protocolStep : RawTerm sourceScope}
    {payloadType : Ty level sourceScope}
    {channelRawSource channelRawTarget payloadRawSource payloadRawTarget : RawTerm sourceScope}
    {channelSource : Term sourceCtx (Ty.session protocolStep) channelRawSource}
    {channelTarget : Term sourceCtx (Ty.session protocolStep) channelRawTarget}
    {payloadSource : Term sourceCtx payloadType payloadRawSource}
    {payloadTarget : Term sourceCtx payloadType payloadRawTarget}
    (channelStep :
      Step.par (Term.rename termRenaming channelSource)
               (Term.rename termRenaming channelTarget))
    (payloadStep :
      Step.par (Term.rename termRenaming payloadSource)
               (Term.rename termRenaming payloadTarget)) :
    Step.par
      (Term.rename termRenaming (Term.sessionSend protocolStep channelSource payloadSource))
      (Term.rename termRenaming (Term.sessionSend protocolStep channelTarget payloadTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.sessionSendCong channelStep payloadStep

/-- Cong arm `sessionRecvCong` of typed-Step.par rename equivariance.

Session receive reduces in its channel, at the structurally-renaming
`Ty.session protocolStep`.  Cast-free, one sub-step. -/
theorem rename_compatible_typed_sessionRecvCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {protocolStep : RawTerm sourceScope}
    {channelRawSource channelRawTarget : RawTerm sourceScope}
    {channelSource : Term sourceCtx (Ty.session protocolStep) channelRawSource}
    {channelTarget : Term sourceCtx (Ty.session protocolStep) channelRawTarget}
    (channelStep :
      Step.par (Term.rename termRenaming channelSource)
               (Term.rename termRenaming channelTarget)) :
    Step.par
      (Term.rename termRenaming (Term.sessionRecv channelSource))
      (Term.rename termRenaming (Term.sessionRecv channelTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.sessionRecvCong channelStep

/-- Cong arm `effectPerformCong` of typed-Step.par rename equivariance.

Effect perform reduces in its operation term and its argument bundle.
`Term.rename` renames `effectTag`, `.map`s the operation signature and the
`CanPerform` witness, and recurses on the two terms — all structural, no
type cast.  Every effect-payload index (`effectTag` / `effectRow` /
`operationSignature` / `canPerformOperation`) is implicit in
`Step.par.effectPerformCong`, so the bare two-step application elaborates and
`exact` resolves the implicits against the renamed goal. -/
theorem rename_compatible_typed_effectPerformCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {effectTag : RawTerm sourceScope}
    {effectRow : Effects.EffectRow}
    {operationSignature : Effects.OperationSignature (Ty level sourceScope)}
    {canPerformOperation : Effects.CanPerform effectRow operationSignature}
    {operationRawSource operationRawTarget argumentsRawSource argumentsRawTarget : RawTerm sourceScope}
    {operationSource :
      Term sourceCtx (Ty.effect operationSignature.argumentCarrier effectTag) operationRawSource}
    {operationTarget :
      Term sourceCtx (Ty.effect operationSignature.argumentCarrier effectTag) operationRawTarget}
    {argumentsSource : Term sourceCtx operationSignature.argumentCarrier argumentsRawSource}
    {argumentsTarget : Term sourceCtx operationSignature.argumentCarrier argumentsRawTarget}
    (operationStep :
      Step.par (Term.rename termRenaming operationSource)
               (Term.rename termRenaming operationTarget))
    (argumentsStep :
      Step.par (Term.rename termRenaming argumentsSource)
               (Term.rename termRenaming argumentsTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationSource argumentsSource))
      (Term.rename termRenaming
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationTarget argumentsTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.effectPerformCong operationStep argumentsStep

/-- Cong arm `cumulUpInnerCong` of typed-Step.par rename equivariance.

Universe cumulativity-up reduces in its inner type code, at the closed-ish
`Ty.universe lowerLevel levelLeLow` (the universe level + bound proofs ride
through unchanged — renaming touches neither).  `Term.rename` on `cumulUp`
is cast-free (it reconstructs the ctor at `targetCtx` and recurses on the
code), so the push is definitional, one sub-step. -/
theorem rename_compatible_typed_cumulUpInnerCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeSourceRaw codeTargetRaw : RawTerm sourceScope}
    {typeCodeSource : Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeSourceRaw}
    {typeCodeTarget : Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeTargetRaw}
    (typeCodeStep :
      Step.par (Term.rename termRenaming typeCodeSource)
               (Term.rename termRenaming typeCodeTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow levelLeHigh typeCodeSource))
      (Term.rename termRenaming
        (Term.cumulUp lowerLevel higherLevel cumulMonotone levelLeLow levelLeHigh typeCodeTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.cumulUpInnerCong lowerLevel higherLevel cumulMonotone
    levelLeLow levelLeHigh typeCodeStep

/-- Reduction arm `eqType` of typed-Step.par rename equivariance.

The first NON-congruence arm: `eqType` is the univalence rfl-fragment
reduction `equivReflIdAtId ⟶ equivReflId` (source and target are DIFFERENT
constructors), so there is no recursive sub-step premise — the headline
induction's `eqType` case has no IH.  Both endpoints rename cast-free
(`equivReflIdAtId innerLevel innerLevelLt (carrier.rename rho)
(carrierRaw.rename rho)` and `equivReflId (carrier.rename rho)`), so after
`dsimp` the goal IS the renamed instance of the same rule; re-apply
`Step.par.eqType` at the renamed `carrier` / `carrierRaw`.  This is the
template for the β/ι reduction arms still to come. -/
theorem rename_compatible_typed_eqType
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level sourceScope)
    (carrierRaw : RawTerm sourceScope) :
    Step.par
      (Term.rename termRenaming
        (Term.equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw))
      (Term.rename termRenaming (Term.equivReflId carrier)) := by
  dsimp only [Term.rename]
  exact Step.par.eqType innerLevel innerLevelLt (carrier.rename rho) (carrierRaw.rename rho)

/-- Cong arm `reflCong` of typed-Step.par rename equivariance (raw-premise).

`Term.refl` carries its witness as a RAW term, so its parallel-cong reduces
via a `RawStep.par` premise, not a typed sub-step.  The headline induction's
`reflCong` case therefore has no typed IH — instead we transport the raw
premise through `RawStep.par.rename_compatible rho` to land at the renamed
raw witnesses, and feed that into `Step.par.reflCong` with the renamed
carrier.  Cast-free (`Term.refl` renames carrier + witness structurally).
This is the template for the raw-premise cong family (refl / funext /
type-codes). -/
theorem rename_compatible_typed_reflCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (carrier : Ty level sourceScope)
    {witnessRawSource witnessRawTarget : RawTerm sourceScope}
    (witnessStep : RawStep.par witnessRawSource witnessRawTarget) :
    Step.par
      (Term.rename termRenaming (Term.refl carrier witnessRawSource))
      (Term.rename termRenaming (Term.refl carrier witnessRawTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.reflCong (carrier.rename rho)
    (RawStep.par.rename_compatible rho witnessStep)

/-- Cong arm `funextReflAtIdCong` of typed-Step.par rename equivariance
(raw-premise).  `Term.funextReflAtId` carries its pointwise-apply body as a
RAW term at `scope + 1`, so the cong reduces via a `RawStep.par` premise.
Transport it through `RawStep.par.rename_compatible rho.lift` (the body lives
under one binder, hence the lifted renaming) and feed `Step.par`
`.funextReflAtIdCong` with the renamed domain/codomain.  Cast-free. -/
theorem rename_compatible_typed_funextReflAtIdCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    {applyRawSource applyRawTarget : RawTerm (sourceScope + 1)}
    (applyStep : RawStep.par applyRawSource applyRawTarget) :
    Step.par
      (Term.rename termRenaming (Term.funextReflAtId domainType codomainType applyRawSource))
      (Term.rename termRenaming (Term.funextReflAtId domainType codomainType applyRawTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.funextReflAtIdCong (domainType.rename rho) (codomainType.rename rho)
    (RawStep.par.rename_compatible rho.lift applyStep)

/-- Cong arm `funextIntroHetCong` of typed-Step.par rename equivariance
(raw-premise, two payloads).  `Term.funextIntroHet` carries TWO raw apply
bodies at `scope + 1`, so the cong reduces via two `RawStep.par` premises;
transport each through `RawStep.par.rename_compatible rho.lift`.  Cast-free. -/
theorem rename_compatible_typed_funextIntroHetCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    {applyARawSource applyARawTarget applyBRawSource applyBRawTarget : RawTerm (sourceScope + 1)}
    (applyAStep : RawStep.par applyARawSource applyARawTarget)
    (applyBStep : RawStep.par applyBRawSource applyBRawTarget) :
    Step.par
      (Term.rename termRenaming
        (Term.funextIntroHet domainType codomainType applyARawSource applyBRawSource))
      (Term.rename termRenaming
        (Term.funextIntroHet domainType codomainType applyARawTarget applyBRawTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.funextIntroHetCong (domainType.rename rho) (codomainType.rename rho)
    (RawStep.par.rename_compatible rho.lift applyAStep)
    (RawStep.par.rename_compatible rho.lift applyBStep)

/-- Cong arm `arrowCodeCong` of typed-Step.par rename equivariance (raw-premise).
`Term.arrowCode` is the universe code for the function type; both of its
payloads are RAW codes at `scope`, so the cong reduces via two `RawStep.par`
premises transported through `RawStep.par.rename_compatible rho`.  The
`levelLe` universe-bound proof is scope-independent and passes through the
renamed reduct unchanged.  Cast-free. -/
theorem rename_compatible_typed_arrowCodeCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRawSource domainCodeRawTarget
     codomainCodeRawSource codomainCodeRawTarget : RawTerm sourceScope}
    (domainStep : RawStep.par domainCodeRawSource domainCodeRawTarget)
    (codomainStep : RawStep.par codomainCodeRawSource codomainCodeRawTarget) :
    Step.par
      (Term.rename termRenaming
        (Term.arrowCode outerLevel levelLe domainCodeRawSource codomainCodeRawSource))
      (Term.rename termRenaming
        (Term.arrowCode outerLevel levelLe domainCodeRawTarget codomainCodeRawTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.arrowCodeCong outerLevel levelLe
    (RawStep.par.rename_compatible rho domainStep)
    (RawStep.par.rename_compatible rho codomainStep)

/-- Cong arm `piTyCodeCong` of typed-Step.par rename equivariance (raw-premise,
binder-shape).  `Term.piTyCode`'s codomain code lives at `scope + 1`, so its
premise transports through `RawStep.par.rename_compatible rho.lift` while the
domain code uses `rho`.  Cast-free. -/
theorem rename_compatible_typed_piTyCodeCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRawSource domainCodeRawTarget : RawTerm sourceScope}
    {codomainCodeRawSource codomainCodeRawTarget : RawTerm (sourceScope + 1)}
    (domainStep : RawStep.par domainCodeRawSource domainCodeRawTarget)
    (codomainStep : RawStep.par codomainCodeRawSource codomainCodeRawTarget) :
    Step.par
      (Term.rename termRenaming
        (Term.piTyCode outerLevel levelLe domainCodeRawSource codomainCodeRawSource))
      (Term.rename termRenaming
        (Term.piTyCode outerLevel levelLe domainCodeRawTarget codomainCodeRawTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.piTyCodeCong outerLevel levelLe
    (RawStep.par.rename_compatible rho domainStep)
    (RawStep.par.rename_compatible rho.lift codomainStep)

/-- Cong arm `sigmaTyCodeCong` of typed-Step.par rename equivariance (raw-premise,
binder-shape).  Like `piTyCodeCong`, the second code lives at `scope + 1` and
transports through `rho.lift`; the first code uses `rho`.  Cast-free. -/
theorem rename_compatible_typed_sigmaTyCodeCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRawSource firstCodeRawTarget : RawTerm sourceScope}
    {secondCodeRawSource secondCodeRawTarget : RawTerm (sourceScope + 1)}
    (firstStep : RawStep.par firstCodeRawSource firstCodeRawTarget)
    (secondStep : RawStep.par secondCodeRawSource secondCodeRawTarget) :
    Step.par
      (Term.rename termRenaming
        (Term.sigmaTyCode outerLevel levelLe firstCodeRawSource secondCodeRawSource))
      (Term.rename termRenaming
        (Term.sigmaTyCode outerLevel levelLe firstCodeRawTarget secondCodeRawTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.sigmaTyCodeCong outerLevel levelLe
    (RawStep.par.rename_compatible rho firstStep)
    (RawStep.par.rename_compatible rho.lift secondStep)

/-- Cong arm `productCodeCong` of typed-Step.par rename equivariance (raw-premise).
Both component codes are at `scope`, transported through `rho`.  Cast-free. -/
theorem rename_compatible_typed_productCodeCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRawSource firstCodeRawTarget
     secondCodeRawSource secondCodeRawTarget : RawTerm sourceScope}
    (firstStep : RawStep.par firstCodeRawSource firstCodeRawTarget)
    (secondStep : RawStep.par secondCodeRawSource secondCodeRawTarget) :
    Step.par
      (Term.rename termRenaming
        (Term.productCode outerLevel levelLe firstCodeRawSource secondCodeRawSource))
      (Term.rename termRenaming
        (Term.productCode outerLevel levelLe firstCodeRawTarget secondCodeRawTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.productCodeCong outerLevel levelLe
    (RawStep.par.rename_compatible rho firstStep)
    (RawStep.par.rename_compatible rho secondStep)

/-- Cong arm `sumCodeCong` of typed-Step.par rename equivariance (raw-premise).
Both side codes are at `scope`, transported through `rho`.  Cast-free. -/
theorem rename_compatible_typed_sumCodeCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRawSource leftCodeRawTarget
     rightCodeRawSource rightCodeRawTarget : RawTerm sourceScope}
    (leftStep : RawStep.par leftCodeRawSource leftCodeRawTarget)
    (rightStep : RawStep.par rightCodeRawSource rightCodeRawTarget) :
    Step.par
      (Term.rename termRenaming
        (Term.sumCode outerLevel levelLe leftCodeRawSource rightCodeRawSource))
      (Term.rename termRenaming
        (Term.sumCode outerLevel levelLe leftCodeRawTarget rightCodeRawTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.sumCodeCong outerLevel levelLe
    (RawStep.par.rename_compatible rho leftStep)
    (RawStep.par.rename_compatible rho rightStep)

/-- Cong arm `listCodeCong` of typed-Step.par rename equivariance (raw-premise,
single payload).  The element code at `scope` transports through `rho`.
Cast-free. -/
theorem rename_compatible_typed_listCodeCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRawSource elementCodeRawTarget : RawTerm sourceScope}
    (elementStep : RawStep.par elementCodeRawSource elementCodeRawTarget) :
    Step.par
      (Term.rename termRenaming
        (Term.listCode outerLevel levelLe elementCodeRawSource))
      (Term.rename termRenaming
        (Term.listCode outerLevel levelLe elementCodeRawTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.listCodeCong outerLevel levelLe
    (RawStep.par.rename_compatible rho elementStep)

/-- Cong arm `optionCodeCong` of typed-Step.par rename equivariance (raw-premise,
single payload).  The element code at `scope` transports through `rho`.
Cast-free. -/
theorem rename_compatible_typed_optionCodeCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRawSource elementCodeRawTarget : RawTerm sourceScope}
    (elementStep : RawStep.par elementCodeRawSource elementCodeRawTarget) :
    Step.par
      (Term.rename termRenaming
        (Term.optionCode outerLevel levelLe elementCodeRawSource))
      (Term.rename termRenaming
        (Term.optionCode outerLevel levelLe elementCodeRawTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.optionCodeCong outerLevel levelLe
    (RawStep.par.rename_compatible rho elementStep)

/-- Cong arm `eitherCodeCong` of typed-Step.par rename equivariance (raw-premise).
Both side codes are at `scope`, transported through `rho`.  Cast-free. -/
theorem rename_compatible_typed_eitherCodeCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRawSource leftCodeRawTarget
     rightCodeRawSource rightCodeRawTarget : RawTerm sourceScope}
    (leftStep : RawStep.par leftCodeRawSource leftCodeRawTarget)
    (rightStep : RawStep.par rightCodeRawSource rightCodeRawTarget) :
    Step.par
      (Term.rename termRenaming
        (Term.eitherCode outerLevel levelLe leftCodeRawSource rightCodeRawSource))
      (Term.rename termRenaming
        (Term.eitherCode outerLevel levelLe leftCodeRawTarget rightCodeRawTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.eitherCodeCong outerLevel levelLe
    (RawStep.par.rename_compatible rho leftStep)
    (RawStep.par.rename_compatible rho rightStep)

/-- Cong arm `idCodeCong` of typed-Step.par rename equivariance (raw-premise,
three payloads).  Carrier code and both endpoints are at `scope`, transported
through `rho`.  Cast-free. -/
theorem rename_compatible_typed_idCodeCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {carrierCodeRawSource carrierCodeRawTarget
     leftRawSource leftRawTarget rightRawSource rightRawTarget : RawTerm sourceScope}
    (carrierStep : RawStep.par carrierCodeRawSource carrierCodeRawTarget)
    (leftStep : RawStep.par leftRawSource leftRawTarget)
    (rightStep : RawStep.par rightRawSource rightRawTarget) :
    Step.par
      (Term.rename termRenaming
        (Term.idCode outerLevel levelLe carrierCodeRawSource leftRawSource rightRawSource))
      (Term.rename termRenaming
        (Term.idCode outerLevel levelLe carrierCodeRawTarget leftRawTarget rightRawTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.idCodeCong outerLevel levelLe
    (RawStep.par.rename_compatible rho carrierStep)
    (RawStep.par.rename_compatible rho leftStep)
    (RawStep.par.rename_compatible rho rightStep)

/-- Cong arm `equivCodeCong` of typed-Step.par rename equivariance (raw-premise).
Both carrier codes are at `scope`, transported through `rho`.  Cast-free. -/
theorem rename_compatible_typed_equivCodeCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {carrierARawSource carrierARawTarget
     carrierBRawSource carrierBRawTarget : RawTerm sourceScope}
    (carrierAStep : RawStep.par carrierARawSource carrierARawTarget)
    (carrierBStep : RawStep.par carrierBRawSource carrierBRawTarget) :
    Step.par
      (Term.rename termRenaming
        (Term.equivCode outerLevel levelLe carrierARawSource carrierBRawSource))
      (Term.rename termRenaming
        (Term.equivCode outerLevel levelLe carrierARawTarget carrierBRawTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.equivCodeCong outerLevel levelLe
    (RawStep.par.rename_compatible rho carrierAStep)
    (RawStep.par.rename_compatible rho carrierBStep)

/-- Cong arm `equivAppCong` of typed-Step.par rename equivariance (typed-IH).
`Term.equivApp` applies an equivalence to an argument; both are typed
sub-terms, so the cong threads two typed `Step.par` sub-derivations (delivered
pre-renamed as hypotheses).  `Term.rename` on `equivApp` recurses structurally
on both children with no outer type cast (`Ty.equiv` and the carriers are
non-binder), so the push is definitional. -/
theorem rename_compatible_typed_equivAppCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrierA carrierB : Ty level sourceScope}
    {equivRawSource equivRawTarget
     argumentRawSource argumentRawTarget : RawTerm sourceScope}
    {equivSource : Term sourceCtx (Ty.equiv carrierA carrierB) equivRawSource}
    {equivTarget : Term sourceCtx (Ty.equiv carrierA carrierB) equivRawTarget}
    {argumentSource : Term sourceCtx carrierA argumentRawSource}
    {argumentTarget : Term sourceCtx carrierA argumentRawTarget}
    (equivStep :
      Step.par (Term.rename termRenaming equivSource)
               (Term.rename termRenaming equivTarget))
    (argumentStep :
      Step.par (Term.rename termRenaming argumentSource)
               (Term.rename termRenaming argumentTarget)) :
    Step.par
      (Term.rename termRenaming (Term.equivApp equivSource argumentSource))
      (Term.rename termRenaming (Term.equivApp equivTarget argumentTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.equivAppCong equivStep argumentStep

/-- Cong arm `equivApplyCong` of typed-Step.par rename equivariance (typed-IH).
Univalence-β application `Term.equivApply` mirrors `equivApp`: two typed
sub-terms (equivalence + argument), two typed `Step.par` sub-derivations, a
cast-free structural rename.  Definitional push. -/
theorem rename_compatible_typed_equivApplyCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrierA carrierB : Ty level sourceScope}
    {equivRawSource equivRawTarget
     argumentRawSource argumentRawTarget : RawTerm sourceScope}
    {equivSource : Term sourceCtx (Ty.equiv carrierA carrierB) equivRawSource}
    {equivTarget : Term sourceCtx (Ty.equiv carrierA carrierB) equivRawTarget}
    {argumentSource : Term sourceCtx carrierA argumentRawSource}
    {argumentTarget : Term sourceCtx carrierA argumentRawTarget}
    (equivStep :
      Step.par (Term.rename termRenaming equivSource)
               (Term.rename termRenaming equivTarget))
    (argumentStep :
      Step.par (Term.rename termRenaming argumentSource)
               (Term.rename termRenaming argumentTarget)) :
    Step.par
      (Term.rename termRenaming (Term.equivApply equivSource argumentSource))
      (Term.rename termRenaming (Term.equivApply equivTarget argumentTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.equivApplyCong equivStep argumentStep

/-- Cong arm `uaIntroHetCong` of typed-Step.par rename equivariance (typed-IH,
single sub-term).  `Term.uaIntroHet` packages an equivalence witness under a
universe-level + cumul-witness header and two schematic carrier raws; the cong
reduces in the single typed `equivWitness` sub-term.  `Term.rename` renames the
carrier raws via `rho` and recurses on the witness with no cast — the witness's
raw `RawTerm.equivIntro _ _` renames pointwise.  The scope-independent
`innerLevel`/`innerLevelLt` pass through unchanged. -/
theorem rename_compatible_typed_uaIntroHetCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRawSource forwardRawTarget
     backwardRawSource backwardRawTarget : RawTerm sourceScope}
    {equivWitnessSource :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRawSource backwardRawSource)}
    {equivWitnessTarget :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRawTarget backwardRawTarget)}
    (equivWitnessStep :
      Step.par (Term.rename termRenaming equivWitnessSource)
               (Term.rename termRenaming equivWitnessTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw equivWitnessSource))
      (Term.rename termRenaming
        (Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw equivWitnessTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.uaIntroHetCong innerLevel innerLevelLt
    (carrierARaw.rename rho) (carrierBRaw.rename rho) equivWitnessStep

/-- Cong arm `uaToEquivCong` of typed-Step.par rename equivariance (typed-IH,
single sub-term).  The univalence-β extractor `Term.uaToEquiv` reduces in its
single typed `proof` sub-term (a path at the universe).  `Term.rename` renames
the two carrier types + two schematic type-code raws via `rho` and recurses on
the proof; the proof's type `Ty.id (Ty.universe ...) leftTyRaw rightTyRaw`
renames with the universe constant and the endpoints via `rho`.  No cast. -/
theorem rename_compatible_typed_uaToEquivCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level sourceScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    {proofRawSource proofRawTarget : RawTerm sourceScope}
    {proofSource :
      Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRawSource}
    {proofTarget :
      Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
        proofRawTarget}
    (proofStep :
      Step.par (Term.rename termRenaming proofSource)
               (Term.rename termRenaming proofTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy
          leftTyRaw rightTyRaw proofSource))
      (Term.rename termRenaming
        (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy
          leftTyRaw rightTyRaw proofTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.uaToEquivCong innerLevel innerLevelLt
    (leftTy.rename rho) (rightTy.rename rho)
    (leftTyRaw.rename rho) (rightTyRaw.rename rho) proofStep

/-- Cong arm `oeqReflCong` of typed-Step.par rename equivariance (raw-premise).
`Term.oeqRefl` is an observational-equality refl whose witness is a RAW term, so
the cong reduces via a `RawStep.par` premise transported through
`RawStep.par.rename_compatible rho`.  The carrier renames structurally.
Cast-free. -/
theorem rename_compatible_typed_oeqReflCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (carrier : Ty level sourceScope)
    {witnessRawSource witnessRawTarget : RawTerm sourceScope}
    (witnessStep : RawStep.par witnessRawSource witnessRawTarget) :
    Step.par
      (Term.rename termRenaming (Term.oeqRefl carrier witnessRawSource))
      (Term.rename termRenaming (Term.oeqRefl carrier witnessRawTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.oeqReflCong (RawStep.par.rename_compatible rho witnessStep)

/-- Cong arm `idStrictReflCong` of typed-Step.par rename equivariance
(raw-premise).  `Term.idStrictRefl` is the strict-identity refl (only in
`Mode.strict`); its witness is a RAW term so the cong reduces via a
`RawStep.par` premise transported through `RawStep.par.rename_compatible rho`.
Renaming is mode-preserving, so the `modeIsStrict` proof rides through unchanged;
the carrier renames structurally.  Cast-free. -/
theorem rename_compatible_typed_idStrictReflCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level sourceScope)
    {witnessRawSource witnessRawTarget : RawTerm sourceScope}
    (witnessStep : RawStep.par witnessRawSource witnessRawTarget) :
    Step.par
      (Term.rename termRenaming (Term.idStrictRefl modeIsStrict carrier witnessRawSource))
      (Term.rename termRenaming (Term.idStrictRefl modeIsStrict carrier witnessRawTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.idStrictReflCong modeIsStrict
    (RawStep.par.rename_compatible rho witnessStep)

/-- Cong arm `pathLamCong` of typed-Step.par rename equivariance (cast-bearing,
binder).  A cubical path-lambda reduces in its body, which lives at the WEAKENED
carrier `carrierType.weaken` under an interval binder.  `Term.rename` on
`pathLam` recurses the body under the lifted renaming and then transports its
type by `Ty.weaken_rename_commute rho carrierType` (rename-past-weaken commute).
The body type is the SAME on both source and target endpoints (it depends only
on `carrierType`, fixed across the reduction), so the single body step is cast
on BOTH endpoints by the one equality before assembling `pathLamCong`. -/
theorem rename_compatible_typed_pathLamCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level sourceScope)
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {bodyRawSource bodyRawTarget : RawTerm (sourceScope + 1)}
    {bodySource : Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRawSource}
    {bodyTarget : Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRawTarget}
    (bodyStep :
      Step.par (Term.rename (termRenaming.lift Ty.interval) bodySource)
               (Term.rename (termRenaming.lift Ty.interval) bodyTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint bodySource))
      (Term.rename termRenaming
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint bodyTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.pathLamCong modeIsUnivalent
    (Step.par.castTargetType (Ty.weaken_rename_commute rho carrierType)
      (Step.par.castSourceType (Ty.weaken_rename_commute rho carrierType) bodyStep))

/-- Cong arm `oeqFunextCong` of typed-Step.par rename equivariance (cast-bearing).
Observational-equality funext reduces in its single pointwise-equality proof,
whose type is `oeqFunextPointwiseType domainType codomainType leftFunctionRaw
rightFunctionRaw`.  `Term.rename` on `oeqFunext` recurses the proof and
transports its type by `oeqFunextPointwiseType_rename` (the schematic
type renames structurally).  The proof type is fixed across the reduction
(the function raws are explicit ctor args, not the reduced child), so cast the
single proof step on BOTH endpoints by the one equality before assembling
`oeqFunextCong`. -/
theorem rename_compatible_typed_oeqFunextCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    (leftFunctionRaw rightFunctionRaw : RawTerm sourceScope)
    {pointwiseRawSource pointwiseRawTarget : RawTerm sourceScope}
    {pointwiseSource :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType leftFunctionRaw rightFunctionRaw)
        pointwiseRawSource}
    {pointwiseTarget :
      Term sourceCtx
        (oeqFunextPointwiseType domainType codomainType leftFunctionRaw rightFunctionRaw)
        pointwiseRawTarget}
    (pointwiseStep :
      Step.par (Term.rename termRenaming pointwiseSource)
               (Term.rename termRenaming pointwiseTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.oeqFunext domainType codomainType leftFunctionRaw rightFunctionRaw pointwiseSource))
      (Term.rename termRenaming
        (Term.oeqFunext domainType codomainType leftFunctionRaw rightFunctionRaw pointwiseTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.oeqFunextCong (domainType.rename rho) (codomainType.rename rho)
    (leftFunctionRaw.rename rho) (rightFunctionRaw.rename rho)
    (Step.par.castTargetType
      (oeqFunextPointwiseType_rename rho domainType codomainType
        leftFunctionRaw rightFunctionRaw)
      (Step.par.castSourceType
        (oeqFunextPointwiseType_rename rho domainType codomainType
          leftFunctionRaw rightFunctionRaw)
        pointwiseStep))

/-- Reduction arm `eqArrow` of typed-Step.par rename equivariance (0-premise,
target-cast).  The funext rfl-fragment reduction `funextReflAtId → funextRefl`
carries no Step.par premises.  `Term.rename` on the source (`funextReflAtId`) is
cast-free, but on the target (`funextRefl`) it transports the type by
`(funextReflType_rename ...).symm`.  So re-apply `Step.par.eqArrow` at the
renamed args and cast only its TARGET endpoint by that one equality. -/
theorem rename_compatible_typed_eqArrow
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1)) :
    Step.par
      (Term.rename termRenaming (Term.funextReflAtId domainType codomainType applyRaw))
      (Term.rename termRenaming (Term.funextRefl domainType codomainType applyRaw)) := by
  dsimp only [Term.rename]
  exact Step.par.castTargetType
    (funextReflType_rename rho domainType codomainType applyRaw).symm
    (Step.par.eqArrow (domainType.rename rho) (codomainType.rename rho)
      (applyRaw.rename rho.lift))

/-- Reduction arm `eqTypeHet` of typed-Step.par rename equivariance (0-premise,
cast-free).  Heterogeneous univalence `uaIntroHet ... equivWitness → equivWitness`
carries no premises; the source (`uaIntroHet`) renames cast-free and the target
is the bare witness (recursive `Term.rename`).  Re-apply `Step.par.eqTypeHet` at
the renamed schematic raws and renamed witness; the witness's raw stays
`RawTerm.equivIntro _ _` after renaming, matching the ctor's index. -/
theorem rename_compatible_typed_eqTypeHet
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level sourceScope}
    (carrierARaw carrierBRaw : RawTerm sourceScope)
    {forwardRaw backwardRaw : RawTerm sourceScope}
    (equivWitness :
      Term sourceCtx (Ty.equiv carrierA carrierB)
        (RawTerm.equivIntro forwardRaw backwardRaw)) :
    Step.par
      (Term.rename termRenaming
        (Term.uaIntroHet innerLevel innerLevelLt carrierARaw carrierBRaw equivWitness))
      (Term.rename termRenaming equivWitness) := by
  dsimp only [Term.rename]
  exact Step.par.eqTypeHet innerLevel innerLevelLt
    (carrierARaw.rename rho) (carrierBRaw.rename rho)
    (Term.rename termRenaming equivWitness)

/-- Reduction arm `eqArrowHet` of typed-Step.par rename equivariance (0-premise,
target-cast).  Heterogeneous funext `funextIntroHet ... applyARaw applyBRaw →
funextRefl ... applyARaw` carries no premises; the source (`funextIntroHet`)
renames cast-free, the target (`funextRefl`) transports by
`(funextReflType_rename ... applyARaw).symm` (keyed on the target's applyARaw).
Re-apply `Step.par.eqArrowHet` at renamed args, cast only the TARGET. -/
theorem rename_compatible_typed_eqArrowHet
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    (applyARaw applyBRaw : RawTerm (sourceScope + 1)) :
    Step.par
      (Term.rename termRenaming
        (Term.funextIntroHet domainType codomainType applyARaw applyBRaw))
      (Term.rename termRenaming
        (Term.funextRefl domainType codomainType applyARaw)) := by
  dsimp only [Term.rename]
  exact Step.par.castTargetType
    (funextReflType_rename rho domainType codomainType applyARaw).symm
    (Step.par.eqArrowHet (domainType.rename rho) (codomainType.rename rho)
      (applyARaw.rename rho.lift) (applyBRaw.rename rho.lift))

/-- Cong arm `funextReflCong` of typed-Step.par rename equivariance (raw-premise,
both-endpoints cast-bearing).  `Term.funextRefl` carries its applyRaw payload as
a RAW term at `scope + 1`, so the cong reduces via a `RawStep.par` premise
through `RawStep.par.rename_compatible rho.lift`.  Both endpoints' `Term.rename`
transport by `(funextReflType_rename ...).symm` — keyed on the SOURCE applyRaw
for the source endpoint and the TARGET applyRaw for the target endpoint, so the
two casts differ and each endpoint is transported separately. -/
theorem rename_compatible_typed_funextReflCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    {applyRawSource applyRawTarget : RawTerm (sourceScope + 1)}
    (applyStep : RawStep.par applyRawSource applyRawTarget) :
    Step.par
      (Term.rename termRenaming (Term.funextRefl domainType codomainType applyRawSource))
      (Term.rename termRenaming (Term.funextRefl domainType codomainType applyRawTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.castTargetType
    (funextReflType_rename rho domainType codomainType applyRawTarget).symm
    (Step.par.castSourceType
      (funextReflType_rename rho domainType codomainType applyRawSource).symm
      (Step.par.funextReflCong (domainType.rename rho) (codomainType.rename rho)
        (RawStep.par.rename_compatible rho.lift applyStep)))

end Step.par

end LeanFX2
