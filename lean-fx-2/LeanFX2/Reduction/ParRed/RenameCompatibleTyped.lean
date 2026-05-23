import LeanFX2.Reduction.ParRed.ParInductive
import LeanFX2.Reduction.ParRed.ParCasts
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

end Step.par

end LeanFX2
