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

end Step.par

end LeanFX2
