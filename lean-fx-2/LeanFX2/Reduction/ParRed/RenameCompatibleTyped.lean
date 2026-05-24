import LeanFX2.Reduction.ParRed.ParInductive
import LeanFX2.Reduction.ParRed.ParCasts
import LeanFX2.Term.Rename
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.CastHEq
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure.SingletonPrecompose
import LeanFX2.Term.Subst0RenameCommute
import LeanFX2.Reduction.RawParCompatible.NamedCompatibility

/-! # RenameCompatibleTyped — TODO POLYCELL: BODY DISABLED

Body depends on cd_lemma / Conv.canonical_form / parStar.confluence /
RawStep.parStar orchestration deleted in commit c2efaccf (cascade-fake
bulldoze).  Replacement: FXcdLemma / FXConv view defs per polycell.md §5.
Imports are preserved at top so downstream transitive imports still work.
-/

/- TODO POLYCELL: original body preserved as block comment


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

/-- Cong arm `equivIntroHetCong` of typed-Step.par rename equivariance (typed-IH,
two function sub-derivations + cast-bearing inverse witnesses).  `Term.equivIntroHet`
packages a forward function, a backward function, and two inverse-law witnesses
(`leftInv` at `equivIntroHetLeftInverseType`, `rightInv` at
`equivIntroHetRightInverseType`); the cong reduces only in the forward/backward
positions and lets the inverse witnesses be replaced freely (their types shift
with the reduced functions, with no canonical reduced witness to relate).  Under
renaming, `Term.rename`'s own `equivIntroHet` arm inserts
`equivIntroHetLeftInverseType_rename ▸` / `equivIntroHetRightInverseType_rename ▸`
casts into BOTH endpoints, so after `dsimp only [Term.rename]` those casts already
sit in the goal — the constructor's implicit witness args unify against them
directly, and only the two function premises are threaded. -/
theorem rename_compatible_typed_equivIntroHetCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrierA carrierB : Ty level sourceScope}
    {forwardRawSource forwardRawTarget
     backwardRawSource backwardRawTarget : RawTerm sourceScope}
    {forwardSource : Term sourceCtx (Ty.arrow carrierA carrierB) forwardRawSource}
    {forwardTarget : Term sourceCtx (Ty.arrow carrierA carrierB) forwardRawTarget}
    {backwardSource : Term sourceCtx (Ty.arrow carrierB carrierA) backwardRawSource}
    {backwardTarget : Term sourceCtx (Ty.arrow carrierB carrierA) backwardRawTarget}
    {leftInvSourceRaw rightInvSourceRaw
     leftInvTargetRaw rightInvTargetRaw : RawTerm sourceScope}
    {leftInvSource :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRawSource backwardRawSource)
        leftInvSourceRaw}
    {rightInvSource :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRawSource backwardRawSource)
        rightInvSourceRaw}
    {leftInvTarget :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRawTarget backwardRawTarget)
        leftInvTargetRaw}
    {rightInvTarget :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRawTarget backwardRawTarget)
        rightInvTargetRaw}
    (forwardStep :
      Step.par (Term.rename termRenaming forwardSource)
               (Term.rename termRenaming forwardTarget))
    (backwardStep :
      Step.par (Term.rename termRenaming backwardSource)
               (Term.rename termRenaming backwardTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.equivIntroHet forwardSource backwardSource leftInvSource rightInvSource))
      (Term.rename termRenaming
        (Term.equivIntroHet forwardTarget backwardTarget leftInvTarget rightInvTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.equivIntroHetCong forwardStep backwardStep

/-- Cong arm `equivIntroCong` of typed-Step.par rename equivariance.  Raw-name
parity alias of `equivIntroHetCong` — identical signature and `Term.equivIntroHet`
carrier, differing only in that the underlying raw constructor is named
`RawStep.par.equivIntroCong`.  Same proof shape: thread the two renamed function
premises; the rename-arm casts on the inverse witnesses are read off the goal. -/
theorem rename_compatible_typed_equivIntroCong
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrierA carrierB : Ty level sourceScope}
    {forwardRawSource forwardRawTarget
     backwardRawSource backwardRawTarget : RawTerm sourceScope}
    {forwardSource : Term sourceCtx (Ty.arrow carrierA carrierB) forwardRawSource}
    {forwardTarget : Term sourceCtx (Ty.arrow carrierA carrierB) forwardRawTarget}
    {backwardSource : Term sourceCtx (Ty.arrow carrierB carrierA) backwardRawSource}
    {backwardTarget : Term sourceCtx (Ty.arrow carrierB carrierA) backwardRawTarget}
    {leftInvSourceRaw rightInvSourceRaw
     leftInvTargetRaw rightInvTargetRaw : RawTerm sourceScope}
    {leftInvSource :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRawSource backwardRawSource)
        leftInvSourceRaw}
    {rightInvSource :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRawSource backwardRawSource)
        rightInvSourceRaw}
    {leftInvTarget :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRawTarget backwardRawTarget)
        leftInvTargetRaw}
    {rightInvTarget :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRawTarget backwardRawTarget)
        rightInvTargetRaw}
    (forwardStep :
      Step.par (Term.rename termRenaming forwardSource)
               (Term.rename termRenaming forwardTarget))
    (backwardStep :
      Step.par (Term.rename termRenaming backwardSource)
               (Term.rename termRenaming backwardTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.equivIntroHet forwardSource backwardSource leftInvSource rightInvSource))
      (Term.rename termRenaming
        (Term.equivIntroHet forwardTarget backwardTarget leftInvTarget rightInvTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.equivIntroCong forwardStep backwardStep

/-- Cong arm `pathApp` of typed-Step.par rename equivariance (typed-IH, two
sub-derivations, cast-free).  `Term.pathApp` applies a path to an interval point;
the cong reduces in both the path and interval positions.  Both subterms live at
the unshifted `scope` and the carrier types (`Ty.path …`, `Ty.interval`) rename
structurally, so `Term.rename`'s `pathApp` arm carries no cast — a definitional
push closes the goal once the two renamed sub-steps are supplied.  This is the
bare-named cong half of the `pathApp` / `pathAppCong` raw-name-parity pair (both
are genuine `Step.par` constructors producing `Term.pathApp` reducts; the headline
induction needs one arm per constructor).  The `modeIsUnivalent` witness is shared
by both endpoints (renaming preserves mode) and threaded explicitly. -/
theorem rename_compatible_typed_pathApp
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRawSource pathRawTarget intervalRawSource intervalRawTarget :
      RawTerm sourceScope}
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
  exact Step.par.pathApp modeIsUnivalent pathStep intervalStep

/-- Cong arm `glueIntro` of typed-Step.par rename equivariance (typed-IH, two
sub-derivations, cast-free).  `Term.glueIntro` packages a base value and a partial
value (both at `baseType`) under a boundary witness; the cong reduces in both
value positions.  `baseType` and `boundaryWitness` rename structurally, the two
values at unshifted `scope`, so the `Term.rename` `glueIntro` arm is cast-free.
Bare-named half of the `glueIntro` / `glueIntroCong` raw-name-parity pair. -/
theorem rename_compatible_typed_glueIntro
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness : RawTerm sourceScope}
    {baseRawSource baseRawTarget partialRawSource partialRawTarget :
      RawTerm sourceScope}
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
  exact Step.par.glueIntro modeIsUnivalent baseStep partialStep

/-- Cong arm `glueElim` of typed-Step.par rename equivariance (typed-IH, single
sub-derivation, cast-free).  `Term.glueElim` extracts the base value from a glued
value at `Ty.glue baseType boundaryWitness`; the cong reduces in the glued value.
`Ty.glue` renames structurally, so the `Term.rename` `glueElim` arm carries no
cast.  Bare-named half of the `glueElim` / `glueElimCong` raw-name-parity pair. -/
theorem rename_compatible_typed_glueElim
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness : RawTerm sourceScope}
    {gluedRawSource gluedRawTarget : RawTerm sourceScope}
    {gluedSource :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRawSource}
    {gluedTarget :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRawTarget}
    (gluedStep :
      Step.par (Term.rename termRenaming gluedSource)
               (Term.rename termRenaming gluedTarget)) :
    Step.par
      (Term.rename termRenaming (Term.glueElim modeIsUnivalent gluedSource))
      (Term.rename termRenaming (Term.glueElim modeIsUnivalent gluedTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.glueElim modeIsUnivalent gluedStep

/-- Cong arm `transp` of typed-Step.par rename equivariance (typed-IH, two
sub-derivations, cast-free).  `Term.transp` transports a source value along a
universe-level type path; the cong reduces in the type-path and source-value
positions.  Bare-named half of the `transp` / `transpCong` raw-name-parity pair;
mirror of `transpCong` with the same cast-free definitional push (the four `_`
solve `sourceType` / `targetType` / `sourceTypeRaw` / `targetTypeRaw` against the
renamed goal). -/
theorem rename_compatible_typed_transp
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
  exact Step.par.transp modeIsUnivalent universeLevel universeLevelLt _ _ _ _
    typePathStep sourceValueStep

/-- Cong arm `hcomp` of typed-Step.par rename equivariance (typed-IH, two
sub-derivations, cast-free).  `Term.hcomp` composes sides and cap, both at the
non-dependent `carrierType`; the cong reduces in both positions.  Bare-named half
of the `hcomp` / `hcompCong` raw-name-parity pair. -/
theorem rename_compatible_typed_hcomp
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
  exact Step.par.hcomp modeIsUnivalent sidesStep capStep

/-- Cong arm `pathLam` of typed-Step.par rename equivariance (typed-IH, single
sub-derivation under an interval binder, cast-bearing).  `Term.pathLam` binds an
interval variable; its body lives at `carrierType.weaken` in the extended context,
so the sub-step renames via `termRenaming.lift Ty.interval` and both endpoints
transport by `Ty.weaken_rename_commute rho carrierType`.  Bare-named half of the
`pathLam` / `pathLamCong` raw-name-parity pair; identical cast structure to
`pathLamCong`. -/
theorem rename_compatible_typed_pathLam
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
  exact Step.par.pathLam modeIsUnivalent
    (Step.par.castTargetType (Ty.weaken_rename_commute rho carrierType)
      (Step.par.castSourceType (Ty.weaken_rename_commute rho carrierType) bodyStep))

/-- β arm `betaFstPair` of typed-Step.par rename equivariance (shallow Σ first
projection, single sub-derivation).  `Term.fst (Term.pair a b) ⟶ a'` with
`Step.par a a'`; the discarded second component `b` is carried as an explicit
constructor argument.  Under renaming, the redex unfolds through the `fst` arm
(cast-free) and the `pair` arm (which transports its second component by
`Ty.subst0_rename_commute secondType firstType firstRawSource rho`), so the
reconstructed `secondValueSource` supplied to `Step.par.betaFstPair` carries the
SAME forward cast that the `Term.rename` `pair` arm placed in the goal — the
`exact` then rebuilds the identical renamed redex.  The reduct side
(`firstValueTarget`) is substitution-free, so no cast there. -/
theorem rename_compatible_typed_betaFstPair
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {firstType : Ty level sourceScope} {secondType : Ty level (sourceScope + 1)}
    {firstRawSource firstRawTarget : RawTerm sourceScope}
    {secondRawSource : RawTerm sourceScope}
    {firstValueSource : Term sourceCtx firstType firstRawSource}
    {firstValueTarget : Term sourceCtx firstType firstRawTarget}
    (secondValueSource :
      Term sourceCtx (secondType.subst0 firstType firstRawSource) secondRawSource)
    (firstStep :
      Step.par (Term.rename termRenaming firstValueSource)
               (Term.rename termRenaming firstValueTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.fst (Term.pair (secondType := secondType)
          firstValueSource secondValueSource)))
      (Term.rename termRenaming firstValueTarget) := by
  dsimp only [Term.rename]
  exact Step.par.betaFstPair
    (Ty.subst0_rename_commute secondType firstType firstRawSource rho ▸
      Term.rename termRenaming secondValueSource)
    firstStep

/-- β arm `betaGlueElimIntro` of typed-Step.par rename equivariance (shallow glue
elimination, two sub-derivations, cast-free).  `glueElim (glueIntro base partial)
⟶ base'` with `Step.par base base'`; the discarded partial component reduces in
parallel.  Both `base` and `partial` live at the non-dependent `baseType`, and the
`glueElim` / `glueIntro` rename arms are cast-free, so the redex unfolds with no
`subst0` transport and the reduct (`baseTarget`) is substitution-free — a
definitional push after `dsimp`. -/
theorem rename_compatible_typed_betaGlueElimIntro
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness : RawTerm sourceScope}
    {baseRawSource baseRawTarget partialRawSource partialRawTarget :
      RawTerm sourceScope}
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
        (Term.glueElim modeIsUnivalent
          (Term.glueIntro modeIsUnivalent baseType boundaryWitness
            baseSource partialSource)))
      (Term.rename termRenaming baseTarget) := by
  dsimp only [Term.rename]
  exact Step.par.betaGlueElimIntro modeIsUnivalent baseStep partialStep

/-- β arm `betaRecordProjIntro` of typed-Step.par rename equivariance (shallow
single-field record projection, single sub-derivation, cast-free).  `recordProj
(recordIntro field) ⟶ field'` with `Step.par field field'`.  The single field
lives at the non-dependent `singleFieldType`; `recordProj` / `recordIntro` rename
structurally, so the reduct (`firstTarget`) is substitution-free. -/
theorem rename_compatible_typed_betaRecordProjIntro
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
      (Term.rename termRenaming (Term.recordProj (Term.recordIntro firstSource)))
      (Term.rename termRenaming firstTarget) := by
  dsimp only [Term.rename]
  exact Step.par.betaRecordProjIntro firstStep

/-- β arm `betaModElimIntro` of typed-Step.par rename equivariance (shallow modal
elimination, single sub-derivation, cast-free).  `modElim (modIntro x) ⟶ x'` with
`Step.par x x'`.  `modIntro` / `modElim` rename structurally over the
non-dependent `innerType`, so the reduct (`innerTarget`) is substitution-free. -/
theorem rename_compatible_typed_betaModElimIntro
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
      (Term.rename termRenaming (Term.modElim (Term.modIntro innerSource)))
      (Term.rename termRenaming innerTarget) := by
  dsimp only [Term.rename]
  exact Step.par.betaModElimIntro innerStep

/-- β arm `betaRefineElimIntro` of typed-Step.par rename equivariance (shallow
refinement elimination, two sub-derivations, cast-free).  `refineElim (refineIntro
pred value proof) ⟶ value'` with `Step.par value value'`; the erased proof
component (at `Ty.unit`) reduces in parallel.  The refinement predicate lives at
`scope + 1` and renames via `rho.lift` with no `▸`, the value at the non-dependent
`baseType`, so the reduct (`valueTarget`) is substitution-free. -/
theorem rename_compatible_typed_betaRefineElimIntro
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {valueRawSource valueRawTarget proofRawSource proofRawTarget :
      RawTerm sourceScope}
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
      (Term.rename termRenaming
        (Term.refineElim (Term.refineIntro predicate valueSource proofSource)))
      (Term.rename termRenaming valueTarget) := by
  dsimp only [Term.rename]
  exact Step.par.betaRefineElimIntro valueStep proofStep

/-- β arm `betaCodataDestUnfold` of typed-Step.par rename equivariance (shallow
codata observation, two sub-derivations, cast-free).  `codataDest (codataUnfold
state transition) ⟶ app transition' state'` with `Step.par state state'` and
`Step.par transition transition'`.  The reduct is a NON-dependent `Term.app` (the
transition has arrow type `Ty.arrow stateType outputType`, so its result type is
`outputType` with no `subst0`), and `codataDest` / `codataUnfold` / `app` all
rename structurally — so both the redex and the application reduct are cast-free
under `Term.rename`. -/
theorem rename_compatible_typed_betaCodataDestUnfold
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {stateType outputType : Ty level sourceScope}
    {stateRawSource stateRawTarget transitionRawSource transitionRawTarget :
      RawTerm sourceScope}
    {stateSource : Term sourceCtx stateType stateRawSource}
    {stateTarget : Term sourceCtx stateType stateRawTarget}
    {transitionSource :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRawSource}
    {transitionTarget :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRawTarget}
    (stateStep :
      Step.par (Term.rename termRenaming stateSource)
               (Term.rename termRenaming stateTarget))
    (transitionStep :
      Step.par (Term.rename termRenaming transitionSource)
               (Term.rename termRenaming transitionTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.codataDest (Term.codataUnfold stateSource transitionSource)))
      (Term.rename termRenaming (Term.app transitionTarget stateTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.betaCodataDestUnfold stateStep transitionStep

/-- β arm `betaModElimIntroDeep` of typed-Step.par rename equivariance (deep modal
elimination, develops-to premise, cast-free).  `modElim x ⟶ y` when `x` develops
to `modIntro y` (premise `Step.par x (modIntro y)`).  The reduct (`innerTarget`)
is substitution-free at the non-dependent `innerType`, and the develops-to premise
mentions only the cast-free `modIntro` intro form — so stating the premise in
intro-of-rename form (`Term.modIntro (Term.rename … innerTarget)`, defeq to
`Term.rename … (Term.modIntro innerTarget)`) lets `exact` close with no
double-transport.  The headline IH supplies exactly this renamed develops-to
premise. -/
theorem rename_compatible_typed_betaModElimIntroDeep
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
               (Term.modIntro (Term.rename termRenaming innerTarget))) :
    Step.par
      (Term.rename termRenaming (Term.modElim innerSource))
      (Term.rename termRenaming innerTarget) := by
  dsimp only [Term.rename]
  exact Step.par.betaModElimIntroDeep innerStep

/-- β arm `betaCodataDestUnfoldDeep` of typed-Step.par rename equivariance (deep
codata observation, develops-to premise, cast-free).  `codataDest c ⟶ app
transition state` when `c` develops to `codataUnfold state transition`.  The
reduct is a non-dependent `Term.app`, and the develops-to premise mentions only
the cast-free `codataUnfold` intro form — so stating the premise in
intro-of-rename form lets `exact` close with no double-transport. -/
theorem rename_compatible_typed_betaCodataDestUnfoldDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {stateType outputType : Ty level sourceScope}
    {codataRawSource stateRawTarget transitionRawTarget : RawTerm sourceScope}
    {codataSource :
      Term sourceCtx (Ty.codata stateType outputType) codataRawSource}
    {stateTarget : Term sourceCtx stateType stateRawTarget}
    {transitionTarget :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRawTarget}
    (codataStep :
      Step.par (Term.rename termRenaming codataSource)
               (Term.codataUnfold (Term.rename termRenaming stateTarget)
                 (Term.rename termRenaming transitionTarget))) :
    Step.par
      (Term.rename termRenaming (Term.codataDest codataSource))
      (Term.rename termRenaming (Term.app transitionTarget stateTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.betaCodataDestUnfoldDeep codataStep

/-- β arm `betaGlueElimIntroDeep` of typed-Step.par rename equivariance (deep
cubical Glue elimination, develops-to premise, cast-free).  `glueElim g ⟶ base`
when `g` develops to `glueIntro base partial`.  The reduct (`baseTarget`) lives at
the non-dependent `baseType`, and `glueIntro` / `glueElim` rename structurally
(`baseType` and `boundaryWitness` via `.rename rho`, no `▸`).  Stating the
develops-to premise in whole-rename form (`Term.rename … (Term.glueIntro …)`,
exactly the headline IH) and normalising both sides with `dsimp only [Term.rename]`
lets `exact` close with no double-transport. -/
theorem rename_compatible_typed_betaGlueElimIntroDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness : RawTerm sourceScope}
    {gluedRawSource baseRawTarget partialRawTarget : RawTerm sourceScope}
    {gluedSource :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRawSource}
    {baseTarget : Term sourceCtx baseType baseRawTarget}
    {partialTarget : Term sourceCtx baseType partialRawTarget}
    (gluedStep :
      Step.par (Term.rename termRenaming gluedSource)
               (Term.rename termRenaming
                 (Term.glueIntro modeIsUnivalent baseType boundaryWitness
                   baseTarget partialTarget))) :
    Step.par
      (Term.rename termRenaming (Term.glueElim modeIsUnivalent gluedSource))
      (Term.rename termRenaming baseTarget) := by
  dsimp only [Term.rename] at gluedStep ⊢
  exact Step.par.betaGlueElimIntroDeep modeIsUnivalent gluedStep

/-- β arm `betaRecordProjIntroDeep` of typed-Step.par rename equivariance (deep
single-field record projection, develops-to premise, cast-free).  `recordProj r ⟶
field` when `r` develops to `recordIntro field`.  The single field lives at the
non-dependent `singleFieldType`; `recordProj` / `recordIntro` rename structurally,
so the reduct (`firstTarget`) is substitution-free. -/
theorem rename_compatible_typed_betaRecordProjIntroDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {singleFieldType : Ty level sourceScope}
    {recordRawSource firstRawTarget : RawTerm sourceScope}
    {recordSource : Term sourceCtx (Ty.record singleFieldType) recordRawSource}
    {firstTarget : Term sourceCtx singleFieldType firstRawTarget}
    (recordStep :
      Step.par (Term.rename termRenaming recordSource)
               (Term.rename termRenaming (Term.recordIntro firstTarget))) :
    Step.par
      (Term.rename termRenaming (Term.recordProj recordSource))
      (Term.rename termRenaming firstTarget) := by
  dsimp only [Term.rename] at recordStep ⊢
  exact Step.par.betaRecordProjIntroDeep recordStep

/-- β arm `betaRefineElimIntroDeep` of typed-Step.par rename equivariance (deep
refinement elimination, develops-to premise, cast-free).  `refineElim r ⟶ value`
when `r` develops to `refineIntro pred value proof`.  The value lives at the
non-dependent `baseType` and the predicate at `scope + 1` renames via `rho.lift`
with no `▸`, so the reduct (`valueTarget`) is substitution-free. -/
theorem rename_compatible_typed_betaRefineElimIntroDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {baseType : Ty level sourceScope}
    {predicate : RawTerm (sourceScope + 1)}
    {refinedRawSource valueRawTarget proofRawTarget : RawTerm sourceScope}
    {refinedSource : Term sourceCtx (Ty.refine baseType predicate) refinedRawSource}
    {valueTarget : Term sourceCtx baseType valueRawTarget}
    {proofTarget : Term sourceCtx Ty.unit proofRawTarget}
    (refinedStep :
      Step.par (Term.rename termRenaming refinedSource)
               (Term.rename termRenaming
                 (Term.refineIntro predicate valueTarget proofTarget))) :
    Step.par
      (Term.rename termRenaming (Term.refineElim refinedSource))
      (Term.rename termRenaming valueTarget) := by
  dsimp only [Term.rename] at refinedStep ⊢
  exact Step.par.betaRefineElimIntroDeep refinedStep

/-- β arm `betaFstPairDeep` of typed-Step.par rename equivariance (deep Σ-fst
projection, develops-to premise, cast-free reduct).  `fst p ⟶ first` when `p`
develops to `pair first second`.  The reduct (`firstValueTarget`) lives at the
non-dependent `firstType`; `fst` renames cast-free.  The pair-rename arm DOES place
a `Ty.subst0_rename_commute ▸` cast — but only on the SECOND component
(`secondValueTarget` at `secondType.subst0 …`), which the constructor's
existential absorbs and the conclusion discards.  So the double-transport
obstruction (which blocks `betaSndPair`, whose reduct IS the cast-bearing second
component) does not arise here. -/
theorem rename_compatible_typed_betaFstPairDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRawSource firstRawTarget secondRawTarget : RawTerm sourceScope}
    {pairTermSource :
      Term sourceCtx (Ty.sigmaTy firstType secondType) pairRawSource}
    {firstValueTarget : Term sourceCtx firstType firstRawTarget}
    {secondValueTarget :
      Term sourceCtx (secondType.subst0 firstType firstRawTarget) secondRawTarget}
    (pairStep :
      Step.par (Term.rename termRenaming pairTermSource)
               (Term.rename termRenaming
                 (Term.pair (secondType := secondType)
                   firstValueTarget secondValueTarget))) :
    Step.par
      (Term.rename termRenaming
        (Term.fst (secondType := secondType) pairTermSource))
      (Term.rename termRenaming firstValueTarget) := by
  dsimp only [Term.rename] at pairStep ⊢
  exact Step.par.betaFstPairDeep pairStep

/-- Heterogeneous congruence for the `typePath` argument of `Term.transp` at fixed
endpoints: when the two paths' raw indices agree (`pathRawEq`) and the paths are
`HEq`, the two transports are `HEq`.  Proven `subst` (the raw indices are free
variables here, so it applies) then `cases` on the now-homogeneous `HEq` — no
`congr`, hence propext-free.  Consumed by the `transpReflBeta`/`transpReflBetaDeep`
rename-equivariance arms to discharge the `Step.par.castSourceTermHeq` witness. -/
theorem transp_typePath_heqCongr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level scope)
    (sourceTypeRaw targetTypeRaw : RawTerm scope)
    {pathRawA pathRawB sourceRaw : RawTerm scope}
    (pathRawEq : pathRawA = pathRawB)
    {pathA :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw) pathRawA}
    {pathB :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw) pathRawB}
    (pathHeq : HEq pathA pathB)
    (sourceValue : Term context sourceType sourceRaw) :
    HEq
      (Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw pathA sourceValue)
      (Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw pathB sourceValue) := by
  cases pathRawEq
  cases pathHeq
  rfl

/-- β arm `transpReflBeta` of typed-Step.par rename equivariance (shallow cubical
transport at a homogeneous CONSTANT path, single sub-derivation).  `transp (pathLam
typeRaw.weaken) source ⟶ target` with `Step.par source target`.  The reduct
(`sourceValueTarget`) lives at the plain non-dependent `sourceType` — cast-free on
the reduct side.  The obstruction is the `typePath` argument: its raw `pathLam
typeRaw.weaken` renames to `pathLam ((typeRaw.weaken).rename rho.lift)`, while the
constructor pins it at `pathLam (X.weaken)`.  These agree only via
`RawTerm.weaken_rename_commute` on a TYPE INDEX, so the goal's renamed `typePath`
and the constructor's commuted `typePath` differ heterogeneously.  The bridge is
`Step.par.castSourceTermHeq` (ParCasts): supply the transp raw-index equality
(`RawTerm.transp _.toRaw _.toRaw` per `Term.toRaw_transp`, discharged by the
commute) plus the `HEq` between the two transps (they differ only in the one
`▸`-cast argument, so `congr 1` reduces it to `eqRec_heq`).  Zero-axiom. -/
theorem rename_compatible_typed_transpReflBeta
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType : Ty level sourceScope)
    {typeRaw sourceRawSource sourceRawTarget : RawTerm sourceScope}
    (typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt) typeRaw typeRaw)
        (RawTerm.pathLam typeRaw.weaken))
    {sourceValueSource : Term sourceCtx sourceType sourceRawSource}
    {sourceValueTarget : Term sourceCtx sourceType sourceRawTarget}
    (sourceStep :
      Step.par (Term.rename termRenaming sourceValueSource)
               (Term.rename termRenaming sourceValueTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType sourceType typeRaw typeRaw typePath sourceValueSource))
      (Term.rename termRenaming sourceValueTarget) := by
  dsimp only [Term.rename]
  have pathRawCommute :
      (RawTerm.pathLam typeRaw.weaken).rename rho
        = RawTerm.pathLam ((typeRaw.rename rho).weaken) :=
    congrArg RawTerm.pathLam (RawTerm.weaken_rename_commute rho typeRaw)
  refine Step.par.castSourceTermHeq ?rawEq ?heq
    (Step.par.transpReflBeta modeIsUnivalent universeLevel universeLevelLt
      (sourceType.rename rho)
      (pathRawCommute ▸ Term.rename termRenaming typePath)
      sourceStep)
  · exact congrArg (fun bodyRaw => (RawTerm.pathLam bodyRaw).transp (sourceRawSource.rename rho))
      (RawTerm.weaken_rename_commute rho typeRaw).symm
  · exact transp_typePath_heqCongr modeIsUnivalent universeLevel universeLevelLt
      (sourceType.rename rho) (sourceType.rename rho)
      (typeRaw.rename rho) (typeRaw.rename rho)
      pathRawCommute.symm (eqRec_heq _ _)
      (Term.rename termRenaming sourceValueSource)

/-- β arm `transpReflBetaDeep` of typed-Step.par rename equivariance (deep cubical
transport at a path that DEVELOPS to a constant `pathLam`).  Unlike the shallow
`transpReflBeta`, the typed `typePath` here carries a FREE raw `pathRawSource`, so
it renames purely structurally — NO `Step.par.castSourceTermHeq` is needed on the
transport.  The single non-trivial step is the RAW develops-to premise `pathStep :
RawStep.par pathRawSource (pathLam typeRawTarget.weaken)`: renaming it via
`RawStep.par.rename` gives target `(pathLam typeRawTarget.weaken).rename rho`, which
the constructor wants as `pathLam ((typeRawTarget.rename rho).weaken)` — bridged by a
single `▸` with `RawTerm.weaken_rename_commute` (on a plain `RawTerm` index of
`RawStep.par`, no dependent-typing tangle).  The reduct (`sourceValueTarget`) is at
the plain `sourceType`, cast-free. -/
theorem rename_compatible_typed_transpReflBetaDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType : Ty level sourceScope)
    {typeRaw pathRawSource typeRawTarget : RawTerm sourceScope}
    {sourceRawSource sourceRawTarget : RawTerm sourceScope}
    (typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt) typeRaw typeRaw)
        pathRawSource)
    (pathStep :
      RawStep.par pathRawSource (RawTerm.pathLam typeRawTarget.weaken))
    {sourceValueSource : Term sourceCtx sourceType sourceRawSource}
    {sourceValueTarget : Term sourceCtx sourceType sourceRawTarget}
    (sourceStep :
      Step.par (Term.rename termRenaming sourceValueSource)
               (Term.rename termRenaming sourceValueTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType sourceType typeRaw typeRaw typePath sourceValueSource))
      (Term.rename termRenaming sourceValueTarget) := by
  have targetRawCommute :
      (RawTerm.pathLam typeRawTarget.weaken).rename rho
        = RawTerm.pathLam ((typeRawTarget.rename rho).weaken) :=
    congrArg RawTerm.pathLam (RawTerm.weaken_rename_commute rho typeRawTarget)
  dsimp only [Term.rename]
  exact Step.par.transpReflBetaDeep modeIsUnivalent universeLevel universeLevelLt
    (sourceType.rename rho)
    (Term.rename termRenaming typePath)
    (targetRawCommute ▸ RawStep.par.rename rho pathStep)
    sourceStep

/-- Heterogeneous congruence for the `sidesPath` argument of `Term.hcompPath` at
fixed endpoints (the `hcompBeta` analog of `transp_typePath_heqCongr`).  `subst` the
free raw indices then `cases` the homogeneous `HEq` — propext-free. -/
theorem hcompPath_sidesPath_heqCongr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    (leftEndpoint rightEndpoint : RawTerm scope)
    {sidesRawA sidesRawB capRaw : RawTerm scope}
    (sidesRawEq : sidesRawA = sidesRawB)
    {sidesA :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) sidesRawA}
    {sidesB :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) sidesRawB}
    (sidesHeq : HEq sidesA sidesB)
    (capValue : Term context carrierType capRaw) :
    HEq
      (Term.hcompPath modeIsUnivalent leftEndpoint rightEndpoint sidesA capValue)
      (Term.hcompPath modeIsUnivalent leftEndpoint rightEndpoint sidesB capValue) := by
  cases sidesRawEq
  cases sidesHeq
  rfl

/-- β arm `hcompBeta` of typed-Step.par rename equivariance (shallow cubical hcomp at
a homogeneous CONSTANT sides path).  `hcompPath (pathLam capRawSource.weaken) cap ⟶
cap'` with `Step.par cap cap'`.  The reduct (`capValueTarget`) is at the plain
`carrierType`, cast-free; the `sidesPath` carries `pathLam capRawSource.weaken`, the
same weaken/rename type-index obstruction as `transpReflBeta` — bridged by
`Step.par.castSourceTermHeq` + `hcompPath_sidesPath_heqCongr`.  Zero-axiom. -/
theorem rename_compatible_typed_hcompBeta
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {capRawSource capRawTarget : RawTerm sourceScope}
    (sidesPath :
      Term sourceCtx (Ty.path carrierType capRawSource capRawSource)
        (RawTerm.pathLam capRawSource.weaken))
    {capValueSource : Term sourceCtx carrierType capRawSource}
    {capValueTarget : Term sourceCtx carrierType capRawTarget}
    (capStep :
      Step.par (Term.rename termRenaming capValueSource)
               (Term.rename termRenaming capValueTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.hcompPath modeIsUnivalent
          (leftEndpoint := capRawSource) (rightEndpoint := capRawSource)
          sidesPath capValueSource))
      (Term.rename termRenaming capValueTarget) := by
  have pathRawCommute :
      (RawTerm.pathLam capRawSource.weaken).rename rho
        = RawTerm.pathLam ((capRawSource.rename rho).weaken) :=
    congrArg RawTerm.pathLam (RawTerm.weaken_rename_commute rho capRawSource)
  dsimp only [Term.rename]
  refine Step.par.castSourceTermHeq ?rawEq ?heq
    (Step.par.hcompBeta modeIsUnivalent
      (pathRawCommute ▸ Term.rename termRenaming sidesPath)
      capStep)
  · exact congrArg
      (fun bodyRaw => RawTerm.hcomp (RawTerm.pathLam bodyRaw) (capRawSource.rename rho))
      (RawTerm.weaken_rename_commute rho capRawSource).symm
  · exact hcompPath_sidesPath_heqCongr modeIsUnivalent
      (capRawSource.rename rho) (capRawSource.rename rho)
      pathRawCommute.symm (eqRec_heq _ _)
      (Term.rename termRenaming capValueSource)

/-- β arm `hcompBetaDeep` of typed-Step.par rename equivariance (deep cubical hcomp at
a sides path that DEVELOPS to the constant `pathLam capRawSource.weaken`).  Unlike the
shallow `hcompBeta`, the typed `sidesPath` here carries a FREE raw `sidesPathRawSource`,
so it renames purely structurally — NO `Step.par.castSourceTermHeq` is needed on the
composition.  The single non-trivial step is the RAW develops-to premise `sidesPathStep
: RawStep.par sidesPathRawSource (pathLam capRawSource.weaken)`: renaming it via
`RawStep.par.rename` gives target `(pathLam capRawSource.weaken).rename rho`, which the
constructor wants as `pathLam ((capRawSource.rename rho).weaken)` — bridged by a single
`▸` with `RawTerm.weaken_rename_commute` (on a plain `RawTerm` index of `RawStep.par`,
no dependent-typing tangle).  The reduct (`capValueTarget`) is at the plain `carrierType`,
cast-free.  Mirrors `rename_compatible_typed_transpReflBetaDeep`. -/
theorem rename_compatible_typed_hcompBetaDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {sidesPathRawSource capRawSource capRawTarget : RawTerm sourceScope}
    (sidesPath :
      Term sourceCtx (Ty.path carrierType capRawSource capRawSource)
        sidesPathRawSource)
    (sidesPathStep :
      RawStep.par sidesPathRawSource (RawTerm.pathLam capRawSource.weaken))
    {capValueSource : Term sourceCtx carrierType capRawSource}
    {capValueTarget : Term sourceCtx carrierType capRawTarget}
    (capStep :
      Step.par (Term.rename termRenaming capValueSource)
               (Term.rename termRenaming capValueTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.hcompPath modeIsUnivalent
          (leftEndpoint := capRawSource) (rightEndpoint := capRawSource)
          sidesPath capValueSource))
      (Term.rename termRenaming capValueTarget) := by
  have targetRawCommute :
      (RawTerm.pathLam capRawSource.weaken).rename rho
        = RawTerm.pathLam ((capRawSource.rename rho).weaken) :=
    congrArg RawTerm.pathLam (RawTerm.weaken_rename_commute rho capRawSource)
  dsimp only [Term.rename]
  exact Step.par.hcompBetaDeep modeIsUnivalent
    (Term.rename termRenaming sidesPath)
    (targetRawCommute ▸ RawStep.par.rename rho sidesPathStep)
    capStep

/-- ι arm `iotaNatElimZero` of typed-Step.par rename equivariance.

`natElim 0 z s ⟶ z'` reduces only the zero branch; the successor
branch is carried unchanged.  The motive is non-dependent
(`Ty level scope`), so `Term.rename` pushes through `natElim` and the
literal `natZero` scrutinee cast-free — the reduct `zeroTarget` sits at
the redex's type `motiveType`. -/
theorem rename_compatible_typed_iotaNatElimZero
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level sourceScope}
    {zeroRawSource zeroRawTarget succRaw : RawTerm sourceScope}
    {zeroSource : Term sourceCtx motiveType zeroRawSource}
    {zeroTarget : Term sourceCtx motiveType zeroRawTarget}
    (succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw)
    (zeroStep :
      Step.par (Term.rename termRenaming zeroSource)
               (Term.rename termRenaming zeroTarget)) :
    Step.par
      (Term.rename termRenaming (Term.natElim Term.natZero zeroSource succBranch))
      (Term.rename termRenaming zeroTarget) := by
  dsimp only [Term.rename]
  exact Step.par.iotaNatElimZero (Term.rename termRenaming succBranch) zeroStep

/-- ι arm `iotaNatElimSucc` of typed-Step.par rename equivariance.

`natElim (succ n) z s ⟶ s' n'` reduces the predecessor and successor
branches; the zero branch is carried unchanged.  Non-dependent motive,
so `Term.rename` pushes through `natElim`, `natSucc`, and the `app`
reduct cast-free. -/
theorem rename_compatible_typed_iotaNatElimSucc
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level sourceScope}
    {predecessorRawSource predecessorRawTarget zeroRaw
     succRawSource succRawTarget : RawTerm sourceScope}
    {predecessorSource : Term sourceCtx Ty.nat predecessorRawSource}
    {predecessorTarget : Term sourceCtx Ty.nat predecessorRawTarget}
    (zeroBranch : Term sourceCtx motiveType zeroRaw)
    {succSource : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRawSource}
    {succTarget : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRawTarget}
    (predecessorStep :
      Step.par (Term.rename termRenaming predecessorSource)
               (Term.rename termRenaming predecessorTarget))
    (succStep :
      Step.par (Term.rename termRenaming succSource)
               (Term.rename termRenaming succTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.natElim (Term.natSucc predecessorSource) zeroBranch succSource))
      (Term.rename termRenaming (Term.app succTarget predecessorTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.iotaNatElimSucc (Term.rename termRenaming zeroBranch)
    predecessorStep succStep

/-- ι arm `iotaNatRecZero` of typed-Step.par rename equivariance.

`natRec 0 z s ⟶ z'`; mirrors `iotaNatElimZero` with the `natRec`
successor type `arrow nat (arrow motiveType motiveType)`.  Cast-free. -/
theorem rename_compatible_typed_iotaNatRecZero
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level sourceScope}
    {zeroRawSource zeroRawTarget succRaw : RawTerm sourceScope}
    {zeroSource : Term sourceCtx motiveType zeroRawSource}
    {zeroTarget : Term sourceCtx motiveType zeroRawTarget}
    (succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
    (zeroStep :
      Step.par (Term.rename termRenaming zeroSource)
               (Term.rename termRenaming zeroTarget)) :
    Step.par
      (Term.rename termRenaming (Term.natRec Term.natZero zeroSource succBranch))
      (Term.rename termRenaming zeroTarget) := by
  dsimp only [Term.rename]
  exact Step.par.iotaNatRecZero (Term.rename termRenaming succBranch) zeroStep

/-- ι arm `iotaNatRecSucc` of typed-Step.par rename equivariance.

`natRec (succ n) z s ⟶ s' n' (natRec n' z' s')` reduces the
predecessor, zero, and successor branches.  Non-dependent motive, so
`Term.rename` pushes through `natRec`, `natSucc`, and the nested
`app`/`natRec` reduct cast-free. -/
theorem rename_compatible_typed_iotaNatRecSucc
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level sourceScope}
    {predecessorRawSource predecessorRawTarget
     zeroRawSource zeroRawTarget
     succRawSource succRawTarget : RawTerm sourceScope}
    {predecessorSource : Term sourceCtx Ty.nat predecessorRawSource}
    {predecessorTarget : Term sourceCtx Ty.nat predecessorRawTarget}
    {zeroSource : Term sourceCtx motiveType zeroRawSource}
    {zeroTarget : Term sourceCtx motiveType zeroRawTarget}
    {succSource :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawSource}
    {succTarget :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawTarget}
    (predecessorStep :
      Step.par (Term.rename termRenaming predecessorSource)
               (Term.rename termRenaming predecessorTarget))
    (zeroStep :
      Step.par (Term.rename termRenaming zeroSource)
               (Term.rename termRenaming zeroTarget))
    (succStep :
      Step.par (Term.rename termRenaming succSource)
               (Term.rename termRenaming succTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.natRec (Term.natSucc predecessorSource) zeroSource succSource))
      (Term.rename termRenaming
        (Term.app (Term.app succTarget predecessorTarget)
                  (Term.natRec predecessorTarget zeroTarget succTarget))) := by
  dsimp only [Term.rename]
  exact Step.par.iotaNatRecSucc predecessorStep zeroStep succStep

/-- ι arm `iotaListElimNil` of typed-Step.par rename equivariance.

`listElim nil n c ⟶ n'` reduces only the nil branch; the cons branch
is carried unchanged.  Non-dependent motive over structurally-renaming
`Ty.listType`, so `Term.rename` pushes through `listElim` and the
`listNil` scrutinee cast-free. -/
theorem rename_compatible_typed_iotaListElimNil
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType motiveType : Ty level sourceScope}
    {nilRawSource nilRawTarget consRaw : RawTerm sourceScope}
    {nilSource : Term sourceCtx motiveType nilRawSource}
    {nilTarget : Term sourceCtx motiveType nilRawTarget}
    (consBranch :
      Term sourceCtx
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType)) consRaw)
    (nilStep :
      Step.par (Term.rename termRenaming nilSource)
               (Term.rename termRenaming nilTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.listElim (elementType := elementType) Term.listNil nilSource consBranch))
      (Term.rename termRenaming nilTarget) := by
  dsimp only [Term.rename]
  exact Step.par.iotaListElimNil (Term.rename termRenaming consBranch) nilStep

/-- ι arm `iotaListElimCons` of typed-Step.par rename equivariance.

`listElim (cons h t) n c ⟶ c' h' t'` reduces head, tail, and cons
branch; the nil branch is carried unchanged.  Non-dependent motive,
so `Term.rename` pushes through `listElim`, `listCons`, and the nested
`app` reduct cast-free. -/
theorem rename_compatible_typed_iotaListElimCons
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType motiveType : Ty level sourceScope}
    {headRawSource headRawTarget tailRawSource tailRawTarget
     nilRaw consRawSource consRawTarget : RawTerm sourceScope}
    {headSource : Term sourceCtx elementType headRawSource}
    {headTarget : Term sourceCtx elementType headRawTarget}
    {tailSource : Term sourceCtx (Ty.listType elementType) tailRawSource}
    {tailTarget : Term sourceCtx (Ty.listType elementType) tailRawTarget}
    (nilBranch : Term sourceCtx motiveType nilRaw)
    {consSource :
      Term sourceCtx
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
        consRawSource}
    {consTarget :
      Term sourceCtx
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
        consRawTarget}
    (headStep :
      Step.par (Term.rename termRenaming headSource)
               (Term.rename termRenaming headTarget))
    (tailStep :
      Step.par (Term.rename termRenaming tailSource)
               (Term.rename termRenaming tailTarget))
    (consStep :
      Step.par (Term.rename termRenaming consSource)
               (Term.rename termRenaming consTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.listElim (Term.listCons headSource tailSource) nilBranch consSource))
      (Term.rename termRenaming (Term.app (Term.app consTarget headTarget) tailTarget))
    := by
  dsimp only [Term.rename]
  exact Step.par.iotaListElimCons (Term.rename termRenaming nilBranch)
    headStep tailStep consStep

/-- ι arm `iotaOptionMatchNone` of typed-Step.par rename equivariance.

`optionMatch none n s ⟶ n'` reduces only the none branch; the some
branch is carried unchanged.  Non-dependent motive, cast-free push. -/
theorem rename_compatible_typed_iotaOptionMatchNone
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType motiveType : Ty level sourceScope}
    {noneRawSource noneRawTarget someRaw : RawTerm sourceScope}
    {noneSource : Term sourceCtx motiveType noneRawSource}
    {noneTarget : Term sourceCtx motiveType noneRawTarget}
    (someBranch : Term sourceCtx (Ty.arrow elementType motiveType) someRaw)
    (noneStep :
      Step.par (Term.rename termRenaming noneSource)
               (Term.rename termRenaming noneTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.optionMatch (elementType := elementType) Term.optionNone
          noneSource someBranch))
      (Term.rename termRenaming noneTarget) := by
  dsimp only [Term.rename]
  exact Step.par.iotaOptionMatchNone (Term.rename termRenaming someBranch) noneStep

/-- ι arm `iotaOptionMatchSome` of typed-Step.par rename equivariance.

`optionMatch (some v) n s ⟶ s' v'` reduces value and some branch; the
none branch is carried unchanged.  Non-dependent motive, so
`Term.rename` pushes through `optionMatch`, `optionSome`, and the `app`
reduct cast-free. -/
theorem rename_compatible_typed_iotaOptionMatchSome
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType motiveType : Ty level sourceScope}
    {valueRawSource valueRawTarget noneRaw
     someRawSource someRawTarget : RawTerm sourceScope}
    {valueSource : Term sourceCtx elementType valueRawSource}
    {valueTarget : Term sourceCtx elementType valueRawTarget}
    (noneBranch : Term sourceCtx motiveType noneRaw)
    {someSource : Term sourceCtx (Ty.arrow elementType motiveType) someRawSource}
    {someTarget : Term sourceCtx (Ty.arrow elementType motiveType) someRawTarget}
    (valueStep :
      Step.par (Term.rename termRenaming valueSource)
               (Term.rename termRenaming valueTarget))
    (someStep :
      Step.par (Term.rename termRenaming someSource)
               (Term.rename termRenaming someTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.optionMatch (Term.optionSome valueSource) noneBranch someSource))
      (Term.rename termRenaming (Term.app someTarget valueTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.iotaOptionMatchSome (Term.rename termRenaming noneBranch)
    valueStep someStep

/-- ι arm `iotaEitherMatchInl` of typed-Step.par rename equivariance.

`eitherMatch (inl v) lb rb ⟶ lb' v'` reduces value and left branch;
the right branch is carried unchanged.  Non-dependent motive, so
`Term.rename` pushes through `eitherMatch`, `eitherInl`, and the `app`
reduct cast-free. -/
theorem rename_compatible_typed_iotaEitherMatchInl
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftType rightType motiveType : Ty level sourceScope}
    {valueRawSource valueRawTarget leftRawSource leftRawTarget rightRaw
     : RawTerm sourceScope}
    {valueSource : Term sourceCtx leftType valueRawSource}
    {valueTarget : Term sourceCtx leftType valueRawTarget}
    {leftSource : Term sourceCtx (Ty.arrow leftType motiveType) leftRawSource}
    {leftTarget : Term sourceCtx (Ty.arrow leftType motiveType) leftRawTarget}
    (rightBranch : Term sourceCtx (Ty.arrow rightType motiveType) rightRaw)
    (valueStep :
      Step.par (Term.rename termRenaming valueSource)
               (Term.rename termRenaming valueTarget))
    (leftStep :
      Step.par (Term.rename termRenaming leftSource)
               (Term.rename termRenaming leftTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.eitherMatch (Term.eitherInl (rightType := rightType) valueSource)
          leftSource rightBranch))
      (Term.rename termRenaming (Term.app leftTarget valueTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.iotaEitherMatchInl (Term.rename termRenaming rightBranch)
    valueStep leftStep

/-- ι arm `iotaEitherMatchInr` of typed-Step.par rename equivariance.

`eitherMatch (inr v) lb rb ⟶ rb' v'` reduces value and right branch;
the left branch is carried unchanged.  Non-dependent motive, so
`Term.rename` pushes through `eitherMatch`, `eitherInr`, and the `app`
reduct cast-free. -/
theorem rename_compatible_typed_iotaEitherMatchInr
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftType rightType motiveType : Ty level sourceScope}
    {valueRawSource valueRawTarget leftRaw rightRawSource rightRawTarget
     : RawTerm sourceScope}
    {valueSource : Term sourceCtx rightType valueRawSource}
    {valueTarget : Term sourceCtx rightType valueRawTarget}
    (leftBranch : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw)
    {rightSource : Term sourceCtx (Ty.arrow rightType motiveType) rightRawSource}
    {rightTarget : Term sourceCtx (Ty.arrow rightType motiveType) rightRawTarget}
    (valueStep :
      Step.par (Term.rename termRenaming valueSource)
               (Term.rename termRenaming valueTarget))
    (rightStep :
      Step.par (Term.rename termRenaming rightSource)
               (Term.rename termRenaming rightTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.eitherMatch (Term.eitherInr (leftType := leftType) valueSource)
          leftBranch rightSource))
      (Term.rename termRenaming (Term.app rightTarget valueTarget)) := by
  dsimp only [Term.rename]
  exact Step.par.iotaEitherMatchInr (Term.rename termRenaming leftBranch)
    valueStep rightStep

/-- ι arm `iotaIdJRefl` of typed-Step.par rename equivariance.

`J base (refl c e) ⟶ base'` reduces only the base case; the `refl`
witness is canonical.  Non-dependent motive (the J dep-motive refactor
has not landed), so `Term.rename` pushes through `idJ` and the `refl`
scrutinee — `refl` renames structurally to `refl (c.rename) (e.rename)`
— cast-free, the reduct `baseTarget` at `motiveType`. -/
theorem rename_compatible_typed_iotaIdJRefl
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (carrier : Ty level sourceScope) (endpoint : RawTerm sourceScope)
    {motiveType : Ty level sourceScope}
    {baseRawSource baseRawTarget : RawTerm sourceScope}
    {baseSource : Term sourceCtx motiveType baseRawSource}
    {baseTarget : Term sourceCtx motiveType baseRawTarget}
    (baseStep :
      Step.par (Term.rename termRenaming baseSource)
               (Term.rename termRenaming baseTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.idJ (carrier := carrier) (leftEndpoint := endpoint)
          (rightEndpoint := endpoint) baseSource (Term.refl carrier endpoint)))
      (Term.rename termRenaming baseTarget) := by
  dsimp only [Term.rename]
  exact Step.par.iotaIdJRefl (carrier.rename rho) (endpoint.rename rho) baseStep

/-- ι arm `iotaIdStrictRecRefl` of typed-Step.par rename equivariance.

`idStrictRec base (idStrictRefl c e) ⟶ base'` in strict mode.  The mode
proof `modeIsStrict` is preserved by renaming; `idStrictRefl` renames
structurally; non-dependent motive — cast-free push to the reduct
`baseTarget` at `motiveType`. -/
theorem rename_compatible_typed_iotaIdStrictRecRefl
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level sourceScope) (endpoint : RawTerm sourceScope)
    {motiveType : Ty level sourceScope}
    {baseRawSource baseRawTarget : RawTerm sourceScope}
    {baseSource : Term sourceCtx motiveType baseRawSource}
    {baseTarget : Term sourceCtx motiveType baseRawTarget}
    (baseStep :
      Step.par (Term.rename termRenaming baseSource)
               (Term.rename termRenaming baseTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.idStrictRec (carrier := carrier) (leftEndpoint := endpoint)
          (rightEndpoint := endpoint) modeIsStrict baseSource
          (Term.idStrictRefl modeIsStrict carrier endpoint)))
      (Term.rename termRenaming baseTarget) := by
  dsimp only [Term.rename]
  exact Step.par.iotaIdStrictRecRefl modeIsStrict (carrier.rename rho)
    (endpoint.rename rho) baseStep

/-- ι arm `iotaBoolElimTrue` of typed-Step.par rename equivariance.

`boolElim true t e ⟶ t'` reduces only the then branch; the else branch
is carried unchanged.  Cast-bearing: the motive is dependent
(`Ty level (scope+1)`), so the branch and result types are
`motiveType.subst0 Ty.bool _`, which renaming reshapes via
`Ty.subst0_rename_commute`.  `Term.rename` of the source `boolElim`
already bakes in the result cast (`commTrue.symm ▸ …`), matched by the
outer `castSourceType`.  The bare-`thenTarget` reduct needs a cast
round-trip that does not cancel definitionally, closed by an
`eqRec_heq` HEq cancellation through `castTargetTermHeq`. -/
theorem rename_compatible_typed_iotaBoolElimTrue
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level (sourceScope + 1)}
    {thenRawSource thenRawTarget elseRaw : RawTerm sourceScope}
    {thenSource :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRawSource}
    {thenTarget :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRawTarget}
    (elseBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw)
    (thenStep :
      Step.par (Term.rename termRenaming thenSource)
               (Term.rename termRenaming thenTarget)) :
    Step.par
      (Term.rename termRenaming (Term.boolElim Term.boolTrue thenSource elseBranch))
      (Term.rename termRenaming thenTarget) := by
  dsimp only [Term.rename]
  have trueCommute := Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho
  have falseCommute := Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho
  exact Step.par.castTargetTermHeq rfl
    (HEq.trans
      (Term.type_eq_cast_heq trueCommute.symm (trueCommute ▸ Term.rename termRenaming thenTarget))
      (Term.type_eq_cast_heq trueCommute (Term.rename termRenaming thenTarget)))
    (Step.par.castTargetType trueCommute.symm
      (Step.par.castSourceType trueCommute.symm
        (Step.par.iotaBoolElimTrue
          (falseCommute ▸ Term.rename termRenaming elseBranch)
          (Step.par.castSourceType trueCommute
            (Step.par.castTargetType trueCommute thenStep)))))

/-- ι arm `iotaBoolElimFalse` of typed-Step.par rename equivariance.

`boolElim false t e ⟶ e'`; mirror of `iotaBoolElimTrue` with the else
branch reducing and the then branch carried.  The result/scrutinee cast
is `falseCommute` (scrutinee `boolFalse`); same `eqRec_heq` HEq
cancellation on the bare-`elseTarget` reduct. -/
theorem rename_compatible_typed_iotaBoolElimFalse
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level (sourceScope + 1)}
    {thenRaw elseRawSource elseRawTarget : RawTerm sourceScope}
    (thenBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    {elseSource :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRawSource}
    {elseTarget :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRawTarget}
    (elseStep :
      Step.par (Term.rename termRenaming elseSource)
               (Term.rename termRenaming elseTarget)) :
    Step.par
      (Term.rename termRenaming (Term.boolElim Term.boolFalse thenBranch elseSource))
      (Term.rename termRenaming elseTarget) := by
  dsimp only [Term.rename]
  have trueCommute := Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho
  have falseCommute := Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho
  exact Step.par.castTargetTermHeq rfl
    (HEq.trans
      (Term.type_eq_cast_heq falseCommute.symm
        (falseCommute ▸ Term.rename termRenaming elseTarget))
      (Term.type_eq_cast_heq falseCommute (Term.rename termRenaming elseTarget)))
    (Step.par.castTargetType falseCommute.symm
      (Step.par.castSourceType falseCommute.symm
        (Step.par.iotaBoolElimFalse
          (trueCommute ▸ Term.rename termRenaming thenBranch)
          (Step.par.castSourceType falseCommute
            (Step.par.castTargetType falseCommute elseStep)))))

/-- β arm `betaApp` of typed-Step.par rename equivariance.

`(λx. body) arg ⟶ body[arg/x]` for the non-dependent application.
This is the hardest arm: the reduct `subst0 bodyTarget argumentTarget`
develops into a substitution, so the renamed reduct must commute via
**T8** (`Term.subst0_rename_commute`), and the non-dependent lam carries
the body at `codomainType.weaken` so the body-cast is reconciled by
`Term.subst0_body_heq_of_eq` over `Ty.weaken_rename_commute`.  The
source matches the `betaApp` redex definitionally (the `app`/`lam`
rename arms bake in exactly the `weaken_rename_commute` body cast).  The
reduct's type/raw gap is closed by `castTargetType` (Ty-level
`subst0_rename_commute` + the weaken congruence) then `castTargetTermHeq`
(raw-level `subst0_rename_commute` + the composite HEq).  Zero-axiom. -/
theorem rename_compatible_typed_betaApp
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType codomainType : Ty level sourceScope}
    {bodyRawSource bodyRawTarget : RawTerm (sourceScope + 1)}
    {argumentRawSource argumentRawTarget : RawTerm sourceScope}
    {bodySource : Term (sourceCtx.cons domainType) codomainType.weaken bodyRawSource}
    {bodyTarget : Term (sourceCtx.cons domainType) codomainType.weaken bodyRawTarget}
    {argumentSource : Term sourceCtx domainType argumentRawSource}
    {argumentTarget : Term sourceCtx domainType argumentRawTarget}
    (bodyStep :
      Step.par (Term.rename (termRenaming.lift domainType) bodySource)
               (Term.rename (termRenaming.lift domainType) bodyTarget))
    (argumentStep :
      Step.par (Term.rename termRenaming argumentSource)
               (Term.rename termRenaming argumentTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.app (Term.lam (codomainType := codomainType) bodySource) argumentSource))
      (Term.rename termRenaming (Term.subst0 bodyTarget argumentTarget)) := by
  dsimp only [Term.rename]
  have weakenComm := Ty.weaken_rename_commute rho codomainType
  -- Ty-level alignment of the renamed reduct's type: the `betaApp` constructor
  -- pins the codomain at `(codomainType.rename rho).weaken`, whereas the goal's
  -- naturally-renamed reduct sits at `((codomainType.weaken).subst0 …).rename rho`.
  have tyAlign :
      ((codomainType.rename rho).weaken).subst0 (domainType.rename rho)
            (argumentRawTarget.rename rho)
        = ((codomainType.weaken).subst0 domainType argumentRawTarget).rename rho :=
    ((Ty.subst0_rename_commute codomainType.weaken domainType argumentRawTarget rho).trans
      (congrArg
        (fun codomain =>
          Ty.subst0 codomain (domainType.rename rho) (argumentRawTarget.rename rho))
        weakenComm)).symm
  -- Elaborate the `castTargetType`-wrapped constructor FIRST (as a non-hole
  -- argument) so its concrete target pins `targetOriginal`; the raw-index HEq is
  -- deferred to the trailing `exact`, dodging the `▸` higher-order metavar.
  refine Step.par.castTargetTermHeq
    (RawTerm.subst0_rename_commute bodyRawTarget argumentRawTarget rho).symm
    ?heqBridge
    (Step.par.castTargetType tyAlign
      (Step.par.betaApp
        (Step.par.castSourceType weakenComm (Step.par.castTargetType weakenComm bodyStep))
        argumentStep))
  exact HEq.trans
    (Term.type_eq_cast_heq tyAlign
      (Term.subst0
        (weakenComm ▸ Term.rename (termRenaming.lift domainType) bodyTarget)
        (Term.rename termRenaming argumentTarget)))
    (HEq.trans
      (Term.subst0_body_heq_of_eq weakenComm.symm rfl
        (Term.type_eq_cast_heq weakenComm
          (Term.rename (termRenaming.lift domainType) bodyTarget)))
      (Term.subst0_rename_commute termRenaming bodyTarget argumentTarget).symm)

/-- β arm `betaAppPi` of typed-Step.par rename equivariance.

`(λx. body) arg ⟶ body[arg/x]` for the dependent Π application.  Simpler
than `betaApp`: the dependent `lamPi` body lives at `codomainType` (a
`Ty (scope+1)`) rather than `codomainType.weaken`, so the `lamPi` rename
arm is cast-free and the reduct bridge is exactly **T8**
(`Term.subst0_rename_commute`) — no `subst0_body_heq_of_eq` weaken
reconciliation.  The `appPi` rename arm DOES carry an outer
`Ty.subst0_rename_commute` cast on the β-redex result type, so the source
is realigned by `castSourceType`; the reduct's Ty index by
`castTargetType` and raw index by `castTargetTermHeq`.  Zero-axiom. -/
theorem rename_compatible_typed_betaAppPi
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType : Ty level sourceScope} {codomainType : Ty level (sourceScope + 1)}
    {bodyRawSource bodyRawTarget : RawTerm (sourceScope + 1)}
    {argumentRawSource argumentRawTarget : RawTerm sourceScope}
    {bodySource : Term (sourceCtx.cons domainType) codomainType bodyRawSource}
    {bodyTarget : Term (sourceCtx.cons domainType) codomainType bodyRawTarget}
    {argumentSource : Term sourceCtx domainType argumentRawSource}
    {argumentTarget : Term sourceCtx domainType argumentRawTarget}
    (bodyStep :
      Step.par (Term.rename (termRenaming.lift domainType) bodySource)
               (Term.rename (termRenaming.lift domainType) bodyTarget))
    (argumentStep :
      Step.par (Term.rename termRenaming argumentSource)
               (Term.rename termRenaming argumentTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.appPi (Term.lamPi (domainType := domainType) bodySource) argumentSource))
      (Term.rename termRenaming (Term.subst0 bodyTarget argumentTarget)) := by
  dsimp only [Term.rename]
  refine Step.par.castTargetTermHeq
    (RawTerm.subst0_rename_commute bodyRawTarget argumentRawTarget rho).symm
    ?heqBridge
    (Step.par.castTargetType
      (Ty.subst0_rename_commute codomainType domainType argumentRawTarget rho).symm
      (Step.par.castSourceType
        (Ty.subst0_rename_commute codomainType domainType argumentRawSource rho).symm
        (Step.par.betaAppPi bodyStep argumentStep)))
  exact HEq.trans
    (Term.type_eq_cast_heq
      (Ty.subst0_rename_commute codomainType domainType argumentRawTarget rho).symm
      (Term.subst0 (Term.rename (termRenaming.lift domainType) bodyTarget)
        (Term.rename termRenaming argumentTarget)))
    (Term.subst0_rename_commute termRenaming bodyTarget argumentTarget).symm

/-- Deep ι arm `iotaNatElimZeroDeep`: scrutinee parallel-reduces to `natZero`,
then `natElim` fires to the zero branch.  Cast-free (non-dependent motive);
`natZero` renames to itself so the scrutinee step transports definitionally. -/
theorem rename_compatible_typed_iotaNatElimZeroDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRawSource zeroRawTarget succRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroSource : Term sourceCtx motiveType zeroRawSource}
    {zeroTarget : Term sourceCtx motiveType zeroRawTarget}
    (succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutinee)
               (Term.rename termRenaming Term.natZero))
    (zeroStep :
      Step.par (Term.rename termRenaming zeroSource)
               (Term.rename termRenaming zeroTarget)) :
    Step.par
      (Term.rename termRenaming (Term.natElim scrutinee zeroSource succBranch))
      (Term.rename termRenaming zeroTarget) := by
  dsimp only [Term.rename] at scrutineeStep ⊢
  exact Step.par.iotaNatElimZeroDeep (Term.rename termRenaming succBranch)
    scrutineeStep zeroStep

/-- Deep ι arm `iotaNatElimSuccDeep`: scrutinee reduces to `natSucc pred`,
then `natElim` fires to `app succTarget pred`.  Cast-free. -/
theorem rename_compatible_typed_iotaNatElimSuccDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level sourceScope}
    {scrutineeRaw predecessorRaw zeroRaw succRawSource succRawTarget : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {predecessor : Term sourceCtx Ty.nat predecessorRaw}
    (zeroBranch : Term sourceCtx motiveType zeroRaw)
    {succSource : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRawSource}
    {succTarget : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRawTarget}
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutinee)
               (Term.rename termRenaming (Term.natSucc predecessor)))
    (succStep :
      Step.par (Term.rename termRenaming succSource)
               (Term.rename termRenaming succTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.natElim scrutinee zeroBranch succSource))
      (Term.rename termRenaming (Term.app succTarget predecessor)) := by
  dsimp only [Term.rename] at scrutineeStep ⊢
  exact Step.par.iotaNatElimSuccDeep (Term.rename termRenaming zeroBranch)
    scrutineeStep succStep

/-- Deep ι arm `iotaNatRecZeroDeep`: mirrors `iotaNatElimZeroDeep` for
`natRec` with the recursor successor type.  Cast-free. -/
theorem rename_compatible_typed_iotaNatRecZeroDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRawSource zeroRawTarget succRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroSource : Term sourceCtx motiveType zeroRawSource}
    {zeroTarget : Term sourceCtx motiveType zeroRawTarget}
    (succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutinee)
               (Term.rename termRenaming Term.natZero))
    (zeroStep :
      Step.par (Term.rename termRenaming zeroSource)
               (Term.rename termRenaming zeroTarget)) :
    Step.par
      (Term.rename termRenaming (Term.natRec scrutinee zeroSource succBranch))
      (Term.rename termRenaming zeroTarget) := by
  dsimp only [Term.rename] at scrutineeStep ⊢
  exact Step.par.iotaNatRecZeroDeep (Term.rename termRenaming succBranch)
    scrutineeStep zeroStep

/-- Deep ι arm `iotaNatRecSuccDeep`: scrutinee reduces to `natSucc pred`,
then `natRec` fires to the nested `app`/`natRec` reduct.  Cast-free. -/
theorem rename_compatible_typed_iotaNatRecSuccDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level sourceScope}
    {scrutineeRaw predecessorRaw zeroRawSource zeroRawTarget
     succRawSource succRawTarget : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {predecessor : Term sourceCtx Ty.nat predecessorRaw}
    {zeroSource : Term sourceCtx motiveType zeroRawSource}
    {zeroTarget : Term sourceCtx motiveType zeroRawTarget}
    {succSource :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawSource}
    {succTarget :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawTarget}
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutinee)
               (Term.rename termRenaming (Term.natSucc predecessor)))
    (zeroStep :
      Step.par (Term.rename termRenaming zeroSource)
               (Term.rename termRenaming zeroTarget))
    (succStep :
      Step.par (Term.rename termRenaming succSource)
               (Term.rename termRenaming succTarget)) :
    Step.par
      (Term.rename termRenaming (Term.natRec scrutinee zeroSource succSource))
      (Term.rename termRenaming
        (Term.app (Term.app succTarget predecessor)
                  (Term.natRec predecessor zeroTarget succTarget))) := by
  dsimp only [Term.rename] at scrutineeStep ⊢
  exact Step.par.iotaNatRecSuccDeep scrutineeStep zeroStep succStep

/-- Deep ι arm `iotaListElimNilDeep`: scrutinee reduces to `listNil`, then
`listElim` fires to the nil branch.  Cast-free. -/
theorem rename_compatible_typed_iotaListElimNilDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw nilRawSource nilRawTarget consRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx (Ty.listType elementType) scrutineeRaw}
    {nilSource : Term sourceCtx motiveType nilRawSource}
    {nilTarget : Term sourceCtx motiveType nilRawTarget}
    (consBranch :
      Term sourceCtx
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType)) consRaw)
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutinee)
               (Term.rename termRenaming (Term.listNil (elementType := elementType))))
    (nilStep :
      Step.par (Term.rename termRenaming nilSource)
               (Term.rename termRenaming nilTarget)) :
    Step.par
      (Term.rename termRenaming (Term.listElim scrutinee nilSource consBranch))
      (Term.rename termRenaming nilTarget) := by
  dsimp only [Term.rename] at scrutineeStep ⊢
  exact Step.par.iotaListElimNilDeep (Term.rename termRenaming consBranch)
    scrutineeStep nilStep

/-- Deep ι arm `iotaListElimConsDeep`: scrutinee reduces to `listCons h t`,
then `listElim` fires to the nested `app` reduct.  Cast-free. -/
theorem rename_compatible_typed_iotaListElimConsDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw headRaw tailRaw nilRaw consRawSource consRawTarget : RawTerm sourceScope}
    {scrutinee : Term sourceCtx (Ty.listType elementType) scrutineeRaw}
    {headTerm : Term sourceCtx elementType headRaw}
    {tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw}
    (nilBranch : Term sourceCtx motiveType nilRaw)
    {consSource :
      Term sourceCtx
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType)) consRawSource}
    {consTarget :
      Term sourceCtx
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType)) consRawTarget}
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutinee)
               (Term.rename termRenaming (Term.listCons headTerm tailTerm)))
    (consStep :
      Step.par (Term.rename termRenaming consSource)
               (Term.rename termRenaming consTarget)) :
    Step.par
      (Term.rename termRenaming (Term.listElim scrutinee nilBranch consSource))
      (Term.rename termRenaming
        (Term.app (Term.app consTarget headTerm) tailTerm)) := by
  dsimp only [Term.rename] at scrutineeStep ⊢
  exact Step.par.iotaListElimConsDeep (Term.rename termRenaming nilBranch)
    scrutineeStep consStep

/-- Deep ι arm `iotaOptionMatchNoneDeep`: scrutinee reduces to `optionNone`,
then `optionMatch` fires to the none branch.  Cast-free. -/
theorem rename_compatible_typed_iotaOptionMatchNoneDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw noneRawSource noneRawTarget someRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneSource : Term sourceCtx motiveType noneRawSource}
    {noneTarget : Term sourceCtx motiveType noneRawTarget}
    (someBranch : Term sourceCtx (Ty.arrow elementType motiveType) someRaw)
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutinee)
               (Term.rename termRenaming (Term.optionNone (elementType := elementType))))
    (noneStep :
      Step.par (Term.rename termRenaming noneSource)
               (Term.rename termRenaming noneTarget)) :
    Step.par
      (Term.rename termRenaming (Term.optionMatch scrutinee noneSource someBranch))
      (Term.rename termRenaming noneTarget) := by
  dsimp only [Term.rename] at scrutineeStep ⊢
  exact Step.par.iotaOptionMatchNoneDeep (Term.rename termRenaming someBranch)
    scrutineeStep noneStep

/-- Deep ι arm `iotaOptionMatchSomeDeep`: scrutinee reduces to `optionSome v`,
then `optionMatch` fires to `app someTarget v`.  Cast-free. -/
theorem rename_compatible_typed_iotaOptionMatchSomeDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {elementType motiveType : Ty level sourceScope}
    {scrutineeRaw valueRaw noneRaw someRawSource someRawTarget : RawTerm sourceScope}
    {scrutinee : Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {valueTerm : Term sourceCtx elementType valueRaw}
    (noneBranch : Term sourceCtx motiveType noneRaw)
    {someSource : Term sourceCtx (Ty.arrow elementType motiveType) someRawSource}
    {someTarget : Term sourceCtx (Ty.arrow elementType motiveType) someRawTarget}
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutinee)
               (Term.rename termRenaming (Term.optionSome valueTerm)))
    (someStep :
      Step.par (Term.rename termRenaming someSource)
               (Term.rename termRenaming someTarget)) :
    Step.par
      (Term.rename termRenaming (Term.optionMatch scrutinee noneBranch someSource))
      (Term.rename termRenaming (Term.app someTarget valueTerm)) := by
  dsimp only [Term.rename] at scrutineeStep ⊢
  exact Step.par.iotaOptionMatchSomeDeep (Term.rename termRenaming noneBranch)
    scrutineeStep someStep

/-- Deep ι arm `iotaEitherMatchInlDeep`: scrutinee reduces to `eitherInl v`,
then `eitherMatch` fires to `app leftTarget v`.  Cast-free. -/
theorem rename_compatible_typed_iotaEitherMatchInlDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftType rightType motiveType : Ty level sourceScope}
    {scrutineeRaw valueRaw leftRawSource leftRawTarget rightRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {valueTerm : Term sourceCtx leftType valueRaw}
    {leftSource : Term sourceCtx (Ty.arrow leftType motiveType) leftRawSource}
    {leftTarget : Term sourceCtx (Ty.arrow leftType motiveType) leftRawTarget}
    (rightBranch : Term sourceCtx (Ty.arrow rightType motiveType) rightRaw)
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutinee)
               (Term.rename termRenaming (Term.eitherInl (rightType := rightType) valueTerm)))
    (leftStep :
      Step.par (Term.rename termRenaming leftSource)
               (Term.rename termRenaming leftTarget)) :
    Step.par
      (Term.rename termRenaming (Term.eitherMatch scrutinee leftSource rightBranch))
      (Term.rename termRenaming (Term.app leftTarget valueTerm)) := by
  dsimp only [Term.rename] at scrutineeStep ⊢
  exact Step.par.iotaEitherMatchInlDeep (Term.rename termRenaming rightBranch)
    scrutineeStep leftStep

/-- Deep ι arm `iotaEitherMatchInrDeep`: scrutinee reduces to `eitherInr v`,
then `eitherMatch` fires to `app rightTarget v`.  Cast-free. -/
theorem rename_compatible_typed_iotaEitherMatchInrDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {leftType rightType motiveType : Ty level sourceScope}
    {scrutineeRaw valueRaw leftRaw rightRawSource rightRawTarget : RawTerm sourceScope}
    {scrutinee : Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {valueTerm : Term sourceCtx rightType valueRaw}
    (leftBranch : Term sourceCtx (Ty.arrow leftType motiveType) leftRaw)
    {rightSource : Term sourceCtx (Ty.arrow rightType motiveType) rightRawSource}
    {rightTarget : Term sourceCtx (Ty.arrow rightType motiveType) rightRawTarget}
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutinee)
               (Term.rename termRenaming (Term.eitherInr (leftType := leftType) valueTerm)))
    (rightStep :
      Step.par (Term.rename termRenaming rightSource)
               (Term.rename termRenaming rightTarget)) :
    Step.par
      (Term.rename termRenaming (Term.eitherMatch scrutinee leftBranch rightSource))
      (Term.rename termRenaming (Term.app rightTarget valueTerm)) := by
  dsimp only [Term.rename] at scrutineeStep ⊢
  exact Step.par.iotaEitherMatchInrDeep (Term.rename termRenaming leftBranch)
    scrutineeStep rightStep

/-- Deep ι arm `iotaIdJReflDeep`: witness reduces to `refl`, then `idJ` fires
to the base.  Cast-free (non-dependent motive); `refl` renames structurally. -/
theorem rename_compatible_typed_iotaIdJReflDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (carrier : Ty level sourceScope) (endpoint : RawTerm sourceScope)
    {motiveType : Ty level sourceScope}
    {baseRawSource baseRawTarget witnessRawSource : RawTerm sourceScope}
    {baseSource : Term sourceCtx motiveType baseRawSource}
    {baseTarget : Term sourceCtx motiveType baseRawTarget}
    {witnessSource : Term sourceCtx (Ty.id carrier endpoint endpoint) witnessRawSource}
    (witnessStep :
      Step.par (Term.rename termRenaming witnessSource)
               (Term.rename termRenaming (Term.refl carrier endpoint)))
    (baseStep :
      Step.par (Term.rename termRenaming baseSource)
               (Term.rename termRenaming baseTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.idJ (carrier := carrier) (leftEndpoint := endpoint)
          (rightEndpoint := endpoint) baseSource witnessSource))
      (Term.rename termRenaming baseTarget) := by
  dsimp only [Term.rename] at witnessStep ⊢
  exact Step.par.iotaIdJReflDeep witnessStep baseStep

/-- Deep strict-id ι arm `iotaIdStrictRecReflDeep`: witness reduces to
`idStrictRefl`, then strict rec fires to the base.  Cast-free; the mode
proof `modeIsStrict` is preserved by renaming. -/
theorem rename_compatible_typed_iotaIdStrictRecReflDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level sourceScope) (endpoint : RawTerm sourceScope)
    {motiveType : Ty level sourceScope}
    {baseRawSource baseRawTarget witnessRawSource : RawTerm sourceScope}
    {baseSource : Term sourceCtx motiveType baseRawSource}
    {baseTarget : Term sourceCtx motiveType baseRawTarget}
    {witnessSource : Term sourceCtx (Ty.idStrict carrier endpoint endpoint) witnessRawSource}
    (witnessStep :
      Step.par (Term.rename termRenaming witnessSource)
               (Term.rename termRenaming (Term.idStrictRefl modeIsStrict carrier endpoint)))
    (baseStep :
      Step.par (Term.rename termRenaming baseSource)
               (Term.rename termRenaming baseTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.idStrictRec (carrier := carrier) (leftEndpoint := endpoint)
          (rightEndpoint := endpoint) modeIsStrict baseSource witnessSource))
      (Term.rename termRenaming baseTarget) := by
  dsimp only [Term.rename] at witnessStep ⊢
  exact Step.par.iotaIdStrictRecReflDeep modeIsStrict witnessStep baseStep

/-- Shallow cubical β arm `betaPathApp`: `(pathLam body) @ interval ⟶
body[interval]`.  Structurally identical to `betaApp` — the `pathLam` body
lives at `carrierType.weaken` (so the `pathLam` rename arm carries the
`weaken_rename_commute` body cast, reconciled by `subst0_body_heq_of_eq`),
the reduct develops into `subst0` (bridged by **T8**), and the `pathApp`
rename arm is itself cast-free so the source needs no realignment.  The
substituent is `Ty.interval`; `modeIsUnivalent` threads unchanged.
Zero-axiom. -/
theorem rename_compatible_typed_betaPathApp
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {bodyRawSource bodyRawTarget : RawTerm (sourceScope + 1)}
    {intervalRawSource intervalRawTarget : RawTerm sourceScope}
    {bodySource : Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRawSource}
    {bodyTarget : Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRawTarget}
    {intervalSource : Term sourceCtx Ty.interval intervalRawSource}
    {intervalTarget : Term sourceCtx Ty.interval intervalRawTarget}
    (bodyStep :
      Step.par (Term.rename (termRenaming.lift Ty.interval) bodySource)
               (Term.rename (termRenaming.lift Ty.interval) bodyTarget))
    (intervalStep :
      Step.par (Term.rename termRenaming intervalSource)
               (Term.rename termRenaming intervalTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.pathApp modeIsUnivalent
          (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint bodySource)
          intervalSource))
      (Term.rename termRenaming (Term.subst0 bodyTarget intervalTarget)) := by
  dsimp only [Term.rename]
  have weakenComm := Ty.weaken_rename_commute rho carrierType
  have tyAlign :
      ((carrierType.rename rho).weaken).subst0 Ty.interval (intervalRawTarget.rename rho)
        = ((carrierType.weaken).subst0 Ty.interval intervalRawTarget).rename rho :=
    ((Ty.subst0_rename_commute carrierType.weaken Ty.interval intervalRawTarget rho).trans
      (congrArg
        (fun codomain =>
          Ty.subst0 codomain Ty.interval (intervalRawTarget.rename rho))
        weakenComm)).symm
  refine Step.par.castTargetTermHeq
    (RawTerm.subst0_rename_commute bodyRawTarget intervalRawTarget rho).symm
    ?heqBridge
    (Step.par.castTargetType tyAlign
      (Step.par.betaPathApp modeIsUnivalent
        (Step.par.castSourceType weakenComm (Step.par.castTargetType weakenComm bodyStep))
        intervalStep))
  exact HEq.trans
    (Term.type_eq_cast_heq tyAlign
      (Term.subst0
        (weakenComm ▸ Term.rename (termRenaming.lift Ty.interval) bodyTarget)
        (Term.rename termRenaming intervalTarget)))
    (HEq.trans
      (Term.subst0_body_heq_of_eq weakenComm.symm rfl
        (Term.type_eq_cast_heq weakenComm
          (Term.rename (termRenaming.lift Ty.interval) bodyTarget)))
      (Term.subst0_rename_commute termRenaming bodyTarget intervalTarget).symm)

/-- Deep ι arm `iotaBoolElimTrueDeep`: scrutinee parallel-reduces to
`boolTrue`, then `boolElim` fires to the then branch.  Cast-bearing
(dependent motive): the `boolElim` rename arm carries an OUTER
`subst0_rename_commute` cast at the SCRUTINEE raw (`scrutineeCommute`,
distinct from the `trueCommute` branch cast since the scrutinee is a
variable here), plus per-branch `trueCommute`/`falseCommute` casts.
Mirrors the non-Deep `iotaBoolElimTrue` cast stack with the outer source
realignment switched to `scrutineeCommute`.  Zero-axiom. -/
theorem rename_compatible_typed_iotaBoolElimTrueDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level (sourceScope + 1)}
    {scrutineeRaw thenRawSource thenRawTarget elseRaw : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenSource :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRawSource}
    {thenTarget :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRawTarget}
    (elseBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw)
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutinee)
               (Term.rename termRenaming Term.boolTrue))
    (thenStep :
      Step.par (Term.rename termRenaming thenSource)
               (Term.rename termRenaming thenTarget)) :
    Step.par
      (Term.rename termRenaming (Term.boolElim scrutinee thenSource elseBranch))
      (Term.rename termRenaming thenTarget) := by
  dsimp only [Term.rename] at scrutineeStep ⊢
  have scrutineeCommute := Ty.subst0_rename_commute motiveType Ty.bool scrutineeRaw rho
  have trueCommute := Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho
  have falseCommute := Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho
  exact Step.par.castTargetTermHeq rfl
    (HEq.trans
      (Term.type_eq_cast_heq trueCommute.symm (trueCommute ▸ Term.rename termRenaming thenTarget))
      (Term.type_eq_cast_heq trueCommute (Term.rename termRenaming thenTarget)))
    (Step.par.castTargetType trueCommute.symm
      (Step.par.castSourceType scrutineeCommute.symm
        (Step.par.iotaBoolElimTrueDeep
          (falseCommute ▸ Term.rename termRenaming elseBranch)
          scrutineeStep
          (Step.par.castSourceType trueCommute
            (Step.par.castTargetType trueCommute thenStep)))))

/-- Deep ι arm `iotaBoolElimFalseDeep`: scrutinee parallel-reduces to
`boolFalse`, then `boolElim` fires to the else branch.  Mirror of
`iotaBoolElimTrueDeep` with the reduct cast `falseCommute` (the else
branch reduces) and the same outer `scrutineeCommute` source
realignment.  Zero-axiom. -/
theorem rename_compatible_typed_iotaBoolElimFalseDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {motiveType : Ty level (sourceScope + 1)}
    {scrutineeRaw thenRaw elseRawSource elseRawTarget : RawTerm sourceScope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    (thenBranch :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    {elseSource :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRawSource}
    {elseTarget :
      Term sourceCtx (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRawTarget}
    (scrutineeStep :
      Step.par (Term.rename termRenaming scrutinee)
               (Term.rename termRenaming Term.boolFalse))
    (elseStep :
      Step.par (Term.rename termRenaming elseSource)
               (Term.rename termRenaming elseTarget)) :
    Step.par
      (Term.rename termRenaming (Term.boolElim scrutinee thenBranch elseSource))
      (Term.rename termRenaming elseTarget) := by
  dsimp only [Term.rename] at scrutineeStep ⊢
  have scrutineeCommute := Ty.subst0_rename_commute motiveType Ty.bool scrutineeRaw rho
  have trueCommute := Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolTrue rho
  have falseCommute := Ty.subst0_rename_commute motiveType Ty.bool RawTerm.boolFalse rho
  exact Step.par.castTargetTermHeq rfl
    (HEq.trans
      (Term.type_eq_cast_heq falseCommute.symm (falseCommute ▸ Term.rename termRenaming elseTarget))
      (Term.type_eq_cast_heq falseCommute (Term.rename termRenaming elseTarget)))
    (Step.par.castTargetType falseCommute.symm
      (Step.par.castSourceType scrutineeCommute.symm
        (Step.par.iotaBoolElimFalseDeep
          (trueCommute ▸ Term.rename termRenaming thenBranch)
          scrutineeStep
          (Step.par.castSourceType falseCommute
            (Step.par.castTargetType falseCommute elseStep)))))

/-- Deep β arm `betaAppDeep`: the function parallel-reduces *to* a literal
`lam`, then `app` contracts.  Same reduct stack as `betaApp` (the renamed
`lam` target carries the `weaken_rename_commute` body cast, reconciled by
`subst0_body_heq_of_eq` + T8); the `app` source is cast-free so the
function-step is passed straight to the constructor.  Zero-axiom. -/
theorem rename_compatible_typed_betaAppDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType codomainType : Ty level sourceScope}
    {bodyRawTarget : RawTerm (sourceScope + 1)}
    {argumentRawSource argumentRawTarget functionRawSourceOuter : RawTerm sourceScope}
    {functionTermSource :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRawSourceOuter}
    {bodyTarget : Term (sourceCtx.cons domainType) codomainType.weaken bodyRawTarget}
    {argumentSource : Term sourceCtx domainType argumentRawSource}
    {argumentTarget : Term sourceCtx domainType argumentRawTarget}
    (functionStep :
      Step.par (Term.rename termRenaming functionTermSource)
               (Term.rename termRenaming
                 (Term.lam (codomainType := codomainType) bodyTarget)))
    (argumentStep :
      Step.par (Term.rename termRenaming argumentSource)
               (Term.rename termRenaming argumentTarget)) :
    Step.par
      (Term.rename termRenaming (Term.app functionTermSource argumentSource))
      (Term.rename termRenaming (Term.subst0 bodyTarget argumentTarget)) := by
  dsimp only [Term.rename] at functionStep ⊢
  have weakenComm := Ty.weaken_rename_commute rho codomainType
  have tyAlign :
      ((codomainType.rename rho).weaken).subst0 (domainType.rename rho)
            (argumentRawTarget.rename rho)
        = ((codomainType.weaken).subst0 domainType argumentRawTarget).rename rho :=
    ((Ty.subst0_rename_commute codomainType.weaken domainType argumentRawTarget rho).trans
      (congrArg
        (fun codomain =>
          Ty.subst0 codomain (domainType.rename rho) (argumentRawTarget.rename rho))
        weakenComm)).symm
  refine Step.par.castTargetTermHeq
    (RawTerm.subst0_rename_commute bodyRawTarget argumentRawTarget rho).symm
    ?heqBridge
    (Step.par.castTargetType tyAlign
      (Step.par.betaAppDeep
        (functionRawSource := bodyRawTarget.rename rho.lift) functionStep argumentStep))
  exact HEq.trans
    (Term.type_eq_cast_heq tyAlign
      (Term.subst0
        (weakenComm ▸ Term.rename (termRenaming.lift domainType) bodyTarget)
        (Term.rename termRenaming argumentTarget)))
    (HEq.trans
      (Term.subst0_body_heq_of_eq weakenComm.symm rfl
        (Term.type_eq_cast_heq weakenComm
          (Term.rename (termRenaming.lift domainType) bodyTarget)))
      (Term.subst0_rename_commute termRenaming bodyTarget argumentTarget).symm)

/-- Deep β arm `betaAppPiDeep`: the dependent function parallel-reduces *to*
a literal `lamPi`, then `appPi` contracts.  Same reduct stack as
`betaAppPi` (cast-free `lamPi` body => reduct bridge is exactly T8); the
`appPi` source carries the `subst0_rename_commute` cast realigned by
`castSourceType`.  Zero-axiom. -/
theorem rename_compatible_typed_betaAppPiDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType : Ty level sourceScope} {codomainType : Ty level (sourceScope + 1)}
    {bodyRawTarget : RawTerm (sourceScope + 1)}
    {argumentRawSource argumentRawTarget functionRawSourceOuter : RawTerm sourceScope}
    {functionTermSource :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRawSourceOuter}
    {bodyTarget : Term (sourceCtx.cons domainType) codomainType bodyRawTarget}
    {argumentSource : Term sourceCtx domainType argumentRawSource}
    {argumentTarget : Term sourceCtx domainType argumentRawTarget}
    (functionStep :
      Step.par (Term.rename termRenaming functionTermSource)
               (Term.rename termRenaming
                 (Term.lamPi (domainType := domainType) bodyTarget)))
    (argumentStep :
      Step.par (Term.rename termRenaming argumentSource)
               (Term.rename termRenaming argumentTarget)) :
    Step.par
      (Term.rename termRenaming (Term.appPi functionTermSource argumentSource))
      (Term.rename termRenaming (Term.subst0 bodyTarget argumentTarget)) := by
  dsimp only [Term.rename] at functionStep ⊢
  refine Step.par.castTargetTermHeq
    (RawTerm.subst0_rename_commute bodyRawTarget argumentRawTarget rho).symm
    ?heqBridge
    (Step.par.castTargetType
      (Ty.subst0_rename_commute codomainType domainType argumentRawTarget rho).symm
      (Step.par.castSourceType
        (Ty.subst0_rename_commute codomainType domainType argumentRawSource rho).symm
        (Step.par.betaAppPiDeep functionStep argumentStep)))
  exact HEq.trans
    (Term.type_eq_cast_heq
      (Ty.subst0_rename_commute codomainType domainType argumentRawTarget rho).symm
      (Term.subst0 (Term.rename (termRenaming.lift domainType) bodyTarget)
        (Term.rename termRenaming argumentTarget)))
    (Term.subst0_rename_commute termRenaming bodyTarget argumentTarget).symm

/-- Deep cubical β arm `betaPathAppDeep`: the path term parallel-reduces *to*
a literal `pathLam`, then `pathApp` contracts.  Same reduct stack as
`betaPathApp` (weaken body cast + T8); the `pathApp` source is cast-free so
the path-step is passed straight to the constructor.  `modeIsUnivalent`
threads unchanged.  Zero-axiom. -/
theorem rename_compatible_typed_betaPathAppDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRawSource intervalRawSource intervalRawTarget : RawTerm sourceScope}
    {bodyRawTarget : RawTerm (sourceScope + 1)}
    {pathSource :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint) pathRawSource}
    {bodyTarget : Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRawTarget}
    {intervalSource : Term sourceCtx Ty.interval intervalRawSource}
    {intervalTarget : Term sourceCtx Ty.interval intervalRawTarget}
    (pathStep :
      Step.par (Term.rename termRenaming pathSource)
               (Term.rename termRenaming
                 (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
                   bodyTarget)))
    (intervalStep :
      Step.par (Term.rename termRenaming intervalSource)
               (Term.rename termRenaming intervalTarget)) :
    Step.par
      (Term.rename termRenaming (Term.pathApp modeIsUnivalent pathSource intervalSource))
      (Term.rename termRenaming (Term.subst0 bodyTarget intervalTarget)) := by
  dsimp only [Term.rename] at pathStep ⊢
  have weakenComm := Ty.weaken_rename_commute rho carrierType
  have tyAlign :
      ((carrierType.rename rho).weaken).subst0 Ty.interval (intervalRawTarget.rename rho)
        = ((carrierType.weaken).subst0 Ty.interval intervalRawTarget).rename rho :=
    ((Ty.subst0_rename_commute carrierType.weaken Ty.interval intervalRawTarget rho).trans
      (congrArg
        (fun codomain =>
          Ty.subst0 codomain Ty.interval (intervalRawTarget.rename rho))
        weakenComm)).symm
  refine Step.par.castTargetTermHeq
    (RawTerm.subst0_rename_commute bodyRawTarget intervalRawTarget rho).symm
    ?heqBridge
    (Step.par.castTargetType tyAlign
      (Step.par.betaPathAppDeep modeIsUnivalent pathStep intervalStep))
  exact HEq.trans
    (Term.type_eq_cast_heq tyAlign
      (Term.subst0
        (weakenComm ▸ Term.rename (termRenaming.lift Ty.interval) bodyTarget)
        (Term.rename termRenaming intervalTarget)))
    (HEq.trans
      (Term.subst0_body_heq_of_eq weakenComm.symm rfl
        (Term.type_eq_cast_heq weakenComm
          (Term.rename (termRenaming.lift Ty.interval) bodyTarget)))
      (Term.subst0_rename_commute termRenaming bodyTarget intervalTarget).symm)

/-- HEq congruence for the `betaPathReflApp` source: given the pathLam body's
raw equality plus its `HEq`, the two `pathApp (pathLam … body) interval` terms
are `HEq`.  `subst` the body raw (which makes the indices defeq) then `cases`
the now-homogeneous body `HEq` — the `betaPathReflApp` analog of
`transp_typePath_heqCongr`.  Zero-axiom. -/
theorem pathReflApp_body_heqCongr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRawA bodyRawB : RawTerm (scope + 1)} {intervalRaw : RawTerm scope}
    (bodyRawEq : bodyRawA = bodyRawB)
    {bodyA : Term (context.cons Ty.interval) carrierType.weaken bodyRawA}
    {bodyB : Term (context.cons Ty.interval) carrierType.weaken bodyRawB}
    (bodyHeq : HEq bodyA bodyB)
    (intervalTerm : Term context Ty.interval intervalRaw) :
    HEq
      (Term.pathApp modeIsUnivalent
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint bodyA)
        intervalTerm)
      (Term.pathApp modeIsUnivalent
        (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint bodyB)
        intervalTerm) := by
  cases bodyRawEq
  cases bodyHeq
  rfl

/-- β arm `betaPathReflApp` of typed-Step.par rename equivariance: cubical path
β at a constant (`weaken`ed) body — `pathApp (pathLam value.weaken) interval ⟶
value`.  The reduct is `valueTarget` at the bare `carrierType`, cast-free.  The
source obstruction mirrors `transpReflBeta`: the renamed pathLam body
`weakenComm ▸ rename(lift)(weaken value)` differs from the constructor's
`weaken (rename value)` heterogeneously, reconciled by `Term.rename_weaken_commute`
(term-level) + `type_eq_cast_heq`; bridged into the `Step.par` by
`castSourceTermHeq` + `pathReflApp_body_heqCongr`, with the raw index aligned by
`RawTerm.weaken_rename_commute`.  Zero-axiom. -/
theorem rename_compatible_typed_betaPathReflApp
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty level sourceScope)
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {valueRawSource valueRawTarget intervalRawSource intervalRawTarget : RawTerm sourceScope}
    {valueSource : Term sourceCtx carrierType valueRawSource}
    {valueTarget : Term sourceCtx carrierType valueRawTarget}
    {intervalSource : Term sourceCtx Ty.interval intervalRawSource}
    {intervalTarget : Term sourceCtx Ty.interval intervalRawTarget}
    (valueStep :
      Step.par (Term.rename termRenaming valueSource)
               (Term.rename termRenaming valueTarget))
    (intervalStep :
      Step.par (Term.rename termRenaming intervalSource)
               (Term.rename termRenaming intervalTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.pathApp modeIsUnivalent
          (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
            (Term.weaken Ty.interval valueSource))
          intervalSource))
      (Term.rename termRenaming valueTarget) := by
  dsimp only [Term.rename]
  have weakenComm := Ty.weaken_rename_commute rho carrierType
  refine Step.par.castSourceTermHeq ?rawEq ?heq
    (Step.par.betaPathReflApp modeIsUnivalent (carrierType.rename rho)
      (leftEndpoint.rename rho) (rightEndpoint.rename rho) valueStep intervalStep)
  · exact congrArg
      (fun bodyRaw =>
        RawTerm.pathApp (RawTerm.pathLam bodyRaw) (intervalRawSource.rename rho))
      (RawTerm.weaken_rename_commute rho valueRawSource).symm
  · exact pathReflApp_body_heqCongr modeIsUnivalent (carrierType.rename rho)
      (leftEndpoint.rename rho) (rightEndpoint.rename rho)
      (RawTerm.weaken_rename_commute rho valueRawSource).symm
      (HEq.trans
        (Term.rename_weaken_commute termRenaming Ty.interval valueSource).symm
        (Term.type_eq_cast_heq weakenComm
          (Term.rename (termRenaming.lift Ty.interval)
            (Term.weaken Ty.interval valueSource))).symm)
      (Term.rename termRenaming intervalSource)

/-- HEq congruence for `Term.appPi` over a function that differs only by a
codomain type-index transport: when the two functions share a raw index and are
`HEq` (their `Ty.piTy` codomains being propositionally equal), the two applications
are `HEq`.  `subst` the codomain equality (making the two Π types defeq) then `cases`
the now-homogeneous function `HEq`.  Consumed by the `betaFunextReflApp` source
bridge, where the renamed `funextRefl` carries a `funextReflType_rename` cast on its
Π codomain.  Zero-axiom. -/
theorem appPi_function_heqCongr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (domainType : Ty level scope) {codomainA codomainB : Ty level (scope + 1)}
    (codomainEq : codomainA = codomainB)
    {functionRaw : RawTerm scope}
    {functionA : Term context (Ty.piTy domainType codomainA) functionRaw}
    {functionB : Term context (Ty.piTy domainType codomainB) functionRaw}
    (functionHeq : HEq functionA functionB)
    {argumentRaw : RawTerm scope} (argumentTerm : Term context domainType argumentRaw) :
    HEq (Term.appPi functionA argumentTerm) (Term.appPi functionB argumentTerm) := by
  cases codomainEq
  cases functionHeq
  rfl

/-- HEq congruence for `Term.refl` over its carrier type and raw witness: equal
carriers and equal witnesses give `HEq`-equal `refl`s.  Bridges the `betaFunextReflApp`
reduct, whose `Term.refl` carrier (`codomainType.weaken.subst0 …`) and witness
(`applyRawTarget.subst0 …`) each pick up a `*_rename_commute` transport under renaming.
Zero-axiom. -/
theorem refl_heqCongr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope} {witnessA witnessB : RawTerm scope}
    (carrierEq : carrierA = carrierB) (witnessEq : witnessA = witnessB) :
    HEq (Term.refl (context := context) carrierA witnessA)
        (Term.refl (context := context) carrierB witnessB) := by
  cases carrierEq
  cases witnessEq
  rfl

/-- β arm `betaFunextReflApp` of typed-Step.par rename equivariance: applying the
canonical funext-refl witness to an argument, `appPi (funextRefl A B applyRaw) arg ⟶
refl (B.weaken.subst0 A arg)(applyRaw.subst0 arg)`.  The hardest arm in the file: the
renamed source nests two type casts (the `appPi`-result `subst0_rename_commute` cast
and the `funextRefl` `funextReflType_rename` codomain cast), and the `Term.refl` reduct
needs both a carrier type-index transport (`subst0`+`weaken` distribution) and a
`RawTerm.refl` witness raw-index transport (`RawTerm.subst0_rename_commute`).  The raw
`applyRaw` premise lifts via `RawStep.par.rename`.  Source/target are bridged separately
by `castSourceType`+`castSourceTermHeq` / `castTargetType`+`castTargetTermHeq`, with the
HEqs supplied by `appPi_function_heqCongr` / `refl_heqCongr`.  Zero-axiom. -/
theorem rename_compatible_typed_betaFunextReflApp
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (domainType codomainType : Ty level sourceScope)
    {applyRawSource applyRawTarget : RawTerm (sourceScope + 1)}
    {argumentRawSource argumentRawTarget : RawTerm sourceScope}
    {argumentSource : Term sourceCtx domainType argumentRawSource}
    {argumentTarget : Term sourceCtx domainType argumentRawTarget}
    (rawStep : RawStep.par applyRawSource applyRawTarget)
    (argStep :
      Step.par (Term.rename termRenaming argumentSource)
               (Term.rename termRenaming argumentTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.appPi (Term.funextRefl domainType codomainType applyRawSource)
                    argumentSource))
      (Term.rename termRenaming
        (Term.refl (codomainType.weaken.subst0 domainType argumentRawTarget)
                   (applyRawTarget.subst0 argumentRawTarget))) := by
  dsimp only [Term.rename]
  -- Reduct (target) bridges: witness raw + carrier type, both via `subst0`/`weaken`
  -- rename-commute.
  have witnessEqTgt :
      (applyRawTarget.rename rho.lift).subst0 (argumentRawTarget.rename rho)
        = (applyRawTarget.subst0 argumentRawTarget).rename rho :=
    (RawTerm.subst0_rename_commute applyRawTarget argumentRawTarget rho).symm
  have carrierEqTgt :
      (codomainType.rename rho).weaken.subst0 (domainType.rename rho) (argumentRawTarget.rename rho)
        = (codomainType.weaken.subst0 domainType argumentRawTarget).rename rho :=
    ((Ty.subst0_rename_commute codomainType.weaken domainType argumentRawTarget rho).trans
      (congrArg (fun w => Ty.subst0 w (domainType.rename rho) (argumentRawTarget.rename rho))
        (Ty.weaken_rename_commute rho codomainType))).symm
  have tgtTyEq :
      Ty.id ((codomainType.rename rho).weaken.subst0 (domainType.rename rho) (argumentRawTarget.rename rho))
          ((applyRawTarget.rename rho.lift).subst0 (argumentRawTarget.rename rho))
          ((applyRawTarget.rename rho.lift).subst0 (argumentRawTarget.rename rho))
        = (Ty.id (codomainType.weaken.subst0 domainType argumentRawTarget)
            (applyRawTarget.subst0 argumentRawTarget)
            (applyRawTarget.subst0 argumentRawTarget)).rename rho := by
    rw [carrierEqTgt, witnessEqTgt]; rfl
  -- Source type bridge: the `appPi`-result `subst0` of the renamed funext-refl Π
  -- codomain equals the renamed original result type.
  have srcTyEq :
      Ty.subst0 (Ty.id (codomainType.rename rho).weaken (applyRawSource.rename rho.lift)
            (applyRawSource.rename rho.lift))
          (domainType.rename rho) (argumentRawSource.rename rho)
        = (Ty.subst0 (Ty.id codomainType.weaken applyRawSource applyRawSource)
            domainType argumentRawSource).rename rho :=
    ((Ty.subst0_rename_commute (Ty.id codomainType.weaken applyRawSource applyRawSource)
        domainType argumentRawSource rho).trans
      (congrArg (fun w => Ty.subst0 (Ty.id w (applyRawSource.rename rho.lift)
          (applyRawSource.rename rho.lift)) (domainType.rename rho) (argumentRawSource.rename rho))
        (Ty.weaken_rename_commute rho codomainType))).symm
  -- Source funext-refl codomain bridge (for the `appPi` function HEq).
  have codomainEqSrc :
      Ty.id (codomainType.rename rho).weaken (applyRawSource.rename rho.lift)
          (applyRawSource.rename rho.lift)
        = (Ty.id codomainType.weaken applyRawSource applyRawSource).rename rho.lift :=
    congrArg (fun w => Ty.id w (applyRawSource.rename rho.lift) (applyRawSource.rename rho.lift))
      (Ty.weaken_rename_commute rho codomainType).symm
  refine Step.par.castSourceTermHeq rfl ?srcHeq
    (Step.par.castSourceType srcTyEq
      (Step.par.castTargetTermHeq (congrArg RawTerm.refl witnessEqTgt) ?tgtHeq
        (Step.par.castTargetType tgtTyEq
          (Step.par.betaFunextReflApp (domainType.rename rho) (codomainType.rename rho)
            (RawStep.par.rename rho.lift rawStep) argStep))))
  case tgtHeq =>
    exact HEq.trans (Term.type_eq_cast_heq tgtTyEq _) (refl_heqCongr carrierEqTgt witnessEqTgt)
  case srcHeq =>
    exact HEq.trans (Term.type_eq_cast_heq srcTyEq _)
      (HEq.trans
        (appPi_function_heqCongr (domainType.rename rho) codomainEqSrc
          (Term.type_eq_cast_heq
            (funextReflType_rename rho domainType codomainType applyRawSource).symm
            (Term.funextRefl (domainType.rename rho) (codomainType.rename rho)
              (applyRawSource.rename rho.lift))).symm
          (Term.rename termRenaming argumentSource))
        (Term.type_eq_cast_heq
          (Ty.subst0_rename_commute (Ty.id codomainType.weaken applyRawSource applyRawSource)
            domainType argumentRawSource rho).symm _).symm)

/-- Deep β arm `betaFunextReflAppDeep` of typed-Step.par rename equivariance: the
function position of the application reduces in parallel to a funext-refl witness
(`Step.par functionTermSource (funextRefl A B applyRaw)`), and `appPi functionTermSource
arg ⟶ refl (B.weaken.subst0 A arg)(applyRaw.subst0 arg)`.

Simpler than the shallow arm on the SOURCE side — the application's function is a
general `functionTermSource`, not a literal `funextRefl`, so the renamed source carries
only the outer `appPi`-result `subst0_rename_commute` cast (no inner `funextReflType_rename`
cast), and `castSourceType` alone discharges it (proof-irrelevance absorbs which cast
proof).  The function-step premise's `funextRefl` target picks up the
`funextReflType_rename` cast under renaming, peeled by `castTargetType_cancel`.  The
reduct bridges (`tgtTyEq` / `tgtRaw` / `tgtHeq`) are identical to the shallow arm.
Zero-axiom. -/
theorem rename_compatible_typed_betaFunextReflAppDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType codomainType : Ty level sourceScope}
    {applyRawTarget : RawTerm (sourceScope + 1)}
    {argumentRawSource argumentRawTarget : RawTerm sourceScope}
    {functionRawSourceOuter : RawTerm sourceScope}
    {functionTermSource :
      Term sourceCtx (funextReflType domainType codomainType applyRawTarget)
        functionRawSourceOuter}
    {argumentSource : Term sourceCtx domainType argumentRawSource}
    {argumentTarget : Term sourceCtx domainType argumentRawTarget}
    (functionStep :
      Step.par (Term.rename termRenaming functionTermSource)
               (Term.rename termRenaming
                 (Term.funextRefl (context := sourceCtx)
                   domainType codomainType applyRawTarget)))
    (argStep :
      Step.par (Term.rename termRenaming argumentSource)
               (Term.rename termRenaming argumentTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.appPi functionTermSource argumentSource))
      (Term.rename termRenaming
        (Term.refl (codomainType.weaken.subst0 domainType argumentRawTarget)
                   (applyRawTarget.subst0 argumentRawTarget))) := by
  dsimp only [Term.rename] at functionStep ⊢
  have witnessEqTgt :
      (applyRawTarget.rename rho.lift).subst0 (argumentRawTarget.rename rho)
        = (applyRawTarget.subst0 argumentRawTarget).rename rho :=
    (RawTerm.subst0_rename_commute applyRawTarget argumentRawTarget rho).symm
  have carrierEqTgt :
      (codomainType.rename rho).weaken.subst0 (domainType.rename rho) (argumentRawTarget.rename rho)
        = (codomainType.weaken.subst0 domainType argumentRawTarget).rename rho :=
    ((Ty.subst0_rename_commute codomainType.weaken domainType argumentRawTarget rho).trans
      (congrArg (fun w => Ty.subst0 w (domainType.rename rho) (argumentRawTarget.rename rho))
        (Ty.weaken_rename_commute rho codomainType))).symm
  have tgtTyEq :
      Ty.id ((codomainType.rename rho).weaken.subst0 (domainType.rename rho) (argumentRawTarget.rename rho))
          ((applyRawTarget.rename rho.lift).subst0 (argumentRawTarget.rename rho))
          ((applyRawTarget.rename rho.lift).subst0 (argumentRawTarget.rename rho))
        = (Ty.id (codomainType.weaken.subst0 domainType argumentRawTarget)
            (applyRawTarget.subst0 argumentRawTarget)
            (applyRawTarget.subst0 argumentRawTarget)).rename rho := by
    rw [carrierEqTgt, witnessEqTgt]; rfl
  have srcTyEq :
      Ty.subst0 (Ty.id (codomainType.rename rho).weaken (applyRawTarget.rename rho.lift)
            (applyRawTarget.rename rho.lift))
          (domainType.rename rho) (argumentRawSource.rename rho)
        = (Ty.subst0 (Ty.id codomainType.weaken applyRawTarget applyRawTarget)
            domainType argumentRawSource).rename rho :=
    ((Ty.subst0_rename_commute (Ty.id codomainType.weaken applyRawTarget applyRawTarget)
        domainType argumentRawSource rho).trans
      (congrArg (fun w => Ty.subst0 (Ty.id w (applyRawTarget.rename rho.lift)
          (applyRawTarget.rename rho.lift)) (domainType.rename rho) (argumentRawSource.rename rho))
        (Ty.weaken_rename_commute rho codomainType))).symm
  -- Source function codomain bridge (for the `appPi` function HEq): the renamed
  -- function lives at the bare-renamed `funextReflType`, the goal's `appPi` sees it
  -- through the `Ty.piTy`/`Ty.id` rename arms — the two codomains agree by
  -- `weaken_rename_commute`.
  have codomainEqSrc :
      Ty.id (codomainType.rename rho).weaken (applyRawTarget.rename rho.lift)
          (applyRawTarget.rename rho.lift)
        = (Ty.id codomainType.weaken applyRawTarget applyRawTarget).rename rho.lift :=
    congrArg (fun w => Ty.id w (applyRawTarget.rename rho.lift) (applyRawTarget.rename rho.lift))
      (Ty.weaken_rename_commute rho codomainType).symm
  refine Step.par.castSourceTermHeq rfl ?srcHeq
    (Step.par.castSourceType srcTyEq
      (Step.par.castTargetTermHeq (congrArg RawTerm.refl witnessEqTgt) ?tgtHeq
        (Step.par.castTargetType tgtTyEq
          (Step.par.betaFunextReflAppDeep
            (Step.par.castTargetTypeHeq
              (funextReflType_rename rho domainType codomainType applyRawTarget)
              (Term.type_eq_cast_heq
                (funextReflType_rename rho domainType codomainType applyRawTarget).symm
                (Term.funextRefl (context := targetCtx) (domainType.rename rho)
                  (codomainType.rename rho) (applyRawTarget.rename rho.lift))).symm
              (Step.par.castSourceType
                (funextReflType_rename rho domainType codomainType applyRawTarget)
                functionStep))
            argStep))))
  case tgtHeq =>
    exact HEq.trans (Term.type_eq_cast_heq tgtTyEq _) (refl_heqCongr carrierEqTgt witnessEqTgt)
  case srcHeq =>
    exact HEq.trans (Term.type_eq_cast_heq srcTyEq _)
      (HEq.trans
        (appPi_function_heqCongr (domainType.rename rho) codomainEqSrc
          (Term.type_eq_cast_heq
            (funextReflType_rename rho domainType codomainType applyRawTarget)
            (Term.rename termRenaming functionTermSource))
          (Term.rename termRenaming argumentSource))
        (Term.type_eq_cast_heq
          (Ty.subst0_rename_commute (Ty.id codomainType.weaken applyRawTarget applyRawTarget)
            domainType argumentRawSource rho).symm _).symm)

/-- β arm `betaSndPair` of typed-Step.par rename equivariance: shallow Σ-snd
projection `snd (pair a b) ⟶ b'` with `Step.par b b'`.

Unlike `betaFstPair` (whose reduct lives at the bare `firstType`), the `snd` reduct
lives at `secondType.subst0 firstType (RawTerm.fst pairRaw)`, and the `snd` rename
arm carries a `Ty.subst0_rename_commute` cast on the projection witness
`RawTerm.fst (RawTerm.pair firstRaw secondRawSource)`.  This is the type index where
gap #1950 (`RawTerm.fst (RawTerm.pair x y)` does not β-reduce to `x` definitionally)
would bite — but it bites only the *substitution* direction.  For *renaming*, the
un-reduced projection appears identically on both the goal source (via the `snd`
arm's cast) and the constructor source (the `snd`-of-`pair` type formula), so it
cancels; only the `subst0`-distribution transport on the reduct remains.  The
renamed argument is presented to the constructor pre-cast (both endpoints lifted to
the distributed type), and the residual output cast is peeled by
`castTargetType_cancel`.  Zero-axiom. -/
theorem rename_compatible_typed_betaSndPair
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {firstType : Ty level sourceScope} {secondType : Ty level (sourceScope + 1)}
    {firstRaw : RawTerm sourceScope}
    {secondRawSource secondRawTarget : RawTerm sourceScope}
    (firstValue : Term sourceCtx firstType firstRaw)
    {secondValueSource :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRawSource}
    {secondValueTarget :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRawTarget}
    (secondStep :
      Step.par (Term.rename termRenaming secondValueSource)
               (Term.rename termRenaming secondValueTarget)) :
    Step.par
      (Term.rename termRenaming
        (Term.snd (Term.pair (secondType := secondType)
          firstValue secondValueSource)))
      (Term.rename termRenaming secondValueTarget) := by
  dsimp only [Term.rename]
  exact Step.par.castSourceType
    (Ty.subst0_rename_commute secondType firstType
      (RawTerm.fst (RawTerm.pair firstRaw secondRawSource)) rho).symm
    (Step.par.castTargetType_cancel
      (Ty.subst0_rename_commute secondType firstType firstRaw rho)
      (Term.rename termRenaming secondValueTarget)
      (Step.par.betaSndPair (Term.rename termRenaming firstValue)
        (Step.par.castTargetType
          (Ty.subst0_rename_commute secondType firstType firstRaw rho)
          (Step.par.castSourceType
            (Ty.subst0_rename_commute secondType firstType firstRaw rho)
            secondStep))))

/-- Deep β arm `betaSndPairDeep` of typed-Step.par rename equivariance: the scrutinee
of `snd` reduces in parallel to a pair (`Step.par pairSource (pair a b)`), and
`snd pairSource ⟶ b`.  The renamed premise's pair-shaped target already carries the
`subst0`-distribution cast on its second component (from the `pair` rename arm), so it
feeds the constructor directly; only the `snd` source cast (`castSourceType`) and the
reduct's `subst0`-distribution transport (`castTargetType_cancel`) wrap the result —
the same gap-#1950-cancels-under-rename mechanism as the shallow arm.  Zero-axiom. -/
theorem rename_compatible_typed_betaSndPairDeep
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {firstType : Ty level sourceScope} {secondType : Ty level (sourceScope + 1)}
    {pairRawSource firstRawTarget secondRawTarget : RawTerm sourceScope}
    {pairTermSource :
      Term sourceCtx (Ty.sigmaTy firstType secondType) pairRawSource}
    {firstValueTarget : Term sourceCtx firstType firstRawTarget}
    {secondValueTarget :
      Term sourceCtx (secondType.subst0 firstType firstRawTarget) secondRawTarget}
    (pairStep :
      Step.par (Term.rename termRenaming pairTermSource)
               (Term.rename termRenaming
                 (Term.pair (secondType := secondType)
                   firstValueTarget secondValueTarget))) :
    Step.par
      (Term.rename termRenaming
        (Term.snd (secondType := secondType) pairTermSource))
      (Term.rename termRenaming secondValueTarget) := by
  dsimp only [Term.rename] at pairStep ⊢
  exact Step.par.castSourceType
    (Ty.subst0_rename_commute secondType firstType (RawTerm.fst pairRawSource) rho).symm
    (Step.par.castTargetType_cancel
      (Ty.subst0_rename_commute secondType firstType firstRawTarget rho)
      (Term.rename termRenaming secondValueTarget)
      (Step.par.betaSndPairDeep pairStep))

/-- Typed parallel reduction is compatible with renaming (forward direction,
#2027 unblock-C.t6.stepCompat): renaming both endpoints of a `Step.par`
derivation yields a `Step.par` between the rename-images.  The universal
headline composing the 133 per-constructor arms `rename_compatible_typed_<ctor>`
by induction on the derivation.  Each induction case carries its sub-derivation
induction hypotheses already in renamed form (`Step.par (rename sub) (rename
sub')`), exactly matching the corresponding arm's premise shape, so the case is
discharged by applying that arm and filling its renamed-sub-step / raw-step
premises from the case context.  The `first | …` block dispatches on the
constructor: only the matching arm's `apply` unifies (head-constructor agreement
in the conclusion), `assumption` then closes the residual induction-hypothesis
goals.  Zero-axiom — every arm is, and the dispatch adds only `apply`/`assumption`.
This is the typed counterpart to `RawStep.par.rename_compatible`. -/
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
    (parallelStep : Step.par beforeTerm afterTerm) :
    Step.par (Term.rename termRenaming beforeTerm)
             (Term.rename termRenaming afterTerm) := by
  induction parallelStep generalizing targetScope targetCtx <;>
    first
      | (apply rename_compatible_typed_app termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_appPi termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_arrowCodeCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaApp termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaAppDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaAppPi termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaAppPiDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaCodataDestUnfold termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaCodataDestUnfoldDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaFstPair termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaFstPairDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaFunextReflApp termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaFunextReflAppDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaGlueElimIntro termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaGlueElimIntroDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaModElimIntro termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaModElimIntroDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaPathApp termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaPathAppDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaPathReflApp termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaRecordProjIntro termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaRecordProjIntroDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaRefineElimIntro termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaRefineElimIntroDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaSndPair termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_betaSndPairDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_boolElim termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_codataDestCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_codataUnfoldCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_cumulUpInnerCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_effectPerformCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_eitherCodeCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_eitherInl termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_eitherInr termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_eitherMatch termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_eqArrow termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_eqArrowHet termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_eqType termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_eqTypeHet termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_equivAppCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_equivApplyCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_equivCodeCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_equivIntroCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_equivIntroHetCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_fst termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_funextIntroHetCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_funextReflAtIdCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_funextReflCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_glueElim termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_glueElimCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_glueIntro termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_glueIntroCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_hcomp termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_hcompBeta termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_hcompBetaDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_hcompCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_hcompPathCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_idCodeCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_idJ termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_idStrictRecCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_idStrictReflCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_intervalJoinCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_intervalMeetCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_intervalOppCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaBoolElimFalse termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaBoolElimFalseDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaBoolElimTrue termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaBoolElimTrueDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaEitherMatchInl termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaEitherMatchInlDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaEitherMatchInr termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaEitherMatchInrDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaIdJRefl termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaIdJReflDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaIdStrictRecRefl termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaIdStrictRecReflDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaListElimCons termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaListElimConsDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaListElimNil termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaListElimNilDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaNatElimSucc termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaNatElimSuccDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaNatElimZero termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaNatElimZeroDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaNatRecSucc termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaNatRecSuccDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaNatRecZero termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaNatRecZeroDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaOptionMatchNone termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaOptionMatchNoneDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaOptionMatchSome termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_iotaOptionMatchSomeDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_lam termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_lamPi termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_listCodeCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_listCons termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_listElim termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_modElim termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_modIntro termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_natElim termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_natRec termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_natSucc termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_oeqFunextCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_oeqJCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_oeqReflCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_optionCodeCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_optionMatch termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_optionSome termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_pair termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_pathApp termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_pathAppCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_pathLam termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_pathLamCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_piTyCodeCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_productCodeCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_recordIntroCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_recordProjCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_refineElimCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_refineIntroCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_refl termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_reflCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_sessionRecvCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_sessionSendCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_sigmaTyCodeCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_snd termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_subsume termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_sumCodeCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_transp termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_transpCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_transpReflBeta termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_transpReflBetaDeep termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_uaIntroHetCong termRenaming <;> apply_assumption)
      | (apply rename_compatible_typed_uaToEquivCong termRenaming <;> apply_assumption)

end Step.par

end LeanFX2

-/
