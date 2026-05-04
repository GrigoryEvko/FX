import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.Action

/-! # RawSubst — Layer 0 raw substitution algebra.

Function-typed rawRenaming and substitution per
`feedback_lean_function_typed_subst.md`.  Defining these as functions
(not inductives) lets `lift` propagate scope through structural
recursion without invoking Nat-arithmetic identities (which would
force `Eq.mpr` + propext).

## Operations provided

* `RawRenaming source target := Fin source → Fin target`
* `RawRenaming.identity / .lift / .weaken`
* `RawTerm.rename : RawTerm source → RawRenaming source target → RawTerm target`
* `RawTermSubst source target := Fin source → RawTerm target`
* `RawTermSubst.identity / .lift / .singleton`
* `RawTerm.subst : RawTerm source → RawTermSubst source target → RawTerm target`
* `RawTerm.subst0` — single-binder substitution (uses `singleton`)

## NO `dropNewest`

Per lean-fx-2's architectural commitment (`CLAUDE.md`), there is no
`RawTermSubst.dropNewest` placeholder.  Single-binder substitution
always uses `RawTermSubst.singleton rawArg` carrying the actual raw
argument at position 0.

## All operations marked @[reducible]

Per `feedback_lean_reducible_weaken.md`, structural-recursion
functions used in inductive constructor signatures (downstream Term's
ctors will reference these) MUST be `@[reducible]`.  Otherwise
Lean's unifier fails to elaborate constructor applications whose
types involve them.
-/

namespace LeanFX2

/-! ## Renamings -/

/-- A raw rawRenaming: `Fin source → Fin target`. -/
@[reducible] def RawRenaming (source target : Nat) : Type := Fin source → Fin target

/-- Identity rawRenaming. -/
@[reducible] def RawRenaming.identity {scope : Nat} : RawRenaming scope scope :=
  fun position => position

/-- Lift rawRenaming under a binder: position 0 stays, others shift. -/
@[reducible] def RawRenaming.lift {source target : Nat}
    (rawRenaming : RawRenaming source target) : RawRenaming (source + 1) (target + 1)
  | ⟨0, _⟩      => ⟨0, Nat.zero_lt_succ _⟩
  | ⟨k + 1, h⟩  => Fin.succ (rawRenaming ⟨k, Nat.lt_of_succ_lt_succ h⟩)

/-- Weakening rawRenaming: shift all positions by 1. -/
@[reducible] def RawRenaming.weaken {scope : Nat} : RawRenaming scope (scope + 1) :=
  fun position => Fin.succ position

/-- Compose two rawRenamings. -/
@[reducible] def RawRenaming.compose {scopeA scopeB scopeC : Nat}
    (firstRenaming : RawRenaming scopeA scopeB)
    (secondRenaming : RawRenaming scopeB scopeC) :
    RawRenaming scopeA scopeC :=
  fun position => secondRenaming (firstRenaming position)

/-- Apply a rawRenaming to a raw term. -/
def RawTerm.rename : ∀ {source target : Nat},
    RawTerm source → RawRenaming source target → RawTerm target
  | _, _, .var position, rawRenaming => .var (rawRenaming position)
  | _, _, .unit, _ => .unit
  | _, _, .lam body, rawRenaming => .lam (body.rename rawRenaming.lift)
  | _, _, .app functionTerm argumentTerm, rawRenaming =>
      .app (functionTerm.rename rawRenaming) (argumentTerm.rename rawRenaming)
  | _, _, .pair firstValue secondValue, rawRenaming =>
      .pair (firstValue.rename rawRenaming) (secondValue.rename rawRenaming)
  | _, _, .fst pairTerm, rawRenaming => .fst (pairTerm.rename rawRenaming)
  | _, _, .snd pairTerm, rawRenaming => .snd (pairTerm.rename rawRenaming)
  | _, _, .boolTrue, _ => .boolTrue
  | _, _, .boolFalse, _ => .boolFalse
  | _, _, .boolElim scrutinee thenBranch elseBranch, rawRenaming =>
      .boolElim (scrutinee.rename rawRenaming)
                (thenBranch.rename rawRenaming)
                (elseBranch.rename rawRenaming)
  | _, _, .natZero, _ => .natZero
  | _, _, .natSucc predecessor, rawRenaming => .natSucc (predecessor.rename rawRenaming)
  | _, _, .natElim scrutinee zeroBranch succBranch, rawRenaming =>
      .natElim (scrutinee.rename rawRenaming)
               (zeroBranch.rename rawRenaming)
               (succBranch.rename rawRenaming)
  | _, _, .natRec scrutinee zeroBranch succBranch, rawRenaming =>
      .natRec (scrutinee.rename rawRenaming)
              (zeroBranch.rename rawRenaming)
              (succBranch.rename rawRenaming)
  | _, _, .listNil, _ => .listNil
  | _, _, .listCons headTerm tailTerm, rawRenaming =>
      .listCons (headTerm.rename rawRenaming) (tailTerm.rename rawRenaming)
  | _, _, .listElim scrutinee nilBranch consBranch, rawRenaming =>
      .listElim (scrutinee.rename rawRenaming)
                (nilBranch.rename rawRenaming)
                (consBranch.rename rawRenaming)
  | _, _, .optionNone, _ => .optionNone
  | _, _, .optionSome valueTerm, rawRenaming => .optionSome (valueTerm.rename rawRenaming)
  | _, _, .optionMatch scrutinee noneBranch someBranch, rawRenaming =>
      .optionMatch (scrutinee.rename rawRenaming)
                   (noneBranch.rename rawRenaming)
                   (someBranch.rename rawRenaming)
  | _, _, .eitherInl valueTerm, rawRenaming => .eitherInl (valueTerm.rename rawRenaming)
  | _, _, .eitherInr valueTerm, rawRenaming => .eitherInr (valueTerm.rename rawRenaming)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch, rawRenaming =>
      .eitherMatch (scrutinee.rename rawRenaming)
                   (leftBranch.rename rawRenaming)
                   (rightBranch.rename rawRenaming)
  | _, _, .refl rawWitness, rawRenaming => .refl (rawWitness.rename rawRenaming)
  | _, _, .idJ baseCase witness, rawRenaming =>
      .idJ (baseCase.rename rawRenaming) (witness.rename rawRenaming)
  | _, _, .modIntro inner, rawRenaming => .modIntro (inner.rename rawRenaming)
  | _, _, .modElim inner, rawRenaming => .modElim (inner.rename rawRenaming)
  | _, _, .subsume inner, rawRenaming => .subsume (inner.rename rawRenaming)
  -- D1.6 cubical interval + path
  | _, _, .interval0, _ => .interval0
  | _, _, .interval1, _ => .interval1
  | _, _, .intervalOpp i, rawRenaming => .intervalOpp (i.rename rawRenaming)
  | _, _, .intervalMeet l r, rawRenaming =>
      .intervalMeet (l.rename rawRenaming) (r.rename rawRenaming)
  | _, _, .intervalJoin l r, rawRenaming =>
      .intervalJoin (l.rename rawRenaming) (r.rename rawRenaming)
  | _, _, .pathLam body, rawRenaming =>
      .pathLam (body.rename rawRenaming.lift)
  | _, _, .pathApp pathTerm intervalArg, rawRenaming =>
      .pathApp (pathTerm.rename rawRenaming) (intervalArg.rename rawRenaming)
  | _, _, .glueIntro baseValue partialValue, rawRenaming =>
      .glueIntro (baseValue.rename rawRenaming) (partialValue.rename rawRenaming)
  | _, _, .glueElim gluedValue, rawRenaming =>
      .glueElim (gluedValue.rename rawRenaming)
  | _, _, .transp path source, rawRenaming =>
      .transp (path.rename rawRenaming) (source.rename rawRenaming)
  | _, _, .hcomp sides cap, rawRenaming =>
      .hcomp (sides.rename rawRenaming) (cap.rename rawRenaming)
  -- D1.6 observational + strict equality
  | _, _, .oeqRefl witness, rawRenaming => .oeqRefl (witness.rename rawRenaming)
  | _, _, .oeqJ baseCase witness, rawRenaming =>
      .oeqJ (baseCase.rename rawRenaming) (witness.rename rawRenaming)
  | _, _, .oeqFunext pointwiseEquality, rawRenaming =>
      .oeqFunext (pointwiseEquality.rename rawRenaming)
  | _, _, .idStrictRefl witness, rawRenaming =>
      .idStrictRefl (witness.rename rawRenaming)
  | _, _, .idStrictRec baseCase witness, rawRenaming =>
      .idStrictRec (baseCase.rename rawRenaming) (witness.rename rawRenaming)
  -- D1.6 type equivalence
  | _, _, .equivIntro fwd bwd, rawRenaming =>
      .equivIntro (fwd.rename rawRenaming) (bwd.rename rawRenaming)
  | _, _, .equivApp equivTerm argument, rawRenaming =>
      .equivApp (equivTerm.rename rawRenaming) (argument.rename rawRenaming)
  -- D1.6 refinement, record, codata
  | _, _, .refineIntro rawValue predicateProof, rawRenaming =>
      .refineIntro (rawValue.rename rawRenaming)
                   (predicateProof.rename rawRenaming)
  | _, _, .refineElim refinedValue, rawRenaming =>
      .refineElim (refinedValue.rename rawRenaming)
  | _, _, .recordIntro firstField, rawRenaming =>
      .recordIntro (firstField.rename rawRenaming)
  | _, _, .recordProj recordValue, rawRenaming =>
      .recordProj (recordValue.rename rawRenaming)
  | _, _, .codataUnfold initialState transition, rawRenaming =>
      .codataUnfold (initialState.rename rawRenaming)
                    (transition.rename rawRenaming)
  | _, _, .codataDest codataValue, rawRenaming =>
      .codataDest (codataValue.rename rawRenaming)
  -- D1.6 sessions, effects
  | _, _, .sessionSend channel payload, rawRenaming =>
      .sessionSend (channel.rename rawRenaming) (payload.rename rawRenaming)
  | _, _, .sessionRecv channel, rawRenaming =>
      .sessionRecv (channel.rename rawRenaming)
  | _, _, .effectPerform operationTag arguments, rawRenaming =>
      .effectPerform (operationTag.rename rawRenaming)
                     (arguments.rename rawRenaming)
  -- D1.6/A2: universeCode is scope-polymorphic — rename is identity
  -- on the inner-level payload (no Fin variables to remap).
  | _, _, .universeCode innerLevel, _ =>
      .universeCode innerLevel

/-- Single-binder weakening on a raw term. -/
@[reducible] def RawTerm.weaken {scope : Nat} (term : RawTerm scope) : RawTerm (scope + 1) :=
  term.rename RawRenaming.weaken

/-! ## Pointwise + composition lemmas for raw renaming.

These are needed to prove the `weaken/lift` commute laws that
downstream Term.rename / Ty.subst use.  Proofs use `induction` tactic
(propext-free per `feedback_lean_zero_axiom_match.md` Rule 6) and
chain rewrites via `rw`. -/

/-- Lift respects pointwise equality. -/
theorem RawRenaming.lift_pointwise {sourceScope targetScope : Nat}
    {rho1 rho2 : RawRenaming sourceScope targetScope}
    (renamingEq : ∀ position, rho1 position = rho2 position) :
    ∀ position, rho1.lift position = rho2.lift position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      simp only [RawRenaming.lift]
      exact congrArg Fin.succ (renamingEq ⟨k, Nat.lt_of_succ_lt_succ h⟩)

/-- RawTerm.rename respects pointwise renaming equality. -/
theorem RawTerm.rename_pointwise {sourceScope targetScope : Nat}
    {rho1 rho2 : RawRenaming sourceScope targetScope}
    (renamingEq : ∀ position, rho1 position = rho2 position) :
    ∀ (term : RawTerm sourceScope), term.rename rho1 = term.rename rho2 := by
  intro term
  induction term generalizing targetScope with
  | var position =>
      simp only [RawTerm.rename]; rw [renamingEq position]
  | unit => rfl
  | lam body bodyIH =>
      simp only [RawTerm.rename]; rw [bodyIH (RawRenaming.lift_pointwise renamingEq)]
  | app fn arg fnIH argIH =>
      simp only [RawTerm.rename]; rw [fnIH renamingEq, argIH renamingEq]
  | pair fv sv fvIH svIH =>
      simp only [RawTerm.rename]; rw [fvIH renamingEq, svIH renamingEq]
  | fst pairTerm pairIH =>
      simp only [RawTerm.rename]; rw [pairIH renamingEq]
  | snd pairTerm pairIH =>
      simp only [RawTerm.rename]; rw [pairIH renamingEq]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim s t e sIH tIH eIH =>
      simp only [RawTerm.rename]; rw [sIH renamingEq, tIH renamingEq, eIH renamingEq]
  | natZero => rfl
  | natSucc p pIH =>
      simp only [RawTerm.rename]; rw [pIH renamingEq]
  | natElim s z c sIH zIH cIH =>
      simp only [RawTerm.rename]; rw [sIH renamingEq, zIH renamingEq, cIH renamingEq]
  | natRec s z c sIH zIH cIH =>
      simp only [RawTerm.rename]; rw [sIH renamingEq, zIH renamingEq, cIH renamingEq]
  | listNil => rfl
  | listCons h t hIH tIH =>
      simp only [RawTerm.rename]; rw [hIH renamingEq, tIH renamingEq]
  | listElim s n c sIH nIH cIH =>
      simp only [RawTerm.rename]; rw [sIH renamingEq, nIH renamingEq, cIH renamingEq]
  | optionNone => rfl
  | optionSome v vIH =>
      simp only [RawTerm.rename]; rw [vIH renamingEq]
  | optionMatch s n c sIH nIH cIH =>
      simp only [RawTerm.rename]; rw [sIH renamingEq, nIH renamingEq, cIH renamingEq]
  | eitherInl v vIH =>
      simp only [RawTerm.rename]; rw [vIH renamingEq]
  | eitherInr v vIH =>
      simp only [RawTerm.rename]; rw [vIH renamingEq]
  | eitherMatch s l r sIH lIH rIH =>
      simp only [RawTerm.rename]; rw [sIH renamingEq, lIH renamingEq, rIH renamingEq]
  | refl witness witnessIH =>
      simp only [RawTerm.rename]; rw [witnessIH renamingEq]
  | idJ base witness baseIH witnessIH =>
      simp only [RawTerm.rename]; rw [baseIH renamingEq, witnessIH renamingEq]
  | modIntro inner innerIH =>
      simp only [RawTerm.rename]; rw [innerIH renamingEq]
  | modElim inner innerIH =>
      simp only [RawTerm.rename]; rw [innerIH renamingEq]
  | subsume inner innerIH =>
      simp only [RawTerm.rename]; rw [innerIH renamingEq]
  -- D1.6 cubical interval + path
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp i iIH =>
      simp only [RawTerm.rename]; rw [iIH renamingEq]
  | intervalMeet l r lIH rIH =>
      simp only [RawTerm.rename]; rw [lIH renamingEq, rIH renamingEq]
  | intervalJoin l r lIH rIH =>
      simp only [RawTerm.rename]; rw [lIH renamingEq, rIH renamingEq]
  | pathLam body bodyIH =>
      simp only [RawTerm.rename]
      rw [bodyIH (RawRenaming.lift_pointwise renamingEq)]
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      simp only [RawTerm.rename]; rw [pathIH renamingEq, intervalIH renamingEq]
  | glueIntro baseValue partialValue baseIH partialIH =>
      simp only [RawTerm.rename]; rw [baseIH renamingEq, partialIH renamingEq]
  | glueElim gluedValue gluedIH =>
      simp only [RawTerm.rename]; rw [gluedIH renamingEq]
  | transp path source pathIH sourceIH =>
      simp only [RawTerm.rename]; rw [pathIH renamingEq, sourceIH renamingEq]
  | hcomp sides cap sidesIH capIH =>
      simp only [RawTerm.rename]; rw [sidesIH renamingEq, capIH renamingEq]
  -- D1.6 observational + strict equality
  | oeqRefl witness witnessIH =>
      simp only [RawTerm.rename]; rw [witnessIH renamingEq]
  | oeqJ baseCase witness baseIH witnessIH =>
      simp only [RawTerm.rename]; rw [baseIH renamingEq, witnessIH renamingEq]
  | oeqFunext pointwiseEquality pointwiseIH =>
      simp only [RawTerm.rename]; rw [pointwiseIH renamingEq]
  | idStrictRefl witness witnessIH =>
      simp only [RawTerm.rename]; rw [witnessIH renamingEq]
  | idStrictRec baseCase witness baseIH witnessIH =>
      simp only [RawTerm.rename]; rw [baseIH renamingEq, witnessIH renamingEq]
  -- D1.6 type equivalence
  | equivIntro fwd bwd fwdIH bwdIH =>
      simp only [RawTerm.rename]; rw [fwdIH renamingEq, bwdIH renamingEq]
  | equivApp equivTerm argument equivIH argIH =>
      simp only [RawTerm.rename]; rw [equivIH renamingEq, argIH renamingEq]
  -- D1.6 refinement / record / codata
  | refineIntro rawValue predicateProof valueIH proofIH =>
      simp only [RawTerm.rename]; rw [valueIH renamingEq, proofIH renamingEq]
  | refineElim refinedValue refinedIH =>
      simp only [RawTerm.rename]; rw [refinedIH renamingEq]
  | recordIntro firstField firstIH =>
      simp only [RawTerm.rename]; rw [firstIH renamingEq]
  | recordProj recordValue recordIH =>
      simp only [RawTerm.rename]; rw [recordIH renamingEq]
  | codataUnfold initialState transition stateIH transIH =>
      simp only [RawTerm.rename]; rw [stateIH renamingEq, transIH renamingEq]
  | codataDest codataValue codataIH =>
      simp only [RawTerm.rename]; rw [codataIH renamingEq]
  -- D1.6 sessions, effects
  | sessionSend channel payload chIH payloadIH =>
      simp only [RawTerm.rename]; rw [chIH renamingEq, payloadIH renamingEq]
  | sessionRecv channel chIH =>
      simp only [RawTerm.rename]; rw [chIH renamingEq]
  | effectPerform operationTag arguments tagIH argsIH =>
      simp only [RawTerm.rename]; rw [tagIH renamingEq, argsIH renamingEq]
  | universeCode innerLevel => rfl

/-- Compose two raw renamings into a single rename. -/
theorem RawTerm.rename_compose {sourceScope middleScope targetScope : Nat}
    (rho1 : RawRenaming sourceScope middleScope)
    (rho2 : RawRenaming middleScope targetScope)
    (term : RawTerm sourceScope) :
    (term.rename rho1).rename rho2 =
      term.rename (fun position => rho2 (rho1 position)) := by
  induction term generalizing middleScope targetScope with
  | var position => rfl
  | unit => rfl
  | lam body bodyIH =>
      simp only [RawTerm.rename]
      rw [bodyIH rho1.lift rho2.lift]
      congr 1
      apply RawTerm.rename_pointwise
      intro position
      cases position with
      | mk val isLt =>
        cases val with
        | zero => rfl
        | succ k => rfl
  | app fn arg fnIH argIH =>
      simp only [RawTerm.rename]; rw [fnIH rho1 rho2, argIH rho1 rho2]
  | pair fv sv fvIH svIH =>
      simp only [RawTerm.rename]; rw [fvIH rho1 rho2, svIH rho1 rho2]
  | fst pairTerm pairIH => simp only [RawTerm.rename]; rw [pairIH rho1 rho2]
  | snd pairTerm pairIH => simp only [RawTerm.rename]; rw [pairIH rho1 rho2]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim s t e sIH tIH eIH =>
      simp only [RawTerm.rename]; rw [sIH rho1 rho2, tIH rho1 rho2, eIH rho1 rho2]
  | natZero => rfl
  | natSucc p pIH => simp only [RawTerm.rename]; rw [pIH rho1 rho2]
  | natElim s z c sIH zIH cIH =>
      simp only [RawTerm.rename]; rw [sIH rho1 rho2, zIH rho1 rho2, cIH rho1 rho2]
  | natRec s z c sIH zIH cIH =>
      simp only [RawTerm.rename]; rw [sIH rho1 rho2, zIH rho1 rho2, cIH rho1 rho2]
  | listNil => rfl
  | listCons h t hIH tIH =>
      simp only [RawTerm.rename]; rw [hIH rho1 rho2, tIH rho1 rho2]
  | listElim s n c sIH nIH cIH =>
      simp only [RawTerm.rename]; rw [sIH rho1 rho2, nIH rho1 rho2, cIH rho1 rho2]
  | optionNone => rfl
  | optionSome v vIH => simp only [RawTerm.rename]; rw [vIH rho1 rho2]
  | optionMatch s n c sIH nIH cIH =>
      simp only [RawTerm.rename]; rw [sIH rho1 rho2, nIH rho1 rho2, cIH rho1 rho2]
  | eitherInl v vIH => simp only [RawTerm.rename]; rw [vIH rho1 rho2]
  | eitherInr v vIH => simp only [RawTerm.rename]; rw [vIH rho1 rho2]
  | eitherMatch s l r sIH lIH rIH =>
      simp only [RawTerm.rename]; rw [sIH rho1 rho2, lIH rho1 rho2, rIH rho1 rho2]
  | refl witness witnessIH => simp only [RawTerm.rename]; rw [witnessIH rho1 rho2]
  | idJ base witness baseIH witnessIH =>
      simp only [RawTerm.rename]; rw [baseIH rho1 rho2, witnessIH rho1 rho2]
  | modIntro inner innerIH => simp only [RawTerm.rename]; rw [innerIH rho1 rho2]
  | modElim inner innerIH => simp only [RawTerm.rename]; rw [innerIH rho1 rho2]
  | subsume inner innerIH => simp only [RawTerm.rename]; rw [innerIH rho1 rho2]
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp i iIH => simp only [RawTerm.rename]; rw [iIH rho1 rho2]
  | intervalMeet l r lIH rIH =>
      simp only [RawTerm.rename]; rw [lIH rho1 rho2, rIH rho1 rho2]
  | intervalJoin l r lIH rIH =>
      simp only [RawTerm.rename]; rw [lIH rho1 rho2, rIH rho1 rho2]
  | pathLam body bodyIH =>
      simp only [RawTerm.rename]
      rw [bodyIH rho1.lift rho2.lift]
      congr 1
      apply RawTerm.rename_pointwise
      intro position
      cases position with
      | mk val isLt =>
        cases val with
        | zero => rfl
        | succ k => rfl
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      simp only [RawTerm.rename]; rw [pathIH rho1 rho2, intervalIH rho1 rho2]
  | glueIntro baseValue partialValue baseIH partialIH =>
      simp only [RawTerm.rename]; rw [baseIH rho1 rho2, partialIH rho1 rho2]
  | glueElim gluedValue gluedIH =>
      simp only [RawTerm.rename]; rw [gluedIH rho1 rho2]
  | transp path source pathIH sourceIH =>
      simp only [RawTerm.rename]; rw [pathIH rho1 rho2, sourceIH rho1 rho2]
  | hcomp sides cap sidesIH capIH =>
      simp only [RawTerm.rename]; rw [sidesIH rho1 rho2, capIH rho1 rho2]
  | oeqRefl witness witnessIH =>
      simp only [RawTerm.rename]; rw [witnessIH rho1 rho2]
  | oeqJ baseCase witness baseIH witnessIH =>
      simp only [RawTerm.rename]; rw [baseIH rho1 rho2, witnessIH rho1 rho2]
  | oeqFunext pointwiseEquality pointwiseIH =>
      simp only [RawTerm.rename]; rw [pointwiseIH rho1 rho2]
  | idStrictRefl witness witnessIH =>
      simp only [RawTerm.rename]; rw [witnessIH rho1 rho2]
  | idStrictRec baseCase witness baseIH witnessIH =>
      simp only [RawTerm.rename]; rw [baseIH rho1 rho2, witnessIH rho1 rho2]
  | equivIntro fwd bwd fwdIH bwdIH =>
      simp only [RawTerm.rename]; rw [fwdIH rho1 rho2, bwdIH rho1 rho2]
  | equivApp equivTerm argument equivIH argIH =>
      simp only [RawTerm.rename]; rw [equivIH rho1 rho2, argIH rho1 rho2]
  | refineIntro rawValue predicateProof valueIH proofIH =>
      simp only [RawTerm.rename]; rw [valueIH rho1 rho2, proofIH rho1 rho2]
  | refineElim refinedValue refinedIH =>
      simp only [RawTerm.rename]; rw [refinedIH rho1 rho2]
  | recordIntro firstField firstIH =>
      simp only [RawTerm.rename]; rw [firstIH rho1 rho2]
  | recordProj recordValue recordIH =>
      simp only [RawTerm.rename]; rw [recordIH rho1 rho2]
  | codataUnfold initialState transition stateIH transIH =>
      simp only [RawTerm.rename]; rw [stateIH rho1 rho2, transIH rho1 rho2]
  | codataDest codataValue codataIH =>
      simp only [RawTerm.rename]; rw [codataIH rho1 rho2]
  | sessionSend channel payload chIH payloadIH =>
      simp only [RawTerm.rename]; rw [chIH rho1 rho2, payloadIH rho1 rho2]
  | sessionRecv channel chIH =>
      simp only [RawTerm.rename]; rw [chIH rho1 rho2]
  | effectPerform operationTag arguments tagIH argsIH =>
      simp only [RawTerm.rename]; rw [tagIH rho1 rho2, argsIH rho1 rho2]
  | universeCode innerLevel => rfl

/-- The load-bearing weaken/lift commute identity (pointwise).
    `weaken.compose rho.lift = rho.compose weaken` per position. -/
theorem RawRenaming.weaken_lift_commute {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) :
    ∀ position, rho.lift (RawRenaming.weaken position) =
                RawRenaming.weaken (rho position) :=
  fun _ => rfl

/-- weaken-after-rename equals rename-after-weaken on raw terms. -/
theorem RawTerm.weaken_rename_commute {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) (term : RawTerm sourceScope) :
    term.weaken.rename rho.lift = (term.rename rho).weaken := by
  show (term.rename RawRenaming.weaken).rename rho.lift =
       (term.rename rho).rename RawRenaming.weaken
  rw [RawTerm.rename_compose RawRenaming.weaken rho.lift term,
      RawTerm.rename_compose rho RawRenaming.weaken term]
  exact RawTerm.rename_pointwise (RawRenaming.weaken_lift_commute rho) term

/-! ## Substitutions -/

/-- A raw term substitution: `Fin source → RawTerm target`. -/
@[reducible] def RawTermSubst (source target : Nat) : Type :=
  Fin source → RawTerm target

/-- Identity substitution: each position to its variable. -/
@[reducible] def RawTermSubst.identity {scope : Nat} : RawTermSubst scope scope :=
  fun position => RawTerm.var position

/-- Lift a substitution under a binder. -/
@[reducible] def RawTermSubst.lift {source target : Nat}
    (sigma : RawTermSubst source target) : RawTermSubst (source + 1) (target + 1)
  | ⟨0, _⟩      => RawTerm.var ⟨0, Nat.zero_lt_succ _⟩
  | ⟨k + 1, h⟩  => (sigma ⟨k, Nat.lt_of_succ_lt_succ h⟩).rename RawRenaming.weaken

/-- Single-binder substitution: position 0 → rawArg, position k+1 → var k.

This is the load-bearing β-reduction substitution.  In lean-fx-2 this
is the ONE singleton operation; there is NO `dropNewest` variant. -/
@[reducible] def RawTermSubst.singleton {scope : Nat}
    (rawArg : RawTerm scope) : RawTermSubst (scope + 1) scope
  | ⟨0, _⟩      => rawArg
  | ⟨k + 1, h⟩  => RawTerm.var ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- Convert a rawRenaming to a substitution. -/
@[reducible] def RawRenaming.toSubst {source target : Nat}
    (rawRenaming : RawRenaming source target) : RawTermSubst source target :=
  fun position => RawTerm.var (rawRenaming position)

/-- Apply a substitution to a raw term. -/
def RawTerm.subst : ∀ {source target : Nat},
    RawTerm source → RawTermSubst source target → RawTerm target
  | _, _, .var position, sigma => sigma position
  | _, _, .unit, _ => .unit
  | _, _, .lam body, sigma => .lam (body.subst sigma.lift)
  | _, _, .app functionTerm argumentTerm, sigma =>
      .app (functionTerm.subst sigma) (argumentTerm.subst sigma)
  | _, _, .pair firstValue secondValue, sigma =>
      .pair (firstValue.subst sigma) (secondValue.subst sigma)
  | _, _, .fst pairTerm, sigma => .fst (pairTerm.subst sigma)
  | _, _, .snd pairTerm, sigma => .snd (pairTerm.subst sigma)
  | _, _, .boolTrue, _ => .boolTrue
  | _, _, .boolFalse, _ => .boolFalse
  | _, _, .boolElim scrutinee thenBranch elseBranch, sigma =>
      .boolElim (scrutinee.subst sigma)
                (thenBranch.subst sigma)
                (elseBranch.subst sigma)
  | _, _, .natZero, _ => .natZero
  | _, _, .natSucc predecessor, sigma => .natSucc (predecessor.subst sigma)
  | _, _, .natElim scrutinee zeroBranch succBranch, sigma =>
      .natElim (scrutinee.subst sigma)
               (zeroBranch.subst sigma)
               (succBranch.subst sigma)
  | _, _, .natRec scrutinee zeroBranch succBranch, sigma =>
      .natRec (scrutinee.subst sigma)
              (zeroBranch.subst sigma)
              (succBranch.subst sigma)
  | _, _, .listNil, _ => .listNil
  | _, _, .listCons headTerm tailTerm, sigma =>
      .listCons (headTerm.subst sigma) (tailTerm.subst sigma)
  | _, _, .listElim scrutinee nilBranch consBranch, sigma =>
      .listElim (scrutinee.subst sigma)
                (nilBranch.subst sigma)
                (consBranch.subst sigma)
  | _, _, .optionNone, _ => .optionNone
  | _, _, .optionSome valueTerm, sigma => .optionSome (valueTerm.subst sigma)
  | _, _, .optionMatch scrutinee noneBranch someBranch, sigma =>
      .optionMatch (scrutinee.subst sigma)
                   (noneBranch.subst sigma)
                   (someBranch.subst sigma)
  | _, _, .eitherInl valueTerm, sigma => .eitherInl (valueTerm.subst sigma)
  | _, _, .eitherInr valueTerm, sigma => .eitherInr (valueTerm.subst sigma)
  | _, _, .eitherMatch scrutinee leftBranch rightBranch, sigma =>
      .eitherMatch (scrutinee.subst sigma)
                   (leftBranch.subst sigma)
                   (rightBranch.subst sigma)
  | _, _, .refl rawWitness, sigma => .refl (rawWitness.subst sigma)
  | _, _, .idJ baseCase witness, sigma =>
      .idJ (baseCase.subst sigma) (witness.subst sigma)
  | _, _, .modIntro inner, sigma => .modIntro (inner.subst sigma)
  | _, _, .modElim inner, sigma => .modElim (inner.subst sigma)
  | _, _, .subsume inner, sigma => .subsume (inner.subst sigma)
  -- D1.6 cubical interval + path
  | _, _, .interval0, _ => .interval0
  | _, _, .interval1, _ => .interval1
  | _, _, .intervalOpp i, sigma => .intervalOpp (i.subst sigma)
  | _, _, .intervalMeet l r, sigma =>
      .intervalMeet (l.subst sigma) (r.subst sigma)
  | _, _, .intervalJoin l r, sigma =>
      .intervalJoin (l.subst sigma) (r.subst sigma)
  | _, _, .pathLam body, sigma =>
      .pathLam (body.subst sigma.lift)
  | _, _, .pathApp pathTerm intervalArg, sigma =>
      .pathApp (pathTerm.subst sigma) (intervalArg.subst sigma)
  | _, _, .glueIntro baseValue partialValue, sigma =>
      .glueIntro (baseValue.subst sigma) (partialValue.subst sigma)
  | _, _, .glueElim gluedValue, sigma => .glueElim (gluedValue.subst sigma)
  | _, _, .transp path source, sigma =>
      .transp (path.subst sigma) (source.subst sigma)
  | _, _, .hcomp sides cap, sigma =>
      .hcomp (sides.subst sigma) (cap.subst sigma)
  -- D1.6 observational + strict equality
  | _, _, .oeqRefl witness, sigma => .oeqRefl (witness.subst sigma)
  | _, _, .oeqJ baseCase witness, sigma =>
      .oeqJ (baseCase.subst sigma) (witness.subst sigma)
  | _, _, .oeqFunext pointwiseEquality, sigma =>
      .oeqFunext (pointwiseEquality.subst sigma)
  | _, _, .idStrictRefl witness, sigma =>
      .idStrictRefl (witness.subst sigma)
  | _, _, .idStrictRec baseCase witness, sigma =>
      .idStrictRec (baseCase.subst sigma) (witness.subst sigma)
  -- D1.6 type equivalence
  | _, _, .equivIntro fwd bwd, sigma =>
      .equivIntro (fwd.subst sigma) (bwd.subst sigma)
  | _, _, .equivApp equivTerm argument, sigma =>
      .equivApp (equivTerm.subst sigma) (argument.subst sigma)
  -- D1.6 refinement / record / codata
  | _, _, .refineIntro rawValue predicateProof, sigma =>
      .refineIntro (rawValue.subst sigma) (predicateProof.subst sigma)
  | _, _, .refineElim refinedValue, sigma => .refineElim (refinedValue.subst sigma)
  | _, _, .recordIntro firstField, sigma => .recordIntro (firstField.subst sigma)
  | _, _, .recordProj recordValue, sigma => .recordProj (recordValue.subst sigma)
  | _, _, .codataUnfold initialState transition, sigma =>
      .codataUnfold (initialState.subst sigma) (transition.subst sigma)
  | _, _, .codataDest codataValue, sigma => .codataDest (codataValue.subst sigma)
  -- D1.6 sessions, effects
  | _, _, .sessionSend channel payload, sigma =>
      .sessionSend (channel.subst sigma) (payload.subst sigma)
  | _, _, .sessionRecv channel, sigma => .sessionRecv (channel.subst sigma)
  | _, _, .effectPerform operationTag arguments, sigma =>
      .effectPerform (operationTag.subst sigma) (arguments.subst sigma)
  -- D1.6/A2: universeCode is scope-polymorphic — subst is identity
  -- on the inner-level payload (no Fin variables to substitute).
  | _, _, .universeCode innerLevel, _ =>
      .universeCode innerLevel

/-- Single-variable substitution: substitute `rawArg` for var 0. -/
@[reducible] def RawTerm.subst0 {scope : Nat} (body : RawTerm (scope + 1))
    (rawArg : RawTerm scope) : RawTerm scope :=
  body.subst (RawTermSubst.singleton rawArg)

/-! ## Pointwise + composition lemmas for raw substitution.

Mirror of the renaming-side foundation: `subst_pointwise`,
`subst_compose`, and the cross-direction `rename_subst_commute` /
`subst_rename_commute` lemmas needed by `Ty.subst0_rename_commute`
(load-bearing for the typed `Term.rename`'s appPi/pair/snd cases).

All proofs use the same induction-tactic pattern as the rename
lemmas: structural induction on the term, simp + rw chain through
each ctor, lift-side properties propagated via dedicated pointwise
lemmas.  All zero-axiom (recursor-based, no propext leak). -/

/-- Lift respects pointwise equality on substitutions. -/
theorem RawTermSubst.lift_pointwise {sourceScope targetScope : Nat}
    {sigma1 sigma2 : RawTermSubst sourceScope targetScope}
    (substEq : ∀ position, sigma1 position = sigma2 position) :
    ∀ position, sigma1.lift position = sigma2.lift position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      simp only [RawTermSubst.lift]
      rw [substEq ⟨k, Nat.lt_of_succ_lt_succ h⟩]

/-- RawTerm.subst respects pointwise substitution equality. -/
theorem RawTerm.subst_pointwise {sourceScope targetScope : Nat}
    {sigma1 sigma2 : RawTermSubst sourceScope targetScope}
    (substEq : ∀ position, sigma1 position = sigma2 position) :
    ∀ (term : RawTerm sourceScope), term.subst sigma1 = term.subst sigma2 := by
  intro term
  induction term generalizing targetScope with
  | var position =>
      simp only [RawTerm.subst]; rw [substEq position]
  | unit => rfl
  | lam body bodyIH =>
      simp only [RawTerm.subst]
      rw [bodyIH (RawTermSubst.lift_pointwise substEq)]
  | app fn arg fnIH argIH =>
      simp only [RawTerm.subst]; rw [fnIH substEq, argIH substEq]
  | pair fv sv fvIH svIH =>
      simp only [RawTerm.subst]; rw [fvIH substEq, svIH substEq]
  | fst pairTerm pairIH =>
      simp only [RawTerm.subst]; rw [pairIH substEq]
  | snd pairTerm pairIH =>
      simp only [RawTerm.subst]; rw [pairIH substEq]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim s t e sIH tIH eIH =>
      simp only [RawTerm.subst]; rw [sIH substEq, tIH substEq, eIH substEq]
  | natZero => rfl
  | natSucc p pIH =>
      simp only [RawTerm.subst]; rw [pIH substEq]
  | natElim s z c sIH zIH cIH =>
      simp only [RawTerm.subst]; rw [sIH substEq, zIH substEq, cIH substEq]
  | natRec s z c sIH zIH cIH =>
      simp only [RawTerm.subst]; rw [sIH substEq, zIH substEq, cIH substEq]
  | listNil => rfl
  | listCons headTerm tailTerm headIH tailIH =>
      simp only [RawTerm.subst]; rw [headIH substEq, tailIH substEq]
  | listElim s n c sIH nIH cIH =>
      simp only [RawTerm.subst]; rw [sIH substEq, nIH substEq, cIH substEq]
  | optionNone => rfl
  | optionSome v vIH =>
      simp only [RawTerm.subst]; rw [vIH substEq]
  | optionMatch s n c sIH nIH cIH =>
      simp only [RawTerm.subst]; rw [sIH substEq, nIH substEq, cIH substEq]
  | eitherInl v vIH =>
      simp only [RawTerm.subst]; rw [vIH substEq]
  | eitherInr v vIH =>
      simp only [RawTerm.subst]; rw [vIH substEq]
  | eitherMatch s l r sIH lIH rIH =>
      simp only [RawTerm.subst]; rw [sIH substEq, lIH substEq, rIH substEq]
  | refl witness witnessIH =>
      simp only [RawTerm.subst]; rw [witnessIH substEq]
  | idJ base witness baseIH witnessIH =>
      simp only [RawTerm.subst]; rw [baseIH substEq, witnessIH substEq]
  | modIntro inner innerIH =>
      simp only [RawTerm.subst]; rw [innerIH substEq]
  | modElim inner innerIH =>
      simp only [RawTerm.subst]; rw [innerIH substEq]
  | subsume inner innerIH =>
      simp only [RawTerm.subst]; rw [innerIH substEq]
  -- D1.6 cubical interval + path
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp i iIH =>
      simp only [RawTerm.subst]; rw [iIH substEq]
  | intervalMeet l r lIH rIH =>
      simp only [RawTerm.subst]; rw [lIH substEq, rIH substEq]
  | intervalJoin l r lIH rIH =>
      simp only [RawTerm.subst]; rw [lIH substEq, rIH substEq]
  | pathLam body bodyIH =>
      simp only [RawTerm.subst]
      rw [bodyIH (RawTermSubst.lift_pointwise substEq)]
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      simp only [RawTerm.subst]; rw [pathIH substEq, intervalIH substEq]
  | glueIntro baseValue partialValue baseIH partialIH =>
      simp only [RawTerm.subst]; rw [baseIH substEq, partialIH substEq]
  | glueElim gluedValue gluedIH =>
      simp only [RawTerm.subst]; rw [gluedIH substEq]
  | transp path source pathIH sourceIH =>
      simp only [RawTerm.subst]; rw [pathIH substEq, sourceIH substEq]
  | hcomp sides cap sidesIH capIH =>
      simp only [RawTerm.subst]; rw [sidesIH substEq, capIH substEq]
  -- D1.6 observational + strict equality
  | oeqRefl witness witnessIH =>
      simp only [RawTerm.subst]; rw [witnessIH substEq]
  | oeqJ baseCase witness baseIH witnessIH =>
      simp only [RawTerm.subst]; rw [baseIH substEq, witnessIH substEq]
  | oeqFunext pointwiseEquality pointwiseIH =>
      simp only [RawTerm.subst]; rw [pointwiseIH substEq]
  | idStrictRefl witness witnessIH =>
      simp only [RawTerm.subst]; rw [witnessIH substEq]
  | idStrictRec baseCase witness baseIH witnessIH =>
      simp only [RawTerm.subst]; rw [baseIH substEq, witnessIH substEq]
  -- D1.6 type equivalence
  | equivIntro fwd bwd fwdIH bwdIH =>
      simp only [RawTerm.subst]; rw [fwdIH substEq, bwdIH substEq]
  | equivApp equivTerm argument equivIH argIH =>
      simp only [RawTerm.subst]; rw [equivIH substEq, argIH substEq]
  -- D1.6 refinement / record / codata
  | refineIntro rawValue predicateProof valueIH proofIH =>
      simp only [RawTerm.subst]; rw [valueIH substEq, proofIH substEq]
  | refineElim refinedValue refinedIH =>
      simp only [RawTerm.subst]; rw [refinedIH substEq]
  | recordIntro firstField firstIH =>
      simp only [RawTerm.subst]; rw [firstIH substEq]
  | recordProj recordValue recordIH =>
      simp only [RawTerm.subst]; rw [recordIH substEq]
  | codataUnfold initialState transition stateIH transIH =>
      simp only [RawTerm.subst]; rw [stateIH substEq, transIH substEq]
  | codataDest codataValue codataIH =>
      simp only [RawTerm.subst]; rw [codataIH substEq]
  -- D1.6 sessions, effects
  | sessionSend channel payload chIH payloadIH =>
      simp only [RawTerm.subst]; rw [chIH substEq, payloadIH substEq]
  | sessionRecv channel chIH =>
      simp only [RawTerm.subst]; rw [chIH substEq]
  | effectPerform operationTag arguments tagIH argsIH =>
      simp only [RawTerm.subst]; rw [tagIH substEq, argsIH substEq]
  | universeCode innerLevel => rfl

/-! ### Cross-direction: rename-after-subst and subst-after-rename. -/

/-- Lifted-renamed substitution agrees pointwise: substituting after
renaming = substituting under the renamed positions. -/
theorem RawTermSubst.lift_renaming_pull {sourceScope middleScope targetScope : Nat}
    (rho : RawRenaming sourceScope middleScope)
    (sigma : RawTermSubst middleScope targetScope) :
    ∀ position,
      sigma.lift (rho.lift position) =
        RawTermSubst.lift (fun i => sigma (rho i)) position
  | ⟨0, _⟩      => rfl
  | ⟨_ + 1, _⟩  => rfl

/-- rename-then-subst factors through pre-composed substitution. -/
theorem RawTerm.rename_subst_commute {sourceScope middleScope targetScope : Nat}
    (rho : RawRenaming sourceScope middleScope)
    (sigma : RawTermSubst middleScope targetScope)
    (term : RawTerm sourceScope) :
    (term.rename rho).subst sigma = term.subst (fun position => sigma (rho position)) := by
  induction term generalizing middleScope targetScope with
  | var position => rfl
  | unit => rfl
  | lam body bodyIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [bodyIH rho.lift sigma.lift]
      congr 1
      apply RawTerm.subst_pointwise
      exact RawTermSubst.lift_renaming_pull rho sigma
  | app fn arg fnIH argIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [fnIH rho sigma, argIH rho sigma]
  | pair fv sv fvIH svIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [fvIH rho sigma, svIH rho sigma]
  | fst pairTerm pairIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [pairIH rho sigma]
  | snd pairTerm pairIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [pairIH rho sigma]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim s t e sIH tIH eIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [sIH rho sigma, tIH rho sigma, eIH rho sigma]
  | natZero => rfl
  | natSucc p pIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [pIH rho sigma]
  | natElim s z c sIH zIH cIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [sIH rho sigma, zIH rho sigma, cIH rho sigma]
  | natRec s z c sIH zIH cIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [sIH rho sigma, zIH rho sigma, cIH rho sigma]
  | listNil => rfl
  | listCons headTerm tailTerm headIH tailIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [headIH rho sigma, tailIH rho sigma]
  | listElim s n c sIH nIH cIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [sIH rho sigma, nIH rho sigma, cIH rho sigma]
  | optionNone => rfl
  | optionSome v vIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [vIH rho sigma]
  | optionMatch s n c sIH nIH cIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [sIH rho sigma, nIH rho sigma, cIH rho sigma]
  | eitherInl v vIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [vIH rho sigma]
  | eitherInr v vIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [vIH rho sigma]
  | eitherMatch s l r sIH lIH rIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [sIH rho sigma, lIH rho sigma, rIH rho sigma]
  | refl witness witnessIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [witnessIH rho sigma]
  | idJ base witness baseIH witnessIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [baseIH rho sigma, witnessIH rho sigma]
  | modIntro inner innerIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [innerIH rho sigma]
  | modElim inner innerIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [innerIH rho sigma]
  | subsume inner innerIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [innerIH rho sigma]
  -- D1.6 cubical interval + path
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp i iIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [iIH rho sigma]
  | intervalMeet l r lIH rIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [lIH rho sigma, rIH rho sigma]
  | intervalJoin l r lIH rIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [lIH rho sigma, rIH rho sigma]
  | pathLam body bodyIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [bodyIH rho.lift sigma.lift]
      congr 1
      apply RawTerm.subst_pointwise
      exact RawTermSubst.lift_renaming_pull rho sigma
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [pathIH rho sigma, intervalIH rho sigma]
  | glueIntro baseValue partialValue baseIH partialIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [baseIH rho sigma, partialIH rho sigma]
  | glueElim gluedValue gluedIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [gluedIH rho sigma]
  | transp path source pathIH sourceIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [pathIH rho sigma, sourceIH rho sigma]
  | hcomp sides cap sidesIH capIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [sidesIH rho sigma, capIH rho sigma]
  -- D1.6 observational + strict equality
  | oeqRefl witness witnessIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [witnessIH rho sigma]
  | oeqJ baseCase witness baseIH witnessIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [baseIH rho sigma, witnessIH rho sigma]
  | oeqFunext pointwiseEquality pointwiseIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [pointwiseIH rho sigma]
  | idStrictRefl witness witnessIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [witnessIH rho sigma]
  | idStrictRec baseCase witness baseIH witnessIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [baseIH rho sigma, witnessIH rho sigma]
  -- D1.6 type equivalence
  | equivIntro fwd bwd fwdIH bwdIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [fwdIH rho sigma, bwdIH rho sigma]
  | equivApp equivTerm argument equivIH argIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [equivIH rho sigma, argIH rho sigma]
  -- D1.6 refinement / record / codata
  | refineIntro rawValue predicateProof valueIH proofIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [valueIH rho sigma, proofIH rho sigma]
  | refineElim refinedValue refinedIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [refinedIH rho sigma]
  | recordIntro firstField firstIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [firstIH rho sigma]
  | recordProj recordValue recordIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [recordIH rho sigma]
  | codataUnfold initialState transition stateIH transIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [stateIH rho sigma, transIH rho sigma]
  | codataDest codataValue codataIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [codataIH rho sigma]
  -- D1.6 sessions, effects
  | sessionSend channel payload chIH payloadIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [chIH rho sigma, payloadIH rho sigma]
  | sessionRecv channel chIH =>
      simp only [RawTerm.rename, RawTerm.subst]; rw [chIH rho sigma]
  | effectPerform operationTag arguments tagIH argsIH =>
      simp only [RawTerm.rename, RawTerm.subst]
      rw [tagIH rho sigma, argsIH rho sigma]
  | universeCode innerLevel => rfl

/-- Lifted-then-renamed substitution agrees pointwise with renamed-then-lifted. -/
theorem RawTermSubst.lift_then_rename_lift {sourceScope middleScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope middleScope)
    (rho : RawRenaming middleScope targetScope) :
    ∀ position,
      (sigma.lift position).rename rho.lift =
        RawTermSubst.lift (fun i => (sigma i).rename rho) position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      simp only [RawTermSubst.lift]
      rw [RawTerm.rename_compose RawRenaming.weaken rho.lift
            (sigma ⟨k, Nat.lt_of_succ_lt_succ h⟩),
          RawTerm.rename_compose rho RawRenaming.weaken
            (sigma ⟨k, Nat.lt_of_succ_lt_succ h⟩)]
      apply RawTerm.rename_pointwise
      intro p
      exact RawRenaming.weaken_lift_commute rho p

/-- subst-then-rename factors through post-composed substitution. -/
theorem RawTerm.subst_rename_commute {sourceScope middleScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope middleScope)
    (rho : RawRenaming middleScope targetScope)
    (term : RawTerm sourceScope) :
    (term.subst sigma).rename rho =
      term.subst (fun position => (sigma position).rename rho) := by
  induction term generalizing middleScope targetScope with
  | var position => rfl
  | unit => rfl
  | lam body bodyIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [bodyIH sigma.lift rho.lift]
      congr 1
      apply RawTerm.subst_pointwise
      exact RawTermSubst.lift_then_rename_lift sigma rho
  | app fn arg fnIH argIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [fnIH sigma rho, argIH sigma rho]
  | pair fv sv fvIH svIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [fvIH sigma rho, svIH sigma rho]
  | fst pairTerm pairIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [pairIH sigma rho]
  | snd pairTerm pairIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [pairIH sigma rho]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim s t e sIH tIH eIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [sIH sigma rho, tIH sigma rho, eIH sigma rho]
  | natZero => rfl
  | natSucc p pIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [pIH sigma rho]
  | natElim s z c sIH zIH cIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [sIH sigma rho, zIH sigma rho, cIH sigma rho]
  | natRec s z c sIH zIH cIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [sIH sigma rho, zIH sigma rho, cIH sigma rho]
  | listNil => rfl
  | listCons headTerm tailTerm headIH tailIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [headIH sigma rho, tailIH sigma rho]
  | listElim s n c sIH nIH cIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [sIH sigma rho, nIH sigma rho, cIH sigma rho]
  | optionNone => rfl
  | optionSome v vIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [vIH sigma rho]
  | optionMatch s n c sIH nIH cIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [sIH sigma rho, nIH sigma rho, cIH sigma rho]
  | eitherInl v vIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [vIH sigma rho]
  | eitherInr v vIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [vIH sigma rho]
  | eitherMatch s l r sIH lIH rIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [sIH sigma rho, lIH sigma rho, rIH sigma rho]
  | refl witness witnessIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [witnessIH sigma rho]
  | idJ base witness baseIH witnessIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [baseIH sigma rho, witnessIH sigma rho]
  | modIntro inner innerIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [innerIH sigma rho]
  | modElim inner innerIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [innerIH sigma rho]
  | subsume inner innerIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [innerIH sigma rho]
  -- D1.6 cubical interval + path
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp i iIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [iIH sigma rho]
  | intervalMeet l r lIH rIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [lIH sigma rho, rIH sigma rho]
  | intervalJoin l r lIH rIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [lIH sigma rho, rIH sigma rho]
  | pathLam body bodyIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [bodyIH sigma.lift rho.lift]
      congr 1
      apply RawTerm.subst_pointwise
      exact RawTermSubst.lift_then_rename_lift sigma rho
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [pathIH sigma rho, intervalIH sigma rho]
  | glueIntro baseValue partialValue baseIH partialIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [baseIH sigma rho, partialIH sigma rho]
  | glueElim gluedValue gluedIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [gluedIH sigma rho]
  | transp path source pathIH sourceIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [pathIH sigma rho, sourceIH sigma rho]
  | hcomp sides cap sidesIH capIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [sidesIH sigma rho, capIH sigma rho]
  -- D1.6 observational + strict equality
  | oeqRefl witness witnessIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [witnessIH sigma rho]
  | oeqJ baseCase witness baseIH witnessIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [baseIH sigma rho, witnessIH sigma rho]
  | oeqFunext pointwiseEquality pointwiseIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [pointwiseIH sigma rho]
  | idStrictRefl witness witnessIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [witnessIH sigma rho]
  | idStrictRec baseCase witness baseIH witnessIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [baseIH sigma rho, witnessIH sigma rho]
  -- D1.6 type equivalence
  | equivIntro fwd bwd fwdIH bwdIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [fwdIH sigma rho, bwdIH sigma rho]
  | equivApp equivTerm argument equivIH argIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [equivIH sigma rho, argIH sigma rho]
  -- D1.6 refinement / record / codata
  | refineIntro rawValue predicateProof valueIH proofIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [valueIH sigma rho, proofIH sigma rho]
  | refineElim refinedValue refinedIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [refinedIH sigma rho]
  | recordIntro firstField firstIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [firstIH sigma rho]
  | recordProj recordValue recordIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [recordIH sigma rho]
  | codataUnfold initialState transition stateIH transIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [stateIH sigma rho, transIH sigma rho]
  | codataDest codataValue codataIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [codataIH sigma rho]
  -- D1.6 sessions, effects
  | sessionSend channel payload chIH payloadIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [chIH sigma rho, payloadIH sigma rho]
  | sessionRecv channel chIH =>
      simp only [RawTerm.subst, RawTerm.rename]; rw [chIH sigma rho]
  | effectPerform operationTag arguments tagIH argsIH =>
      simp only [RawTerm.subst, RawTerm.rename]
      rw [tagIH sigma rho, argsIH sigma rho]
  | universeCode innerLevel => rfl

/-! ### subst-subst composition. -/

/-- Compose two substitutions: substituting by the first, then the
second, equals substituting once by the composed substitution. -/
@[reducible] def RawTermSubst.compose {sourceScope middleScope targetScope : Nat}
    (sigma1 : RawTermSubst sourceScope middleScope)
    (sigma2 : RawTermSubst middleScope targetScope) :
    RawTermSubst sourceScope targetScope :=
  fun position => (sigma1 position).subst sigma2

/-- Lift commutes with substitution composition (pointwise). -/
theorem RawTermSubst.lift_compose_pointwise {sourceScope middleScope targetScope : Nat}
    (sigma1 : RawTermSubst sourceScope middleScope)
    (sigma2 : RawTermSubst middleScope targetScope) :
    ∀ position,
      (RawTermSubst.compose sigma1 sigma2).lift position =
        RawTermSubst.compose sigma1.lift sigma2.lift position
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, h⟩  => by
      simp only [RawTermSubst.lift, RawTermSubst.compose]
      rw [RawTerm.subst_rename_commute sigma2 RawRenaming.weaken
            (sigma1 ⟨k, Nat.lt_of_succ_lt_succ h⟩),
          RawTerm.rename_subst_commute RawRenaming.weaken sigma2.lift
            (sigma1 ⟨k, Nat.lt_of_succ_lt_succ h⟩)]
      apply RawTerm.subst_pointwise
      intro p
      cases p with
      | mk val isLt => rfl

/-- Substitution composes: applying two substitutions sequentially
equals applying the composed substitution once. -/
theorem RawTerm.subst_compose {sourceScope middleScope targetScope : Nat}
    (sigma1 : RawTermSubst sourceScope middleScope)
    (sigma2 : RawTermSubst middleScope targetScope)
    (term : RawTerm sourceScope) :
    (term.subst sigma1).subst sigma2 =
      term.subst (RawTermSubst.compose sigma1 sigma2) := by
  induction term generalizing middleScope targetScope with
  | var position => rfl
  | unit => rfl
  | lam body bodyIH =>
      simp only [RawTerm.subst]
      rw [bodyIH sigma1.lift sigma2.lift]
      congr 1
      apply RawTerm.subst_pointwise
      intro p
      exact (RawTermSubst.lift_compose_pointwise sigma1 sigma2 p).symm
  | app fn arg fnIH argIH =>
      simp only [RawTerm.subst]; rw [fnIH sigma1 sigma2, argIH sigma1 sigma2]
  | pair fv sv fvIH svIH =>
      simp only [RawTerm.subst]; rw [fvIH sigma1 sigma2, svIH sigma1 sigma2]
  | fst pairTerm pairIH =>
      simp only [RawTerm.subst]; rw [pairIH sigma1 sigma2]
  | snd pairTerm pairIH =>
      simp only [RawTerm.subst]; rw [pairIH sigma1 sigma2]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim s t e sIH tIH eIH =>
      simp only [RawTerm.subst]
      rw [sIH sigma1 sigma2, tIH sigma1 sigma2, eIH sigma1 sigma2]
  | natZero => rfl
  | natSucc p pIH =>
      simp only [RawTerm.subst]; rw [pIH sigma1 sigma2]
  | natElim s z c sIH zIH cIH =>
      simp only [RawTerm.subst]
      rw [sIH sigma1 sigma2, zIH sigma1 sigma2, cIH sigma1 sigma2]
  | natRec s z c sIH zIH cIH =>
      simp only [RawTerm.subst]
      rw [sIH sigma1 sigma2, zIH sigma1 sigma2, cIH sigma1 sigma2]
  | listNil => rfl
  | listCons headTerm tailTerm headIH tailIH =>
      simp only [RawTerm.subst]
      rw [headIH sigma1 sigma2, tailIH sigma1 sigma2]
  | listElim s n c sIH nIH cIH =>
      simp only [RawTerm.subst]
      rw [sIH sigma1 sigma2, nIH sigma1 sigma2, cIH sigma1 sigma2]
  | optionNone => rfl
  | optionSome v vIH =>
      simp only [RawTerm.subst]; rw [vIH sigma1 sigma2]
  | optionMatch s n c sIH nIH cIH =>
      simp only [RawTerm.subst]
      rw [sIH sigma1 sigma2, nIH sigma1 sigma2, cIH sigma1 sigma2]
  | eitherInl v vIH =>
      simp only [RawTerm.subst]; rw [vIH sigma1 sigma2]
  | eitherInr v vIH =>
      simp only [RawTerm.subst]; rw [vIH sigma1 sigma2]
  | eitherMatch s l r sIH lIH rIH =>
      simp only [RawTerm.subst]
      rw [sIH sigma1 sigma2, lIH sigma1 sigma2, rIH sigma1 sigma2]
  | refl witness witnessIH =>
      simp only [RawTerm.subst]; rw [witnessIH sigma1 sigma2]
  | idJ base witness baseIH witnessIH =>
      simp only [RawTerm.subst]
      rw [baseIH sigma1 sigma2, witnessIH sigma1 sigma2]
  | modIntro inner innerIH =>
      simp only [RawTerm.subst]; rw [innerIH sigma1 sigma2]
  | modElim inner innerIH =>
      simp only [RawTerm.subst]; rw [innerIH sigma1 sigma2]
  | subsume inner innerIH =>
      simp only [RawTerm.subst]; rw [innerIH sigma1 sigma2]
  -- D1.6 cubical interval + path
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp i iIH =>
      simp only [RawTerm.subst]; rw [iIH sigma1 sigma2]
  | intervalMeet l r lIH rIH =>
      simp only [RawTerm.subst]; rw [lIH sigma1 sigma2, rIH sigma1 sigma2]
  | intervalJoin l r lIH rIH =>
      simp only [RawTerm.subst]; rw [lIH sigma1 sigma2, rIH sigma1 sigma2]
  | pathLam body bodyIH =>
      simp only [RawTerm.subst]
      rw [bodyIH sigma1.lift sigma2.lift]
      congr 1
      apply RawTerm.subst_pointwise
      intro p
      exact (RawTermSubst.lift_compose_pointwise sigma1 sigma2 p).symm
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      simp only [RawTerm.subst]; rw [pathIH sigma1 sigma2, intervalIH sigma1 sigma2]
  | glueIntro baseValue partialValue baseIH partialIH =>
      simp only [RawTerm.subst]; rw [baseIH sigma1 sigma2, partialIH sigma1 sigma2]
  | glueElim gluedValue gluedIH =>
      simp only [RawTerm.subst]; rw [gluedIH sigma1 sigma2]
  | transp path source pathIH sourceIH =>
      simp only [RawTerm.subst]; rw [pathIH sigma1 sigma2, sourceIH sigma1 sigma2]
  | hcomp sides cap sidesIH capIH =>
      simp only [RawTerm.subst]; rw [sidesIH sigma1 sigma2, capIH sigma1 sigma2]
  -- D1.6 observational + strict equality
  | oeqRefl witness witnessIH =>
      simp only [RawTerm.subst]; rw [witnessIH sigma1 sigma2]
  | oeqJ baseCase witness baseIH witnessIH =>
      simp only [RawTerm.subst]; rw [baseIH sigma1 sigma2, witnessIH sigma1 sigma2]
  | oeqFunext pointwiseEquality pointwiseIH =>
      simp only [RawTerm.subst]; rw [pointwiseIH sigma1 sigma2]
  | idStrictRefl witness witnessIH =>
      simp only [RawTerm.subst]; rw [witnessIH sigma1 sigma2]
  | idStrictRec baseCase witness baseIH witnessIH =>
      simp only [RawTerm.subst]; rw [baseIH sigma1 sigma2, witnessIH sigma1 sigma2]
  -- D1.6 type equivalence
  | equivIntro fwd bwd fwdIH bwdIH =>
      simp only [RawTerm.subst]; rw [fwdIH sigma1 sigma2, bwdIH sigma1 sigma2]
  | equivApp equivTerm argument equivIH argIH =>
      simp only [RawTerm.subst]; rw [equivIH sigma1 sigma2, argIH sigma1 sigma2]
  -- D1.6 refinement / record / codata
  | refineIntro rawValue predicateProof valueIH proofIH =>
      simp only [RawTerm.subst]; rw [valueIH sigma1 sigma2, proofIH sigma1 sigma2]
  | refineElim refinedValue refinedIH =>
      simp only [RawTerm.subst]; rw [refinedIH sigma1 sigma2]
  | recordIntro firstField firstIH =>
      simp only [RawTerm.subst]; rw [firstIH sigma1 sigma2]
  | recordProj recordValue recordIH =>
      simp only [RawTerm.subst]; rw [recordIH sigma1 sigma2]
  | codataUnfold initialState transition stateIH transIH =>
      simp only [RawTerm.subst]; rw [stateIH sigma1 sigma2, transIH sigma1 sigma2]
  | codataDest codataValue codataIH =>
      simp only [RawTerm.subst]; rw [codataIH sigma1 sigma2]
  -- D1.6 sessions, effects
  | sessionSend channel payload chIH payloadIH =>
      simp only [RawTerm.subst]; rw [chIH sigma1 sigma2, payloadIH sigma1 sigma2]
  | sessionRecv channel chIH =>
      simp only [RawTerm.subst]; rw [chIH sigma1 sigma2]
  | effectPerform operationTag arguments tagIH argsIH =>
      simp only [RawTerm.subst]; rw [tagIH sigma1 sigma2, argsIH sigma1 sigma2]
  | universeCode innerLevel => rfl

/-! ### Single-binder β-substitution commute (load-bearing).

`subst0_rename_commute`: renaming a β-redex's reduct equals β-reducing
the renamed redex.  This is what `Term.rename`'s appPi/pair/snd cases
need to discharge type-index obligations. -/

/-- Pointwise property: singleton-after-renaming = renaming-after-singleton. -/
theorem RawTermSubst.singleton_rename_commute_pointwise {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (rawArg : RawTerm sourceScope) :
    ∀ position,
      ((RawTermSubst.singleton rawArg) position).rename rho =
        (RawTermSubst.singleton (rawArg.rename rho)) (rho.lift position)
  | ⟨0, _⟩      => rfl
  | ⟨_ + 1, _⟩  => rfl

/-- Renaming a single-variable substitution result equals single-variable
substitution after renaming under the lift.  Load-bearing for typed
`Term.rename` on β-redex result types. -/
theorem RawTerm.subst0_rename_commute {sourceScope targetScope : Nat}
    (body : RawTerm (sourceScope + 1))
    (rawArg : RawTerm sourceScope)
    (rho : RawRenaming sourceScope targetScope) :
    (body.subst0 rawArg).rename rho =
      (body.rename rho.lift).subst0 (rawArg.rename rho) := by
  show (body.subst (RawTermSubst.singleton rawArg)).rename rho =
       (body.rename rho.lift).subst (RawTermSubst.singleton (rawArg.rename rho))
  rw [RawTerm.subst_rename_commute (RawTermSubst.singleton rawArg) rho body,
      RawTerm.rename_subst_commute rho.lift
        (RawTermSubst.singleton (rawArg.rename rho)) body]
  apply RawTerm.subst_pointwise
  exact RawTermSubst.singleton_rename_commute_pointwise rho rawArg

/-! ### Identity substitution + load-bearing β-reduction lemmas. -/

/-- Lift of identity substitution agrees pointwise with identity. -/
theorem RawTermSubst.identity_lift_pointwise {scope : Nat} :
    ∀ position,
      (@RawTermSubst.identity scope).lift position = RawTermSubst.identity position
  | ⟨0, _⟩      => rfl
  | ⟨_ + 1, _⟩  => rfl

/-- Substituting by the identity is the identity. -/
theorem RawTerm.subst_identity {scope : Nat} (term : RawTerm scope) :
    term.subst RawTermSubst.identity = term := by
  induction term with
  | var position => rfl
  | unit => rfl
  | lam body bodyIH =>
      simp only [RawTerm.subst]
      rw [RawTerm.subst_pointwise RawTermSubst.identity_lift_pointwise body, bodyIH]
  | app fn arg fnIH argIH =>
      simp only [RawTerm.subst]; rw [fnIH, argIH]
  | pair fv sv fvIH svIH =>
      simp only [RawTerm.subst]; rw [fvIH, svIH]
  | fst pairTerm pairIH =>
      simp only [RawTerm.subst]; rw [pairIH]
  | snd pairTerm pairIH =>
      simp only [RawTerm.subst]; rw [pairIH]
  | boolTrue => rfl
  | boolFalse => rfl
  | boolElim s t e sIH tIH eIH =>
      simp only [RawTerm.subst]; rw [sIH, tIH, eIH]
  | natZero => rfl
  | natSucc p pIH =>
      simp only [RawTerm.subst]; rw [pIH]
  | natElim s z c sIH zIH cIH =>
      simp only [RawTerm.subst]; rw [sIH, zIH, cIH]
  | natRec s z c sIH zIH cIH =>
      simp only [RawTerm.subst]; rw [sIH, zIH, cIH]
  | listNil => rfl
  | listCons h t hIH tIH =>
      simp only [RawTerm.subst]; rw [hIH, tIH]
  | listElim s n c sIH nIH cIH =>
      simp only [RawTerm.subst]; rw [sIH, nIH, cIH]
  | optionNone => rfl
  | optionSome v vIH =>
      simp only [RawTerm.subst]; rw [vIH]
  | optionMatch s n c sIH nIH cIH =>
      simp only [RawTerm.subst]; rw [sIH, nIH, cIH]
  | eitherInl v vIH =>
      simp only [RawTerm.subst]; rw [vIH]
  | eitherInr v vIH =>
      simp only [RawTerm.subst]; rw [vIH]
  | eitherMatch s l r sIH lIH rIH =>
      simp only [RawTerm.subst]; rw [sIH, lIH, rIH]
  | refl witness witnessIH =>
      simp only [RawTerm.subst]; rw [witnessIH]
  | idJ base witness baseIH witnessIH =>
      simp only [RawTerm.subst]; rw [baseIH, witnessIH]
  | modIntro inner innerIH =>
      simp only [RawTerm.subst]; rw [innerIH]
  | modElim inner innerIH =>
      simp only [RawTerm.subst]; rw [innerIH]
  | subsume inner innerIH =>
      simp only [RawTerm.subst]; rw [innerIH]
  -- D1.6 cubical interval + path
  | interval0 => rfl
  | interval1 => rfl
  | intervalOpp i iIH =>
      simp only [RawTerm.subst]; rw [iIH]
  | intervalMeet l r lIH rIH =>
      simp only [RawTerm.subst]; rw [lIH, rIH]
  | intervalJoin l r lIH rIH =>
      simp only [RawTerm.subst]; rw [lIH, rIH]
  | pathLam body bodyIH =>
      simp only [RawTerm.subst]
      rw [RawTerm.subst_pointwise RawTermSubst.identity_lift_pointwise body, bodyIH]
  | pathApp pathTerm intervalArg pathIH intervalIH =>
      simp only [RawTerm.subst]; rw [pathIH, intervalIH]
  | glueIntro baseValue partialValue baseIH partialIH =>
      simp only [RawTerm.subst]; rw [baseIH, partialIH]
  | glueElim gluedValue gluedIH =>
      simp only [RawTerm.subst]; rw [gluedIH]
  | transp path source pathIH sourceIH =>
      simp only [RawTerm.subst]; rw [pathIH, sourceIH]
  | hcomp sides cap sidesIH capIH =>
      simp only [RawTerm.subst]; rw [sidesIH, capIH]
  -- D1.6 observational + strict equality
  | oeqRefl witness witnessIH =>
      simp only [RawTerm.subst]; rw [witnessIH]
  | oeqJ baseCase witness baseIH witnessIH =>
      simp only [RawTerm.subst]; rw [baseIH, witnessIH]
  | oeqFunext pointwiseEquality pointwiseIH =>
      simp only [RawTerm.subst]; rw [pointwiseIH]
  | idStrictRefl witness witnessIH =>
      simp only [RawTerm.subst]; rw [witnessIH]
  | idStrictRec baseCase witness baseIH witnessIH =>
      simp only [RawTerm.subst]; rw [baseIH, witnessIH]
  -- D1.6 type equivalence
  | equivIntro fwd bwd fwdIH bwdIH =>
      simp only [RawTerm.subst]; rw [fwdIH, bwdIH]
  | equivApp equivTerm argument equivIH argIH =>
      simp only [RawTerm.subst]; rw [equivIH, argIH]
  -- D1.6 refinement / record / codata
  | refineIntro rawValue predicateProof valueIH proofIH =>
      simp only [RawTerm.subst]; rw [valueIH, proofIH]
  | refineElim refinedValue refinedIH =>
      simp only [RawTerm.subst]; rw [refinedIH]
  | recordIntro firstField firstIH =>
      simp only [RawTerm.subst]; rw [firstIH]
  | recordProj recordValue recordIH =>
      simp only [RawTerm.subst]; rw [recordIH]
  | codataUnfold initialState transition stateIH transIH =>
      simp only [RawTerm.subst]; rw [stateIH, transIH]
  | codataDest codataValue codataIH =>
      simp only [RawTerm.subst]; rw [codataIH]
  -- D1.6 sessions, effects
  | sessionSend channel payload chIH payloadIH =>
      simp only [RawTerm.subst]; rw [chIH, payloadIH]
  | sessionRecv channel chIH =>
      simp only [RawTerm.subst]; rw [chIH]
  | effectPerform operationTag arguments tagIH argsIH =>
      simp only [RawTerm.subst]; rw [tagIH, argsIH]
  | universeCode innerLevel => rfl

/-- Pre-composing weaken with a singleton (on RawTermSubst) gives the
identity substitution pointwise. -/
theorem RawTermSubst.weaken_then_singleton_pointwise {scope : Nat}
    (rawArg : RawTerm scope) :
    ∀ position,
      (RawTermSubst.singleton rawArg) (RawRenaming.weaken position) =
        RawTermSubst.identity position :=
  fun _ => rfl

/-- Weakening a raw term then substituting by a singleton returns the
original term — the load-bearing β-reduction lemma on raw terms. -/
theorem RawTerm.weaken_subst_singleton {scope : Nat}
    (term rawArg : RawTerm scope) :
    term.weaken.subst (RawTermSubst.singleton rawArg) = term := by
  show (term.rename RawRenaming.weaken).subst (RawTermSubst.singleton rawArg) = term
  rw [RawTerm.rename_subst_commute RawRenaming.weaken (RawTermSubst.singleton rawArg) term,
      RawTerm.subst_pointwise (RawTermSubst.weaken_then_singleton_pointwise rawArg) term,
      RawTerm.subst_identity term]

/-- Lift commutes with renameOutput (RawTerm side, weaken-flavor). -/
theorem RawTermSubst.weaken_lift_subst_pointwise {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope) :
    ∀ position,
      sigma.lift (RawRenaming.weaken position) = (sigma position).rename RawRenaming.weaken :=
  fun _ => rfl

/-- weaken-after-subst equals subst-after-weaken on raw terms. -/
theorem RawTerm.weaken_subst_commute {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope) (term : RawTerm sourceScope) :
    term.weaken.subst sigma.lift = (term.subst sigma).weaken := by
  show (term.rename RawRenaming.weaken).subst sigma.lift =
       (term.subst sigma).rename RawRenaming.weaken
  rw [RawTerm.rename_subst_commute RawRenaming.weaken sigma.lift term,
      RawTerm.subst_rename_commute sigma RawRenaming.weaken term]
  apply RawTerm.subst_pointwise
  exact RawTermSubst.weaken_lift_subst_pointwise sigma

/-! ## Tier 3 / MEGA-Z1.B — Action typeclass instances (raw layer).

Wrap the existing `RawRenaming` and `RawTermSubst` operations as
`Action` typeclass instances.  These are the raw-side Container
inhabitants of the universal-action-with-binding framework shipped in
`Foundation/Action.lean` (Z1.A).  Per the Z1.A docstring, these
instances supply:
* `liftForTy` and `liftForRaw` — set to the same existing `lift`
  (the operation is binder-shape-agnostic at the raw layer)
* `compose`, `identity`, `headIndex` — the existing top-level operations
* `composeAtHeadIndex` — the abstract pointwise behaviour exposed
  opaquely so the typeclass laws can be witnessed without funext.

All laws ship by `rfl` after `@[reducible]` unfolding plus, for the
substitution case, `RawTerm.subst_compose` / `RawTerm.subst_identity`. -/

/-- `Action` instance for `RawRenaming`.  Renamings are pure functions
`Fin source → Fin target`; compose is function composition; lift is
the existing `RawRenaming.lift`.  All laws hold by `rfl` (renaming is
the first-order action). -/
instance : Action RawRenaming where
  ActionTarget       := Fin
  headIndex          := fun rho position => rho position
  liftForTy          := fun rho => rho.lift
  liftForRaw         := fun rho => rho.lift
  identity           := RawRenaming.identity
  compose            := RawRenaming.compose
  composeAtHeadIndex := fun firstRenaming secondRenaming position =>
    secondRenaming (firstRenaming position)
  compose_assoc_pointwise            := fun _ _ _ _ => rfl
  compose_identity_left_pointwise    := fun _ _ => rfl
  compose_identity_right_pointwise   := fun _ _ => rfl
  headIndex_compose                  := fun _ _ _ => rfl

/-- Equivalence theorem: `RawRenaming.identity` is the identity action. -/
theorem RawRenaming.identity_eq_action {scope : Nat} :
    (RawRenaming.identity : RawRenaming scope scope) =
      (Action.identity : RawRenaming scope scope) := rfl

/-- Equivalence theorem: `RawRenaming.lift` agrees with
`Action.liftForTy`. -/
theorem RawRenaming.lift_eq_actionForTy {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) :
    rho.lift = Action.liftForTy rho := rfl

/-- Equivalence theorem: `RawRenaming.lift` agrees with
`Action.liftForRaw`. -/
theorem RawRenaming.lift_eq_actionForRaw {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) :
    rho.lift = Action.liftForRaw rho := rfl

/-- Equivalence theorem: `RawRenaming.compose` is the action's compose. -/
theorem RawRenaming.compose_eq_action
    {scopeA scopeB scopeC : Nat}
    (firstRenaming  : RawRenaming scopeA scopeB)
    (secondRenaming : RawRenaming scopeB scopeC) :
    RawRenaming.compose firstRenaming secondRenaming =
      Action.compose firstRenaming secondRenaming := rfl

/-- `Action` instance for `RawTermSubst`.  Substitutions are functions
`Fin source → RawTerm target`; compose threads through `RawTerm.subst`;
lift is the existing `RawTermSubst.lift`.

`composeAtHeadIndex` exposes `(σ1 pos).subst σ2` opaquely.  Laws
unfold via `RawTerm.subst_compose` (associativity) and
`RawTerm.subst_identity` (right unit); left unit is `rfl` since
`RawTermSubst.identity pos = RawTerm.var pos` and `Ty.subst` /
`RawTerm.subst` map a bare variable to the looked-up substituent. -/
instance : Action RawTermSubst where
  ActionTarget       := RawTerm
  headIndex          := fun sigma position => sigma position
  liftForTy          := fun sigma => sigma.lift
  liftForRaw         := fun sigma => sigma.lift
  identity           := RawTermSubst.identity
  compose            := RawTermSubst.compose
  composeAtHeadIndex := fun firstSigma secondSigma position =>
    (firstSigma position).subst secondSigma
  compose_assoc_pointwise firstSigma middleSigma lastSigma position := by
    -- Associativity reduces to `RawTerm.subst_compose` on the looked-up
    -- substituent at the source position.
    show ((RawTermSubst.compose firstSigma middleSigma) position).subst lastSigma =
         (firstSigma position).subst (RawTermSubst.compose middleSigma lastSigma)
    show ((firstSigma position).subst middleSigma).subst lastSigma =
         (firstSigma position).subst (RawTermSubst.compose middleSigma lastSigma)
    exact RawTerm.subst_compose middleSigma lastSigma (firstSigma position)
  compose_identity_left_pointwise someSigma position := by
    -- Identity-on-the-left: looking up at identity gives `RawTerm.var
    -- position`, and substituting `RawTerm.var position` against any
    -- σ is `σ position` by the var-arm of `RawTerm.subst`.
    show (RawTermSubst.identity position).subst someSigma = someSigma position
    rfl
  compose_identity_right_pointwise someSigma position := by
    -- Identity-on-the-right: substituting `someSigma position` by the
    -- identity substitution returns `someSigma position`.
    exact RawTerm.subst_identity (someSigma position)
  headIndex_compose firstSigma secondSigma position := by
    -- `RawTermSubst.compose σ1 σ2 pos = (σ1 pos).subst σ2` by the
    -- definition of `compose`; equals `composeAtHeadIndex σ1 σ2 pos`.
    rfl

/-- Equivalence theorem: `RawTermSubst.identity` is the action's identity. -/
theorem RawTermSubst.identity_eq_action {scope : Nat} :
    (RawTermSubst.identity : RawTermSubst scope scope) =
      (Action.identity : RawTermSubst scope scope) := rfl

/-- Equivalence theorem: `RawTermSubst.lift` agrees with
`Action.liftForTy`. -/
theorem RawTermSubst.lift_eq_actionForTy {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope) :
    sigma.lift = Action.liftForTy sigma := rfl

/-- Equivalence theorem: `RawTermSubst.lift` agrees with
`Action.liftForRaw`. -/
theorem RawTermSubst.lift_eq_actionForRaw {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope) :
    sigma.lift = Action.liftForRaw sigma := rfl

/-- Equivalence theorem: `RawTermSubst.compose` is the action's compose. -/
theorem RawTermSubst.compose_eq_action {sourceScope middleScope targetScope : Nat}
    (firstSigma  : RawTermSubst sourceScope middleScope)
    (secondSigma : RawTermSubst middleScope targetScope) :
    RawTermSubst.compose firstSigma secondSigma =
      Action.compose firstSigma secondSigma := rfl

/-! ## Tier 3 / MEGA-Z4.A — `ActsOnRawTermVar` instances.

`RawTerm.act` (defined in `Foundation/RawTerm.lean`) takes a Container
with `[Action Container]` and `[ActsOnRawTermVar Container]`.  The
Container's `Action` instance ships above (Z1.B); the
`ActsOnRawTermVar` instances are Z4.A additions, mirroring Z2.A's
`ActsOnTyVar` discipline at the raw layer.

For `RawRenaming`, `varToRawTerm` wraps the renamed Fin back as
`RawTerm.var` — this matches the `var` arm of the existing
`RawTerm.rename` definition.

For `RawTermSubst`, `varToRawTerm` returns the substituent term
directly (`sigma position`) — this matches the `var` arm of the
existing `RawTerm.subst` definition.

Once these instances are in scope, `RawTerm.act t (someRenaming :
RawRenaming src tgt)` reduces by `rfl` to the same shape as
`RawTerm.rename t someRenaming` for representative ctors; similarly
for `RawTermSubst`. -/

/-- `ActsOnRawTermVar` instance: `RawRenaming` wraps renamed Fin as
`RawTerm.var`. -/
instance : ActsOnRawTermVar RawRenaming where
  varToRawTerm := fun someRenaming position => RawTerm.var (someRenaming position)

/-- `ActsOnRawTermVar` instance: `RawTermSubst` returns the
substituent RawTerm directly. -/
instance : ActsOnRawTermVar RawTermSubst where
  varToRawTerm := fun sigma position => sigma position

/-! ## Tier 3 / MEGA-Z5.A.1 — `ActsOnRawTermVarLifts` typeclass + instances.

The closed-payload HoTT ctors that Z5.A's `Term.act` recursion engine
must traverse (`Term.equivReflId`, `Term.funextRefl`, etc.) bury a
`RawTerm.var ⟨0, _⟩` under `Action.liftForRaw action`.  Without a
reduction law for that specific shape, the typeclass dispatch
through `RawTerm.act` cannot rewrite the closed payload to a
`rfl`-equivalent target.

`ActsOnRawTermVarLifts` adds two extra fields to the `Action +
ActsOnRawTermVar` pair: a reduction law for the var-zero case under
`liftForRaw`, and a corresponding law for the var-succ case.
Concretely:

* `liftForRaw_var_zero` — under any lifted action, position `0`
  resolves to `RawTerm.var ⟨0, _⟩` in the target's lifted scope.
* `liftForRaw_var_succ` — under any lifted action, position `k+1`
  resolves to `RawTerm.weaken (varToRawTerm action k)`.

For all three Containers that the Tier 3 framework currently ships
(`RawRenaming`, `RawTermSubst`, `Subst level`), both laws hold by
`rfl` after the existing `@[reducible]` `lift` definitions unfold
— the `RawRenaming.lift` / `RawTermSubst.lift` / `Subst.lift`
definitions were chosen with these reductions in mind.

`ActsOnRawTermVarLifts` does NOT extend `Action` or
`ActsOnRawTermVar`; it sits alongside them as a separate constraint,
keeping the typeclass dependency lattice flat (mirroring the
discipline of Z2.A's `ActsOnTyVar` / Z4.A's `ActsOnRawTermVar`).
Consumers (`Term.act` in Z5.A, downstream HoTT ctor traversal arms)
take all three constraints as separate `[…]` arguments. -/

/-- Bridge typeclass: var-zero and var-succ reductions of
`varToRawTerm` under `Action.liftForRaw`.

Both laws hold by `rfl` for every Container that lifts variables
through `RawRenaming.lift` / `RawTermSubst.lift` / `Subst.lift`'s
`forRaw` discipline (i.e. position `0` maps to `RawTerm.var
⟨0, _⟩`, position `k+1` maps to `RawTerm.weaken` of the renamed/
substituted source). -/
class ActsOnRawTermVarLifts (Container : Nat → Nat → Type)
    [Action Container] [ActsOnRawTermVar Container] where
  /-- At position `0` under `Action.liftForRaw`, the lifted action
  produces `RawTerm.var ⟨0, _⟩` in the target's lifted scope. -/
  liftForRaw_var_zero : ∀ {sourceScope targetScope : Nat}
      (someAction : Container sourceScope targetScope),
        ActsOnRawTermVar.varToRawTerm
            (Action.liftForRaw someAction)
            (⟨0, Nat.zero_lt_succ sourceScope⟩ : Fin (sourceScope + 1))
          = (RawTerm.var ⟨0, Nat.zero_lt_succ targetScope⟩ :
              RawTerm (targetScope + 1))
  /-- At position `k+1` under `Action.liftForRaw`, the lifted action
  produces `RawTerm.weaken` of the action applied to `k`. -/
  liftForRaw_var_succ : ∀ {sourceScope targetScope : Nat}
      (someAction : Container sourceScope targetScope)
      (predecessorIndex : Fin sourceScope),
        ActsOnRawTermVar.varToRawTerm
            (Action.liftForRaw someAction)
            ⟨predecessorIndex.val + 1,
              Nat.succ_lt_succ predecessorIndex.isLt⟩
          = RawTerm.weaken
              (ActsOnRawTermVar.varToRawTerm someAction predecessorIndex)

/-- `ActsOnRawTermVarLifts` instance for `RawRenaming`.

* `liftForRaw_var_zero` — `(rho.lift) ⟨0, _⟩ = ⟨0, Nat.zero_lt_succ _⟩`
  by the var-zero arm of `RawRenaming.lift`; `varToRawTerm` then wraps
  it as `RawTerm.var ⟨0, _⟩`.  Holds by `rfl` after `@[reducible]`
  unfolding of `RawRenaming.lift`.

* `liftForRaw_var_succ` — `(rho.lift) ⟨k+1, h⟩ = Fin.succ (rho ⟨k, _⟩)`
  by the var-succ arm of `RawRenaming.lift`; `varToRawTerm` wraps
  that as `RawTerm.var (Fin.succ (rho ⟨k, _⟩))`.  On the RHS,
  `RawTerm.weaken (RawTerm.var (rho ⟨k, _⟩))
    = (RawTerm.var (rho ⟨k, _⟩)).rename RawRenaming.weaken
    = RawTerm.var (Fin.succ (rho ⟨k, _⟩))`
  by the var-arm of `RawTerm.rename` and the definition of
  `RawRenaming.weaken`.  Holds by `rfl`. -/
instance : ActsOnRawTermVarLifts RawRenaming where
  liftForRaw_var_zero := fun _ => rfl
  liftForRaw_var_succ := fun _ _ => rfl

/-- `ActsOnRawTermVarLifts` instance for `RawTermSubst`.

* `liftForRaw_var_zero` — `(sigma.lift) ⟨0, _⟩ = RawTerm.var
  ⟨0, Nat.zero_lt_succ _⟩` by the var-zero arm of
  `RawTermSubst.lift`; `varToRawTerm` returns it directly.  Holds
  by `rfl`.

* `liftForRaw_var_succ` — `(sigma.lift) ⟨k+1, h⟩
    = (sigma ⟨k, _⟩).rename RawRenaming.weaken`
  by the var-succ arm of `RawTermSubst.lift`; this is the definition
  of `RawTerm.weaken (sigma ⟨k, _⟩)`, which in turn equals
  `RawTerm.weaken (varToRawTerm sigma ⟨k, _⟩)` since
  `varToRawTerm sigma pos = sigma pos`.  Holds by `rfl`. -/
instance : ActsOnRawTermVarLifts RawTermSubst where
  liftForRaw_var_zero := fun _ => rfl
  liftForRaw_var_succ := fun _ _ => rfl

/-! ## Smoke equivalences with existing `RawTerm.rename` / `RawTerm.subst`.

The `RawTerm.act` engine over `RawRenaming` should produce the same
result as the existing `RawTerm.rename`; over `RawTermSubst`, the
same as `RawTerm.subst`.  The full equivalence theorems (~56-case
structural inductions) are deferred to the Z4.B redirect milestone.
For Z4.A we ship the per-ctor `rfl`-bodied smoke theorems
demonstrating that the engine reduces correctly at leaf, recursive,
binder, and var positions on each Container. -/

/-- Smoke: identity-of-act on `RawTerm.unit` under a renaming. -/
theorem RawTerm.act_rawRenaming_unit_smoke
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope) :
    (RawTerm.unit (scope := sourceScope)).act someRenaming = .unit := rfl

/-- Smoke: var-arm under a renaming wraps the renamed Fin. -/
theorem RawTerm.act_rawRenaming_var_smoke
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (position : Fin sourceScope) :
    (RawTerm.var position).act someRenaming = RawTerm.var (someRenaming position) := rfl

/-- Smoke: app-arm under a renaming recurses both subterms. -/
theorem RawTerm.act_rawRenaming_app_smoke
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (functionTerm argumentTerm : RawTerm sourceScope) :
    (RawTerm.app functionTerm argumentTerm).act someRenaming =
      RawTerm.app (functionTerm.act someRenaming) (argumentTerm.act someRenaming) := rfl

/-- Smoke: lam-arm under a renaming uses `Action.liftForRaw`. -/
theorem RawTerm.act_rawRenaming_lam_smoke
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (body : RawTerm (sourceScope + 1)) :
    (RawTerm.lam body).act someRenaming =
      RawTerm.lam (body.act (Action.liftForRaw someRenaming)) := rfl

/-- Smoke: pathLam-arm under a renaming uses `Action.liftForRaw`. -/
theorem RawTerm.act_rawRenaming_pathLam_smoke
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (body : RawTerm (sourceScope + 1)) :
    (RawTerm.pathLam body).act someRenaming =
      RawTerm.pathLam (body.act (Action.liftForRaw someRenaming)) := rfl

/-- Smoke: universeCode is scope-polymorphic and unchanged by act. -/
theorem RawTerm.act_rawRenaming_universeCode_smoke
    {sourceScope targetScope : Nat}
    (someRenaming : RawRenaming sourceScope targetScope)
    (innerLevel : Nat) :
    (RawTerm.universeCode (scope := sourceScope) innerLevel).act someRenaming =
      RawTerm.universeCode innerLevel := rfl

/-- Smoke: identity-of-act on `RawTerm.unit` under a substitution. -/
theorem RawTerm.act_rawTermSubst_unit_smoke
    {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope) :
    (RawTerm.unit (scope := sourceScope)).act sigma = .unit := rfl

/-- Smoke: var-arm under a substitution returns the substituent. -/
theorem RawTerm.act_rawTermSubst_var_smoke
    {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope)
    (position : Fin sourceScope) :
    (RawTerm.var position).act sigma = sigma position := rfl

/-- Smoke: app-arm under a substitution recurses both subterms. -/
theorem RawTerm.act_rawTermSubst_app_smoke
    {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope)
    (functionTerm argumentTerm : RawTerm sourceScope) :
    (RawTerm.app functionTerm argumentTerm).act sigma =
      RawTerm.app (functionTerm.act sigma) (argumentTerm.act sigma) := rfl

/-- Smoke: lam-arm under a substitution uses `Action.liftForRaw`. -/
theorem RawTerm.act_rawTermSubst_lam_smoke
    {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope)
    (body : RawTerm (sourceScope + 1)) :
    (RawTerm.lam body).act sigma =
      RawTerm.lam (body.act (Action.liftForRaw sigma)) := rfl

/-- Smoke: pathLam-arm under a substitution uses `Action.liftForRaw`. -/
theorem RawTerm.act_rawTermSubst_pathLam_smoke
    {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope)
    (body : RawTerm (sourceScope + 1)) :
    (RawTerm.pathLam body).act sigma =
      RawTerm.pathLam (body.act (Action.liftForRaw sigma)) := rfl

/-- Smoke: universeCode is scope-polymorphic under substitution too. -/
theorem RawTerm.act_rawTermSubst_universeCode_smoke
    {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope)
    (innerLevel : Nat) :
    (RawTerm.universeCode (scope := sourceScope) innerLevel).act sigma =
      RawTerm.universeCode innerLevel := rfl

/-- Smoke: identity-action on `RawTerm.unit` reduces to the same term
under `RawRenaming.identity`. -/
theorem RawTerm.act_identity_rawRenaming_unit_smoke {scope : Nat} :
    (RawTerm.unit (scope := scope)).act (RawRenaming.identity (scope := scope)) =
      RawTerm.unit := rfl

/-- Smoke: identity-action on `RawTerm.unit` reduces to the same term
under `RawTermSubst.identity`. -/
theorem RawTerm.act_identity_rawTermSubst_unit_smoke {scope : Nat} :
    (RawTerm.unit (scope := scope)).act (RawTermSubst.identity (scope := scope)) =
      RawTerm.unit := rfl

/-- Smoke: identity-action on `RawTerm.var` reduces to the same
variable under `RawRenaming.identity`. -/
theorem RawTerm.act_identity_rawRenaming_var_smoke
    {scope : Nat} (position : Fin scope) :
    (RawTerm.var position).act (RawRenaming.identity (scope := scope)) =
      RawTerm.var position := rfl

/-- Smoke: identity-action on `RawTerm.var` reduces to the same
variable under `RawTermSubst.identity`. -/
theorem RawTerm.act_identity_rawTermSubst_var_smoke
    {scope : Nat} (position : Fin scope) :
    (RawTerm.var position).act (RawTermSubst.identity (scope := scope)) =
      RawTerm.var position := rfl

end LeanFX2
