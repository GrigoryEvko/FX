import LeanFX2.Foundation.RawTerm

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

end LeanFX2
