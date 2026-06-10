import FX1Poly.Typed.TypedChurchNegation
import FX1Poly.Core.RawTermSubstLiftWeaken

/-! # FX1Poly/Typed/TypedChurchBooleanOperations — the term model COMPUTES conjunction and disjunction

`TypedChurchNegation` showed the term model computes Boolean NEGATION (and that negation is an involution).
This file adds the two BINARY Boolean operations — conjunction (`∧`) and disjunction (`∨`) — completing the
Boolean-operation set and exhibiting De Morgan's laws, so the Church booleans carry a computed Boolean algebra.

A Church boolean is the selector `λA.λt.λf. (t or f)`; `churchTrue` returns its first candidate, `churchFalse`
the second.  The binary operations route the FIRST argument as the selector:

  * `churchAnd = λa.λb. a P b churchFalse`     — `a` true ⟹ `b`; `a` false ⟹ `churchFalse`;
  * `churchOr  = λa.λb. a P churchTrue b`       — `a` true ⟹ `churchTrue`; `a` false ⟹ `b`.

(`P = branchMotivePlaceholder`, the inert type argument — see the predicativity note below.)

## The symbolic-left-strictness finding (the genuinely interesting de Bruijn observation)

The two operations have DIFFERENT symbolic reduction behaviour, and the asymmetry is structural:

  * `churchOr_trueAnything`  : `or true _ ↝* true`  for ANY (symbolic) second argument;
  * `churchOr_falseAnything` : `or false b ↝* b`   for ANY (symbolic) second argument;
  * `churchAnd_falseAnything`: `and false _ ↝* false` for ANY (symbolic) second argument;
  * but `and true b` only reduces for CONCRETE `b` (the truth-table entries `churchAnd_trueTrue/trueFalse`).

The reason: `churchTrue`'s body is the NON-innermost de Bruijn variable (`var 1`), whose resolution through the
`subst0` lifting fold stays stuck on a SYMBOLIC branch, while `churchFalse`'s body is the INNERMOST variable
(`var 0`), which resolves symbolically.  So an operation is symbolic-friendly in its second argument exactly when
the selected branch is the SECOND (else) branch — `or false b` (else = `b`) and `and false _` (else =
`churchFalse`) and `or true _` (then = the CONCRETE `churchTrue`) all reduce; `and true b` (then = the SYMBOLIC
`b`) does not.  OR is therefore FULLY left-strict (both `or true _` and `or false _` determined symbolically);
AND is left-strict only on `false`.  This is the same wall flagged in `TypedChurchNegation` for `churchTrue`'s
selection, here turned into a precise operational asymmetry.

## De Morgan and discrimination

`deMorgan_and_{trueTrue,trueFalse,falseTrue,falseFalse}` : `¬(a ∧ b) =Conv (¬a) ∨ (¬b)` on every truth-table
input — both sides compute to the same Church boolean, established by `Conv.app_cong` congruences over the
shipped negation reductions.  `churchAnd_discriminates` : `and true true ≢ and true false`, so `∧` genuinely
separates its inputs (via `churchTrue_notConvertible_churchFalse`).

## Why this is COMPUTATIONAL, not typed (the predicativity note, as in `TypedChurchNegation`/`…IsZero`)

A typed `∧ : ChurchBool → ChurchBool → ChurchBool` would instantiate the selector's type binder `A:Type@0` at
`A := ChurchBool`, but `ChurchBool : Type@1` — forbidden by the predicative non-cumulative engine
(`UNIV-PREDICATIVE`).  So the operations ship as pure `StepStar`/`Conv` facts with the inert
`branchMotivePlaceholder` as the type argument; the operations are genuinely computed, only their
predicatively-typed packaging is unavailable.

## Zero-axiom verification

Each operation reduces via `churchAnd_reducesToApplied`/`churchOr_reducesToApplied` (two β-steps through the
finished `*Body_subst_a` / `*PartialBody_subst_b` reshapes — `subst_lift_singleton_weaken_weaken` for the
doubly-weakened constants plus the `rfl` de Bruijn var resolutions) composed with a selection helper.  De Morgan
uses `Conv.app_cong`/`Conv.fromStepStar`/`Conv.trans`/`Conv.sym`.  No `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, or `omega`.  Gated per-declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- A closed, scope-polymorphic domain annotation for the binary Boolean-operation binders.  Under T2 every
`lamCell` carries a domain; for these pure-raw operational fixtures a closed `universeCodeCell` is invariant under
`subst0`/`weaken` and heads no redex, keeping the two-β-step reductions computational. -/
def boolOperationDomainAnn {scope : Nat} : RawTerm scope :=
  universeCodeCell LevelExpr.lzero UniverseFlag.standard

-- ========== selection helpers ==========

/-- `churchFalse` selects its else-branch (the THIRD argument) for ARBITRARY (symbolic) arguments — its body is
the innermost de Bruijn variable, which resolves symbolically. -/
theorem churchFalseSelectsElse (typeArg thenBranch elseBranch : RawTerm 0) :
    StepStar (appCell (appCell (appCell churchFalseLambda typeArg) thenBranch) elseBranch) elseBranch :=
  StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        ((.childCons elseBranch .childNil) : RawTermChildren [0] 0)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
            ((.childCons thenBranch .childNil) : RawTermChildren [0] 0)
            Step.beta))))
    (StepStar.trans
      (Step.cong .gen_app ()
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
          ((.childCons elseBranch .childNil) : RawTermChildren [0] 0)
          Step.beta))
      (StepStar.trans Step.beta (StepStar.refl _)))

/-- `churchTrue` selects a CONCRETE `churchTrue` then-branch for any else-branch — the first branch being
concrete lets the non-innermost `var 1` body resolve. -/
theorem churchTrueSelectsConcreteTrue (typeArg elseBranch : RawTerm 0) :
    StepStar (appCell (appCell (appCell churchTrueLambda typeArg) churchTrueLambda) elseBranch) churchTrueLambda :=
  StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        ((.childCons elseBranch .childNil) : RawTermChildren [0] 0)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
            ((.childCons churchTrueLambda .childNil) : RawTermChildren [0] 0)
            Step.beta))))
    (StepStar.trans
      (Step.cong .gen_app ()
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
          ((.childCons elseBranch .childNil) : RawTermChildren [0] 0)
          Step.beta))
      (StepStar.trans Step.beta (StepStar.refl _)))

/-- `churchTrue` selects a CONCRETE `churchFalse` then-branch for any else-branch. -/
theorem churchTrueSelectsConcreteFalse (typeArg elseBranch : RawTerm 0) :
    StepStar (appCell (appCell (appCell churchTrueLambda typeArg) churchFalseLambda) elseBranch) churchFalseLambda :=
  StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        ((.childCons elseBranch .childNil) : RawTermChildren [0] 0)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
            ((.childCons churchFalseLambda .childNil) : RawTermChildren [0] 0)
            Step.beta))))
    (StepStar.trans
      (Step.cong .gen_app ()
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
          ((.childCons elseBranch .childNil) : RawTermChildren [0] 0)
          Step.beta))
      (StepStar.trans Step.beta (StepStar.refl _)))

-- ========== churchAnd ==========

/-- The Church-encoded conjunction `churchAnd = λa.λb. a P b churchFalse` — `a` selects `b` when true and
`churchFalse` when false.  The constants are weakened under the two binders. -/
abbrev churchAndLambda : RawTerm 0 :=
  lamCell boolOperationDomainAnn (lamCell boolOperationDomainAnn (appCell (appCell (appCell
    (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
    (RawTerm.weaken (RawTerm.weaken branchMotivePlaceholder)))
    RawTerm.newestVar)
    (RawTerm.weaken (RawTerm.weaken churchFalseLambda))))

/-- The β1-contractum of `churchAnd`: `λb. (weaken a) (weaken P) b (weaken churchFalse)`. -/
abbrev churchAndPartial (selectorArg : RawTerm 0) : RawTerm 0 :=
  lamCell boolOperationDomainAnn (appCell (appCell (appCell
    (RawTerm.weaken selectorArg)
    (RawTerm.weaken branchMotivePlaceholder))
    RawTerm.newestVar)
    (RawTerm.weaken churchFalseLambda))

/-- β1 reshape: applying the selector `a` lifts it under the `b` binder and cancels one weakening on each
constant (`subst_lift_singleton_weaken_weaken`); the bound `b` (`var 0`) is unchanged. -/
theorem churchAndBody_subst_a (selectorArg : RawTerm 0) :
    RawTerm.subst0
      (lamCell boolOperationDomainAnn (appCell (appCell (appCell
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
        (RawTerm.weaken (RawTerm.weaken branchMotivePlaceholder)))
        RawTerm.newestVar)
        (RawTerm.weaken (RawTerm.weaken churchFalseLambda)))) selectorArg
      = churchAndPartial selectorArg := by
  dsimp only [RawTerm.subst0, churchAndPartial, boolOperationDomainAnn]
  show lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard) (appCell (appCell (appCell
      (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton selectorArg))
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
      (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton selectorArg))
        (RawTerm.weaken (RawTerm.weaken branchMotivePlaceholder))))
      (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton selectorArg)) RawTerm.newestVar))
      (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton selectorArg))
        (RawTerm.weaken (RawTerm.weaken churchFalseLambda)))) = _
  rw [RawTerm.subst_lift_singleton_weaken_weaken branchMotivePlaceholder selectorArg,
      RawTerm.subst_lift_singleton_weaken_weaken churchFalseLambda selectorArg,
      show RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton selectorArg))
          (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
          = RawTerm.weaken selectorArg from rfl,
      show RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton selectorArg))
          (RawTerm.newestVar (scope := 1)) = RawTerm.newestVar from rfl]

/-- β2 reshape: applying the second argument `b` cancels the remaining weakenings and resolves the bound `b`
(`var 0`), leaving the applied selector `a P b churchFalse`. -/
theorem churchAndPartialBody_subst_b (selectorArg secondArg : RawTerm 0) :
    RawTerm.subst0
      (appCell (appCell (appCell
        (RawTerm.weaken selectorArg)
        (RawTerm.weaken branchMotivePlaceholder))
        RawTerm.newestVar)
        (RawTerm.weaken churchFalseLambda)) secondArg
      = appCell (appCell (appCell selectorArg branchMotivePlaceholder) secondArg) churchFalseLambda := by
  dsimp only [RawTerm.subst0]
  show appCell (appCell (appCell
      (RawTerm.subst (RawTermSubst.singleton secondArg) (RawTerm.weaken selectorArg))
      (RawTerm.subst (RawTermSubst.singleton secondArg) (RawTerm.weaken branchMotivePlaceholder)))
      (RawTerm.subst (RawTermSubst.singleton secondArg) RawTerm.newestVar))
      (RawTerm.subst (RawTermSubst.singleton secondArg) (RawTerm.weaken churchFalseLambda)) = _
  rw [RawTerm.weaken_subst_singleton selectorArg secondArg,
      RawTerm.weaken_subst_singleton branchMotivePlaceholder secondArg,
      RawTerm.weaken_subst_singleton churchFalseLambda secondArg,
      show RawTerm.subst (RawTermSubst.singleton secondArg) RawTerm.newestVar = secondArg from rfl]

/-- `churchAnd a b` reduces (two β-steps) to the applied selector `a P b churchFalse`. -/
theorem churchAnd_reducesToApplied (selectorArg secondArg : RawTerm 0) :
    StepStar (appCell (appCell churchAndLambda selectorArg) secondArg)
      (appCell (appCell (appCell selectorArg branchMotivePlaceholder) secondArg) churchFalseLambda) := by
  have step1 : Step (appCell churchAndLambda selectorArg) (churchAndPartial selectorArg) := by
    rw [← churchAndBody_subst_a selectorArg]; exact Step.beta
  have step2 : Step (appCell (churchAndPartial selectorArg) secondArg)
      (appCell (appCell (appCell selectorArg branchMotivePlaceholder) secondArg) churchFalseLambda) := by
    rw [← churchAndPartialBody_subst_b selectorArg secondArg]; exact Step.beta
  exact StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons secondArg .childNil) step1))
    (StepStar.trans step2 (StepStar.refl _))

/-- ★ `and false _ ↝* false` for ARBITRARY (symbolic) second argument — `churchFalse` selects its second
candidate (the constant `churchFalse`), whose innermost-variable body resolves symbolically.  AND is left-strict
on `false`. -/
theorem churchAnd_falseAnything (secondArg : RawTerm 0) :
    StepStar (appCell (appCell churchAndLambda churchFalseLambda) secondArg) churchFalseLambda :=
  StepStar.trans_compose (churchAnd_reducesToApplied churchFalseLambda secondArg)
    (churchFalseSelectsElse branchMotivePlaceholder secondArg churchFalseLambda)

/-- ★ `and true true ↝* true` (truth-table entry; the symbolic `and true _` is stuck on `churchTrue`'s
non-innermost selection, so the `true` row needs concrete second arguments). -/
theorem churchAnd_trueTrue :
    StepStar (appCell (appCell churchAndLambda churchTrueLambda) churchTrueLambda) churchTrueLambda :=
  StepStar.trans_compose (churchAnd_reducesToApplied churchTrueLambda churchTrueLambda)
    (churchTrueSelectsConcreteTrue branchMotivePlaceholder churchFalseLambda)

/-- ★ `and true false ↝* false`. -/
theorem churchAnd_trueFalse :
    StepStar (appCell (appCell churchAndLambda churchTrueLambda) churchFalseLambda) churchFalseLambda :=
  StepStar.trans_compose (churchAnd_reducesToApplied churchTrueLambda churchFalseLambda)
    (churchTrueSelectsConcreteFalse branchMotivePlaceholder churchFalseLambda)

-- ========== churchOr ==========

/-- The Church-encoded disjunction `churchOr = λa.λb. a P churchTrue b` — `a` selects `churchTrue` when true and
`b` when false. -/
abbrev churchOrLambda : RawTerm 0 :=
  lamCell boolOperationDomainAnn (lamCell boolOperationDomainAnn (appCell (appCell (appCell
    (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
    (RawTerm.weaken (RawTerm.weaken branchMotivePlaceholder)))
    (RawTerm.weaken (RawTerm.weaken churchTrueLambda)))
    RawTerm.newestVar))

/-- The β1-contractum of `churchOr`: `λb. (weaken a) (weaken P) (weaken churchTrue) b`. -/
abbrev churchOrPartial (selectorArg : RawTerm 0) : RawTerm 0 :=
  lamCell boolOperationDomainAnn (appCell (appCell (appCell
    (RawTerm.weaken selectorArg)
    (RawTerm.weaken branchMotivePlaceholder))
    (RawTerm.weaken churchTrueLambda))
    RawTerm.newestVar)

/-- β1 reshape for `churchOr`. -/
theorem churchOrBody_subst_a (selectorArg : RawTerm 0) :
    RawTerm.subst0
      (lamCell boolOperationDomainAnn (appCell (appCell (appCell
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
        (RawTerm.weaken (RawTerm.weaken branchMotivePlaceholder)))
        (RawTerm.weaken (RawTerm.weaken churchTrueLambda)))
        RawTerm.newestVar)) selectorArg
      = churchOrPartial selectorArg := by
  dsimp only [RawTerm.subst0, churchOrPartial, boolOperationDomainAnn]
  show lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard) (appCell (appCell (appCell
      (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton selectorArg))
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
      (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton selectorArg))
        (RawTerm.weaken (RawTerm.weaken branchMotivePlaceholder))))
      (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton selectorArg))
        (RawTerm.weaken (RawTerm.weaken churchTrueLambda))))
      (RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton selectorArg)) RawTerm.newestVar)) = _
  rw [RawTerm.subst_lift_singleton_weaken_weaken branchMotivePlaceholder selectorArg,
      RawTerm.subst_lift_singleton_weaken_weaken churchTrueLambda selectorArg,
      show RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton selectorArg))
          (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
          = RawTerm.weaken selectorArg from rfl,
      show RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton selectorArg))
          (RawTerm.newestVar (scope := 1)) = RawTerm.newestVar from rfl]

/-- β2 reshape for `churchOr`. -/
theorem churchOrPartialBody_subst_b (selectorArg secondArg : RawTerm 0) :
    RawTerm.subst0
      (appCell (appCell (appCell
        (RawTerm.weaken selectorArg)
        (RawTerm.weaken branchMotivePlaceholder))
        (RawTerm.weaken churchTrueLambda))
        RawTerm.newestVar) secondArg
      = appCell (appCell (appCell selectorArg branchMotivePlaceholder) churchTrueLambda) secondArg := by
  dsimp only [RawTerm.subst0]
  show appCell (appCell (appCell
      (RawTerm.subst (RawTermSubst.singleton secondArg) (RawTerm.weaken selectorArg))
      (RawTerm.subst (RawTermSubst.singleton secondArg) (RawTerm.weaken branchMotivePlaceholder)))
      (RawTerm.subst (RawTermSubst.singleton secondArg) (RawTerm.weaken churchTrueLambda)))
      (RawTerm.subst (RawTermSubst.singleton secondArg) RawTerm.newestVar) = _
  rw [RawTerm.weaken_subst_singleton selectorArg secondArg,
      RawTerm.weaken_subst_singleton branchMotivePlaceholder secondArg,
      RawTerm.weaken_subst_singleton churchTrueLambda secondArg,
      show RawTerm.subst (RawTermSubst.singleton secondArg) RawTerm.newestVar = secondArg from rfl]

/-- `churchOr a b` reduces (two β-steps) to the applied selector `a P churchTrue b`. -/
theorem churchOr_reducesToApplied (selectorArg secondArg : RawTerm 0) :
    StepStar (appCell (appCell churchOrLambda selectorArg) secondArg)
      (appCell (appCell (appCell selectorArg branchMotivePlaceholder) churchTrueLambda) secondArg) := by
  have step1 : Step (appCell churchOrLambda selectorArg) (churchOrPartial selectorArg) := by
    rw [← churchOrBody_subst_a selectorArg]; exact Step.beta
  have step2 : Step (appCell (churchOrPartial selectorArg) secondArg)
      (appCell (appCell (appCell selectorArg branchMotivePlaceholder) churchTrueLambda) secondArg) := by
    rw [← churchOrPartialBody_subst_b selectorArg secondArg]; exact Step.beta
  exact StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        (.childCons secondArg .childNil) step1))
    (StepStar.trans step2 (StepStar.refl _))

/-- ★ `or true _ ↝* true` for ARBITRARY (symbolic) second argument — `churchTrue` selects its first candidate
(the CONCRETE `churchTrue`), so the selection resolves for any second argument.  OR is left-strict on `true`. -/
theorem churchOr_trueAnything (secondArg : RawTerm 0) :
    StepStar (appCell (appCell churchOrLambda churchTrueLambda) secondArg) churchTrueLambda :=
  StepStar.trans_compose (churchOr_reducesToApplied churchTrueLambda secondArg)
    (churchTrueSelectsConcreteTrue branchMotivePlaceholder secondArg)

/-- ★ `or false b ↝* b` for ARBITRARY (symbolic) second argument — `churchFalse` selects its second candidate
(the bound `b`), whose innermost-variable resolution handles the symbolic `b`.  Together with
`churchOr_trueAnything`, OR is FULLY determined symbolically by its first argument. -/
theorem churchOr_falseAnything (secondArg : RawTerm 0) :
    StepStar (appCell (appCell churchOrLambda churchFalseLambda) secondArg) secondArg :=
  StepStar.trans_compose (churchOr_reducesToApplied churchFalseLambda secondArg)
    (churchFalseSelectsElse branchMotivePlaceholder churchTrueLambda secondArg)

-- ========== De Morgan (truth-table inputs) ==========

/-- ★ De Morgan at (true, true): `¬(true ∧ true) =Conv (¬true) ∨ (¬true)` — both compute to `false`. -/
theorem deMorgan_and_trueTrue :
    Conv (appCell churchNotLambda (appCell (appCell churchAndLambda churchTrueLambda) churchTrueLambda))
      (appCell (appCell churchOrLambda (appCell churchNotLambda churchTrueLambda))
        (appCell churchNotLambda churchTrueLambda)) :=
  Conv.trans
    (Conv.trans (Conv.app_cong (Conv.refl churchNotLambda) (Conv.fromStepStar churchAnd_trueTrue))
      (Conv.fromStepStar churchNot_negatesTrue))
    (Conv.sym
      (Conv.trans
        (Conv.app_cong (Conv.app_cong (Conv.refl churchOrLambda)
          (Conv.fromStepStar churchNot_negatesTrue)) (Conv.fromStepStar churchNot_negatesTrue))
        (Conv.fromStepStar (churchOr_falseAnything churchFalseLambda))))

/-- ★ De Morgan at (true, false): `¬(true ∧ false) =Conv (¬true) ∨ (¬false)` — both compute to `true`. -/
theorem deMorgan_and_trueFalse :
    Conv (appCell churchNotLambda (appCell (appCell churchAndLambda churchTrueLambda) churchFalseLambda))
      (appCell (appCell churchOrLambda (appCell churchNotLambda churchTrueLambda))
        (appCell churchNotLambda churchFalseLambda)) :=
  Conv.trans
    (Conv.trans (Conv.app_cong (Conv.refl churchNotLambda) (Conv.fromStepStar churchAnd_trueFalse))
      (Conv.fromStepStar churchNot_negatesFalse))
    (Conv.sym
      (Conv.trans
        (Conv.app_cong (Conv.app_cong (Conv.refl churchOrLambda)
          (Conv.fromStepStar churchNot_negatesTrue)) (Conv.fromStepStar churchNot_negatesFalse))
        (Conv.fromStepStar (churchOr_falseAnything churchTrueLambda))))

/-- ★ De Morgan at (false, true): `¬(false ∧ true) =Conv (¬false) ∨ (¬true)` — both compute to `true`. -/
theorem deMorgan_and_falseTrue :
    Conv (appCell churchNotLambda (appCell (appCell churchAndLambda churchFalseLambda) churchTrueLambda))
      (appCell (appCell churchOrLambda (appCell churchNotLambda churchFalseLambda))
        (appCell churchNotLambda churchTrueLambda)) :=
  Conv.trans
    (Conv.trans (Conv.app_cong (Conv.refl churchNotLambda)
        (Conv.fromStepStar (churchAnd_falseAnything churchTrueLambda)))
      (Conv.fromStepStar churchNot_negatesFalse))
    (Conv.sym
      (Conv.trans
        (Conv.app_cong (Conv.app_cong (Conv.refl churchOrLambda)
          (Conv.fromStepStar churchNot_negatesFalse)) (Conv.fromStepStar churchNot_negatesTrue))
        (Conv.fromStepStar (churchOr_trueAnything churchFalseLambda))))

/-- ★ De Morgan at (false, false): `¬(false ∧ false) =Conv (¬false) ∨ (¬false)` — both compute to `true`. -/
theorem deMorgan_and_falseFalse :
    Conv (appCell churchNotLambda (appCell (appCell churchAndLambda churchFalseLambda) churchFalseLambda))
      (appCell (appCell churchOrLambda (appCell churchNotLambda churchFalseLambda))
        (appCell churchNotLambda churchFalseLambda)) :=
  Conv.trans
    (Conv.trans (Conv.app_cong (Conv.refl churchNotLambda)
        (Conv.fromStepStar (churchAnd_falseAnything churchFalseLambda)))
      (Conv.fromStepStar churchNot_negatesFalse))
    (Conv.sym
      (Conv.trans
        (Conv.app_cong (Conv.app_cong (Conv.refl churchOrLambda)
          (Conv.fromStepStar churchNot_negatesFalse)) (Conv.fromStepStar churchNot_negatesFalse))
        (Conv.fromStepStar (churchOr_trueAnything churchTrueLambda))))

-- ========== discrimination (non-vacuity) ==========

/-- `and true true` and `and true false` are non-convertible — `∧` genuinely distinguishes its inputs. -/
theorem churchAnd_discriminates :
    ¬ Conv (appCell (appCell churchAndLambda churchTrueLambda) churchTrueLambda)
        (appCell (appCell churchAndLambda churchTrueLambda) churchFalseLambda) := by
  intro convertibility
  exact churchTrue_notConvertible_churchFalse
    (Conv.trans (Conv.sym (Conv.fromStepStar churchAnd_trueTrue))
      (Conv.trans convertibility (Conv.fromStepStar churchAnd_trueFalse)))

end FX1Poly.Typed
