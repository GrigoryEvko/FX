import FX1Poly.Typed.TypedChurchBooleans

/-! # Foundation/PolyCell/Typed/TypedChurchNegation
    — the term model COMPUTES Boolean negation, and negation is an INVOLUTION

`TypedChurchBooleans` exhibited the Church booleans concretely: `churchTrue` / `churchFalse` are typed at
`Π(A:Type@0). Π(t:A). Π(f:A). A`, they are strongly normalizing, their β-selection picks the right branch, and
they are non-convertible.  This file closes the arc on the BOOLEAN ALGEBRA side: the Π-fragment not only
encodes the booleans but COMPUTES the boolean operations on them, and the computation satisfies the boolean
laws.  We mechanize the first and most fundamental operation — negation — and prove it is an involution.

The Church-encoded negation flips the two selection candidates:

  `churchNot = λb. b A churchFalse churchTrue`

Given a Church boolean `b`, `churchNot` applies it as a selector over the FLIPPED pair `(churchFalse,
churchTrue)`: where `b` would have selected its first candidate it now yields `churchFalse`, and where it would
have selected its second it now yields `churchTrue`.  The type argument `A` (here a placeholder universe code)
is never inspected by the reduction — these are purely operational `StepStar` / `Conv` facts.

Three headline results:

  * `churchNot_negatesTrue`  : `churchNot churchTrue  ↝* churchFalse` — negation of `true` computes to `false`;
  * `churchNot_negatesFalse` : `churchNot churchFalse ↝* churchTrue`  — negation of `false` computes to `true`;
  * `churchNot_doubleNegatesTrue` / `churchNot_doubleNegatesFalse` : `churchNot (churchNot b) =Conv b` — the
    DOUBLE-NEGATION INVOLUTION, the defining law of Boolean complement, holds up to definitional equality.

Each negation runs as a single outer β-step — reshaped through the `subst0`/`weaken` cancellation
`churchNotBody_substitutesToFlippedApplication` — followed by the concrete-branch selection.  The involution
then composes the two negations: `churchNot (churchNot true) =Conv churchNot false =Conv true` via
`Conv.app_cong` (congruence of conversion under application) and `Conv.fromStepStar` (a reduction sequence is a
conversion) and `Conv.trans`.  It parallels the session-duality involution `dual (dual S) = S`: a second
dimension where a kernel-level operation is its own inverse, established here by COMPUTATION rather than by a
structural duality table.

A de Bruijn subtlety governs why both selection helpers below close cleanly.  `churchTrue`'s body is the
NON-innermost variable (`var 1`), whose resolution threads the `subst0` lifting fold and stays stuck on a
SYMBOLIC branch (the wall flagged in `TypedChurchBooleans` for symbolic branches).  But here every branch is a
CONCRETE closed term (`churchFalseLambda` / `churchTrueLambda`), so the fold computes through and even the
`var 1` selection reduces fully — the symbolic wall does not bite the concrete negation.

Zero-axiom: the selections are `Step.cong`/`Step.beta` chains closing by `StepStar.refl` (definitional); the
`subst0` reshape is `weaken_subst_singleton` cancellations plus a `var`-lookup `rfl`; the involution is the
conversion-congruence package from `ConvCongruence`.  No `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, or `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Universe
open StepStar

/-- The placeholder result type `Type@0` supplied to the bound boolean inside `churchNot`.  A Church boolean's
first argument is the common type of its two branches; the negation's selection never inspects it, so any closed
type code serves — this is the operational stand-in. -/
abbrev branchMotivePlaceholder : RawTerm 0 := universeCodeCell LevelExpr.lzero UniverseFlag.standard

/-- ★ The Church-encoded Boolean negation `churchNot = λb. b A churchFalse churchTrue`.  It applies the bound
boolean `b` (de Bruijn `var 0`) as a selector over the FLIPPED candidate pair `(churchFalse, churchTrue)`,
so the branch `b` would have selected is replaced by the opposite Church boolean.  The branches are weakened
under the `λb.` binder. -/
abbrev churchNotLambda : RawTerm 0 :=
  lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
    (appCell (appCell (appCell RawTerm.newestVar (RawTerm.weaken branchMotivePlaceholder))
      (RawTerm.weaken churchFalseLambda)) (RawTerm.weaken churchTrueLambda))

/-- The β-contractum reshape: substituting `boolArg` for the bound `var 0` in the body of `churchNot` collapses
each weakened constant back to itself (`weaken_subst_singleton`) and resolves the head `var 0` to `boolArg`,
yielding `boolArg` applied to the placeholder type and the flipped branches.  This is the bridge from the raw
β-step to the selection lemmas below. -/
theorem churchNotBody_substitutesToFlippedApplication (boolArg : RawTerm 0) :
    RawTerm.subst0 (appCell (appCell (appCell RawTerm.newestVar (RawTerm.weaken branchMotivePlaceholder))
      (RawTerm.weaken churchFalseLambda)) (RawTerm.weaken churchTrueLambda)) boolArg
      = appCell (appCell (appCell boolArg branchMotivePlaceholder) churchFalseLambda) churchTrueLambda := by
  dsimp only [RawTerm.subst0]
  show appCell (appCell (appCell (RawTerm.subst (RawTermSubst.singleton boolArg) RawTerm.newestVar)
      (RawTerm.subst (RawTermSubst.singleton boolArg) (RawTerm.weaken branchMotivePlaceholder)))
      (RawTerm.subst (RawTermSubst.singleton boolArg) (RawTerm.weaken churchFalseLambda)))
      (RawTerm.subst (RawTermSubst.singleton boolArg) (RawTerm.weaken churchTrueLambda))
    = appCell (appCell (appCell boolArg branchMotivePlaceholder) churchFalseLambda) churchTrueLambda
  rw [RawTerm.weaken_subst_singleton branchMotivePlaceholder boolArg,
      RawTerm.weaken_subst_singleton churchFalseLambda boolArg,
      RawTerm.weaken_subst_singleton churchTrueLambda boolArg,
      show RawTerm.subst (RawTermSubst.singleton boolArg) RawTerm.newestVar = boolArg from rfl]

/-- `churchTrue` applied to the placeholder type and the FLIPPED branches `(churchFalse, churchTrue)` selects
its FIRST candidate, the `then`-branch, which is now `churchFalse` — three β-steps (two under the application's
function-position congruence, then the outer β), closing by `StepStar.refl`.  The branches are concrete closed
terms, so the non-innermost `var 1` body resolves fully through the `subst0` fold. -/
theorem churchTrueOnFlippedBranches_reducesToFalse :
    StepStar
      (appCell (appCell (appCell churchTrueLambda branchMotivePlaceholder) churchFalseLambda) churchTrueLambda)
      churchFalseLambda :=
  StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        ((.childCons churchTrueLambda .childNil) : RawTermChildren [0] 0)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
            ((.childCons churchFalseLambda .childNil) : RawTermChildren [0] 0)
            Step.beta))))
    (StepStar.trans
      (Step.cong .gen_app ()
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
          ((.childCons churchTrueLambda .childNil) : RawTermChildren [0] 0)
          Step.beta))
      (StepStar.trans Step.beta (StepStar.refl _)))

/-- `churchFalse` applied to the same arguments selects its SECOND candidate, the `else`-branch, which is now
`churchTrue` — the innermost `var 0` body substitutes directly.  Together with
`churchTrueOnFlippedBranches_reducesToFalse`, the flipped selection realizes the negation table. -/
theorem churchFalseOnFlippedBranches_reducesToTrue :
    StepStar
      (appCell (appCell (appCell churchFalseLambda branchMotivePlaceholder) churchFalseLambda) churchTrueLambda)
      churchTrueLambda :=
  StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        ((.childCons churchTrueLambda .childNil) : RawTermChildren [0] 0)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
            ((.childCons churchFalseLambda .childNil) : RawTermChildren [0] 0)
            Step.beta))))
    (StepStar.trans
      (Step.cong .gen_app ()
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
          ((.childCons churchTrueLambda .childNil) : RawTermChildren [0] 0)
          Step.beta))
      (StepStar.trans Step.beta (StepStar.refl _)))

/-- ★ Negation of `true` COMPUTES to `false`: `churchNot churchTrue ↝* churchFalse`.  One outer β-step
(reshaped through `churchNotBody_substitutesToFlippedApplication`) feeds `churchTrue` into the flipped selector,
which then picks `churchFalse`. -/
theorem churchNot_negatesTrue :
    StepStar (appCell churchNotLambda churchTrueLambda) churchFalseLambda :=
  StepStar.trans
    (by rw [← churchNotBody_substitutesToFlippedApplication churchTrueLambda]; exact Step.beta)
    churchTrueOnFlippedBranches_reducesToFalse

/-- ★ Negation of `false` COMPUTES to `true`: `churchNot churchFalse ↝* churchTrue`. -/
theorem churchNot_negatesFalse :
    StepStar (appCell churchNotLambda churchFalseLambda) churchTrueLambda :=
  StepStar.trans
    (by rw [← churchNotBody_substitutesToFlippedApplication churchFalseLambda]; exact Step.beta)
    churchFalseOnFlippedBranches_reducesToTrue

/-- ★ The DOUBLE-NEGATION INVOLUTION on `true`: `churchNot (churchNot churchTrue) =Conv churchTrue`.  Reducing
the inner negation (`churchNot churchTrue ↝* churchFalse`) under the application congruence `Conv.app_cong`
rewrites the outer call to `churchNot churchFalse`, which then reduces to `churchTrue` — so `¬¬true = true` up
to definitional equality.  The complement law established by COMPUTATION, parallel to the session-duality
involution `dual (dual S) = S`. -/
theorem churchNot_doubleNegatesTrue :
    Conv (appCell churchNotLambda (appCell churchNotLambda churchTrueLambda)) churchTrueLambda :=
  Conv.trans
    (Conv.app_cong (Conv.refl churchNotLambda) (Conv.fromStepStar churchNot_negatesTrue))
    (Conv.fromStepStar churchNot_negatesFalse)

/-- ★ The DOUBLE-NEGATION INVOLUTION on `false`: `churchNot (churchNot churchFalse) =Conv churchFalse`.  The
`false` companion of `churchNot_doubleNegatesTrue`, completing `¬¬b = b` on both Church booleans. -/
theorem churchNot_doubleNegatesFalse :
    Conv (appCell churchNotLambda (appCell churchNotLambda churchFalseLambda)) churchFalseLambda :=
  Conv.trans
    (Conv.app_cong (Conv.refl churchNotLambda) (Conv.fromStepStar churchNot_negatesFalse))
    (Conv.fromStepStar churchNot_negatesTrue)

end FX1Poly.Typed
