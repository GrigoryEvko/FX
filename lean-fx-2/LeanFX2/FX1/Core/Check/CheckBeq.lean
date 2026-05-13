prelude
import LeanFX2.FX1.Core.HasType

/-! # LeanFX2.FX1.Core.Check.CheckBeq

FX1 checker-level equality on `Option`, `Level`, and `Expr` plus their
soundness lemmas.  Foundation for the rest of the checker pipeline.

## Root status

Root-FX1 checker beq slice. -/

namespace LeanFX2.FX1

namespace CheckOption

/-- Constructor injectivity for `Option.some`, kept local to avoid depending
on a host library theorem in the FX1 checker story. -/
theorem some_injective {elementType : Type}
    {leftValue rightValue : elementType}
    (someValuesEqual : Eq (some leftValue) (some rightValue)) :
    Eq leftValue rightValue :=
  match someValuesEqual with
  | Eq.refl _ => Eq.refl leftValue

end CheckOption

namespace Level

/-- Checker equality for the FX1 root universe fragment.

Universe parameters are compared with FX1-native name equality, not host
`String` equality. -/
def checkerBeq : Level -> Level -> Bool
  | Level.zero, Level.zero => true
  | Level.zero, Level.succ _ => false
  | Level.zero, Level.max _ _ => false
  | Level.zero, Level.imax _ _ => false
  | Level.zero, Level.param _ => false
  | Level.succ _, Level.zero => false
  | Level.succ leftBaseLevel, Level.succ rightBaseLevel =>
      Level.checkerBeq leftBaseLevel rightBaseLevel
  | Level.succ _, Level.max _ _ => false
  | Level.succ _, Level.imax _ _ => false
  | Level.succ _, Level.param _ => false
  | Level.max _ _, Level.zero => false
  | Level.max _ _, Level.succ _ => false
  | Level.max leftLeftLevel leftRightLevel,
      Level.max rightLeftLevel rightRightLevel =>
      Bool.and
        (Level.checkerBeq leftLeftLevel rightLeftLevel)
        (Level.checkerBeq leftRightLevel rightRightLevel)
  | Level.max _ _, Level.imax _ _ => false
  | Level.max _ _, Level.param _ => false
  | Level.imax _ _, Level.zero => false
  | Level.imax _ _, Level.succ _ => false
  | Level.imax _ _, Level.max _ _ => false
  | Level.imax leftLeftLevel leftRightLevel,
      Level.imax rightLeftLevel rightRightLevel =>
      Bool.and
        (Level.checkerBeq leftLeftLevel rightLeftLevel)
        (Level.checkerBeq leftRightLevel rightRightLevel)
  | Level.imax _ _, Level.param _ => false
  | Level.param _, Level.zero => false
  | Level.param _, Level.succ _ => false
  | Level.param _, Level.max _ _ => false
  | Level.param _, Level.imax _ _ => false
  | Level.param leftName, Level.param rightName =>
      Name.beq leftName rightName

/-- Soundness of FX1 checker-level universe comparison. -/
theorem checkerBeq_sound
    : forall leftLevel rightLevel : Level,
      Eq (Level.checkerBeq leftLevel rightLevel) true ->
      Eq leftLevel rightLevel
  | Level.zero, Level.zero, _ => Eq.refl Level.zero
  | Level.zero, Level.succ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.zero, Level.max _ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.zero, Level.imax _ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.zero, Level.param _, equalityIsTrue => nomatch equalityIsTrue
  | Level.succ _, Level.zero, equalityIsTrue => nomatch equalityIsTrue
  | Level.succ leftBaseLevel, Level.succ rightBaseLevel, equalityIsTrue =>
      congrArg Level.succ
        (checkerBeq_sound leftBaseLevel rightBaseLevel equalityIsTrue)
  | Level.succ _, Level.max _ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.succ _, Level.imax _ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.succ _, Level.param _, equalityIsTrue => nomatch equalityIsTrue
  | Level.max _ _, Level.zero, equalityIsTrue => nomatch equalityIsTrue
  | Level.max _ _, Level.succ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.max leftLeftLevel leftRightLevel,
      Level.max rightLeftLevel rightRightLevel,
      equalityIsTrue =>
      let leftEquality :=
        checkerBeq_sound
          leftLeftLevel
          rightLeftLevel
          (Boolean.and_true_left equalityIsTrue)
      let rightEquality :=
        checkerBeq_sound
          leftRightLevel
          rightRightLevel
          (Boolean.and_true_right equalityIsTrue)
      Eq.trans
        (congrArg
          (fun rewrittenLeftLevel =>
            Level.max rewrittenLeftLevel leftRightLevel)
          leftEquality)
        (congrArg
          (fun rewrittenRightLevel =>
            Level.max rightLeftLevel rewrittenRightLevel)
          rightEquality)
  | Level.max _ _, Level.imax _ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.max _ _, Level.param _, equalityIsTrue => nomatch equalityIsTrue
  | Level.imax _ _, Level.zero, equalityIsTrue => nomatch equalityIsTrue
  | Level.imax _ _, Level.succ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.imax _ _, Level.max _ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.imax leftLeftLevel leftRightLevel,
      Level.imax rightLeftLevel rightRightLevel,
      equalityIsTrue =>
      let leftEquality :=
        checkerBeq_sound
          leftLeftLevel
          rightLeftLevel
          (Boolean.and_true_left equalityIsTrue)
      let rightEquality :=
        checkerBeq_sound
          leftRightLevel
          rightRightLevel
          (Boolean.and_true_right equalityIsTrue)
      Eq.trans
        (congrArg
          (fun rewrittenLeftLevel =>
            Level.imax rewrittenLeftLevel leftRightLevel)
          leftEquality)
        (congrArg
          (fun rewrittenRightLevel =>
            Level.imax rightLeftLevel rewrittenRightLevel)
          rightEquality)
  | Level.imax _ _, Level.param _, equalityIsTrue => nomatch equalityIsTrue
  | Level.param _, Level.zero, equalityIsTrue => nomatch equalityIsTrue
  | Level.param _, Level.succ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.param _, Level.max _ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.param _, Level.imax _ _, equalityIsTrue => nomatch equalityIsTrue
  | Level.param leftName, Level.param rightName, equalityIsTrue =>
      congrArg Level.param
        (Name.beq_sound leftName rightName equalityIsTrue)

end Level

namespace Expr

/-- Checker equality for the initial FX1 expression fragment. -/
def checkerBeq : Expr -> Expr -> Bool
  | Expr.bvar leftIndex, Expr.bvar rightIndex =>
      NaturalNumber.beq leftIndex rightIndex
  | Expr.bvar _, Expr.sort _ => false
  | Expr.bvar _, Expr.const _ => false
  | Expr.bvar _, Expr.pi _ _ => false
  | Expr.bvar _, Expr.lam _ _ => false
  | Expr.bvar _, Expr.app _ _ => false
  | Expr.sort _, Expr.bvar _ => false
  | Expr.sort leftLevel, Expr.sort rightLevel =>
      Level.checkerBeq leftLevel rightLevel
  | Expr.sort _, Expr.const _ => false
  | Expr.sort _, Expr.pi _ _ => false
  | Expr.sort _, Expr.lam _ _ => false
  | Expr.sort _, Expr.app _ _ => false
  | Expr.const _, Expr.bvar _ => false
  | Expr.const _, Expr.sort _ => false
  | Expr.const leftName, Expr.const rightName =>
      Name.beq leftName rightName
  | Expr.const _, Expr.pi _ _ => false
  | Expr.const _, Expr.lam _ _ => false
  | Expr.const _, Expr.app _ _ => false
  | Expr.pi _ _, Expr.bvar _ => false
  | Expr.pi _ _, Expr.sort _ => false
  | Expr.pi _ _, Expr.const _ => false
  | Expr.pi leftDomain leftBody, Expr.pi rightDomain rightBody =>
      Bool.and
        (Expr.checkerBeq leftDomain rightDomain)
        (Expr.checkerBeq leftBody rightBody)
  | Expr.pi _ _, Expr.lam _ _ => false
  | Expr.pi _ _, Expr.app _ _ => false
  | Expr.lam _ _, Expr.bvar _ => false
  | Expr.lam _ _, Expr.sort _ => false
  | Expr.lam _ _, Expr.const _ => false
  | Expr.lam _ _, Expr.pi _ _ => false
  | Expr.lam leftDomain leftBody, Expr.lam rightDomain rightBody =>
      Bool.and
        (Expr.checkerBeq leftDomain rightDomain)
        (Expr.checkerBeq leftBody rightBody)
  | Expr.lam _ _, Expr.app _ _ => false
  | Expr.app _ _, Expr.bvar _ => false
  | Expr.app _ _, Expr.sort _ => false
  | Expr.app _ _, Expr.const _ => false
  | Expr.app _ _, Expr.pi _ _ => false
  | Expr.app _ _, Expr.lam _ _ => false
  | Expr.app leftFunction leftArgument,
      Expr.app rightFunction rightArgument =>
      Bool.and
        (Expr.checkerBeq leftFunction rightFunction)
        (Expr.checkerBeq leftArgument rightArgument)

/-- Soundness of checker-level expression comparison. -/
theorem checkerBeq_sound
    : forall leftExpr rightExpr : Expr,
      Eq (Expr.checkerBeq leftExpr rightExpr) true ->
      Eq leftExpr rightExpr
  | Expr.bvar leftIndex, Expr.bvar rightIndex, equalityIsTrue =>
      congrArg Expr.bvar
        (NaturalNumber.beq_sound leftIndex rightIndex equalityIsTrue)
  | Expr.bvar _, Expr.sort _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.bvar _, Expr.const _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.bvar _, Expr.pi _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.bvar _, Expr.lam _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.bvar _, Expr.app _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.sort _, Expr.bvar _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.sort leftLevel, Expr.sort rightLevel, equalityIsTrue =>
      congrArg Expr.sort
        (Level.checkerBeq_sound leftLevel rightLevel equalityIsTrue)
  | Expr.sort _, Expr.const _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.sort _, Expr.pi _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.sort _, Expr.lam _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.sort _, Expr.app _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.const _, Expr.bvar _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.const _, Expr.sort _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.const leftName, Expr.const rightName, equalityIsTrue =>
      congrArg Expr.const
        (Name.beq_sound leftName rightName equalityIsTrue)
  | Expr.const _, Expr.pi _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.const _, Expr.lam _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.const _, Expr.app _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.pi _ _, Expr.bvar _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.pi _ _, Expr.sort _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.pi _ _, Expr.const _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.pi leftDomain leftBody, Expr.pi rightDomain rightBody,
      equalityIsTrue =>
      Expr.pi_congr
        (checkerBeq_sound
          leftDomain
          rightDomain
          (Boolean.and_true_left equalityIsTrue))
        (checkerBeq_sound
          leftBody
          rightBody
          (Boolean.and_true_right equalityIsTrue))
  | Expr.pi _ _, Expr.lam _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.pi _ _, Expr.app _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.lam _ _, Expr.bvar _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.lam _ _, Expr.sort _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.lam _ _, Expr.const _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.lam _ _, Expr.pi _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.lam leftDomain leftBody, Expr.lam rightDomain rightBody,
      equalityIsTrue =>
      Expr.lam_congr
        (checkerBeq_sound
          leftDomain
          rightDomain
          (Boolean.and_true_left equalityIsTrue))
        (checkerBeq_sound
          leftBody
          rightBody
          (Boolean.and_true_right equalityIsTrue))
  | Expr.lam _ _, Expr.app _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.app _ _, Expr.bvar _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.app _ _, Expr.sort _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.app _ _, Expr.const _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.app _ _, Expr.pi _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.app _ _, Expr.lam _ _, equalityIsTrue => nomatch equalityIsTrue
  | Expr.app leftFunction leftArgument,
      Expr.app rightFunction rightArgument,
      equalityIsTrue =>
      Expr.app_congr
        (checkerBeq_sound
          leftFunction
          rightFunction
          (Boolean.and_true_left equalityIsTrue))
        (checkerBeq_sound
          leftArgument
          rightArgument
          (Boolean.and_true_right equalityIsTrue))

end Expr

end LeanFX2.FX1
