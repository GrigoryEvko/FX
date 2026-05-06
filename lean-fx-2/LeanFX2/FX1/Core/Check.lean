prelude
import LeanFX2.FX1.Core.HasType

/-! # FX1/Core/Check

Root status: Root-FX1 checker slice.

This module adds the first executable checker slice for the minimal FX1
lambda-Pi core.  It is intentionally incomplete:

* variables, sorts, Pi types, lambdas, and applications are checked;
* constants return `none` until executable name equality has a proved
  zero-axiom soundness theorem;
* equality used by application checking rejects constants and level parameters.

The incompleteness is deliberate.  The executable checker is not part of the
trusted FX1 root until `infer?_sound` / `check_sound` land.  Accepting fewer
programs is the conservative direction; accepting constants before name
equality is proved would widen the TCB.
-/

namespace LeanFX2.FX1

namespace CheckBool

/-- If a Boolean conjunction is true, its left side is true. -/
theorem and_true_left {leftBool rightBool : Bool}
    (andIsTrue : Eq (Bool.and leftBool rightBool) true) :
    Eq leftBool true :=
  match leftBool, rightBool with
  | true, true => Eq.refl true

/-- If a Boolean conjunction is true, its right side is true. -/
theorem and_true_right {leftBool rightBool : Bool}
    (andIsTrue : Eq (Bool.and leftBool rightBool) true) :
    Eq rightBool true :=
  match leftBool, rightBool with
  | true, true => Eq.refl true

end CheckBool

namespace Level

/-- Checker equality for the FX1 root universe fragment.

`param` is rejected for now: comparing parameter names would require a proved
sound executable name equality, and `Name.str` contains host `String`. -/
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
  | Level.param _, Level.param _ => false

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
          (CheckBool.and_true_left equalityIsTrue)
      let rightEquality :=
        checkerBeq_sound
          leftRightLevel
          rightRightLevel
          (CheckBool.and_true_right equalityIsTrue)
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
          (CheckBool.and_true_left equalityIsTrue)
      let rightEquality :=
        checkerBeq_sound
          leftRightLevel
          rightRightLevel
          (CheckBool.and_true_right equalityIsTrue)
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
  | Level.param _, Level.param _, equalityIsTrue => nomatch equalityIsTrue

end Level

namespace Expr

/-- Soundness of `Nat.beq`, kept local to the FX1 checker so no host
decidable equality theorem becomes part of the root story. -/
theorem natBeq_sound
    : forall leftIndex rightIndex : Nat,
      Eq (Nat.beq leftIndex rightIndex) true ->
      Eq leftIndex rightIndex
  | Nat.zero, Nat.zero, _ => Eq.refl Nat.zero
  | Nat.zero, Nat.succ _, equalityIsTrue => nomatch equalityIsTrue
  | Nat.succ _, Nat.zero, equalityIsTrue => nomatch equalityIsTrue
  | Nat.succ leftSmallerIndex, Nat.succ rightSmallerIndex, equalityIsTrue =>
      congrArg Nat.succ
        (natBeq_sound leftSmallerIndex rightSmallerIndex equalityIsTrue)

/-- Checker equality for the initial FX1 expression fragment.

Constants are rejected for now, because `Name.str` uses host `String` and the
checker does not yet have a zero-axiom proof that executable name equality
implies propositional equality. -/
def checkerBeq : Expr -> Expr -> Bool
  | Expr.bvar leftIndex, Expr.bvar rightIndex =>
      Nat.beq leftIndex rightIndex
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
  | Expr.const _, Expr.const _ => false
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
        (natBeq_sound leftIndex rightIndex equalityIsTrue)
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
  | Expr.const _, Expr.const _, equalityIsTrue => nomatch equalityIsTrue
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
          (CheckBool.and_true_left equalityIsTrue))
        (checkerBeq_sound
          leftBody
          rightBody
          (CheckBool.and_true_right equalityIsTrue))
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
          (CheckBool.and_true_left equalityIsTrue))
        (checkerBeq_sound
          leftBody
          rightBody
          (CheckBool.and_true_right equalityIsTrue))
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
          (CheckBool.and_true_left equalityIsTrue))
        (checkerBeq_sound
          leftArgument
          rightArgument
          (CheckBool.and_true_right equalityIsTrue))

end Expr

namespace Context

/-- A successful executable lookup paired with the relational lookup witness
it justifies. -/
structure LookupTypeResult (entries : List Expr) (index : Nat) : Type where
  typeExpr : Expr
  typeAtIndex : Context.HasTypeAt { entries := entries } index typeExpr

/-- Witness-producing lookup for the shifted de Bruijn context lookup used by
the checker. -/
def lookupTypeResultInEntries? :
    (entries : List Expr) -> (index : Nat) ->
      Option (LookupTypeResult entries index)
  | List.nil, _ => none
  | List.cons newestTypeExpr remainingEntries, Nat.zero =>
      some {
        typeExpr := Expr.weaken newestTypeExpr
        typeAtIndex :=
          Context.HasTypeAt.newest
            { entries := remainingEntries }
            newestTypeExpr
      }
  | List.cons newestTypeExpr remainingEntries, Nat.succ remainingIndex =>
      match lookupTypeResultInEntries? remainingEntries remainingIndex with
      | some olderLookup =>
          some {
            typeExpr := Expr.weaken olderLookup.typeExpr
            typeAtIndex :=
              Context.HasTypeAt.older
                newestTypeExpr
                olderLookup.typeAtIndex
          }
      | none => none

/-- Lookup a de Bruijn index and return the binder type shifted into the
current context, matching `Context.HasTypeAt`. -/
def lookupTypeInEntries? : List Expr -> Nat -> Option Expr
  | entries, index =>
      match lookupTypeResultInEntries? entries index with
      | some lookupResult => some lookupResult.typeExpr
      | none => none

/-- Context-level wrapper for `lookupTypeInEntries?`. -/
def lookupType? (context : Context) (index : Nat) : Option Expr :=
  Context.lookupTypeInEntries? context.entries index

end Context

namespace Expr

/-- Infer the type of an FX1 expression in the initial no-constant checker
fragment. -/
def infer? (environment : Environment) (context : Context) : Expr -> Option Expr
  | Expr.bvar index => Context.lookupType? context index
  | Expr.sort sortLevel => some (Expr.sort (Level.succ sortLevel))
  | Expr.const _ => none
  | Expr.pi domainExpr bodyExpr =>
      match Expr.infer? environment context domainExpr with
      | some (Expr.sort domainLevel) =>
          match Expr.infer?
              environment
              (Context.extend context domainExpr)
              bodyExpr with
          | some (Expr.sort bodyLevel) =>
              some (Expr.sort (Level.max domainLevel bodyLevel))
          | some (Expr.bvar _) => none
          | some (Expr.const _) => none
          | some (Expr.pi _ _) => none
          | some (Expr.lam _ _) => none
          | some (Expr.app _ _) => none
          | none => none
      | some (Expr.bvar _) => none
      | some (Expr.const _) => none
      | some (Expr.pi _ _) => none
      | some (Expr.lam _ _) => none
      | some (Expr.app _ _) => none
      | none => none
  | Expr.lam domainExpr bodyExpr =>
      match Expr.infer? environment context domainExpr with
      | some (Expr.sort _) =>
          match Expr.infer?
              environment
              (Context.extend context domainExpr)
              bodyExpr with
          | some bodyTypeExpr => some (Expr.pi domainExpr bodyTypeExpr)
          | none => none
      | some (Expr.bvar _) => none
      | some (Expr.const _) => none
      | some (Expr.pi _ _) => none
      | some (Expr.lam _ _) => none
      | some (Expr.app _ _) => none
      | none => none
  | Expr.app functionExpr argumentExpr =>
      match Expr.infer? environment context functionExpr with
      | some (Expr.pi domainExpr bodyTypeExpr) =>
          match Expr.infer? environment context argumentExpr with
          | some argumentTypeExpr =>
              match Expr.checkerBeq argumentTypeExpr domainExpr with
              | true => some (Expr.subst0 argumentExpr bodyTypeExpr)
              | false => none
          | none => none
      | some (Expr.bvar _) => none
      | some (Expr.sort _) => none
      | some (Expr.const _) => none
      | some (Expr.lam _ _) => none
      | some (Expr.app _ _) => none
      | none => none

/-- Check an expression against an expected type using checker equality. -/
def check? (environment : Environment) (context : Context)
    (expression expectedTypeExpr : Expr) : Bool :=
  match Expr.infer? environment context expression with
  | some inferredTypeExpr =>
      Expr.checkerBeq inferredTypeExpr expectedTypeExpr
  | none => false

end Expr

end LeanFX2.FX1
