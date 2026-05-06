import LeanFX2.FX1Bridge.Unit

/-! # FX1Bridge/Interval

Root status: Bridge.

Closed cubical-interval bridge fragment.  This stages the rich interval type
and its two endpoints as object-level FX1 declarations, then proves that the
empty-context rich `interval0` and `interval1` terms encode to well-typed FX1
constants.

The staged declarations are `axiomDecl` placeholders.  This is Bridge evidence
only; it does not claim the cubical interval is native Root-FX1 content.
-/

namespace LeanFX2
namespace FX1Bridge

/-- Native atom id used for the staged FX1 interval type name. -/
def intervalTypeAtomId : Nat := 13

/-- Native atom id used for the staged FX1 interval zero endpoint name. -/
def interval0AtomId : Nat := 14

/-- Native atom id used for the staged FX1 interval one endpoint name. -/
def interval1AtomId : Nat := 15

/-- Native atom id used for the staged FX1 interval negation operation name. -/
def intervalOppAtomId : Nat := 16

/-- Native atom id used for the staged FX1 interval meet operation name. -/
def intervalMeetAtomId : Nat := 17

/-- Native atom id used for the staged FX1 interval join operation name. -/
def intervalJoinAtomId : Nat := 18

/-- FX1 name for the rich interval type constant. -/
def intervalTypeName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous intervalTypeAtomId

/-- FX1 name for the rich interval zero endpoint. -/
def interval0Name : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous interval0AtomId

/-- FX1 name for the rich interval one endpoint. -/
def interval1Name : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous interval1AtomId

/-- FX1 name for the rich interval negation operation. -/
def intervalOppName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous intervalOppAtomId

/-- FX1 name for the rich interval meet operation. -/
def intervalMeetName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous intervalMeetAtomId

/-- FX1 name for the rich interval join operation. -/
def intervalJoinName : FX1.Name :=
  FX1.Name.str FX1.Name.anonymous intervalJoinAtomId

/-- FX1 expression encoding the rich interval type. -/
def intervalTypeExpr : FX1.Expr :=
  FX1.Expr.const intervalTypeName

/-- FX1 expression encoding the rich interval zero endpoint. -/
def interval0Expr : FX1.Expr :=
  FX1.Expr.const interval0Name

/-- FX1 expression encoding the rich interval one endpoint. -/
def interval1Expr : FX1.Expr :=
  FX1.Expr.const interval1Name

/-- FX1 expression encoding the rich interval negation operation. -/
def intervalOppExpr : FX1.Expr :=
  FX1.Expr.const intervalOppName

/-- FX1 expression encoding the rich interval meet operation. -/
def intervalMeetExpr : FX1.Expr :=
  FX1.Expr.const intervalMeetName

/-- FX1 expression encoding the rich interval join operation. -/
def intervalJoinExpr : FX1.Expr :=
  FX1.Expr.const intervalJoinName

/-- FX1 expression encoding the rich interval negation type. -/
def intervalOppTypeExpr : FX1.Expr :=
  FX1.Expr.pi intervalTypeExpr intervalTypeExpr

/-- FX1 expression encoding a binary interval operation type. -/
def intervalBinaryOpTypeExpr : FX1.Expr :=
  FX1.Expr.pi intervalTypeExpr intervalOppTypeExpr

/-- Staged FX1 declaration for the rich interval type.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def intervalTypeDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl intervalTypeName (FX1.Expr.sort FX1.Level.zero)

/-- Staged FX1 declaration for the rich interval zero endpoint.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def interval0Declaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl interval0Name intervalTypeExpr

/-- Staged FX1 declaration for the rich interval one endpoint.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def interval1Declaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl interval1Name intervalTypeExpr

/-- Staged FX1 declaration for the rich interval negation operation.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def intervalOppDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl intervalOppName intervalOppTypeExpr

/-- Staged FX1 declaration for the rich interval meet operation.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def intervalMeetDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl intervalMeetName intervalBinaryOpTypeExpr

/-- Staged FX1 declaration for the rich interval join operation.

It is an object-level axiom placeholder, so it is not release-root evidence. -/
def intervalJoinDeclaration : FX1.Declaration :=
  FX1.Declaration.axiomDecl intervalJoinName intervalBinaryOpTypeExpr

/-- Environment after declaring the rich interval type constant. -/
def intervalTypeEnvironment : FX1.Environment :=
  FX1.Environment.extend FX1.Environment.empty intervalTypeDeclaration

/-- Environment after declaring the rich interval zero endpoint. -/
def interval0Environment : FX1.Environment :=
  FX1.Environment.extend intervalTypeEnvironment interval0Declaration

/-- Staged bridge environment for the interval endpoint fragment. -/
def intervalEnvironment : FX1.Environment :=
  FX1.Environment.extend interval0Environment interval1Declaration

/-- Staged bridge environment for the interval operation fragment. -/
def intervalOpsEnvironment : FX1.Environment :=
  FX1.Environment.extend intervalEnvironment intervalOppDeclaration

/-- Staged bridge environment after adding interval meet. -/
def intervalMeetEnvironment : FX1.Environment :=
  FX1.Environment.extend intervalOpsEnvironment intervalMeetDeclaration

/-- Staged bridge environment after adding interval meet and join. -/
def intervalLatticeEnvironment : FX1.Environment :=
  FX1.Environment.extend intervalMeetEnvironment intervalJoinDeclaration

/-- Interval-only type encoder for this bridge fragment. -/
def encodeTy_interval : FX1.Expr :=
  intervalTypeExpr

/-- Interval-zero raw-term encoder for this bridge fragment. -/
def encodeRawTerm_interval0 : FX1.Expr :=
  interval0Expr

/-- Interval-one raw-term encoder for this bridge fragment. -/
def encodeRawTerm_interval1 : FX1.Expr :=
  interval1Expr

/-- Interval-negation raw-term encoder over an already encoded child. -/
def encodeRawTerm_intervalOpp (encodedInner : FX1.Expr) : FX1.Expr :=
  FX1.Expr.app intervalOppExpr encodedInner

/-- Interval-meet raw-term encoder over already encoded children. -/
def encodeRawTerm_intervalMeet
    (encodedLeft encodedRight : FX1.Expr) :
    FX1.Expr :=
  FX1.Expr.app (FX1.Expr.app intervalMeetExpr encodedLeft) encodedRight

/-- Interval-join raw-term encoder over already encoded children. -/
def encodeRawTerm_intervalJoin
    (encodedLeft encodedRight : FX1.Expr) :
    FX1.Expr :=
  FX1.Expr.app (FX1.Expr.app intervalJoinExpr encodedLeft) encodedRight

/-- Fragment decoder for the staged rich interval type. -/
def decodeTy_interval {level scope : Nat} :
    FX1.Expr -> Option (Ty level scope) :=
  decodeConstByAtom intervalTypeAtomId (Ty.interval : Ty level scope)

/-- Fragment decoder for the staged rich interval zero endpoint. -/
def decodeRawTerm_interval0 : FX1.Expr -> Option (RawTerm 0) :=
  decodeConstByAtom interval0AtomId RawTerm.interval0

/-- Fragment decoder for the staged rich interval one endpoint. -/
def decodeRawTerm_interval1 : FX1.Expr -> Option (RawTerm 0) :=
  decodeConstByAtom interval1AtomId RawTerm.interval1

/-- Fragment recognizer for the staged interval negation function symbol. -/
def decodeRawTerm_intervalOppSymbol : FX1.Expr -> Option Unit :=
  decodeConstByAtom intervalOppAtomId ()

/-- Fragment recognizer for the staged interval meet function symbol. -/
def decodeRawTerm_intervalMeetSymbol : FX1.Expr -> Option Unit :=
  decodeConstByAtom intervalMeetAtomId ()

/-- Fragment recognizer for the staged interval join function symbol. -/
def decodeRawTerm_intervalJoinSymbol : FX1.Expr -> Option Unit :=
  decodeConstByAtom intervalJoinAtomId ()

/-- The staged interval negation function symbol decodes as itself. -/
theorem decodeRawTerm_intervalOppSymbol_intervalOppExpr :
    Eq (decodeRawTerm_intervalOppSymbol intervalOppExpr) (Option.some ()) :=
  Eq.refl (Option.some ())

/-- The staged interval meet function symbol decodes as itself. -/
theorem decodeRawTerm_intervalMeetSymbol_intervalMeetExpr :
    Eq (decodeRawTerm_intervalMeetSymbol intervalMeetExpr) (Option.some ()) :=
  Eq.refl (Option.some ())

/-- The staged interval join function symbol decodes as itself. -/
theorem decodeRawTerm_intervalJoinSymbol_intervalJoinExpr :
    Eq (decodeRawTerm_intervalJoinSymbol intervalJoinExpr) (Option.some ()) :=
  Eq.refl (Option.some ())

/-- Fragment decoder for a rich interval negation over a supplied child
decoder. -/
def decodeRawTerm_intervalOpp
    (decodeInner : FX1.Expr -> Option (RawTerm 0)) :
    FX1.Expr -> Option (RawTerm 0)
  | FX1.Expr.app functionExpr argumentExpr =>
      match decodeRawTerm_intervalOppSymbol functionExpr with
      | Option.some _ =>
          match decodeInner argumentExpr with
          | Option.some decodedInner =>
              Option.some (RawTerm.intervalOpp decodedInner)
          | Option.none => Option.none
      | Option.none => Option.none
  | FX1.Expr.bvar _ => Option.none
  | FX1.Expr.sort _ => Option.none
  | FX1.Expr.const _ => Option.none
  | FX1.Expr.pi _ _ => Option.none
  | FX1.Expr.lam _ _ => Option.none

/-- Fragment decoder for a rich interval meet over supplied child decoders. -/
def decodeRawTerm_intervalMeet
    (decodeLeft decodeRight : FX1.Expr -> Option (RawTerm 0)) :
    FX1.Expr -> Option (RawTerm 0)
  | FX1.Expr.app (FX1.Expr.app functionExpr leftExpr) rightExpr =>
      match decodeRawTerm_intervalMeetSymbol functionExpr with
      | Option.some _ =>
          match decodeLeft leftExpr with
          | Option.some decodedLeft =>
              match decodeRight rightExpr with
              | Option.some decodedRight =>
                  Option.some (RawTerm.intervalMeet decodedLeft decodedRight)
              | Option.none => Option.none
          | Option.none => Option.none
      | Option.none => Option.none
  | FX1.Expr.bvar _ => Option.none
  | FX1.Expr.sort _ => Option.none
  | FX1.Expr.const _ => Option.none
  | FX1.Expr.pi _ _ => Option.none
  | FX1.Expr.lam _ _ => Option.none
  | FX1.Expr.app (FX1.Expr.bvar _) _ => Option.none
  | FX1.Expr.app (FX1.Expr.sort _) _ => Option.none
  | FX1.Expr.app (FX1.Expr.const _) _ => Option.none
  | FX1.Expr.app (FX1.Expr.pi _ _) _ => Option.none
  | FX1.Expr.app (FX1.Expr.lam _ _) _ => Option.none

/-- Fragment decoder for a rich interval join over supplied child decoders. -/
def decodeRawTerm_intervalJoin
    (decodeLeft decodeRight : FX1.Expr -> Option (RawTerm 0)) :
    FX1.Expr -> Option (RawTerm 0)
  | FX1.Expr.app (FX1.Expr.app functionExpr leftExpr) rightExpr =>
      match decodeRawTerm_intervalJoinSymbol functionExpr with
      | Option.some _ =>
          match decodeLeft leftExpr with
          | Option.some decodedLeft =>
              match decodeRight rightExpr with
              | Option.some decodedRight =>
                  Option.some (RawTerm.intervalJoin decodedLeft decodedRight)
              | Option.none => Option.none
          | Option.none => Option.none
      | Option.none => Option.none
  | FX1.Expr.bvar _ => Option.none
  | FX1.Expr.sort _ => Option.none
  | FX1.Expr.const _ => Option.none
  | FX1.Expr.pi _ _ => Option.none
  | FX1.Expr.lam _ _ => Option.none
  | FX1.Expr.app (FX1.Expr.bvar _) _ => Option.none
  | FX1.Expr.app (FX1.Expr.sort _) _ => Option.none
  | FX1.Expr.app (FX1.Expr.const _) _ => Option.none
  | FX1.Expr.app (FX1.Expr.pi _ _) _ => Option.none
  | FX1.Expr.app (FX1.Expr.lam _ _) _ => Option.none

/-- Interval type encoding computes to the staged FX1 interval type constant. -/
theorem encodeTy_interval_eq_intervalTypeExpr :
    Eq encodeTy_interval intervalTypeExpr :=
  Eq.refl intervalTypeExpr

/-- Interval-zero raw-term encoding computes to the staged FX1 zero endpoint. -/
theorem encodeRawTerm_interval0_eq_interval0Expr :
    Eq encodeRawTerm_interval0 interval0Expr :=
  Eq.refl interval0Expr

/-- Interval-one raw-term encoding computes to the staged FX1 one endpoint. -/
theorem encodeRawTerm_interval1_eq_interval1Expr :
    Eq encodeRawTerm_interval1 interval1Expr :=
  Eq.refl interval1Expr

/-- Interval-negation raw-term encoding computes to FX1 application. -/
theorem encodeRawTerm_intervalOpp_eq_app (encodedInner : FX1.Expr) :
    Eq
      (encodeRawTerm_intervalOpp encodedInner)
      (FX1.Expr.app intervalOppExpr encodedInner) :=
  Eq.refl (FX1.Expr.app intervalOppExpr encodedInner)

/-- Interval-meet raw-term encoding computes to nested FX1 application. -/
theorem encodeRawTerm_intervalMeet_eq_app
    (encodedLeft encodedRight : FX1.Expr) :
    Eq
      (encodeRawTerm_intervalMeet encodedLeft encodedRight)
      (FX1.Expr.app
        (FX1.Expr.app intervalMeetExpr encodedLeft)
        encodedRight) :=
  Eq.refl
    (FX1.Expr.app
      (FX1.Expr.app intervalMeetExpr encodedLeft)
      encodedRight)

/-- Interval-join raw-term encoding computes to nested FX1 application. -/
theorem encodeRawTerm_intervalJoin_eq_app
    (encodedLeft encodedRight : FX1.Expr) :
    Eq
      (encodeRawTerm_intervalJoin encodedLeft encodedRight)
      (FX1.Expr.app
        (FX1.Expr.app intervalJoinExpr encodedLeft)
        encodedRight) :=
  Eq.refl
    (FX1.Expr.app
      (FX1.Expr.app intervalJoinExpr encodedLeft)
      encodedRight)

/-- The staged interval type declaration is well typed in the empty FX1
environment. -/
theorem intervalTypeDeclaration_wellTyped :
    FX1.Declaration.WellTyped
      FX1.Environment.empty
      intervalTypeDeclaration :=
  FX1.Declaration.WellTyped.axiomDecl
    (FX1.HasType.sort FX1.Context.empty FX1.Level.zero)

/-- The staged interval zero endpoint declaration is well typed after the
interval type constant is available. -/
theorem interval0Declaration_wellTyped :
    FX1.Declaration.WellTyped
      intervalTypeEnvironment
      interval0Declaration :=
  FX1.Declaration.WellTyped.axiomDecl
    (FX1.HasType.const
      (FX1.Environment.HasDeclaration.newest
        FX1.Environment.empty
        intervalTypeDeclaration))

/-- The staged interval one endpoint declaration is well typed after the
interval type and zero endpoint are available. -/
theorem interval1Declaration_wellTyped :
    FX1.Declaration.WellTyped
      interval0Environment
      interval1Declaration :=
  FX1.Declaration.WellTyped.axiomDecl
    (FX1.HasType.const
      (FX1.Environment.HasDeclaration.older
        interval0Declaration
        (FX1.Environment.HasDeclaration.newest
          FX1.Environment.empty
          intervalTypeDeclaration)))

/-- The staged interval type environment is well formed. -/
theorem intervalTypeEnvironment_wellFormed :
    FX1.Environment.WellFormed intervalTypeEnvironment :=
  FX1.Environment.WellFormed.extend
    FX1.Environment.WellFormed.empty
    (FX1.Environment.NameFresh.empty intervalTypeName)
    intervalTypeDeclaration_wellTyped

/-- The staged zero endpoint name is distinct from the interval type name. -/
theorem interval0Name_ne_intervalTypeName :
    Not (Eq interval0Name intervalTypeName) :=
  fun namesEqual =>
    let nameBeqEquality := congrArg (FX1.Name.beq interval0Name) namesEqual
    nomatch nameBeqEquality

/-- The staged one endpoint name is distinct from the interval type name. -/
theorem interval1Name_ne_intervalTypeName :
    Not (Eq interval1Name intervalTypeName) :=
  fun namesEqual =>
    let nameBeqEquality := congrArg (FX1.Name.beq interval1Name) namesEqual
    nomatch nameBeqEquality

/-- The staged one endpoint name is distinct from the zero endpoint name. -/
theorem interval1Name_ne_interval0Name :
    Not (Eq interval1Name interval0Name) :=
  fun namesEqual =>
    let nameBeqEquality := congrArg (FX1.Name.beq interval1Name) namesEqual
    nomatch nameBeqEquality

/-- The staged interval negation name is distinct from the interval type
name. -/
theorem intervalOppName_ne_intervalTypeName :
    Not (Eq intervalOppName intervalTypeName) :=
  fun namesEqual =>
    let nameBeqEquality := congrArg (FX1.Name.beq intervalOppName) namesEqual
    nomatch nameBeqEquality

/-- The staged interval negation name is distinct from the zero endpoint
name. -/
theorem intervalOppName_ne_interval0Name :
    Not (Eq intervalOppName interval0Name) :=
  fun namesEqual =>
    let nameBeqEquality := congrArg (FX1.Name.beq intervalOppName) namesEqual
    nomatch nameBeqEquality

/-- The staged interval negation name is distinct from the one endpoint
name. -/
theorem intervalOppName_ne_interval1Name :
    Not (Eq intervalOppName interval1Name) :=
  fun namesEqual =>
    let nameBeqEquality := congrArg (FX1.Name.beq intervalOppName) namesEqual
    nomatch nameBeqEquality

/-- The staged interval meet name is distinct from the interval type name. -/
theorem intervalMeetName_ne_intervalTypeName :
    Not (Eq intervalMeetName intervalTypeName) :=
  fun namesEqual =>
    let nameBeqEquality := congrArg (FX1.Name.beq intervalMeetName) namesEqual
    nomatch nameBeqEquality

/-- The staged interval meet name is distinct from the zero endpoint name. -/
theorem intervalMeetName_ne_interval0Name :
    Not (Eq intervalMeetName interval0Name) :=
  fun namesEqual =>
    let nameBeqEquality := congrArg (FX1.Name.beq intervalMeetName) namesEqual
    nomatch nameBeqEquality

/-- The staged interval meet name is distinct from the one endpoint name. -/
theorem intervalMeetName_ne_interval1Name :
    Not (Eq intervalMeetName interval1Name) :=
  fun namesEqual =>
    let nameBeqEquality := congrArg (FX1.Name.beq intervalMeetName) namesEqual
    nomatch nameBeqEquality

/-- The staged interval meet name is distinct from the interval negation
name. -/
theorem intervalMeetName_ne_intervalOppName :
    Not (Eq intervalMeetName intervalOppName) :=
  fun namesEqual =>
    let nameBeqEquality := congrArg (FX1.Name.beq intervalMeetName) namesEqual
    nomatch nameBeqEquality

/-- The staged interval join name is distinct from the interval type name. -/
theorem intervalJoinName_ne_intervalTypeName :
    Not (Eq intervalJoinName intervalTypeName) :=
  fun namesEqual =>
    let nameBeqEquality := congrArg (FX1.Name.beq intervalJoinName) namesEqual
    nomatch nameBeqEquality

/-- The staged interval join name is distinct from the zero endpoint name. -/
theorem intervalJoinName_ne_interval0Name :
    Not (Eq intervalJoinName interval0Name) :=
  fun namesEqual =>
    let nameBeqEquality := congrArg (FX1.Name.beq intervalJoinName) namesEqual
    nomatch nameBeqEquality

/-- The staged interval join name is distinct from the one endpoint name. -/
theorem intervalJoinName_ne_interval1Name :
    Not (Eq intervalJoinName interval1Name) :=
  fun namesEqual =>
    let nameBeqEquality := congrArg (FX1.Name.beq intervalJoinName) namesEqual
    nomatch nameBeqEquality

/-- The staged interval join name is distinct from the interval negation
name. -/
theorem intervalJoinName_ne_intervalOppName :
    Not (Eq intervalJoinName intervalOppName) :=
  fun namesEqual =>
    let nameBeqEquality := congrArg (FX1.Name.beq intervalJoinName) namesEqual
    nomatch nameBeqEquality

/-- The staged interval join name is distinct from the interval meet name. -/
theorem intervalJoinName_ne_intervalMeetName :
    Not (Eq intervalJoinName intervalMeetName) :=
  fun namesEqual =>
    let nameBeqEquality := congrArg (FX1.Name.beq intervalJoinName) namesEqual
    nomatch nameBeqEquality

/-- The staged zero endpoint name is fresh after the interval type
declaration. -/
theorem interval0Name_fresh :
    FX1.Environment.NameFresh intervalTypeEnvironment interval0Name :=
  FX1.Environment.NameFresh.older
    intervalTypeDeclaration
    (FX1.Environment.NameFresh.empty interval0Name)
    interval0Name_ne_intervalTypeName

/-- The staged one endpoint name is fresh after the interval type and zero
endpoint declarations. -/
theorem interval1Name_fresh :
    FX1.Environment.NameFresh interval0Environment interval1Name :=
  FX1.Environment.NameFresh.older
    interval0Declaration
    (FX1.Environment.NameFresh.older
      intervalTypeDeclaration
      (FX1.Environment.NameFresh.empty interval1Name)
      interval1Name_ne_intervalTypeName)
    interval1Name_ne_interval0Name

/-- The staged interval negation name is fresh after the interval type and
endpoint declarations. -/
theorem intervalOppName_fresh :
    FX1.Environment.NameFresh intervalEnvironment intervalOppName :=
  FX1.Environment.NameFresh.older
    interval1Declaration
    (FX1.Environment.NameFresh.older
      interval0Declaration
      (FX1.Environment.NameFresh.older
        intervalTypeDeclaration
        (FX1.Environment.NameFresh.empty intervalOppName)
        intervalOppName_ne_intervalTypeName)
      intervalOppName_ne_interval0Name)
    intervalOppName_ne_interval1Name

/-- The staged interval meet name is fresh after the interval type, endpoint,
and negation declarations. -/
theorem intervalMeetName_fresh :
    FX1.Environment.NameFresh intervalOpsEnvironment intervalMeetName :=
  FX1.Environment.NameFresh.older
    intervalOppDeclaration
    (FX1.Environment.NameFresh.older
      interval1Declaration
      (FX1.Environment.NameFresh.older
        interval0Declaration
        (FX1.Environment.NameFresh.older
          intervalTypeDeclaration
          (FX1.Environment.NameFresh.empty intervalMeetName)
          intervalMeetName_ne_intervalTypeName)
        intervalMeetName_ne_interval0Name)
      intervalMeetName_ne_interval1Name)
    intervalMeetName_ne_intervalOppName

/-- The staged interval join name is fresh after all previous interval
operation declarations. -/
theorem intervalJoinName_fresh :
    FX1.Environment.NameFresh intervalMeetEnvironment intervalJoinName :=
  FX1.Environment.NameFresh.older
    intervalMeetDeclaration
    (FX1.Environment.NameFresh.older
      intervalOppDeclaration
      (FX1.Environment.NameFresh.older
        interval1Declaration
        (FX1.Environment.NameFresh.older
          interval0Declaration
          (FX1.Environment.NameFresh.older
            intervalTypeDeclaration
            (FX1.Environment.NameFresh.empty intervalJoinName)
            intervalJoinName_ne_intervalTypeName)
          intervalJoinName_ne_interval0Name)
        intervalJoinName_ne_interval1Name)
      intervalJoinName_ne_intervalOppName)
    intervalJoinName_ne_intervalMeetName

/-- The staged interval zero endpoint environment is well formed. -/
theorem interval0Environment_wellFormed :
    FX1.Environment.WellFormed interval0Environment :=
  FX1.Environment.WellFormed.extend
    intervalTypeEnvironment_wellFormed
    interval0Name_fresh
    interval0Declaration_wellTyped

/-- The staged interval bridge environment is well formed. -/
theorem intervalEnvironment_wellFormed :
    FX1.Environment.WellFormed intervalEnvironment :=
  FX1.Environment.WellFormed.extend
    interval0Environment_wellFormed
    interval1Name_fresh
    interval1Declaration_wellTyped

/-- The staged interval type constant has sort zero in the staged interval
environment. -/
theorem intervalTypeExpr_has_sort_in_intervalEnvironment :
    FX1.HasType
      intervalEnvironment
      FX1.Context.empty
      encodeTy_interval
      (FX1.Expr.sort FX1.Level.zero) :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.older
      interval1Declaration
      (FX1.Environment.HasDeclaration.older
        interval0Declaration
        (FX1.Environment.HasDeclaration.newest
          FX1.Environment.empty
          intervalTypeDeclaration)))

/-- The staged interval type constant has sort zero under one interval binder
in the staged interval environment. -/
theorem intervalTypeExpr_has_sort_in_intervalEnvironment_with_binder :
    FX1.HasType
      intervalEnvironment
      (FX1.Context.extend FX1.Context.empty intervalTypeExpr)
      encodeTy_interval
      (FX1.Expr.sort FX1.Level.zero) :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.older
      interval1Declaration
      (FX1.Environment.HasDeclaration.older
        interval0Declaration
        (FX1.Environment.HasDeclaration.newest
          FX1.Environment.empty
          intervalTypeDeclaration)))

/-- The staged interval negation type is well formed in the staged interval
environment. -/
theorem intervalOppTypeExpr_has_sort_in_intervalEnvironment :
    FX1.HasType
      intervalEnvironment
      FX1.Context.empty
      intervalOppTypeExpr
      (FX1.Expr.sort (FX1.Level.max FX1.Level.zero FX1.Level.zero)) :=
  FX1.HasType.pi
    intervalTypeExpr_has_sort_in_intervalEnvironment
    intervalTypeExpr_has_sort_in_intervalEnvironment_with_binder

/-- The staged interval negation declaration is well typed after the interval
type and endpoints are available. -/
theorem intervalOppDeclaration_wellTyped :
    FX1.Declaration.WellTyped
      intervalEnvironment
      intervalOppDeclaration :=
  FX1.Declaration.WellTyped.axiomDecl
    intervalOppTypeExpr_has_sort_in_intervalEnvironment

/-- The staged interval operation bridge environment is well formed. -/
theorem intervalOpsEnvironment_wellFormed :
    FX1.Environment.WellFormed intervalOpsEnvironment :=
  FX1.Environment.WellFormed.extend
    intervalEnvironment_wellFormed
    intervalOppName_fresh
    intervalOppDeclaration_wellTyped

/-- The staged interval type constant has sort zero in the staged interval
operation environment. -/
theorem intervalTypeExpr_has_sort_in_intervalOpsEnvironment :
    FX1.HasType
      intervalOpsEnvironment
      FX1.Context.empty
      encodeTy_interval
      (FX1.Expr.sort FX1.Level.zero) :=
  FX1.HasType.weaken_environment
    intervalOppDeclaration
    intervalTypeExpr_has_sort_in_intervalEnvironment

/-- The staged interval type constant has sort zero in any context under the
staged interval operation environment. -/
theorem intervalTypeExpr_has_sort_in_intervalOpsEnvironment_anyContext
    (context : FX1.Context) :
    FX1.HasType
      intervalOpsEnvironment
      context
      encodeTy_interval
      (FX1.Expr.sort FX1.Level.zero) :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.older
      intervalOppDeclaration
      (FX1.Environment.HasDeclaration.older
        interval1Declaration
        (FX1.Environment.HasDeclaration.older
          interval0Declaration
          (FX1.Environment.HasDeclaration.newest
            FX1.Environment.empty
            intervalTypeDeclaration))))

/-- The staged binary interval operation type is well formed in the staged
interval operation environment. -/
theorem intervalBinaryOpTypeExpr_has_sort_in_intervalOpsEnvironment :
    FX1.HasType
      intervalOpsEnvironment
      FX1.Context.empty
      intervalBinaryOpTypeExpr
      (FX1.Expr.sort
        (FX1.Level.max
          FX1.Level.zero
          (FX1.Level.max FX1.Level.zero FX1.Level.zero))) :=
  FX1.HasType.pi
    (intervalTypeExpr_has_sort_in_intervalOpsEnvironment_anyContext
      FX1.Context.empty)
    (FX1.HasType.pi
      (intervalTypeExpr_has_sort_in_intervalOpsEnvironment_anyContext
        (FX1.Context.extend FX1.Context.empty intervalTypeExpr))
      (intervalTypeExpr_has_sort_in_intervalOpsEnvironment_anyContext
        (FX1.Context.extend
          (FX1.Context.extend FX1.Context.empty intervalTypeExpr)
          intervalTypeExpr)))

/-- The staged interval meet declaration is well typed after the interval
type, endpoint, and negation declarations are available. -/
theorem intervalMeetDeclaration_wellTyped :
    FX1.Declaration.WellTyped
      intervalOpsEnvironment
      intervalMeetDeclaration :=
  FX1.Declaration.WellTyped.axiomDecl
    intervalBinaryOpTypeExpr_has_sort_in_intervalOpsEnvironment

/-- The staged interval meet bridge environment is well formed. -/
theorem intervalMeetEnvironment_wellFormed :
    FX1.Environment.WellFormed intervalMeetEnvironment :=
  FX1.Environment.WellFormed.extend
    intervalOpsEnvironment_wellFormed
    intervalMeetName_fresh
    intervalMeetDeclaration_wellTyped

/-- The staged interval join declaration is well typed after the interval meet
declaration is available. -/
theorem intervalJoinDeclaration_wellTyped :
    FX1.Declaration.WellTyped
      intervalMeetEnvironment
      intervalJoinDeclaration :=
  FX1.Declaration.WellTyped.axiomDecl
    (FX1.HasType.weaken_environment
      intervalMeetDeclaration
      intervalBinaryOpTypeExpr_has_sort_in_intervalOpsEnvironment)

/-- The staged interval lattice bridge environment is well formed. -/
theorem intervalLatticeEnvironment_wellFormed :
    FX1.Environment.WellFormed intervalLatticeEnvironment :=
  FX1.Environment.WellFormed.extend
    intervalMeetEnvironment_wellFormed
    intervalJoinName_fresh
    intervalJoinDeclaration_wellTyped

/-- The encoded rich interval zero endpoint is well typed in the staged FX1
interval environment. -/
theorem encodedInterval0_has_type :
    FX1.HasType
      intervalEnvironment
      FX1.Context.empty
      interval0Expr
      intervalTypeExpr :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.older
      interval1Declaration
      (FX1.Environment.HasDeclaration.newest
        intervalTypeEnvironment
        interval0Declaration))

/-- The encoded rich interval one endpoint is well typed in the staged FX1
interval environment. -/
theorem encodedInterval1_has_type :
    FX1.HasType
      intervalEnvironment
      FX1.Context.empty
      interval1Expr
      intervalTypeExpr :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.newest
      interval0Environment
      interval1Declaration)

/-- The encoded interval negation function is well typed in the staged FX1
interval operation environment. -/
theorem encodedIntervalOppFunction_has_type :
    FX1.HasType
      intervalOpsEnvironment
      FX1.Context.empty
      intervalOppExpr
      intervalOppTypeExpr :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.newest
      intervalEnvironment
      intervalOppDeclaration)

/-- FX1 typing derivation for interval negation applied to an already typed
encoded interval child. -/
theorem encodedIntervalOpp_has_type
    {encodedInner : FX1.Expr}
    (encodedInnerHasType :
      FX1.HasType
        intervalOpsEnvironment
        FX1.Context.empty
        encodedInner
        encodeTy_interval) :
    FX1.HasType
      intervalOpsEnvironment
      FX1.Context.empty
      (encodeRawTerm_intervalOpp encodedInner)
      encodeTy_interval :=
  FX1.HasType.app
    encodedIntervalOppFunction_has_type
    encodedInnerHasType

/-- The encoded interval meet function is well typed in the staged FX1
interval meet environment. -/
theorem encodedIntervalMeetFunction_has_type :
    FX1.HasType
      intervalMeetEnvironment
      FX1.Context.empty
      intervalMeetExpr
      intervalBinaryOpTypeExpr :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.newest
      intervalOpsEnvironment
      intervalMeetDeclaration)

/-- FX1 typing derivation for interval meet applied to already typed encoded
interval children. -/
theorem encodedIntervalMeet_has_type
    {encodedLeft encodedRight : FX1.Expr}
    (encodedLeftHasType :
      FX1.HasType
        intervalMeetEnvironment
        FX1.Context.empty
        encodedLeft
        encodeTy_interval)
    (encodedRightHasType :
      FX1.HasType
        intervalMeetEnvironment
        FX1.Context.empty
        encodedRight
        encodeTy_interval) :
    FX1.HasType
      intervalMeetEnvironment
      FX1.Context.empty
      (encodeRawTerm_intervalMeet encodedLeft encodedRight)
      encodeTy_interval :=
  FX1.HasType.app
    (FX1.HasType.app
      encodedIntervalMeetFunction_has_type
      encodedLeftHasType)
    encodedRightHasType

/-- The encoded interval join function is well typed in the staged FX1
interval lattice environment. -/
theorem encodedIntervalJoinFunction_has_type :
    FX1.HasType
      intervalLatticeEnvironment
      FX1.Context.empty
      intervalJoinExpr
      intervalBinaryOpTypeExpr :=
  FX1.HasType.const
    (FX1.Environment.HasDeclaration.newest
      intervalMeetEnvironment
      intervalJoinDeclaration)

/-- FX1 typing derivation for interval join applied to already typed encoded
interval children. -/
theorem encodedIntervalJoin_has_type
    {encodedLeft encodedRight : FX1.Expr}
    (encodedLeftHasType :
      FX1.HasType
        intervalLatticeEnvironment
        FX1.Context.empty
        encodedLeft
        encodeTy_interval)
    (encodedRightHasType :
      FX1.HasType
        intervalLatticeEnvironment
        FX1.Context.empty
        encodedRight
        encodeTy_interval) :
    FX1.HasType
      intervalLatticeEnvironment
      FX1.Context.empty
      (encodeRawTerm_intervalJoin encodedLeft encodedRight)
      encodeTy_interval :=
  FX1.HasType.app
    (FX1.HasType.app
      encodedIntervalJoinFunction_has_type
      encodedLeftHasType)
    encodedRightHasType

/-- Soundness of the empty-context interval-zero bridge fragment. -/
theorem encodeTermSound_interval0
    {mode : Mode}
    {level : Nat}
    (_intervalTerm :
      Term (Ctx.empty mode level) Ty.interval RawTerm.interval0) :
    FX1.HasType
      intervalEnvironment
      FX1.Context.empty
      encodeRawTerm_interval0
      encodeTy_interval :=
  encodedInterval0_has_type

/-- Exact round-trip evidence for the interval-zero bridge fragment. -/
def encodeTermSound_interval0_roundTrip
    {mode : Mode}
    {level : Nat}
    (_intervalTerm :
      Term (Ctx.empty mode level) Ty.interval RawTerm.interval0) :
    BridgeRoundTrip
      encodeTy_interval
      (decodeTy_interval (level := level) (scope := 0))
      (Ty.interval : Ty level 0)
      encodeRawTerm_interval0
      decodeRawTerm_interval0
      RawTerm.interval0 :=
  {
    typeRoundTrip := Eq.refl (Option.some (Ty.interval : Ty level 0))
    rawRoundTrip := Eq.refl (Option.some RawTerm.interval0)
  }

/-- Soundness of the empty-context interval-one bridge fragment. -/
theorem encodeTermSound_interval1
    {mode : Mode}
    {level : Nat}
    (_intervalTerm :
      Term (Ctx.empty mode level) Ty.interval RawTerm.interval1) :
    FX1.HasType
      intervalEnvironment
      FX1.Context.empty
      encodeRawTerm_interval1
      encodeTy_interval :=
  encodedInterval1_has_type

/-- Exact round-trip evidence for the interval-one bridge fragment. -/
def encodeTermSound_interval1_roundTrip
    {mode : Mode}
    {level : Nat}
    (_intervalTerm :
      Term (Ctx.empty mode level) Ty.interval RawTerm.interval1) :
    BridgeRoundTrip
      encodeTy_interval
      (decodeTy_interval (level := level) (scope := 0))
      (Ty.interval : Ty level 0)
      encodeRawTerm_interval1
      decodeRawTerm_interval1
      RawTerm.interval1 :=
  {
    typeRoundTrip := Eq.refl (Option.some (Ty.interval : Ty level 0))
    rawRoundTrip := Eq.refl (Option.some RawTerm.interval1)
  }

/-- Soundness of interval negation over an already bridged empty-context
interval child. -/
theorem encodeTermSound_intervalOpp
    {mode : Mode}
    {level : Nat}
    {innerRaw : RawTerm 0}
    {encodedInner : FX1.Expr}
    (_intervalOppTerm :
      Term
        (Ctx.empty mode level)
        (Ty.interval : Ty level 0)
        (RawTerm.intervalOpp innerRaw))
    (encodedInnerHasType :
      FX1.HasType
        intervalOpsEnvironment
        FX1.Context.empty
        encodedInner
        encodeTy_interval) :
    FX1.HasType
      intervalOpsEnvironment
      FX1.Context.empty
      (encodeRawTerm_intervalOpp encodedInner)
      encodeTy_interval :=
  encodedIntervalOpp_has_type encodedInnerHasType

/-- Exact round-trip evidence for interval negation, modular in the already
bridged child. -/
def encodeTermSound_intervalOpp_roundTrip
    {mode : Mode}
    {level : Nat}
    {innerRaw : RawTerm 0}
    {encodedInner : FX1.Expr}
    {decodeInner : FX1.Expr -> Option (RawTerm 0)}
    (_intervalOppTerm :
      Term
        (Ctx.empty mode level)
        (Ty.interval : Ty level 0)
        (RawTerm.intervalOpp innerRaw))
    (innerRoundTrip :
      BridgeRoundTrip
        encodeTy_interval
        (decodeTy_interval (level := level) (scope := 0))
        (Ty.interval : Ty level 0)
        encodedInner
        decodeInner
        innerRaw) :
    BridgeRoundTrip
      encodeTy_interval
      (decodeTy_interval (level := level) (scope := 0))
      (Ty.interval : Ty level 0)
      (encodeRawTerm_intervalOpp encodedInner)
      (decodeRawTerm_intervalOpp decodeInner)
      (RawTerm.intervalOpp innerRaw) :=
  {
    typeRoundTrip := Eq.refl (Option.some (Ty.interval : Ty level 0))
    rawRoundTrip := by
      rw [
        encodeRawTerm_intervalOpp,
        decodeRawTerm_intervalOpp,
        decodeRawTerm_intervalOppSymbol_intervalOppExpr,
        innerRoundTrip.rawRoundTrip
      ]
  }

/-- Soundness of interval meet over already bridged empty-context interval
children. -/
theorem encodeTermSound_intervalMeet
    {mode : Mode}
    {level : Nat}
    {leftRaw rightRaw : RawTerm 0}
    {encodedLeft encodedRight : FX1.Expr}
    (_intervalMeetTerm :
      Term
        (Ctx.empty mode level)
        (Ty.interval : Ty level 0)
        (RawTerm.intervalMeet leftRaw rightRaw))
    (encodedLeftHasType :
      FX1.HasType
        intervalMeetEnvironment
        FX1.Context.empty
        encodedLeft
        encodeTy_interval)
    (encodedRightHasType :
      FX1.HasType
        intervalMeetEnvironment
        FX1.Context.empty
        encodedRight
        encodeTy_interval) :
    FX1.HasType
      intervalMeetEnvironment
      FX1.Context.empty
      (encodeRawTerm_intervalMeet encodedLeft encodedRight)
      encodeTy_interval :=
  encodedIntervalMeet_has_type encodedLeftHasType encodedRightHasType

/-- Exact round-trip evidence for interval meet, modular in both already
bridged children. -/
def encodeTermSound_intervalMeet_roundTrip
    {mode : Mode}
    {level : Nat}
    {leftRaw rightRaw : RawTerm 0}
    {encodedLeft encodedRight : FX1.Expr}
    {decodeLeft decodeRight : FX1.Expr -> Option (RawTerm 0)}
    (_intervalMeetTerm :
      Term
        (Ctx.empty mode level)
        (Ty.interval : Ty level 0)
        (RawTerm.intervalMeet leftRaw rightRaw))
    (leftRoundTrip :
      BridgeRoundTrip
        encodeTy_interval
        (decodeTy_interval (level := level) (scope := 0))
        (Ty.interval : Ty level 0)
        encodedLeft
        decodeLeft
        leftRaw)
    (rightRoundTrip :
      BridgeRoundTrip
        encodeTy_interval
        (decodeTy_interval (level := level) (scope := 0))
        (Ty.interval : Ty level 0)
        encodedRight
        decodeRight
        rightRaw) :
    BridgeRoundTrip
      encodeTy_interval
      (decodeTy_interval (level := level) (scope := 0))
      (Ty.interval : Ty level 0)
      (encodeRawTerm_intervalMeet encodedLeft encodedRight)
      (decodeRawTerm_intervalMeet decodeLeft decodeRight)
      (RawTerm.intervalMeet leftRaw rightRaw) :=
  {
    typeRoundTrip := Eq.refl (Option.some (Ty.interval : Ty level 0))
    rawRoundTrip := by
      rw [
        encodeRawTerm_intervalMeet,
        decodeRawTerm_intervalMeet,
        decodeRawTerm_intervalMeetSymbol_intervalMeetExpr,
        leftRoundTrip.rawRoundTrip,
        rightRoundTrip.rawRoundTrip
      ]
  }

/-- Soundness of interval join over already bridged empty-context interval
children. -/
theorem encodeTermSound_intervalJoin
    {mode : Mode}
    {level : Nat}
    {leftRaw rightRaw : RawTerm 0}
    {encodedLeft encodedRight : FX1.Expr}
    (_intervalJoinTerm :
      Term
        (Ctx.empty mode level)
        (Ty.interval : Ty level 0)
        (RawTerm.intervalJoin leftRaw rightRaw))
    (encodedLeftHasType :
      FX1.HasType
        intervalLatticeEnvironment
        FX1.Context.empty
        encodedLeft
        encodeTy_interval)
    (encodedRightHasType :
      FX1.HasType
        intervalLatticeEnvironment
        FX1.Context.empty
        encodedRight
        encodeTy_interval) :
    FX1.HasType
      intervalLatticeEnvironment
      FX1.Context.empty
      (encodeRawTerm_intervalJoin encodedLeft encodedRight)
      encodeTy_interval :=
  encodedIntervalJoin_has_type encodedLeftHasType encodedRightHasType

/-- Exact round-trip evidence for interval join, modular in both already
bridged children. -/
def encodeTermSound_intervalJoin_roundTrip
    {mode : Mode}
    {level : Nat}
    {leftRaw rightRaw : RawTerm 0}
    {encodedLeft encodedRight : FX1.Expr}
    {decodeLeft decodeRight : FX1.Expr -> Option (RawTerm 0)}
    (_intervalJoinTerm :
      Term
        (Ctx.empty mode level)
        (Ty.interval : Ty level 0)
        (RawTerm.intervalJoin leftRaw rightRaw))
    (leftRoundTrip :
      BridgeRoundTrip
        encodeTy_interval
        (decodeTy_interval (level := level) (scope := 0))
        (Ty.interval : Ty level 0)
        encodedLeft
        decodeLeft
        leftRaw)
    (rightRoundTrip :
      BridgeRoundTrip
        encodeTy_interval
        (decodeTy_interval (level := level) (scope := 0))
        (Ty.interval : Ty level 0)
        encodedRight
        decodeRight
        rightRaw) :
    BridgeRoundTrip
      encodeTy_interval
      (decodeTy_interval (level := level) (scope := 0))
      (Ty.interval : Ty level 0)
      (encodeRawTerm_intervalJoin encodedLeft encodedRight)
      (decodeRawTerm_intervalJoin decodeLeft decodeRight)
      (RawTerm.intervalJoin leftRaw rightRaw) :=
  {
    typeRoundTrip := Eq.refl (Option.some (Ty.interval : Ty level 0))
    rawRoundTrip := by
      rw [
        encodeRawTerm_intervalJoin,
        decodeRawTerm_intervalJoin,
        decodeRawTerm_intervalJoinSymbol_intervalJoinExpr,
        leftRoundTrip.rawRoundTrip,
        rightRoundTrip.rawRoundTrip
      ]
  }

end FX1Bridge
end LeanFX2
