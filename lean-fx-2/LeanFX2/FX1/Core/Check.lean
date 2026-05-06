prelude
import LeanFX2.FX1.Core.HasType

/-! # FX1/Core/Check

Root status: Root-FX1 checker slice.

This module adds the first executable checker slice for the minimal FX1
lambda-Pi core.  It is intentionally conservative:

* variables, sorts, Pi types, lambdas, and applications are checked;
* constants are accepted only when executable environment lookup returns a
  proof-carrying declaration membership witness;
* equality used by application checking is structural and FX1-native.

The checker is sound for the fragment it accepts.  Accepting fewer programs is
the conservative direction; each accepted branch must carry its own zero-axiom
typing derivation.
-/

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

namespace Environment

/-- A successful executable declaration lookup paired with the relational
membership witness it justifies. -/
structure LookupDeclarationResult
    (environment : Environment) (queryName : Name) : Type where
  declaration : Declaration
  declarationMember :
    Environment.HasDeclaration environment queryName declaration

/-- Transport a proof-carrying declaration lookup across a proved query-name
equality. -/
def LookupDeclarationResult.rewriteQueryName
    {environment : Environment}
    {leftQueryName rightQueryName : Name}
    (queryNamesEqual : Eq leftQueryName rightQueryName)
    (lookupResult : LookupDeclarationResult environment rightQueryName) :
    LookupDeclarationResult environment leftQueryName :=
  match queryNamesEqual with
  | Eq.refl _ => lookupResult

/-- Soundness payload for executable constant-type lookup. -/
structure FindTypeByNameSoundResult
    (environment : Environment) (queryName : Name) (typeExpr : Expr) :
    Type where
  declaration : Declaration
  declarationMember :
    Environment.HasDeclaration environment queryName declaration
  typeEquality :
    Eq (Declaration.typeExpr declaration) typeExpr

/-- Witness-producing declaration lookup over the raw declaration list.

The recursion follows the executable environment convention: newest
declarations live at the head, so the first matching name wins. -/
def findByNameResultInDeclarations? :
    (declarations : List Declaration) -> (queryName : Name) ->
      Option (LookupDeclarationResult { declarations := declarations } queryName)
  | List.nil, _ => none
  | List.cons declaration remainingDeclarations, queryName =>
      match Name.eqResult queryName (Declaration.name declaration) with
      | EqualityResult.equal nameEquality =>
          let newestLookup :
              LookupDeclarationResult
                { declarations := List.cons declaration remainingDeclarations }
                (Declaration.name declaration) := {
            declaration := declaration
            declarationMember :=
              Environment.HasDeclaration.newest
                { declarations := remainingDeclarations }
                declaration
          }
          some
            (LookupDeclarationResult.rewriteQueryName
              nameEquality
              newestLookup)
      | EqualityResult.notEqual =>
          match Environment.findByNameResultInDeclarations?
              remainingDeclarations
              queryName with
          | some olderLookup =>
              some {
                declaration := olderLookup.declaration
                declarationMember :=
                  Environment.HasDeclaration.older
                    declaration
                    olderLookup.declarationMember
              }
          | none => none

/-- Environment-level wrapper for witness-producing declaration lookup. -/
def findByNameResult? (environment : Environment) (queryName : Name) :
    Option (LookupDeclarationResult environment queryName) :=
  Environment.findByNameResultInDeclarations?
    environment.declarations
    queryName

/-- Project a proof-carrying declaration lookup result to its declared type. -/
def findTypeByNameFromResult?
    {environment : Environment} {queryName : Name} :
    Option (LookupDeclarationResult environment queryName) -> Option Expr
  | some lookupResult => some (Declaration.typeExpr lookupResult.declaration)
  | none => none

/-- Find the declared type for a constant name, if the environment contains
one. -/
def findTypeByName? (environment : Environment) (queryName : Name) :
    Option Expr :=
  Environment.findTypeByNameFromResult?
    (Environment.findByNameResult? environment queryName)

/-- Soundness of executable constant-type lookup. -/
def findTypeByName_sound
    {environment : Environment}
    {queryName : Name}
    {typeExpr : Expr}
    (lookupSucceeded :
      Eq
        (Environment.findTypeByName? environment queryName)
        (some typeExpr)) :
    FindTypeByNameSoundResult environment queryName typeExpr :=
  match h : Environment.findByNameResult? environment queryName with
  | some lookupResult =>
      let projectedEquality :
          Eq
            (some (Declaration.typeExpr lookupResult.declaration))
            (some typeExpr) :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Environment.findTypeByNameFromResult?
                (environment := environment)
                (queryName := queryName))
              h))
          lookupSucceeded
      let typeEquality :=
        CheckOption.some_injective projectedEquality
      {
        declaration := lookupResult.declaration
        declarationMember := lookupResult.declarationMember
        typeEquality := typeEquality
      }
  | none =>
      let noneEqualsSome :
          Eq (none : Option Expr) (some typeExpr) :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Environment.findTypeByNameFromResult?
                (environment := environment)
                (queryName := queryName))
              h))
          lookupSucceeded
      nomatch noneEqualsSome

/-- A successful executable transparent-definition lookup paired with the
propositional transparent-definition witness it justifies. -/
structure TransparentLookupResult
    (environment : Environment) (queryName : Name) : Type where
  typeExpr : Expr
  valueExpr : Expr
  transparentDefinition :
    Environment.TransparentDefinition environment queryName typeExpr valueExpr

/-- Transport a proof-carrying transparent lookup across a proved query-name
equality. -/
def TransparentLookupResult.rewriteQueryName
    {environment : Environment}
    {leftQueryName rightQueryName : Name}
    (queryNamesEqual : Eq leftQueryName rightQueryName)
    (lookupResult : TransparentLookupResult environment rightQueryName) :
    TransparentLookupResult environment leftQueryName :=
  match queryNamesEqual with
  | Eq.refl _ => lookupResult

/-- Soundness payload for executable transparent-value lookup. -/
structure FindTransparentValueSoundResult
    (environment : Environment) (queryName : Name) (valueExpr : Expr) :
    Type where
  typeExpr : Expr
  transparentDefinition :
    Environment.TransparentDefinition environment queryName typeExpr valueExpr

/-- Lift an older transparent lookup through one newer declaration. -/
def TransparentLookupResult.weakenOlder
    {remainingDeclarations : List Declaration}
    {queryName : Name}
    (newDeclaration : Declaration)
    (olderLookup :
      TransparentLookupResult
        { declarations := remainingDeclarations }
        queryName) :
    TransparentLookupResult
      { declarations := List.cons newDeclaration remainingDeclarations }
      queryName := {
  typeExpr := olderLookup.typeExpr
  valueExpr := olderLookup.valueExpr
  transparentDefinition :=
    Environment.TransparentDefinition.older
      newDeclaration
      olderLookup.transparentDefinition
}

/-- Witness-producing transparent-definition lookup over the raw declaration
list.

Newest declarations win.  If the newest matching declaration is an axiom
placeholder, lookup fails rather than searching older declarations with the
same name.  This matches executable environment shadowing while ensuring that
delta never unfolds an axiom declaration. -/
def findTransparentDefinitionResultInDeclarations? :
    (declarations : List Declaration) -> (queryName : Name) ->
      Option
        (TransparentLookupResult
          { declarations := declarations }
          queryName)
  | List.nil, _ => none
  | List.cons (Declaration.axiomDecl declName typeExpr)
      remainingDeclarations, queryName =>
      match Name.eqResult queryName declName with
      | EqualityResult.equal _ => none
      | EqualityResult.notEqual =>
          match Environment.findTransparentDefinitionResultInDeclarations?
              remainingDeclarations
              queryName with
          | some olderLookup =>
              some
                (TransparentLookupResult.weakenOlder
                  (Declaration.axiomDecl declName typeExpr)
                  olderLookup)
          | none => none
  | List.cons (Declaration.defDecl declName typeExpr valueExpr)
      remainingDeclarations, queryName =>
      match Name.eqResult queryName declName with
      | EqualityResult.equal nameEquality =>
          let newestLookup :
              TransparentLookupResult
                { declarations :=
                    List.cons
                      (Declaration.defDecl declName typeExpr valueExpr)
                      remainingDeclarations }
                declName := {
            typeExpr := typeExpr
            valueExpr := valueExpr
            transparentDefinition :=
              Environment.TransparentDefinition.newestDef
                { declarations := remainingDeclarations }
                declName
                typeExpr
                valueExpr
          }
          some
            (TransparentLookupResult.rewriteQueryName
              nameEquality
              newestLookup)
      | EqualityResult.notEqual =>
          match Environment.findTransparentDefinitionResultInDeclarations?
              remainingDeclarations
              queryName with
          | some olderLookup =>
              some
                (TransparentLookupResult.weakenOlder
                  (Declaration.defDecl declName typeExpr valueExpr)
                  olderLookup)
          | none => none
  | List.cons (Declaration.theoremDecl declName typeExpr proofExpr)
      remainingDeclarations, queryName =>
      match Name.eqResult queryName declName with
      | EqualityResult.equal nameEquality =>
          let newestLookup :
              TransparentLookupResult
                { declarations :=
                    List.cons
                      (Declaration.theoremDecl declName typeExpr proofExpr)
                      remainingDeclarations }
                declName := {
            typeExpr := typeExpr
            valueExpr := proofExpr
            transparentDefinition :=
              Environment.TransparentDefinition.newestTheorem
                { declarations := remainingDeclarations }
                declName
                typeExpr
                proofExpr
          }
          some
            (TransparentLookupResult.rewriteQueryName
              nameEquality
              newestLookup)
      | EqualityResult.notEqual =>
          match Environment.findTransparentDefinitionResultInDeclarations?
              remainingDeclarations
              queryName with
          | some olderLookup =>
              some
                (TransparentLookupResult.weakenOlder
                  (Declaration.theoremDecl declName typeExpr proofExpr)
                  olderLookup)
          | none => none

/-- Environment-level wrapper for proof-carrying transparent-definition
lookup. -/
def findTransparentDefinitionResult?
    (environment : Environment) (queryName : Name) :
    Option (TransparentLookupResult environment queryName) :=
  Environment.findTransparentDefinitionResultInDeclarations?
    environment.declarations
    queryName

/-- Project a transparent lookup result to its value expression. -/
def findTransparentValueFromResult?
    {environment : Environment} {queryName : Name} :
    Option (TransparentLookupResult environment queryName) -> Option Expr
  | some lookupResult => some lookupResult.valueExpr
  | none => none

/-- Find the transparent value for a constant name, if the newest matching
declaration is transparent. -/
def findTransparentValue?
    (environment : Environment) (queryName : Name) : Option Expr :=
  Environment.findTransparentValueFromResult?
    (Environment.findTransparentDefinitionResult? environment queryName)

/-- Soundness of executable transparent-value lookup. -/
def findTransparentValue_sound
    {environment : Environment}
    {queryName : Name}
    {valueExpr : Expr}
    (lookupSucceeded :
      Eq
        (Environment.findTransparentValue? environment queryName)
        (some valueExpr)) :
    FindTransparentValueSoundResult environment queryName valueExpr :=
  match h : Environment.findTransparentDefinitionResult? environment queryName with
  | some lookupResult =>
      let projectedEquality :
          Eq (some lookupResult.valueExpr) (some valueExpr) :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Environment.findTransparentValueFromResult?
                (environment := environment)
                (queryName := queryName))
              h))
          lookupSucceeded
      let valueEquality :=
        CheckOption.some_injective projectedEquality
      match valueEquality with
      | Eq.refl _ => {
          typeExpr := lookupResult.typeExpr
          transparentDefinition := lookupResult.transparentDefinition
        }
  | none =>
      let noneEqualsSome :
          Eq (none : Option Expr) (some valueExpr) :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Environment.findTransparentValueFromResult?
                (environment := environment)
                (queryName := queryName))
              h))
          lookupSucceeded
      nomatch noneEqualsSome

end Environment

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

/-- Project a proof-carrying context lookup result to the executable type
payload. -/
def lookupTypeFromResult?
    {entries : List Expr} {index : Nat} :
    Option (LookupTypeResult entries index) -> Option Expr
  | some lookupResult => some lookupResult.typeExpr
  | none => none

/-- Lookup a de Bruijn index and return the binder type shifted into the
current context, matching `Context.HasTypeAt`. -/
def lookupTypeInEntries? : List Expr -> Nat -> Option Expr
  | entries, index =>
      Context.lookupTypeFromResult?
        (Context.lookupTypeResultInEntries? entries index)

/-- Context-level wrapper for `lookupTypeInEntries?`. -/
def lookupType? (context : Context) (index : Nat) : Option Expr :=
  Context.lookupTypeInEntries? context.entries index

/-- Context-level wrapper for witness-producing lookup. -/
def lookupTypeResult? (context : Context) (index : Nat) :
    Option (LookupTypeResult context.entries index) :=
  Context.lookupTypeResultInEntries? context.entries index

/-- Soundness of executable shifted de Bruijn lookup. -/
theorem lookupType_sound
    {context : Context}
    {index : Nat}
    {typeExpr : Expr}
    (lookupSucceeded :
      Eq (Context.lookupType? context index) (some typeExpr)) :
    Context.HasTypeAt context index typeExpr :=
  match h : Context.lookupTypeResult? context index with
  | some lookupResult =>
      let projectedEquality :
          Eq (some lookupResult.typeExpr) (some typeExpr) :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Context.lookupTypeFromResult?
                (entries := context.entries)
                (index := index))
              h))
          lookupSucceeded
      let typeEquality :=
        CheckOption.some_injective projectedEquality
      match typeEquality with
      | Eq.refl _ => lookupResult.typeAtIndex
  | none =>
      let noneEqualsSome :
          Eq (none : Option Expr) (some typeExpr) :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Context.lookupTypeFromResult?
                (entries := context.entries)
                (index := index))
              h))
          lookupSucceeded
      nomatch noneEqualsSome

end Context

namespace Expr

/-- A successful executable head reduction paired with its `EnvStep`
certificate. -/
structure HeadStepResult
    (environment : Environment) (sourceExpr : Expr) : Type where
  targetExpr : Expr
  reductionStep : EnvStep environment sourceExpr targetExpr

/-- Executable head-step search with proof payload.

This is deliberately tiny: beta at the head of an application and delta for a
transparent constant.  Congruence/recursive closure belongs to WHNF and
conversion, which can be layered on this proof-carrying primitive. -/
def headStepResult? (environment : Environment) :
    (sourceExpr : Expr) -> Option (HeadStepResult environment sourceExpr)
  | Expr.const constName =>
      match Environment.findTransparentDefinitionResult? environment constName with
      | some lookupResult =>
          some {
            targetExpr := lookupResult.valueExpr
            reductionStep :=
              EnvStep.delta lookupResult.transparentDefinition
          }
      | none => none
  | Expr.app (Expr.lam domainExpr bodyExpr) argumentExpr =>
      some {
        targetExpr := Expr.subst0 argumentExpr bodyExpr
        reductionStep := EnvStep.beta domainExpr bodyExpr argumentExpr
      }
  | Expr.bvar _ => none
  | Expr.sort _ => none
  | Expr.pi _ _ => none
  | Expr.lam _ _ => none
  | Expr.app (Expr.bvar _) _ => none
  | Expr.app (Expr.sort _) _ => none
  | Expr.app (Expr.const _) _ => none
  | Expr.app (Expr.pi _ _) _ => none
  | Expr.app (Expr.app _ _) _ => none

/-- Project a proof-carrying head-step result to the executable target. -/
def headStepFromResult?
    {environment : Environment} {sourceExpr : Expr} :
    Option (HeadStepResult environment sourceExpr) -> Option Expr
  | some stepResult => some stepResult.targetExpr
  | none => none

/-- Runtime-facing executable head-step search. -/
def headStep? (environment : Environment) (sourceExpr : Expr) : Option Expr :=
  Expr.headStepFromResult?
    (Expr.headStepResult? environment sourceExpr)

/-- Soundness of executable head-step search. -/
def headStep?_sound
    {environment : Environment}
    {sourceExpr targetExpr : Expr}
    (headStepSucceeded :
      Eq (Expr.headStep? environment sourceExpr) (some targetExpr)) :
    EnvStep environment sourceExpr targetExpr :=
  match h : Expr.headStepResult? environment sourceExpr with
  | some stepResult =>
      let projectedEquality :
          Eq (some stepResult.targetExpr) (some targetExpr) :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Expr.headStepFromResult?
                (environment := environment)
                (sourceExpr := sourceExpr))
              h))
          headStepSucceeded
      let targetEquality :=
        CheckOption.some_injective projectedEquality
      match targetEquality with
      | Eq.refl _ => stepResult.reductionStep
  | none =>
      let noneEqualsSome :
          Eq (none : Option Expr) (some targetExpr) :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Expr.headStepFromResult?
                (environment := environment)
                (sourceExpr := sourceExpr))
              h))
          headStepSucceeded
      nomatch noneEqualsSome

/-- A successful checker inference paired with the relational typing
derivation it justifies. -/
structure InferResult
    (environment : Environment) (context : Context) (expression : Expr) :
    Type where
  typeExpr : Expr
  typeDerivation : HasType environment context expression typeExpr

/-- Project a proof-carrying inference result to the executable inferred
type. -/
def inferTypeFromResult?
    {environment : Environment} {context : Context} {expression : Expr} :
    Option (InferResult environment context expression) -> Option Expr
  | some inferenceResult => some inferenceResult.typeExpr
  | none => none

/-- Project a proof-carrying inference result to the executable check result
against an expected type. -/
def checkBoolFromResult?
    {environment : Environment} {context : Context} {expression : Expr}
    (expectedTypeExpr : Expr) :
    Option (InferResult environment context expression) -> Bool
  | some inferenceResult =>
      Expr.checkerBeq inferenceResult.typeExpr expectedTypeExpr
  | none => false

/-- Project a runtime-facing optional inferred type to the executable check
result against an expected type. -/
def checkBoolFromCoreType? (expectedTypeExpr : Expr) :
    Option Expr -> Bool
  | some inferredTypeExpr =>
      Expr.checkerBeq inferredTypeExpr expectedTypeExpr
  | none => false

/-- Executable inference without proof payloads.

This is the runtime-facing checker path: it is intentionally separate from
`inferResult?`, whose dependent result carries typing derivations and currently
uses Lean-generated dependent-recursion infrastructure. -/
def inferCore? (environment : Environment) (context : Context) :
    Expr -> Option Expr
  | Expr.bvar index =>
      Context.lookupType? context index
  | Expr.sort sortLevel =>
      some (Expr.sort (Level.succ sortLevel))
  | Expr.const constName =>
      Environment.findTypeByName? environment constName
  | Expr.pi domainExpr bodyExpr =>
      match Expr.inferCore? environment context domainExpr with
      | some (Expr.sort domainLevel) =>
          match Expr.inferCore?
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
      match Expr.inferCore? environment context domainExpr with
      | some (Expr.sort _) =>
          match Expr.inferCore?
              environment
              (Context.extend context domainExpr)
              bodyExpr with
          | some bodyTypeExpr =>
              some (Expr.pi domainExpr bodyTypeExpr)
          | none => none
      | some (Expr.bvar _) => none
      | some (Expr.const _) => none
      | some (Expr.pi _ _) => none
      | some (Expr.lam _ _) => none
      | some (Expr.app _ _) => none
      | none => none
  | Expr.app functionExpr argumentExpr =>
      match Expr.inferCore? environment context functionExpr with
      | some (Expr.pi domainExpr bodyTypeExpr) =>
          match Expr.inferCore? environment context argumentExpr with
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

/-- Direct soundness for runtime-facing variable inference. -/
theorem inferCore_bvar_sound
    {environment : Environment}
    {context : Context}
    {index : Nat}
    {inferredTypeExpr : Expr}
    (inferenceSucceeded :
      Eq
        (Expr.inferCore? environment context (Expr.bvar index))
        (some inferredTypeExpr)) :
    HasType environment context (Expr.bvar index) inferredTypeExpr :=
  HasType.var
    (Context.lookupType_sound inferenceSucceeded)

/-- Direct soundness for runtime-facing sort inference. -/
theorem inferCore_sort_sound
    {environment : Environment}
    {context : Context}
    {sortLevel : Level}
    {inferredTypeExpr : Expr}
    (inferenceSucceeded :
      Eq
        (Expr.inferCore? environment context (Expr.sort sortLevel))
        (some inferredTypeExpr)) :
    HasType environment context (Expr.sort sortLevel) inferredTypeExpr :=
  let typeEquality :=
    CheckOption.some_injective inferenceSucceeded
  match typeEquality with
  | Eq.refl _ => HasType.sort context sortLevel

/-- Direct soundness for runtime-facing constant inference. -/
theorem inferCore_const_sound
    {environment : Environment}
    {context : Context}
    {constName : Name}
    {inferredTypeExpr : Expr}
    (inferenceSucceeded :
      Eq
        (Expr.inferCore? environment context (Expr.const constName))
        (some inferredTypeExpr)) :
    HasType environment context (Expr.const constName) inferredTypeExpr :=
  let lookupSound :=
    Environment.findTypeByName_sound inferenceSucceeded
  let declaredTypeExpr := Declaration.typeExpr lookupSound.declaration
  let constHasDeclaredType :
      HasType environment context (Expr.const constName) declaredTypeExpr :=
    HasType.const lookupSound.declarationMember
  let typeEquality : Eq declaredTypeExpr inferredTypeExpr :=
    lookupSound.typeEquality
  Eq.ndrec
    (motive := fun currentTypeExpr =>
      HasType environment context (Expr.const constName) currentTypeExpr)
    constHasDeclaredType
    typeEquality

/-- Branch soundness for runtime-facing Pi inference.

This is the constructor-local part of full `inferCore?` soundness: the caller
must still provide soundness for the recursive domain and body inferences. -/
theorem inferCore_pi_from_branch_sound
    {environment : Environment}
    {context : Context}
    {domainExpr bodyExpr inferredTypeExpr : Expr}
    {domainLevel bodyLevel : Level}
    (domainInference :
      Eq
        (Expr.inferCore? environment context domainExpr)
        (some (Expr.sort domainLevel)))
    (bodyInference :
      Eq
        (Expr.inferCore?
          environment
          (Context.extend context domainExpr)
          bodyExpr)
        (some (Expr.sort bodyLevel)))
    (domainHasSort :
      HasType environment context domainExpr (Expr.sort domainLevel))
    (bodyHasSort :
      HasType
        environment
        (Context.extend context domainExpr)
        bodyExpr
        (Expr.sort bodyLevel))
    (inferenceSucceeded :
      Eq
        (Expr.inferCore?
          environment
          context
          (Expr.pi domainExpr bodyExpr))
        (some inferredTypeExpr)) :
    HasType
      environment
      context
      (Expr.pi domainExpr bodyExpr)
      inferredTypeExpr :=
  let branchEquality :
      Eq
        (Expr.inferCore?
          environment
          context
          (Expr.pi domainExpr bodyExpr))
        (some (Expr.sort (Level.max domainLevel bodyLevel))) :=
    let bodyCase : Option Expr -> Option Expr
      | some (Expr.sort currentBodyLevel) =>
          some (Expr.sort (Level.max domainLevel currentBodyLevel))
      | some (Expr.bvar _) => none
      | some (Expr.const _) => none
      | some (Expr.pi _ _) => none
      | some (Expr.lam _ _) => none
      | some (Expr.app _ _) => none
      | none => none
    let domainCase : Option Expr -> Option Expr
      | some (Expr.sort currentDomainLevel) =>
          match Expr.inferCore?
              environment
              (Context.extend context domainExpr)
              bodyExpr with
          | some (Expr.sort currentBodyLevel) =>
              some
                (Expr.sort
                  (Level.max currentDomainLevel currentBodyLevel))
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
    let domainCaseEquality :
        Eq
          (Expr.inferCore?
            environment
            context
            (Expr.pi domainExpr bodyExpr))
          (domainCase
            (Expr.inferCore? environment context domainExpr)) :=
      Eq.refl
        (Expr.inferCore?
          environment
          context
          (Expr.pi domainExpr bodyExpr))
    let domainCaseProjected :=
      congrArg domainCase domainInference
    let bodyCaseEquality :
        Eq
          (domainCase (some (Expr.sort domainLevel)))
          (bodyCase
            (Expr.inferCore?
              environment
              (Context.extend context domainExpr)
              bodyExpr)) :=
      Eq.refl
        (bodyCase
          (Expr.inferCore?
            environment
            (Context.extend context domainExpr)
            bodyExpr))
    let bodyCaseProjected :=
      congrArg bodyCase bodyInference
    Eq.trans
      domainCaseEquality
      (Eq.trans
        domainCaseProjected
        (Eq.trans bodyCaseEquality bodyCaseProjected))
  let typeEquality :=
    CheckOption.some_injective
      (Eq.trans (Eq.symm branchEquality) inferenceSucceeded)
  match typeEquality with
  | Eq.refl _ => HasType.pi domainHasSort bodyHasSort

/-- Branch soundness for runtime-facing lambda inference.

This proves the lambda branch once the domain sort and body type recursive
inferences have already been justified. -/
theorem inferCore_lam_from_branch_sound
    {environment : Environment}
    {context : Context}
    {domainExpr bodyExpr bodyTypeExpr inferredTypeExpr : Expr}
    {domainLevel : Level}
    (domainInference :
      Eq
        (Expr.inferCore? environment context domainExpr)
        (some (Expr.sort domainLevel)))
    (bodyInference :
      Eq
        (Expr.inferCore?
          environment
          (Context.extend context domainExpr)
          bodyExpr)
        (some bodyTypeExpr))
    (domainHasSort :
      HasType environment context domainExpr (Expr.sort domainLevel))
    (bodyHasType :
      HasType
        environment
        (Context.extend context domainExpr)
        bodyExpr
        bodyTypeExpr)
    (inferenceSucceeded :
      Eq
        (Expr.inferCore?
          environment
          context
          (Expr.lam domainExpr bodyExpr))
        (some inferredTypeExpr)) :
    HasType
      environment
      context
      (Expr.lam domainExpr bodyExpr)
      inferredTypeExpr :=
  let branchEquality :
      Eq
        (Expr.inferCore?
          environment
          context
          (Expr.lam domainExpr bodyExpr))
        (some (Expr.pi domainExpr bodyTypeExpr)) :=
    let bodyCase : Option Expr -> Option Expr
      | some currentBodyTypeExpr =>
          some (Expr.pi domainExpr currentBodyTypeExpr)
      | none => none
    let domainCase : Option Expr -> Option Expr
      | some (Expr.sort _) =>
          bodyCase
            (Expr.inferCore?
              environment
              (Context.extend context domainExpr)
              bodyExpr)
      | some (Expr.bvar _) => none
      | some (Expr.const _) => none
      | some (Expr.pi _ _) => none
      | some (Expr.lam _ _) => none
      | some (Expr.app _ _) => none
      | none => none
    let domainCaseEquality :
        Eq
          (Expr.inferCore?
            environment
            context
            (Expr.lam domainExpr bodyExpr))
          (domainCase
            (Expr.inferCore? environment context domainExpr)) :=
      Eq.refl
        (Expr.inferCore?
          environment
          context
          (Expr.lam domainExpr bodyExpr))
    let domainCaseProjected :=
      congrArg domainCase domainInference
    let bodyCaseEquality :
        Eq
          (domainCase (some (Expr.sort domainLevel)))
          (bodyCase
            (Expr.inferCore?
              environment
              (Context.extend context domainExpr)
              bodyExpr)) :=
      Eq.refl
        (bodyCase
          (Expr.inferCore?
            environment
            (Context.extend context domainExpr)
            bodyExpr))
    let bodyCaseProjected :=
      congrArg bodyCase bodyInference
    Eq.trans
      domainCaseEquality
      (Eq.trans
        domainCaseProjected
        (Eq.trans bodyCaseEquality bodyCaseProjected))
  let typeEquality :=
    CheckOption.some_injective
      (Eq.trans (Eq.symm branchEquality) inferenceSucceeded)
  match typeEquality with
  | Eq.refl _ => HasType.lam domainHasSort bodyHasType

/-- Branch soundness for runtime-facing application inference.

This proves the application branch once recursive inference has established a
Pi-typed function and a checker-equal argument type. -/
theorem inferCore_app_from_branch_sound
    {environment : Environment}
    {context : Context}
    {functionExpr argumentExpr domainExpr bodyTypeExpr argumentTypeExpr
      inferredTypeExpr : Expr}
    (functionInference :
      Eq
        (Expr.inferCore? environment context functionExpr)
        (some (Expr.pi domainExpr bodyTypeExpr)))
    (argumentInference :
      Eq
        (Expr.inferCore? environment context argumentExpr)
        (some argumentTypeExpr))
    (argumentTypeCheck :
      Eq (Expr.checkerBeq argumentTypeExpr domainExpr) true)
    (functionHasPi :
      HasType
        environment
        context
        functionExpr
        (Expr.pi domainExpr bodyTypeExpr))
    (argumentHasInferredType :
      HasType environment context argumentExpr argumentTypeExpr)
    (inferenceSucceeded :
      Eq
        (Expr.inferCore?
          environment
          context
          (Expr.app functionExpr argumentExpr))
        (some inferredTypeExpr)) :
    HasType
      environment
      context
      (Expr.app functionExpr argumentExpr)
      inferredTypeExpr :=
  let argumentTypeEquality :=
    Expr.checkerBeq_sound
      argumentTypeExpr
      domainExpr
      argumentTypeCheck
  let argumentHasDomain :
      HasType environment context argumentExpr domainExpr :=
    match argumentTypeEquality with
    | Eq.refl _ => argumentHasInferredType
  let branchEquality :
      Eq
        (Expr.inferCore?
          environment
          context
          (Expr.app functionExpr argumentExpr))
        (some (Expr.subst0 argumentExpr bodyTypeExpr)) :=
    let checkCase : Bool -> Option Expr
      | true => some (Expr.subst0 argumentExpr bodyTypeExpr)
      | false => none
    let argumentCase : Option Expr -> Option Expr
      | some currentArgumentTypeExpr =>
          checkCase (Expr.checkerBeq currentArgumentTypeExpr domainExpr)
      | none => none
    let functionCase : Option Expr -> Option Expr
      | some (Expr.pi currentDomainExpr currentBodyTypeExpr) =>
          match Expr.inferCore? environment context argumentExpr with
          | some currentArgumentTypeExpr =>
              match Expr.checkerBeq
                  currentArgumentTypeExpr
                  currentDomainExpr with
              | true =>
                  some (Expr.subst0 argumentExpr currentBodyTypeExpr)
              | false => none
          | none => none
      | some (Expr.bvar _) => none
      | some (Expr.sort _) => none
      | some (Expr.const _) => none
      | some (Expr.lam _ _) => none
      | some (Expr.app _ _) => none
      | none => none
    let functionCaseEquality :
        Eq
          (Expr.inferCore?
            environment
            context
            (Expr.app functionExpr argumentExpr))
          (functionCase
            (Expr.inferCore? environment context functionExpr)) :=
      Eq.refl
        (Expr.inferCore?
          environment
          context
          (Expr.app functionExpr argumentExpr))
    let functionCaseProjected :=
      congrArg functionCase functionInference
    let argumentCaseEquality :
        Eq
          (functionCase (some (Expr.pi domainExpr bodyTypeExpr)))
          (argumentCase
            (Expr.inferCore? environment context argumentExpr)) :=
      Eq.refl
        (argumentCase
          (Expr.inferCore? environment context argumentExpr))
    let argumentCaseProjected :=
      congrArg argumentCase argumentInference
    let checkCaseEquality :
        Eq
          (argumentCase (some argumentTypeExpr))
          (checkCase (Expr.checkerBeq argumentTypeExpr domainExpr)) :=
      Eq.refl
        (checkCase (Expr.checkerBeq argumentTypeExpr domainExpr))
    let checkCaseProjected :=
      congrArg checkCase argumentTypeCheck
    Eq.trans
      functionCaseEquality
      (Eq.trans
        functionCaseProjected
        (Eq.trans
          argumentCaseEquality
          (Eq.trans argumentCaseProjected
            (Eq.trans checkCaseEquality checkCaseProjected))))
  let typeEquality :=
    CheckOption.some_injective
      (Eq.trans (Eq.symm branchEquality) inferenceSucceeded)
  match typeEquality with
  | Eq.refl _ => HasType.app functionHasPi argumentHasDomain

/-- Turn an impossible runtime-facing inference failure into the requested
typing result.  All callers must provide both the computed `none` branch and
the contradictory accepted `some` result. -/
theorem inferCore_none_absurd
    {environment : Environment}
    {context : Context}
    {expression inferredTypeExpr : Expr}
    (inferenceFailed :
      Eq (Expr.inferCore? environment context expression) none)
    (inferenceSucceeded :
      Eq
        (Expr.inferCore? environment context expression)
        (some inferredTypeExpr)) :
    HasType environment context expression inferredTypeExpr :=
  let noneEqualsSome :=
    Eq.trans (Eq.symm inferenceFailed) inferenceSucceeded
  nomatch noneEqualsSome

/-- Soundness of runtime-facing core inference for the accepted no-constant
fragment. -/
theorem inferCore_sound
    {environment : Environment}
    {context : Context} :
    (expression : Expr) -> {inferredTypeExpr : Expr} ->
      Eq
        (Expr.inferCore? environment context expression)
        (some inferredTypeExpr) ->
      HasType environment context expression inferredTypeExpr
  | Expr.bvar _, _, inferenceSucceeded =>
      inferCore_bvar_sound inferenceSucceeded
  | Expr.sort _, _, inferenceSucceeded =>
      inferCore_sort_sound inferenceSucceeded
  | Expr.const _, _, inferenceSucceeded =>
      inferCore_const_sound inferenceSucceeded
  | Expr.pi domainExpr bodyExpr, inferredTypeExpr, inferenceSucceeded =>
      let piBodyCase (domainLevel : Level) : Option Expr -> Option Expr
        | some (Expr.sort currentBodyLevel) =>
            some (Expr.sort (Level.max domainLevel currentBodyLevel))
        | some (Expr.bvar _) => none
        | some (Expr.const _) => none
        | some (Expr.pi _ _) => none
        | some (Expr.lam _ _) => none
        | some (Expr.app _ _) => none
        | none => none
      let piDomainCase : Option Expr -> Option Expr
        | some (Expr.sort currentDomainLevel) =>
            piBodyCase currentDomainLevel
              (Expr.inferCore?
                environment
                (Context.extend context domainExpr)
                bodyExpr)
        | some (Expr.bvar _) => none
        | some (Expr.const _) => none
        | some (Expr.pi _ _) => none
        | some (Expr.lam _ _) => none
        | some (Expr.app _ _) => none
        | none => none
      let piDomainCaseEquality :
          Eq
            (Expr.inferCore?
              environment
              context
              (Expr.pi domainExpr bodyExpr))
            (piDomainCase
              (Expr.inferCore? environment context domainExpr)) :=
        Eq.refl
          (Expr.inferCore?
            environment
            context
            (Expr.pi domainExpr bodyExpr))
      let failFromDomainCase
          {domainResult : Option Expr}
          (domainInference :
            Eq
              (Expr.inferCore? environment context domainExpr)
              domainResult)
          (domainCaseFailed : Eq (piDomainCase domainResult) none) :
          HasType
            environment
            context
            (Expr.pi domainExpr bodyExpr)
            inferredTypeExpr :=
        inferCore_none_absurd
          (Eq.trans
            piDomainCaseEquality
            (Eq.trans
              (congrArg piDomainCase domainInference)
              domainCaseFailed))
          inferenceSucceeded
      match domainInference :
          Expr.inferCore? environment context domainExpr with
      | some (Expr.sort domainLevel) =>
          let domainHasSort :
              HasType environment context domainExpr (Expr.sort domainLevel) :=
            inferCore_sound
              (environment := environment)
              (context := context)
              domainExpr
              domainInference
          let bodyCaseEquality :
              Eq
                (piDomainCase (some (Expr.sort domainLevel)))
                (piBodyCase domainLevel
                  (Expr.inferCore?
                    environment
                    (Context.extend context domainExpr)
                    bodyExpr)) :=
            Eq.refl
              (piBodyCase domainLevel
                (Expr.inferCore?
                  environment
                  (Context.extend context domainExpr)
                  bodyExpr))
          let failFromBodyCase
              {bodyResult : Option Expr}
              (bodyInference :
                Eq
                  (Expr.inferCore?
                    environment
                    (Context.extend context domainExpr)
                    bodyExpr)
                  bodyResult)
              (bodyCaseFailed :
                Eq (piBodyCase domainLevel bodyResult) none) :
              HasType
                environment
                context
                (Expr.pi domainExpr bodyExpr)
                inferredTypeExpr :=
            inferCore_none_absurd
              (Eq.trans
                piDomainCaseEquality
                (Eq.trans
                  (congrArg piDomainCase domainInference)
                  (Eq.trans
                    bodyCaseEquality
                    (Eq.trans
                      (congrArg (piBodyCase domainLevel) bodyInference)
                      bodyCaseFailed))))
              inferenceSucceeded
          match bodyInference :
              Expr.inferCore?
                environment
                (Context.extend context domainExpr)
                bodyExpr with
          | some (Expr.sort bodyLevel) =>
              let bodyHasSort :
                  HasType
                    environment
                    (Context.extend context domainExpr)
                    bodyExpr
                    (Expr.sort bodyLevel) :=
                inferCore_sound
                  (environment := environment)
                  (context := Context.extend context domainExpr)
                  bodyExpr
                  bodyInference
              inferCore_pi_from_branch_sound
                domainInference
                bodyInference
                domainHasSort
                bodyHasSort
                inferenceSucceeded
          | some (Expr.bvar _) =>
              failFromBodyCase bodyInference (Eq.refl none)
          | some (Expr.const _) =>
              failFromBodyCase bodyInference (Eq.refl none)
          | some (Expr.pi _ _) =>
              failFromBodyCase bodyInference (Eq.refl none)
          | some (Expr.lam _ _) =>
              failFromBodyCase bodyInference (Eq.refl none)
          | some (Expr.app _ _) =>
              failFromBodyCase bodyInference (Eq.refl none)
          | none =>
              failFromBodyCase bodyInference (Eq.refl none)
      | some (Expr.bvar _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | some (Expr.const _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | some (Expr.pi _ _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | some (Expr.lam _ _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | some (Expr.app _ _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | none =>
          failFromDomainCase domainInference (Eq.refl none)
  | Expr.lam domainExpr bodyExpr, inferredTypeExpr, inferenceSucceeded =>
      let lamBodyCase : Option Expr -> Option Expr
        | some currentBodyTypeExpr =>
            some (Expr.pi domainExpr currentBodyTypeExpr)
        | none => none
      let lamDomainCase : Option Expr -> Option Expr
        | some (Expr.sort _) =>
            lamBodyCase
              (Expr.inferCore?
                environment
                (Context.extend context domainExpr)
                bodyExpr)
        | some (Expr.bvar _) => none
        | some (Expr.const _) => none
        | some (Expr.pi _ _) => none
        | some (Expr.lam _ _) => none
        | some (Expr.app _ _) => none
        | none => none
      let lamDomainCaseEquality :
          Eq
            (Expr.inferCore?
              environment
              context
              (Expr.lam domainExpr bodyExpr))
            (lamDomainCase
              (Expr.inferCore? environment context domainExpr)) :=
        Eq.refl
          (Expr.inferCore?
            environment
            context
            (Expr.lam domainExpr bodyExpr))
      let failFromDomainCase
          {domainResult : Option Expr}
          (domainInference :
            Eq
              (Expr.inferCore? environment context domainExpr)
              domainResult)
          (domainCaseFailed : Eq (lamDomainCase domainResult) none) :
          HasType
            environment
            context
            (Expr.lam domainExpr bodyExpr)
            inferredTypeExpr :=
        inferCore_none_absurd
          (Eq.trans
            lamDomainCaseEquality
            (Eq.trans
              (congrArg lamDomainCase domainInference)
              domainCaseFailed))
          inferenceSucceeded
      match domainInference :
          Expr.inferCore? environment context domainExpr with
      | some (Expr.sort domainLevel) =>
          let domainHasSort :
              HasType environment context domainExpr (Expr.sort domainLevel) :=
            inferCore_sound
              (environment := environment)
              (context := context)
              domainExpr
              domainInference
          let bodyCaseEquality :
              Eq
                (lamDomainCase (some (Expr.sort domainLevel)))
                (lamBodyCase
                  (Expr.inferCore?
                    environment
                    (Context.extend context domainExpr)
                    bodyExpr)) :=
            Eq.refl
              (lamBodyCase
                (Expr.inferCore?
                  environment
                  (Context.extend context domainExpr)
                  bodyExpr))
          let failFromBodyCase
              {bodyResult : Option Expr}
              (bodyInference :
                Eq
                  (Expr.inferCore?
                    environment
                    (Context.extend context domainExpr)
                    bodyExpr)
                  bodyResult)
              (bodyCaseFailed : Eq (lamBodyCase bodyResult) none) :
              HasType
                environment
                context
                (Expr.lam domainExpr bodyExpr)
                inferredTypeExpr :=
            inferCore_none_absurd
              (Eq.trans
                lamDomainCaseEquality
                (Eq.trans
                  (congrArg lamDomainCase domainInference)
                  (Eq.trans
                    bodyCaseEquality
                    (Eq.trans
                      (congrArg lamBodyCase bodyInference)
                      bodyCaseFailed))))
              inferenceSucceeded
          match bodyInference :
              Expr.inferCore?
                environment
                (Context.extend context domainExpr)
                bodyExpr with
          | some bodyTypeExpr =>
              let bodyHasType :
                  HasType
                    environment
                    (Context.extend context domainExpr)
                    bodyExpr
                    bodyTypeExpr :=
                inferCore_sound
                  (environment := environment)
                  (context := Context.extend context domainExpr)
                  bodyExpr
                  bodyInference
              inferCore_lam_from_branch_sound
                domainInference
                bodyInference
                domainHasSort
                bodyHasType
                inferenceSucceeded
          | none =>
              failFromBodyCase bodyInference (Eq.refl none)
      | some (Expr.bvar _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | some (Expr.const _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | some (Expr.pi _ _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | some (Expr.lam _ _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | some (Expr.app _ _) =>
          failFromDomainCase domainInference (Eq.refl none)
      | none =>
          failFromDomainCase domainInference (Eq.refl none)
  | Expr.app functionExpr argumentExpr, inferredTypeExpr, inferenceSucceeded =>
      let appCheckCase (bodyTypeExpr : Expr) : Bool -> Option Expr
        | true => some (Expr.subst0 argumentExpr bodyTypeExpr)
        | false => none
      let appArgumentCase
          (domainExpr bodyTypeExpr : Expr) :
          Option Expr -> Option Expr
        | some argumentTypeExpr =>
            appCheckCase bodyTypeExpr
              (Expr.checkerBeq argumentTypeExpr domainExpr)
        | none => none
      let appFunctionCase : Option Expr -> Option Expr
        | some (Expr.pi domainExpr bodyTypeExpr) =>
            appArgumentCase domainExpr bodyTypeExpr
              (Expr.inferCore? environment context argumentExpr)
        | some (Expr.bvar _) => none
        | some (Expr.sort _) => none
        | some (Expr.const _) => none
        | some (Expr.lam _ _) => none
        | some (Expr.app _ _) => none
        | none => none
      let appFunctionCaseEquality :
          Eq
            (Expr.inferCore?
              environment
              context
              (Expr.app functionExpr argumentExpr))
            (appFunctionCase
              (Expr.inferCore? environment context functionExpr)) :=
        Eq.refl
          (Expr.inferCore?
            environment
            context
            (Expr.app functionExpr argumentExpr))
      let failFromFunctionCase
          {functionResult : Option Expr}
          (functionInference :
            Eq
              (Expr.inferCore? environment context functionExpr)
              functionResult)
          (functionCaseFailed :
            Eq (appFunctionCase functionResult) none) :
          HasType
            environment
            context
            (Expr.app functionExpr argumentExpr)
            inferredTypeExpr :=
        inferCore_none_absurd
          (Eq.trans
            appFunctionCaseEquality
            (Eq.trans
              (congrArg appFunctionCase functionInference)
              functionCaseFailed))
          inferenceSucceeded
      match functionInference :
          Expr.inferCore? environment context functionExpr with
      | some (Expr.pi domainExpr bodyTypeExpr) =>
          let functionHasPi :
              HasType
                environment
                context
                functionExpr
                (Expr.pi domainExpr bodyTypeExpr) :=
            inferCore_sound
              (environment := environment)
              (context := context)
              functionExpr
              functionInference
          let argumentCaseEquality :
              Eq
                (appFunctionCase (some (Expr.pi domainExpr bodyTypeExpr)))
                (appArgumentCase domainExpr bodyTypeExpr
                  (Expr.inferCore? environment context argumentExpr)) :=
            Eq.refl
              (appArgumentCase domainExpr bodyTypeExpr
                (Expr.inferCore? environment context argumentExpr))
          let failFromArgumentCase
              {argumentResult : Option Expr}
              (argumentInference :
                Eq
                  (Expr.inferCore? environment context argumentExpr)
                  argumentResult)
              (argumentCaseFailed :
                Eq (appArgumentCase domainExpr bodyTypeExpr argumentResult)
                  none) :
              HasType
                environment
                context
                (Expr.app functionExpr argumentExpr)
                inferredTypeExpr :=
            inferCore_none_absurd
              (Eq.trans
                appFunctionCaseEquality
                (Eq.trans
                  (congrArg appFunctionCase functionInference)
                  (Eq.trans
                    argumentCaseEquality
                    (Eq.trans
                      (congrArg
                        (appArgumentCase domainExpr bodyTypeExpr)
                        argumentInference)
                      argumentCaseFailed))))
              inferenceSucceeded
          match argumentInference :
              Expr.inferCore? environment context argumentExpr with
          | some argumentTypeExpr =>
              let argumentHasInferredType :
                  HasType
                    environment
                    context
                    argumentExpr
                    argumentTypeExpr :=
                inferCore_sound
                  (environment := environment)
                  (context := context)
                  argumentExpr
                  argumentInference
              let checkCaseEquality :
                  Eq
                    (appArgumentCase
                      domainExpr
                      bodyTypeExpr
                      (some argumentTypeExpr))
                    (appCheckCase
                      bodyTypeExpr
                      (Expr.checkerBeq argumentTypeExpr domainExpr)) :=
                Eq.refl
                  (appCheckCase
                    bodyTypeExpr
                    (Expr.checkerBeq argumentTypeExpr domainExpr))
              let failFromCheckCase
                  {checkResult : Bool}
                  (argumentTypeCheck :
                    Eq
                      (Expr.checkerBeq argumentTypeExpr domainExpr)
                      checkResult)
                  (checkCaseFailed :
                    Eq
                      (appCheckCase bodyTypeExpr checkResult)
                      none) :
                  HasType
                    environment
                    context
                    (Expr.app functionExpr argumentExpr)
                    inferredTypeExpr :=
                inferCore_none_absurd
                  (Eq.trans
                    appFunctionCaseEquality
                    (Eq.trans
                      (congrArg appFunctionCase functionInference)
                      (Eq.trans
                        argumentCaseEquality
                        (Eq.trans
                          (congrArg
                            (appArgumentCase domainExpr bodyTypeExpr)
                            argumentInference)
                          (Eq.trans
                            checkCaseEquality
                            (Eq.trans
                              (congrArg
                                (appCheckCase bodyTypeExpr)
                                argumentTypeCheck)
                              checkCaseFailed))))))
                  inferenceSucceeded
              match argumentTypeCheck :
                  Expr.checkerBeq argumentTypeExpr domainExpr with
              | true =>
                  inferCore_app_from_branch_sound
                    functionInference
                    argumentInference
                    argumentTypeCheck
                    functionHasPi
                    argumentHasInferredType
                    inferenceSucceeded
              | false =>
                  failFromCheckCase argumentTypeCheck (Eq.refl none)
          | none =>
              failFromArgumentCase argumentInference (Eq.refl none)
      | some (Expr.bvar _) =>
          failFromFunctionCase functionInference (Eq.refl none)
      | some (Expr.sort _) =>
          failFromFunctionCase functionInference (Eq.refl none)
      | some (Expr.const _) =>
          failFromFunctionCase functionInference (Eq.refl none)
      | some (Expr.lam _ _) =>
          failFromFunctionCase functionInference (Eq.refl none)
      | some (Expr.app _ _) =>
          failFromFunctionCase functionInference (Eq.refl none)
      | none =>
          failFromFunctionCase functionInference (Eq.refl none)

/-- Executable checking against an expected type without proof payloads. -/
def checkCore? (environment : Environment) (context : Context)
    (expression expectedTypeExpr : Expr) : Bool :=
  Expr.checkBoolFromCoreType?
    expectedTypeExpr
    (Expr.inferCore? environment context expression)

/-- Runtime-facing checking is sound whenever the accepted runtime-facing
inference result is already known sound. -/
theorem checkCore_of_inferCore_sound
    {environment : Environment}
    {context : Context}
    {expression inferredTypeExpr expectedTypeExpr : Expr}
    (inferenceSucceeded :
      Eq
        (Expr.inferCore? environment context expression)
        (some inferredTypeExpr))
    (inferredTypeDerivation :
      HasType environment context expression inferredTypeExpr)
    (checkingSucceeded :
      Eq
        (Expr.checkCore?
          environment
          context
          expression
          expectedTypeExpr)
        true) :
    HasType environment context expression expectedTypeExpr :=
  let projectedEquality :
      Eq (Expr.checkerBeq inferredTypeExpr expectedTypeExpr) true :=
    Eq.trans
      (Eq.symm
        (congrArg
          (Expr.checkBoolFromCoreType? expectedTypeExpr)
          inferenceSucceeded))
      checkingSucceeded
  let inferredTypeEquality :=
    Expr.checkerBeq_sound
      inferredTypeExpr
      expectedTypeExpr
      projectedEquality
  match inferredTypeEquality with
  | Eq.refl _ => inferredTypeDerivation

/-- Soundness of runtime-facing checking for the accepted no-constant
fragment. -/
theorem checkCore_sound
    {environment : Environment}
    {context : Context}
    {expression expectedTypeExpr : Expr}
    (checkingSucceeded :
      Eq
        (Expr.checkCore?
          environment
          context
          expression
          expectedTypeExpr)
        true) :
    HasType environment context expression expectedTypeExpr :=
  match inferenceSucceeded :
      Expr.inferCore? environment context expression with
  | some _ =>
      Expr.checkCore_of_inferCore_sound
        inferenceSucceeded
        (Expr.inferCore_sound
          (environment := environment)
          (context := context)
          expression
          inferenceSucceeded)
        checkingSucceeded
  | none =>
      let falseEqualsTrue : Eq false true :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Expr.checkBoolFromCoreType? expectedTypeExpr)
              inferenceSucceeded))
          checkingSucceeded
      nomatch falseEqualsTrue

/-- Direct soundness for runtime-facing variable checking. -/
theorem checkCore_bvar_sound
    {environment : Environment}
    {context : Context}
    {index : Nat}
    {expectedTypeExpr : Expr}
    (checkingSucceeded :
      Eq
        (Expr.checkCore?
          environment
          context
          (Expr.bvar index)
          expectedTypeExpr)
        true) :
    HasType environment context (Expr.bvar index) expectedTypeExpr :=
  match lookupSucceeded : Context.lookupType? context index with
  | some _ =>
      Expr.checkCore_of_inferCore_sound
        lookupSucceeded
        (Expr.inferCore_bvar_sound lookupSucceeded)
        checkingSucceeded
  | none =>
      let falseEqualsTrue : Eq false true :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Expr.checkBoolFromCoreType? expectedTypeExpr)
              lookupSucceeded))
          checkingSucceeded
      nomatch falseEqualsTrue

/-- Direct soundness for runtime-facing sort checking. -/
theorem checkCore_sort_sound
    {environment : Environment}
    {context : Context}
    {sortLevel : Level}
    {expectedTypeExpr : Expr}
    (checkingSucceeded :
      Eq
        (Expr.checkCore?
          environment
          context
          (Expr.sort sortLevel)
          expectedTypeExpr)
        true) :
    HasType environment context (Expr.sort sortLevel) expectedTypeExpr :=
  let inferenceSucceeded :
      Eq
        (Expr.inferCore? environment context (Expr.sort sortLevel))
        (some (Expr.sort (Level.succ sortLevel))) :=
    Eq.refl (some (Expr.sort (Level.succ sortLevel)))
  Expr.checkCore_of_inferCore_sound
    inferenceSucceeded
    (Expr.inferCore_sort_sound inferenceSucceeded)
    checkingSucceeded

/-- Proof-carrying inference for the initial checker fragment. -/
def inferResult?
    (environment : Environment) (context : Context) :
    (expression : Expr) -> Option (InferResult environment context expression)
  | Expr.bvar index =>
      match Context.lookupTypeResult? context index with
      | some lookupResult =>
          some {
            typeExpr := lookupResult.typeExpr
            typeDerivation := HasType.var lookupResult.typeAtIndex
          }
      | none => none
  | Expr.sort sortLevel =>
      some {
        typeExpr := Expr.sort (Level.succ sortLevel)
        typeDerivation := HasType.sort context sortLevel
      }
  | Expr.const constName =>
      match Environment.findByNameResult? environment constName with
      | some lookupResult =>
          some {
            typeExpr := Declaration.typeExpr lookupResult.declaration
            typeDerivation := HasType.const lookupResult.declarationMember
          }
      | none => none
  | Expr.pi domainExpr bodyExpr =>
      match Expr.inferResult? environment context domainExpr with
      | some {
          typeExpr := domainTypeExpr
          typeDerivation := domainTypeDerivation
        } =>
          match domainTypeExpr with
          | Expr.sort domainLevel =>
              match Expr.inferResult?
                  environment
                  (Context.extend context domainExpr)
                  bodyExpr with
              | some {
                  typeExpr := bodyTypeExpr
                  typeDerivation := bodyTypeDerivation
                } =>
                  match bodyTypeExpr with
                  | Expr.sort bodyLevel =>
                      some {
                        typeExpr := Expr.sort
                          (Level.max domainLevel bodyLevel)
                        typeDerivation :=
                          HasType.pi
                            domainTypeDerivation
                            bodyTypeDerivation
                      }
                  | Expr.bvar _ => none
                  | Expr.const _ => none
                  | Expr.pi _ _ => none
                  | Expr.lam _ _ => none
                  | Expr.app _ _ => none
              | none => none
          | Expr.bvar _ => none
          | Expr.const _ => none
          | Expr.pi _ _ => none
          | Expr.lam _ _ => none
          | Expr.app _ _ => none
      | none => none
  | Expr.lam domainExpr bodyExpr =>
      match Expr.inferResult? environment context domainExpr with
      | some {
          typeExpr := domainTypeExpr
          typeDerivation := domainTypeDerivation
        } =>
          match domainTypeExpr with
          | Expr.sort _ =>
              match Expr.inferResult?
                  environment
                  (Context.extend context domainExpr)
                  bodyExpr with
              | some bodyResult =>
                  some {
                    typeExpr := Expr.pi domainExpr bodyResult.typeExpr
                    typeDerivation :=
                      HasType.lam
                        domainTypeDerivation
                        bodyResult.typeDerivation
                  }
              | none => none
          | Expr.bvar _ => none
          | Expr.const _ => none
          | Expr.pi _ _ => none
          | Expr.lam _ _ => none
          | Expr.app _ _ => none
      | none => none
  | Expr.app functionExpr argumentExpr =>
      match Expr.inferResult? environment context functionExpr with
      | some {
          typeExpr := functionTypeExpr
          typeDerivation := functionTypeDerivation
        } =>
          match functionTypeExpr with
          | Expr.pi domainExpr bodyTypeExpr =>
              match Expr.inferResult? environment context argumentExpr with
              | some argumentResult =>
                  match h :
                      Expr.checkerBeq argumentResult.typeExpr domainExpr with
                  | true =>
                      let argumentTypeEquality :=
                        Expr.checkerBeq_sound
                          argumentResult.typeExpr
                          domainExpr
                          h
                      let argumentHasDomain :
                          HasType
                            environment
                            context
                            argumentExpr
                            domainExpr :=
                        match argumentTypeEquality with
                        | Eq.refl _ => argumentResult.typeDerivation
                      some {
                        typeExpr :=
                          Expr.subst0 argumentExpr bodyTypeExpr
                        typeDerivation :=
                          HasType.app
                            functionTypeDerivation
                            argumentHasDomain
                      }
                  | false => none
              | none => none
          | Expr.bvar _ => none
          | Expr.sort _ => none
          | Expr.const _ => none
          | Expr.lam _ _ => none
          | Expr.app _ _ => none
      | none => none

/-- Infer the type of an FX1 expression in the initial no-constant checker
fragment. -/
def infer? (environment : Environment) (context : Context)
    (expression : Expr) : Option Expr :=
  Expr.inferTypeFromResult?
    (Expr.inferResult? environment context expression)

/-- Soundness of executable inference. -/
theorem infer?_sound
    {environment : Environment}
    {context : Context}
    {expression inferredTypeExpr : Expr}
    (inferenceSucceeded :
      Eq
        (Expr.infer? environment context expression)
        (some inferredTypeExpr)) :
    HasType environment context expression inferredTypeExpr :=
  match h :
      Expr.inferResult? environment context expression with
  | some inferenceResult =>
      let projectedEquality :
          Eq (some inferenceResult.typeExpr) (some inferredTypeExpr) :=
        Eq.trans
          (Eq.symm
            (congrArg
              Expr.inferTypeFromResult?
              h))
          inferenceSucceeded
      let typeEquality :=
        CheckOption.some_injective projectedEquality
      match typeEquality with
      | Eq.refl _ => inferenceResult.typeDerivation
  | none =>
      let noneEqualsSome :
          Eq (none : Option Expr) (some inferredTypeExpr) :=
        Eq.trans
          (Eq.symm
            (congrArg
              Expr.inferTypeFromResult?
              h))
          inferenceSucceeded
      nomatch noneEqualsSome

/-- Check an expression against an expected type using checker equality. -/
def check? (environment : Environment) (context : Context)
    (expression expectedTypeExpr : Expr) : Bool :=
  Expr.checkBoolFromResult?
    expectedTypeExpr
    (Expr.inferResult? environment context expression)

/-- Soundness of executable checking. -/
theorem check?_sound
    {environment : Environment}
    {context : Context}
    {expression expectedTypeExpr : Expr}
    (checkingSucceeded :
      Eq
        (Expr.check? environment context expression expectedTypeExpr)
        true) :
    HasType environment context expression expectedTypeExpr :=
  match h :
      Expr.inferResult? environment context expression with
  | some inferenceResult =>
      let projectedEquality :
          Eq
            (Expr.checkerBeq inferenceResult.typeExpr expectedTypeExpr)
            true :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Expr.checkBoolFromResult? expectedTypeExpr)
              h))
          checkingSucceeded
      let inferredTypeEquality :=
        Expr.checkerBeq_sound
          inferenceResult.typeExpr
          expectedTypeExpr
          projectedEquality
      match inferredTypeEquality with
      | Eq.refl _ => inferenceResult.typeDerivation
  | none =>
      let falseEqualsTrue : Eq false true :=
        Eq.trans
          (Eq.symm
            (congrArg
              (Expr.checkBoolFromResult? expectedTypeExpr)
              h))
          checkingSucceeded
      nomatch falseEqualsTrue

end Expr

end LeanFX2.FX1
