prelude
import LeanFX2.FX1.Core.Check.CheckBeq

/-! # LeanFX2.FX1.Core.Check.CheckLookup

Executable witness-producing lookup for the FX1 checker:

* `Environment.findTypeByName?` / `findTransparentValue?` with soundness
* `Context.lookupType?` with soundness

## Root status

Root-FX1 checker lookup slice. -/

namespace LeanFX2.FX1

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

end LeanFX2.FX1
