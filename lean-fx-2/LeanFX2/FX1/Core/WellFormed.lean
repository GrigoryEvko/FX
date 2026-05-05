prelude
import LeanFX2.FX1.Core.HasType

/-! # FX1/Core/WellFormed

Root status: Root-FX1 metatheory scaffold.

Well-formedness predicates for contexts and environments.  These relations are
kept separate from `HasType` so the first typing relation remains small, while
preservation and checker soundness can quantify over well-formed inputs.

Name freshness is propositional rather than executable: the minimal root does
not trust host-side name equality.  Release well-formedness also rejects
`axiomDecl`, so staged environments can be represented without making axioms
part of the release trusted root.
-/

namespace LeanFX2.FX1

namespace Context

/-- A context is well formed when each binder type is itself typed as a sort in
the preceding context. -/
inductive WellFormed (environment : Environment) : Context -> Prop
  /-- The empty context is well formed. -/
  | empty : WellFormed environment Context.empty
  /-- Extending a well-formed context by a type expression preserves
  well-formedness when the new binder type has some sort. -/
  | extend
      {context : Context}
      {typeExpr : Expr}
      {sortLevel : Level}
      (contextWellFormed : WellFormed environment context)
      (typeHasSort :
        HasType environment context typeExpr (Expr.sort sortLevel)) :
      WellFormed environment (Context.extend context typeExpr)

end Context

namespace Environment

/-- `queryName` is fresh for an environment when no existing declaration has
that exact name.  This is propositional and therefore does not require trusting
host-side decidable equality for names. -/
inductive NameFresh : Environment -> Name -> Prop
  /-- Every name is fresh for the empty environment. -/
  | empty (queryName : Name) : NameFresh Environment.empty queryName
  /-- A name remains fresh after extending by a declaration with a distinct
  declaration name. -/
  | older
      {environment : Environment}
      {queryName : Name}
      (newDeclaration : Declaration)
      (olderFresh : NameFresh environment queryName)
      (namesDistinct :
        Not (Eq queryName (Declaration.name newDeclaration))) :
      NameFresh
        (Environment.extend environment newDeclaration)
        queryName

end Environment

namespace Declaration

/-- A declaration is well typed relative to the preceding environment. -/
inductive WellTyped (environment : Environment) : Declaration -> Prop
  /-- Axioms may appear in staged environments when their declared type has a
  sort.  Release well-formedness rejects this constructor separately. -/
  | axiomDecl
      {declName : Name}
      {typeExpr : Expr}
      {sortLevel : Level}
      (typeHasSort :
        HasType environment Context.empty typeExpr (Expr.sort sortLevel)) :
      WellTyped environment (Declaration.axiomDecl declName typeExpr)
  /-- Definitions are well typed when the declared type has a sort and the value
  checks at that declared type. -/
  | defDecl
      {declName : Name}
      {typeExpr valueExpr : Expr}
      {sortLevel : Level}
      (typeHasSort :
        HasType environment Context.empty typeExpr (Expr.sort sortLevel))
      (valueHasType :
        HasType environment Context.empty valueExpr typeExpr) :
      WellTyped environment (Declaration.defDecl declName typeExpr valueExpr)
  /-- Theorem declarations mirror definitions: the proof expression checks at
  the declared theorem type. -/
  | theoremDecl
      {declName : Name}
      {typeExpr proofExpr : Expr}
      {sortLevel : Level}
      (typeHasSort :
        HasType environment Context.empty typeExpr (Expr.sort sortLevel))
      (proofHasType :
        HasType environment Context.empty proofExpr typeExpr) :
      WellTyped environment
        (Declaration.theoremDecl declName typeExpr proofExpr)

/-- Declarations admitted by a release-root environment.  Axiom placeholders are
intentionally absent. -/
inductive IsReleaseDeclaration : Declaration -> Prop
  /-- Transparent definitions are release declarations. -/
  | defDecl
      (declName : Name)
      (typeExpr valueExpr : Expr) :
      IsReleaseDeclaration (Declaration.defDecl declName typeExpr valueExpr)
  /-- Checked theorem proofs are release declarations. -/
  | theoremDecl
      (declName : Name)
      (typeExpr proofExpr : Expr) :
      IsReleaseDeclaration
        (Declaration.theoremDecl declName typeExpr proofExpr)

namespace IsReleaseDeclaration

/-- Release declarations are never axiom placeholders. -/
theorem isAxiomDeclaration_false
    {declaration : Declaration}
    (isReleaseDeclaration : IsReleaseDeclaration declaration) :
    Eq (Declaration.isAxiomDeclaration declaration) false :=
  match isReleaseDeclaration with
  | IsReleaseDeclaration.defDecl _ _ _ => Eq.refl false
  | IsReleaseDeclaration.theoremDecl _ _ _ => Eq.refl false

end IsReleaseDeclaration

end Declaration

namespace Environment

/-- A staged environment is well formed when declarations are typed against the
previous environment and names are fresh.  This still allows axiom placeholders
for development and translation staging. -/
inductive WellFormed : Environment -> Prop
  /-- The empty environment is well formed. -/
  | empty : WellFormed Environment.empty
  /-- Extend a staged environment by one fresh, well-typed declaration. -/
  | extend
      {environment : Environment}
      {declaration : Declaration}
      (environmentWellFormed : WellFormed environment)
      (nameFresh :
        NameFresh environment (Declaration.name declaration))
      (declarationWellTyped :
        Declaration.WellTyped environment declaration) :
      WellFormed (Environment.extend environment declaration)

/-- A release environment is a staged well-formed environment whose declarations
are all release declarations. -/
inductive ReleaseWellFormed : Environment -> Prop
  /-- The empty environment is release-well-formed. -/
  | empty : ReleaseWellFormed Environment.empty
  /-- Extend a release environment by one fresh, typed, non-axiom declaration. -/
  | extend
      {environment : Environment}
      {declaration : Declaration}
      (environmentReleaseWellFormed : ReleaseWellFormed environment)
      (nameFresh :
        NameFresh environment (Declaration.name declaration))
      (declarationWellTyped :
        Declaration.WellTyped environment declaration)
      (isReleaseDeclaration :
        Declaration.IsReleaseDeclaration declaration) :
      ReleaseWellFormed (Environment.extend environment declaration)

namespace ReleaseWellFormed

/-- Release well-formedness implies staged well-formedness. -/
theorem toWellFormed
    {environment : Environment}
    (environmentReleaseWellFormed : ReleaseWellFormed environment) :
    WellFormed environment :=
  match environmentReleaseWellFormed with
  | ReleaseWellFormed.empty => WellFormed.empty
  | ReleaseWellFormed.extend
      precedingReleaseWellFormed nameFresh declarationWellTyped _ =>
      WellFormed.extend
        (toWellFormed precedingReleaseWellFormed)
        nameFresh
        declarationWellTyped

end ReleaseWellFormed

end Environment

end LeanFX2.FX1
