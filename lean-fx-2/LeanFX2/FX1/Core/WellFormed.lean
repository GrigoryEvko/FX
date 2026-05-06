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

namespace WellFormed

/-- Context well-formedness is stable when the environment is extended by one
newer declaration. -/
theorem weaken_environment
    {environment : Environment}
    {context : Context}
    (newDeclaration : Declaration)
    (contextWellFormed : WellFormed environment context) :
    WellFormed (Environment.extend environment newDeclaration) context :=
  match contextWellFormed with
  | WellFormed.empty => WellFormed.empty
  | WellFormed.extend precedingContextWellFormed typeHasSort =>
      WellFormed.extend
        (weaken_environment newDeclaration precedingContextWellFormed)
        (HasType.weaken_environment newDeclaration typeHasSort)

end WellFormed

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

namespace NameFresh

/-- Name freshness is stable under extension by a declaration with a distinct
name. -/
theorem weaken
    {environment : Environment}
    {queryName : Name}
    (newDeclaration : Declaration)
    (olderFresh : NameFresh environment queryName)
    (namesDistinct :
      Not (Eq queryName (Declaration.name newDeclaration))) :
    NameFresh
      (Environment.extend environment newDeclaration)
      queryName :=
  NameFresh.older newDeclaration olderFresh namesDistinct

end NameFresh

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

namespace WellTyped

/-- Declaration well-typedness is stable when the preceding environment is
extended by one newer declaration. -/
theorem weaken_environment
    {environment : Environment}
    {declaration : Declaration}
    (newDeclaration : Declaration)
    (declarationWellTyped : WellTyped environment declaration) :
    WellTyped
      (Environment.extend environment newDeclaration)
      declaration :=
  match declarationWellTyped with
  | WellTyped.axiomDecl typeHasSort =>
      WellTyped.axiomDecl
        (HasType.weaken_environment newDeclaration typeHasSort)
  | WellTyped.defDecl typeHasSort valueHasType =>
      WellTyped.defDecl
        (HasType.weaken_environment newDeclaration typeHasSort)
        (HasType.weaken_environment newDeclaration valueHasType)
  | WellTyped.theoremDecl typeHasSort proofHasType =>
      WellTyped.theoremDecl
        (HasType.weaken_environment newDeclaration typeHasSort)
        (HasType.weaken_environment newDeclaration proofHasType)

end WellTyped

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

namespace TransparentDefinition

/-- A checked newest transparent definition has its value typed at the declared
type after the environment extension that exposes the constant.

This is the local delta-preservation payload for `TransparentDefinition.newestDef`.
Older transparent payloads are transported by `HasType.weaken_environment`. -/
theorem newestDef_value_has_type
    {environment : Environment}
    {declName : Name}
    {typeExpr valueExpr : Expr}
    (definitionWellTyped :
      Declaration.WellTyped
        environment
        (Declaration.defDecl declName typeExpr valueExpr)) :
    HasType
      (Environment.extend environment
        (Declaration.defDecl declName typeExpr valueExpr))
      Context.empty
      valueExpr
      typeExpr :=
  match definitionWellTyped with
  | Declaration.WellTyped.defDecl _ valueHasType =>
      HasType.weaken_environment
        (Declaration.defDecl declName typeExpr valueExpr)
        valueHasType

/-- A checked newest transparent theorem has its proof typed at the declared
type after the environment extension that exposes the theorem constant.

This is the local delta-preservation payload for
`TransparentDefinition.newestTheorem`. -/
theorem newestTheorem_proof_has_type
    {environment : Environment}
    {declName : Name}
    {typeExpr proofExpr : Expr}
    (theoremWellTyped :
      Declaration.WellTyped
        environment
        (Declaration.theoremDecl declName typeExpr proofExpr)) :
    HasType
      (Environment.extend environment
        (Declaration.theoremDecl declName typeExpr proofExpr))
      Context.empty
      proofExpr
      typeExpr :=
  match theoremWellTyped with
  | Declaration.WellTyped.theoremDecl _ proofHasType =>
      HasType.weaken_environment
        (Declaration.theoremDecl declName typeExpr proofExpr)
        proofHasType

end TransparentDefinition

/-- Extending an environment with a transparent definition does not add an
executable axiom placeholder. -/
theorem hasAxiomDeclaration_extend_defDecl
    (environment : Environment)
    (declName : Name)
    (typeExpr valueExpr : Expr) :
    Eq
      (Environment.hasAxiomDeclaration
        (Environment.extend environment
          (Declaration.defDecl declName typeExpr valueExpr)))
      (Environment.hasAxiomDeclaration environment) :=
  Eq.refl (Environment.hasAxiomDeclaration environment)

/-- Extending an environment with a checked theorem does not add an executable
axiom placeholder. -/
theorem hasAxiomDeclaration_extend_theoremDecl
    (environment : Environment)
    (declName : Name)
    (typeExpr proofExpr : Expr) :
    Eq
      (Environment.hasAxiomDeclaration
        (Environment.extend environment
          (Declaration.theoremDecl declName typeExpr proofExpr)))
      (Environment.hasAxiomDeclaration environment) :=
  Eq.refl (Environment.hasAxiomDeclaration environment)

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

/-- Release well-formed environments contain no executable axiom
placeholders.  This connects the propositional release predicate to the
environment-level Boolean gate used by future checker entry points. -/
theorem hasAxiomDeclaration_false
    {environment : Environment}
    (environmentReleaseWellFormed : ReleaseWellFormed environment) :
    Eq (Environment.hasAxiomDeclaration environment) false :=
  match environmentReleaseWellFormed with
  | ReleaseWellFormed.empty => Eq.refl false
  | ReleaseWellFormed.extend
      precedingReleaseWellFormed _ _
      (Declaration.IsReleaseDeclaration.defDecl declName typeExpr valueExpr) =>
      Eq.trans
        (Environment.hasAxiomDeclaration_extend_defDecl
          _ declName typeExpr valueExpr)
        (hasAxiomDeclaration_false precedingReleaseWellFormed)
  | ReleaseWellFormed.extend
      precedingReleaseWellFormed _ _
      (Declaration.IsReleaseDeclaration.theoremDecl declName typeExpr proofExpr) =>
      Eq.trans
        (Environment.hasAxiomDeclaration_extend_theoremDecl
          _ declName typeExpr proofExpr)
        (hasAxiomDeclaration_false precedingReleaseWellFormed)

end ReleaseWellFormed

end Environment

end LeanFX2.FX1
