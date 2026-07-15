import FX1Poly.Typed.Engine.RuleTables.CellTemplate
import FX1Poly.Typed.Engine.RuleTables.ElimRuleTable

/-! # FX1Poly/Typed/Engine/RuleTables/CellTemplateInterpretAdequacy
    — the SR-DSL-0c down-payment: `interpret?` is `rfl`-faithful to the shipped rule outputs/classifiers

SR-DSL-0c reifies every `ElimRule` output type and every obligation classifier as a `CellTemplate` and proves
`interpret? … template = some (the shipped fn)` by `rfl` per row.  This file validates the THREE core
`interpret?` mechanisms end-to-end, each as a pure `rfl`, so the whole DSL approach is de-risked before the full
per-row reification:

  * **`subst0Into` + `childAt`** — the `app` output type `subst0 codomainCode argument`, proved equal to the
    shipped `appElimRule.outputType` (the `paramChild`/`argChild` projection + the `subst0` of a shift-1 body);
  * **the `macroReBasing` DEPTH-PEEL** — the `natElim` succ-branch classifier
    `natElimDependentSuccBranchType motive`, interpreted at the obligation's depth 2 (the `+2` macro peels `2`
    from the depth so `weakenBodyUnderTwoBindersBy 0` is the identity — exactly the `rfl`-faithfulness the peel
    was designed for);
  * **the `universeCode` leaf** — the result-type formedness classifier `universeCodeCell level0 flag`, via
    `resolveLevelSource .level0Existential = level0` and `resolveFlagSource .ruleFlag = flag`.

Each lemma is a single `rfl`: on concrete `childCons` children the shared `ScopedChild` machinery
(`toScopedChildren` / `scopedChildAt?` / `atShift{Zero,One}?`) and the depth weakenings (`weakenBy 0`,
`weakenBodyUnder{One,Two}BinderBy 0`) all reduce definitionally, and so do the shipped rule fields.

## Zero-axiom

Pure `rfl` proofs over the (audited zero-axiom) `interpret?` + the (audited zero-axiom) rule table.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax

/-- The `app` output type as a `CellTemplate`: `subst0` of the one-binder codomain param (`paramChild 1`) by the
argument (`argChild 1`).  Mirrors `appElimRule.outputType`'s `subst0 codomainCode argument`. -/
def appOutputTemplate : CellTemplate := .subst0Into (.paramChild 1) (.childAt (.argChild 1))

/-- **`subst0Into` + `childAt` adequacy.**  `interpret?` on `appOutputTemplate` at depth 0 reproduces the shipped
`appElimRule.outputType` exactly, by `rfl` — the projection of the shift-0 argument and the `subst0` of the
shift-1 codomain body both reduce definitionally on the concrete `childCons` children. -/
theorem appOutputTemplate_adequate {scope : Nat}
    (function argument domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
    (levels : List LevelExpr) (level0 level1 carrierLevel : LevelExpr) (flag : UniverseFlag) :
    CellTemplate.interpret?
        (.childCons function (.childCons argument .childNil) : RawTermChildren [0, 0] scope)
        (.childCons domainCode (.childCons codomainCode .childNil) : RawTermChildren [0, 1] scope)
        levels level0 level1 carrierLevel flag 0 appOutputTemplate
      = some (appElimRule.outputType scope
          (.childCons function (.childCons argument .childNil))
          (.childCons domainCode (.childCons codomainCode .childNil))) :=
  rfl

/-- The `natElim` / `natRec` succ-branch classifier as a `CellTemplate`: the `+2` `macroReBasing` over the motive
(`argChild 0`).  Mirrors the succ obligation's `classifier := natElimDependentSuccBranchType motive` at the
obligation scope `scope + 2`. -/
def natElimSuccBranchClassifierTemplate : CellTemplate :=
  .macroReBasing (.natSuccBranchType (.argChild 0))

/-- **The `macroReBasing` DEPTH-PEEL adequacy.**  Interpreted at the succ obligation's depth 2, the `+2` macro
peels `2` from the depth (`weakenBodyUnderTwoBindersBy 0` = identity) and reproduces the shipped
`natElimDependentSuccBranchType motive` exactly, by `rfl`.  This is the crux validation: the depth-peel makes a
binder-adding branch classifier `rfl`-faithful with NO cast. -/
theorem natElimSuccBranchClassifierTemplate_adequate {scope : Nat}
    (motive : RawTerm (scope + 1)) (baseBranch : RawTerm scope)
    (stepBranch : RawTerm (scope + 2)) (scrutinee : RawTerm scope)
    (params : RawTermChildren [] scope)
    (levels : List LevelExpr) (level0 level1 carrierLevel : LevelExpr) (flag : UniverseFlag) :
    CellTemplate.interpret?
        (.childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil)))
          : RawTermChildren [1, 0, 2, 0] scope)
        params levels level0 level1 carrierLevel flag 2 natElimSuccBranchClassifierTemplate
      = some (natElimDependentSuccBranchType motive) :=
  rfl

/-- The result-type formedness classifier as a `CellTemplate`: the `universeCode` leaf reading the rule's first
level existential + threaded flag.  Mirrors the self-certifying `classifier := universeCodeCell level0 flag`
obligation shared by `pathApp` / the data eliminators / the projections. -/
def universeFormednessClassifierTemplate : CellTemplate :=
  .universeCode .level0Existential .ruleFlag

/-- **The `universeCode` leaf adequacy.**  `interpret?` resolves `.level0Existential` to `level0` and `.ruleFlag`
to `flag` and reproduces the shipped `universeCodeCell level0 flag` exactly, by `rfl` (independent of the cell's
children — the leaf reads only the universe existentials). -/
theorem universeFormednessClassifierTemplate_adequate {scope : Nat}
    (args : RawTermChildren [] scope) (params : RawTermChildren [] scope)
    (levels : List LevelExpr) (level0 level1 carrierLevel : LevelExpr) (flag : UniverseFlag) :
    CellTemplate.interpret? args params levels level0 level1 carrierLevel flag 0
        universeFormednessClassifierTemplate
      = some (universeCodeCell level0 flag) :=
  rfl

/-- The `app` function-premise classifier as a `CellTemplate`: the `piTyCodeCell` built from the shift-0 domain
param (`childAt (paramChild 0)`) and the shift-1 codomain BODY param (`childBodyAt (paramChild 1)`), with the
`Unit` payload family.  Mirrors `appElimRule`'s function obligation `classifier := piTyCodeCell domainCode
codomainCode`. -/
def appFunctionClassifierTemplate : CellTemplate :=
  .builtGen .gen_piTyCode (fun _ => ())
    (.spineCons (.childAt (.paramChild 0)) (.spineCons (.childBodyAt (.paramChild 1)) .spineNil))

/-- **`builtGen` + `childBodyAt` adequacy** (the two remaining mechanisms).  `interpret?` builds the
`piTyCodeCell` from the projected shift-0 domain and — via the new `childBodyAt` node — the raw shift-1 codomain
body, reproducing the shipped `piTyCodeCell domainCode codomainCode` exactly, by `rfl`.  The `childBodyAt` of the
shift-1 codomain is interpreted at the piTyCode child's depth 1 (`weakenBodyUnderOneBinderBy 0` = identity), and
the `Unit` `payloadFamily` resolves to the cell's `()` payload. -/
theorem appFunctionClassifierTemplate_adequate {scope : Nat}
    (args : RawTermChildren [0, 0] scope)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
    (levels : List LevelExpr) (level0 level1 carrierLevel : LevelExpr) (flag : UniverseFlag) :
    CellTemplate.interpret? args
        (.childCons domainCode (.childCons codomainCode .childNil) : RawTermChildren [0, 1] scope)
        levels level0 level1 carrierLevel flag 0 appFunctionClassifierTemplate
      = some (piTyCodeCell domainCode codomainCode) :=
  rfl

end FX1Poly.Typed
