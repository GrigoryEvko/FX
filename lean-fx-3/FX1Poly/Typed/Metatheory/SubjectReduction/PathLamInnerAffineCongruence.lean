import FX1Poly.Typed.Dimensions.Graded.AppScaledSubstMetatheory
import FX1Poly.Core.Equality.Eta.EtaRowFiringSubstrate

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/PathLamInnerAffineCongruence — the inner-affine invariant

The DIMENSIONAL-multiplicity leg of `pathLam` affine subject reduction.  The structural-affinity theorem
(`PathLamStructuralAffinity`) handles only the FIBRANT leg via the Fitch lock; the App-SCALED affine grade
`appScaledDimensionGrade body 0 ≤ one` carries the complementary DIMENSIONAL-multiplicity leg, which must be
shown beta-stable: a body step preserves it.  That is FALSE for a raw body — a non-affine inner `pathLam`
admits an endpoint-β that duplicates the dimension (`appScaledRootPathBeta_le_ofAffine` is conditional).

This file isolates exactly that obligation behind ONE structural invariant: `AllInnerPathLamAffine body` ("every
`pathLam` subterm of `body` has an App-scaled-affine body").  Under it, the App-scaled grade IS beta-stable —
`appScaledDimensionGrade_step_le_ofSitesAffine` — UNCONDITIONALLY, instantiating the downward-closed-predicate
guarded congruence machinery (`appScaledDimensionGrade_step_le_ofGuarded_fueled`).  Every non-`pathApp` root
contraction is grade-non-increasing by PIECE 1 (`appScaledRootRedexPreservedExceptPathApp`); the `pathApp`
(endpoint-β) contraction is discharged from the invariant's witness for the inner body via
`appScaledRootPathBeta_le_ofAffine_unconditional`.

The residual — that a TYPED body satisfies `AllInnerPathLamAffine` (every inner `pathLam` is typed, hence
affine by `invertAtPathLamHead`) — is the A1-SUBST-OPEN subterm-typing metatheory, recorded as the single
honest bridge that closes `PathLamBodyStepPreservesAppScaledAffine`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Modal
open FX1Poly.Axis.Syntax

/- **The inner-affine structural invariant.**  `AllInnerPathLamAffine body` holds when every `pathLam`
subterm of `body` has an App-scaled-affine body (`appScaledDimensionGrade innerBody 0 ≤ one`).  Two
constructors avoid a generator wildcard: a `pathLam`-headed cell additionally demands its body's affine
grade, every other head only the children's invariant.  Mutually recursive with the spine version. -/
mutual
/-- The inner-affine invariant on a term: every `pathLam` subterm has an App-scaled-affine body. -/
inductive AllInnerPathLamAffine : ∀ {scope : Nat}, RawTerm scope → Prop where
  | pathLam {scope : Nat} {body : RawTerm (scope + 1)}
      (bodyAffine :
        UsageGrade.le (RawTerm.appScaledDimensionGrade body ⟨0, Nat.succ_pos scope⟩) UsageGrade.one
          = true)
      (bodyInner : AllInnerPathLamAffine body) :
      AllInnerPathLamAffine (.mkGen .gen_pathLam () (.childCons body .childNil))
  | other {scope : Nat} {generator : Generator} {payload : generator.payload scope}
      {children : RawTermChildren generator.binderShifts scope}
      (notPathLam : generator ≠ .gen_pathLam)
      (childrenInner : AllInnerPathLamAffineChildren children) :
      AllInnerPathLamAffine (.mkGen generator payload children)
inductive AllInnerPathLamAffineChildren :
    ∀ {scope : Nat} {binderShifts : List Nat}, RawTermChildren binderShifts scope → Prop where
  | nil {scope : Nat} : AllInnerPathLamAffineChildren (scope := scope) .childNil
  | cons {scope binderShift : Nat} {restShifts : List Nat} {childHead : RawTerm (scope + binderShift)}
      {childTail : RawTermChildren restShifts scope}
      (headAffine : AllInnerPathLamAffine childHead)
      (tailAffine : AllInnerPathLamAffineChildren childTail) :
      AllInnerPathLamAffineChildren (.childCons childHead childTail)
end

/-- The spine invariant reifies to `allSatisfy` of the term invariant (the downward-closure carrier the
guarded machinery consumes). -/
theorem AllInnerPathLamAffineChildren.toAllSatisfy :
    ∀ {scope : Nat} {binderShifts : List Nat} {children : RawTermChildren binderShifts scope},
      AllInnerPathLamAffineChildren children →
      RawTermChildren.allSatisfy (fun _ term => AllInnerPathLamAffine term) children
  | _, _, _, .nil => True.intro
  | _, _, _, .cons headAffine tailAffine =>
      ⟨headAffine, AllInnerPathLamAffineChildren.toAllSatisfy tailAffine⟩

/-- **`childClosed` for the inner-affine invariant.**  A node satisfying the invariant has all its children
satisfying it — both constructors expose the children's witnesses (the `pathLam` body via `bodyInner`, the
generic children via `childrenInner`). -/
theorem allInnerPathLamAffine_childClosed {scope : Nat} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    (nodeAffine : AllInnerPathLamAffine (.mkGen generator payload children)) :
    RawTermChildren.allSatisfy (fun _ term => AllInnerPathLamAffine term) children := by
  cases nodeAffine with
  | pathLam bodyAffine bodyInner => exact ⟨bodyInner, True.intro⟩
  | other notPathLam childrenInner => exact childrenInner.toAllSatisfy

/-- A `pathLam`-headed term satisfying the invariant exposes its body's App-scaled affine grade (the witness
the endpoint-β contraction consumes).  The `other` constructor is excluded by its `notPathLam` field. -/
theorem allInnerPathLamAffine_pathLamBodyAffine {scope : Nat} {body : RawTerm (scope + 1)}
    (nodeAffine : AllInnerPathLamAffine (.mkGen .gen_pathLam () (.childCons body .childNil))) :
    UsageGrade.le (RawTerm.appScaledDimensionGrade body ⟨0, Nat.succ_pos scope⟩) UsageGrade.one
      = true := by
  cases nodeAffine with
  | pathLam bodyAffine bodyInner => exact bodyAffine
  | other notPathLam childrenInner => exact absurd rfl notPathLam

/-- **`pathApp` is the eliminator of exactly one table row.**  `pathBetaIotaRow` is the unique
`iotaRuleTable` row whose eliminator generator is `gen_pathApp`; every other row's eliminator is a distinct
generator (decided structurally).  The discriminator that routes the guarded root obligation's `pathApp`
branch to the endpoint-β leaf. -/
theorem pathAppRowIsPathBeta (rule : IotaRuleDesc) (isRow : rule ∈ iotaRuleTable)
    (isPathApp : rule.elimGenerator = .gen_pathApp) : rule = pathBetaIotaRow := by
  cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => rfl
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow with
  | head => exact absurd isPathApp (by decide)
  | tail _ isRow => cases isRow

/-- **`rootGuarded` for the inner-affine invariant.**  Every table row's root contraction, AT a redex
satisfying `AllInnerPathLamAffine`, is App-scaled grade-non-increasing: the non-`pathApp` rows
unconditionally (PIECE 1, `appScaledRootRedexPreservedExceptPathApp`), and the `pathApp` (endpoint-β) row
from the invariant's witness for the inner `pathLam` body (`appScaledRootPathBeta_le_ofAffine_unconditional`).
The pathApp redex's first child is the inner `pathLam`; the invariant's downward closure delivers its body's
affine grade. -/
theorem allInnerPathLamAffine_rootGuarded {scope : Nat} (rule : IotaRuleDesc)
    (isRow : rule ∈ iotaRuleTable) (elimPayload : rule.elimGenerator.payload scope)
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope} {reduct : RawTerm scope}
    (redexAffine : AllInnerPathLamAffine (.mkGen rule.elimGenerator elimPayload spine))
    (fires : rule.firesOn? elimPayload spine = some reduct) (dimension : Fin scope) :
    UsageGrade.le (RawTerm.appScaledDimensionGrade reduct dimension)
      (RawTerm.appScaledDimensionGrade
        (.mkGen rule.elimGenerator elimPayload spine) dimension) = true := by
  by_cases isPathApp : rule.elimGenerator = .gen_pathApp
  · -- The `pathApp` row is `pathBetaIotaRow`; decompose the firing and read the inner body's affine grade.
    obtain rfl := pathAppRowIsPathBeta rule isRow isPathApp
    cases elimPayload
    cases spine with
    | childCons functionChild restSpine =>
      cases restSpine with
      | childCons argumentChild tailSpine =>
        cases tailSpine
        obtain ⟨pathBody, functionEq, reductEq⟩ := pathBetaRowFiringDecompose fires
        subst functionEq
        subst reductEq
        have innerNode :
            AllInnerPathLamAffine (.mkGen .gen_pathLam () (.childCons pathBody .childNil)) :=
          (allInnerPathLamAffine_childClosed redexAffine).1
        exact appScaledRootPathBeta_le_ofAffine_unconditional pathBody argumentChild dimension
          (allInnerPathLamAffine_pathLamBodyAffine innerNode)
  · exact appScaledRootRedexPreservedExceptPathApp rule isRow isPathApp elimPayload fires dimension

/-- **★ The App-scaled dimension grade is beta-stable under the inner-affine invariant.**  UNCONDITIONALLY
(no typing): if every `pathLam` subterm of `body` has an App-scaled-affine body, then ANY `Step` of `body`
does not increase the App-scaled grade.  Instantiates the downward-closed-predicate guarded congruence
machinery at `AllInnerPathLamAffine`, discharging its `rootGuarded`/`childClosed` obligations.  This isolates
the residual for `PathLamBodyStepPreservesAppScaledAffine` to the single bridge `typed body ⟹
AllInnerPathLamAffine body` (every inner `pathLam` is typed, hence affine by `invertAtPathLamHead`) — the
A1-SUBST-OPEN subterm-typing metatheory. -/
theorem appScaledDimensionGrade_step_le_ofSitesAffine {scope : Nat} {body body' : RawTerm scope}
    (sitesAffine : AllInnerPathLamAffine body) (stepBody : Step body body') (dimension : Fin scope) :
    UsageGrade.le (RawTerm.appScaledDimensionGrade body' dimension)
      (RawTerm.appScaledDimensionGrade body dimension) = true :=
  RawTerm.appScaledDimensionGrade_step_le_ofGuarded_fueled
    (fun _ term => AllInnerPathLamAffine term)
    (fun rule isRow => allInnerPathLamAffine_rootGuarded rule isRow)
    (fun nodeAffine => allInnerPathLamAffine_childClosed nodeAffine)
    (RawTerm.size body) sitesAffine stepBody dimension (Nat.le_refl _)

end FX1Poly.Typed
