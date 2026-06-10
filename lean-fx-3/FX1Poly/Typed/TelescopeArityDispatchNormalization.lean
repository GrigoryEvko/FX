import FX1Poly.Typed.TelescopeSubstitutedChildrenNormalization

/-! # FX1Poly/Typed/TelescopeArityDispatchNormalization
   — telescope reducibility ⟹ fold-children all-SN, dispatched by arity (GTL-06 brick 3a)

The symbolic-generator membership arm (`dataFormationUnderSubst`) consumes strong
normalization of the substituted child spine in the `foldChildren GenAlgebra.canonical`
spelling — the `subst_nonVar_reduces` right-hand side.  This module supplies that hypothesis
from `TelescopeReducible` at a SYMBOLIC shape, completing the by_cases-free dispatch chain:

  * The shape equation is taken over a FREE `binderShifts` index (`shapeEq : binderShifts =
    consecutiveShifts 0 levels.length`), so `subst` eliminates the index cast outright — the
    children then sit at a literal spine index once `levels` is cased, and the brick-2
    corollaries apply directly.  At a dispatch call site the lemma is applied with
    `binderShifts := generator.binderShifts`; the cast discipline lives HERE, once.
  * The arity dispatch cases `levels` at the three shapes the formation table uses (nullary,
    one-child `[0]`, two-child `[0,1]`); the impossible three-child-and-beyond case is
    discharged from the explicit `arityBound` hypothesis by `Nat.le` inversion — the bound
    itself is the ONE table-coupled fact, supplied at call sites (a self-updating tag-bounded
    decision is the recorded follow-on).

## Zero-axiom verification

`subst` + `match` + the brick-2 corollaries + two `Nat.le_of_succ_le_succ` inversions.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTypedReducibilityCandidates.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Telescope reducibility ⟹ fold-children all-SN, by arity dispatch.**  Over a FREE
`binderShifts` pinned to the consecutive-shifts shape by `shapeEq`, the telescope logical
relation yields strong normalization of the `foldChildren`-substituted spine — the exact
hypothesis of `dataFormationUnderSubst` — at every arity the formation table admits (the
`arityBound` excludes a third child; no current row has one). -/
theorem TelescopeReducible.foldChildrenStronglyNormalizing
    {baseScope targetScope : Nat} {flag : UniverseFlag}
    {binderShifts : List Nat}
    {children : RawTermChildren binderShifts baseScope}
    {substitution : RawTermSubst baseScope (targetScope + 1)}
    {levels : List LevelExpr} (predLevel : Nat)
    (shapeEq : binderShifts = consecutiveShifts 0 levels.length)
    (arityBound : levels.length ≤ 2)
    (telescope : TelescopeReducible flag 0 levels.length substitution levels
      (shapeEq ▸ children)) :
    RawTermChildren.allStronglyNormalizing
      (foldChildren GenAlgebra.canonical substitution children) := by
  subst shapeEq
  match levels, children, telescope with
  | [], .childNil, _telescope =>
      exact True.intro
  | [elementLevel], .childCons elementCode .childNil, telescope =>
      exact telescope.substitutedOneChildSpineStronglyNormalizing
  | [domainLevel, codomainLevel],
      .childCons domainCode (.childCons codomainCode .childNil), telescope =>
      exact telescope.substitutedTwoChildSpineStronglyNormalizing predLevel
  | _ :: _ :: _ :: _, _children, _telescope =>
      exact nomatch Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ arityBound)

end FX1Poly.Typed
