import FX1Poly.Core.FireRootRedex
import FX1Poly.Core.StepSubst

/-! # FX1Poly/Core/CompleteDevelopment
    — the Takahashi complete-development function, propext-clean via `fireRootRedex`.

`TakahashiTriangle.lean` reduces the FX raw-confluence diamond (`#420`, the prize that strong
normalization cannot supply because raw β+ι is not SN) to exhibiting a complete-development function
with the triangle / maximal-reduct property: a function that contracts ALL redexes present in a term
at once (but NOT the redexes created by those contractions), to which every parallel reduct
further parallel-reduces.  This file ships that function.

## The propext-clean construction recipe

A direct definition matching the ~18 redex shapes (β-redex `app (lam body) arg`, each ι-redex
`boolElim true · ·`, …) with overlapping nested patterns plus a fallback generates a Lean matcher
that leaks `propext` (the deeply-nested-overlapping-pattern trap) and defeats the equation compiler.

The clean construction delegates ALL redex-shape detection to the already-propext-clean
`RawTerm.fireRootRedex` (gated in `AuditTyped.lean`), so this file does only flat structural matches:

* `fireRootRedexOrSelf` — fire the root redex if present (`Option.getD` over `fireRootRedex`), else
  keep the cell.  Non-recursive, a single `Option` match.
* `completeDevelopment` / `completeDevelopmentChildren` — develop every child, then fire the root
  redex once.  The only matches are `mkGen` (one constructor) and `childNil`/`childCons` (two
  non-overlapping constructors), so no propext-leaking matcher is generated.

This is exactly Takahashi's complete development: developing the children first contracts all
redexes inside them; firing the (developed) root once contracts the head redex; and because
`fireRootRedex`'s ι-contractums build the recursive eliminator call SYNTACTICALLY (e.g.
`natElim … (succ n) ↦ app (app s n) (natElim … n)`), the redexes CREATED by contraction are left
untouched — the defining property that separates the complete development from full normalization.

`completeDevelopment_stepStar` confirms the development sits inside the existing reduction relation:
the source `StepStar`-reduces to its complete development (children congruence via
`StepStar.ofChildrenStar`, then the root firing via `fireRootRedex_sound`).  This is the soundness
half feeding the eventual `HasMaximalReduct ParStep` proof (the triangle), which discharges the
`ParStep` diamond and hence — through the shipped `Step ⊆ ParStep ⊆ StepStar` sandwich — unconditional
raw confluence.

## Zero-axiom verification

The functions are flat structural mutual recursion (no `termination_by`); `fireRootRedexOrSelf_stepStar`
is `cases` on the `Option` + `fireRootRedex_sound`; `completeDevelopment_stepStar` is term-mode mutual
recursion composing `StepStar.ofChildrenStar`, `StepChildrenStar.here`/`there`/`trans_compose`, and
`StepStar.trans_compose`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega`.  Gated per declaration in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open Foundation

/-- **Fire the root redex, or keep the cell.**  Returns the reduct named by the matching `Step`
constructor when `mkGen generator payload children` is a root redex, otherwise the cell unchanged.
Non-recursive `Option.getD` over the propext-clean `RawTerm.fireRootRedex`. -/
def RawTerm.fireRootRedexOrSelf {scope : Nat} (generator : Generator)
    (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) : RawTerm scope :=
  (RawTerm.fireRootRedex generator payload children).getD
    (.mkGen generator payload children)

mutual
/-- **Takahashi complete development.**  Contracts every redex present in `term` simultaneously —
develop all children, then fire the root redex once — but leaves redexes CREATED by the contraction
untouched.  Propext-clean: the redex-shape detection is delegated to `fireRootRedex`, so this is a
single `mkGen` match. -/
def RawTerm.completeDevelopment {scope : Nat} : (term : RawTerm scope) → RawTerm scope
  | .mkGen generator payload children =>
      RawTerm.fireRootRedexOrSelf generator payload
        (RawTerm.completeDevelopmentChildren children)

/-- Pointwise complete development of a children spine. -/
def RawTerm.completeDevelopmentChildren {binderShifts : List Nat} {scope : Nat} :
    (children : RawTermChildren binderShifts scope) → RawTermChildren binderShifts scope
  | .childNil => .childNil
  | .childCons childHead childTail =>
      .childCons (RawTerm.completeDevelopment childHead)
        (RawTerm.completeDevelopmentChildren childTail)
end

/-- **Root firing is reachable by `StepStar`.**  Either `fireRootRedex` fires a genuine `Step`
(soundness) — one star step — or it returns the cell unchanged (reflexivity). -/
theorem RawTerm.fireRootRedexOrSelf_stepStar {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope} :
    StepStar (.mkGen generator payload children)
      (RawTerm.fireRootRedexOrSelf generator payload children) := by
  unfold RawTerm.fireRootRedexOrSelf
  cases hFired : RawTerm.fireRootRedex generator payload children with
  | none => exact StepStar.refl _
  | some reduct => exact StepStar.single (RawTerm.fireRootRedex_sound hFired)

mutual
/-- **The complete development is reachable from the source by `StepStar`.**  Develop all children
(a congruence chain lifted via `StepStar.ofChildrenStar`), then fire the root redex once
(`fireRootRedexOrSelf_stepStar`); compose with `StepStar.trans_compose`.  The soundness half of the
eventual maximal-reduct / triangle property toward raw confluence (`#420`). -/
theorem RawTerm.completeDevelopment_stepStar {scope : Nat} :
    (term : RawTerm scope) → StepStar term (RawTerm.completeDevelopment term)
  | .mkGen _generator _payload children =>
      StepStar.trans_compose
        (StepStar.ofChildrenStar
          (RawTerm.completeDevelopmentChildren_stepChildrenStar children))
        RawTerm.fireRootRedexOrSelf_stepStar

/-- Pointwise children-spine companion of `completeDevelopment_stepStar`: each child `StepStar`-reduces
to its complete development, replayed through the spine via `here`/`there`/`trans_compose`. -/
theorem RawTerm.completeDevelopmentChildren_stepChildrenStar
    {binderShifts : List Nat} {scope : Nat} :
    (children : RawTermChildren binderShifts scope) →
    StepChildrenStar children (RawTerm.completeDevelopmentChildren children)
  | .childNil => StepChildrenStar.refl _
  | .childCons childHead childTail =>
      StepChildrenStar.trans_compose
        (StepChildrenStar.here childTail
          (RawTerm.completeDevelopment_stepStar childHead))
        (StepChildrenStar.there (RawTerm.completeDevelopment childHead)
          (RawTerm.completeDevelopmentChildren_stepChildrenStar childTail))
end

end FX1Poly.Core
