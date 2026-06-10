import FX1Poly.Typed.BoundedGenFormationSigmaFromTelescope
import FX1Poly.Core.StrongNormalizationCodeFormers

/-! # FX1Poly/Typed/BoundedGenFormationListFromTelescope
    — the bounded `genFormationPi` recursor arm for the `listCode` data former (the 1-child twin of the Σ arm)

The one-child (`[0]` binderShifts) data-former minor-premise body of the bounded grown fundamental theorem, the
`listCode` analogue of `fundamentalGenFormationSigmaFromTelescopeAtBoundedSucc`.  From the SAME telescope IH (the
single element child's bound-reducibility under every closing substitution at the former's decoded output level
`denote (lmaxAll [elementLevel]) env`) it produces the `+1`-closing fundamental conclusion: the former
`List element` is a bound-reducible member of `Type@(lmaxAll [elementLevel])`.

## Why this is the SIMPLEST former arm

Like the Σ arm, the list former is classified by the `neutral` arm of `ReducibleTypeStepBounded` (the relation
has no `listType` arm — only `piType`), so its reducible-as-type at the output level needs ONLY former SN, NOT
the per-component cumulative lifts the Π arm needs.  And UNLIKE the Σ arm, the list former is NON-dependent: a
single element child (no codomain, no var-0 instantiation, no `levelMax_lt`).  `lmaxAll [elementLevel] =
elementLevel` (by `rfl`), so the output `belowBound` IS the element's `belowBound` directly.  The element member,
its level-bound, and its SN come off the shared telescope via `oneChildMember`,
`universeCodeReducibleAtBounded_belowBound`, and `stronglyNormalizing_of_universeMemberAtBounded` exactly as the
Σ arm reads the domain.

## The assembly (all callees shipped)

`oneChildMember` (the bounded one-child telescope projection) gives the element member at `bound`;
`universeCodeReducibleAtBounded_belowBound` reads `elementBelowBound`;
`stronglyNormalizing_of_universeMemberAtBounded` gives the element SN;
`listCode_isStronglyNormalizing_of_element` assembles the former SN; the former's reducibility-as-type at the
output level is the `neutral` arm of `ReducibleTypeStepBounded` (candidate `IsStronglyNormalizing`), with
weak-head-normality via the uniform `cases iotaStep` (a list type former has no root redex) and root-distinctness
from `gen_piTyCode` / `gen_universeCode` by `decide`.  `universeMembershipIntroAtBounded` closes it.

## Zero-axiom verification

One `intro` then a chain of shipped lemma applications plus a `rfl` cell-substitution rewrite (twice) and
`subst_universeCodeCell`, two `show … by decide` generator-disequalities, and one uniform weak-head `cases`.
No induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **The bounded `genFormationPi` recursor arm for the `listCode` data former (one-child data former).**  From
the telescope IH (the element child bound-reducible under every closing substitution at the former's decoded
output level), the former `List element` is a `+1`-closing fundamental member of `Type@(lmaxAll [elementLevel])`.
The 1-child twin of `fundamentalGenFormationSigmaFromTelescopeAtBoundedSucc`; the former's reducible-as-type uses
the `neutral` arm (SN candidate) since the relation has no `listType` arm, and `lmaxAll [elementLevel] =
elementLevel` collapses the output-level bookkeeping. -/
theorem fundamentalGenFormationListFromTelescopeAtBoundedSucc {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {element : RawTerm scope}
    (elementLevel : LevelExpr) (flag : UniverseFlag)
    (telescope : ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        TelescopeReducibleAtBounded env bound
          (LevelExpr.denote (lmaxAll [elementLevel]) env) flag 0 1 substitution
          [elementLevel]
          (.childCons element .childNil)) :
    FundamentalConclusionAtBoundedSucc env bound context
      (.mkGen .gen_listCode () (.childCons element .childNil))
      (universeCodeCell (lmaxAll [elementLevel]) flag) := by
  intro _targetScope substitution envReducible
  have elementMember := (telescope substitution envReducible).oneChildMember
  have elementBelowBound : LevelExpr.denote elementLevel env < bound := by
    obtain ⟨_cand, candReducible, _in⟩ := elementMember
    exact universeCodeReducibleAtBounded_belowBound candReducible
  have belowBound : LevelExpr.denote (lmaxAll [elementLevel]) env < bound := elementBelowBound
  have elementSN :=
    stronglyNormalizing_of_universeMemberAtBounded env bound elementLevel flag _ elementBelowBound elementMember
  have substEq :
      RawTerm.subst substitution (.mkGen .gen_listCode () (.childCons element .childNil))
        = .mkGen .gen_listCode () (.childCons (RawTerm.subst substitution element) .childNil) := rfl
  have listSN :
      IsStronglyNormalizing
        (RawTerm.subst substitution (.mkGen .gen_listCode () (.childCons element .childNil))) := by
    rw [substEq]
    exact listCode_isStronglyNormalizing_of_element elementSN
  have listReducible :
      IsReducibleTypeAtBounded env (LevelExpr.denote (lmaxAll [elementLevel]) env)
        (RawTerm.subst substitution (.mkGen .gen_listCode () (.childCons element .childNil))) := by
    rw [substEq]
    exact ⟨IsStronglyNormalizing,
      ReducibleTypeStepBounded.neutral
        (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
        (show Generator.gen_listCode ≠ Generator.gen_piTyCode by decide)
        (show Generator.gen_listCode ≠ Generator.gen_universeCode by decide)
        (show Generator.gen_listCode ≠ Generator.gen_emptyCode by decide)
        (show Generator.gen_listCode.isFlatDataCode = false by decide)⟩
  rw [subst_universeCodeCell]
  exact universeMembershipIntroAtBounded env (lmaxAll [elementLevel]) flag bound
    (RawTerm.subst substitution (.mkGen .gen_listCode () (.childCons element .childNil)))
    belowBound listSN listReducible

end FX1Poly.Typed
