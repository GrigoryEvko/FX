import FX1Poly.Typed.BoundedGenFormationSigmaFromTelescope
import FX1Poly.Core.StrongNormalizationCodeFormers

/-! # FX1Poly/Typed/BoundedGenFormationOptionFromTelescope
    — the bounded `genFormationPi` recursor arm for the `optionCode` data former (the 1-child twin)

The one-child (`[0]` binderShifts) data-former minor-premise body of the bounded grown fundamental theorem, the
`optionCode` analogue of `fundamentalGenFormationListFromTelescopeAtBoundedSucc`.  From the SAME telescope IH
(the single element child's bound-reducibility under every closing substitution at the former's decoded output
level `denote (lmaxAll [elementLevel]) env`) it produces the `+1`-closing fundamental conclusion: the former
`Option element` is a bound-reducible member of `Type@(lmaxAll [elementLevel])`.

Like the list former it is classified by the `neutral` arm of `ReducibleTypeStepBounded` (the relation has no
`optionType` arm — only `piType`), so its reducible-as-type at the output level needs ONLY former SN, NOT the
per-component cumulative lifts the Π arm needs; and it is NON-dependent: a single element child (no codomain, no
var-0 instantiation), so `lmaxAll [elementLevel] = elementLevel` (by `rfl`) collapses the output `belowBound` to
the element's directly.  The element member, its level-bound, and its SN come off the shared telescope via
`oneChildMember`, `universeCodeReducibleAtBounded_belowBound`, and `stronglyNormalizing_of_universeMemberAt-
Bounded` exactly as the list arm reads its element.  Row-independent — lands ahead of the formation row.

## Zero-axiom verification

One `intro` then a chain of shipped lemma applications plus a `rfl` cell-substitution rewrite (twice) and
`subst_universeCodeCell`, two `show … by decide` generator-disequalities, and one uniform weak-head `cases` —
the verbatim structure of `fundamentalGenFormationListFromTelescopeAtBoundedSucc`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **The bounded `genFormationPi` recursor arm for the `optionCode` data former (one-child data former).**  From
the telescope IH (the element child bound-reducible under every closing substitution at the former's decoded
output level), the former `Option element` is a `+1`-closing fundamental member of
`Type@(lmaxAll [elementLevel])`.  The 1-child twin of `fundamentalGenFormationListFromTelescopeAtBoundedSucc`;
the former's reducible-as-type uses the `neutral` arm (SN candidate) since the relation has no `optionType` arm,
and `lmaxAll [elementLevel] = elementLevel` collapses the output-level bookkeeping. -/
theorem fundamentalGenFormationOptionFromTelescopeAtBoundedSucc {profile : PolyProfile} {scope : Nat}
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
      (.mkGen .gen_optionCode () (.childCons element .childNil))
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
      RawTerm.subst substitution (.mkGen .gen_optionCode () (.childCons element .childNil))
        = .mkGen .gen_optionCode () (.childCons (RawTerm.subst substitution element) .childNil) := rfl
  have optionSN :
      IsStronglyNormalizing
        (RawTerm.subst substitution (.mkGen .gen_optionCode () (.childCons element .childNil))) := by
    rw [substEq]
    exact optionCode_isStronglyNormalizing_of_element elementSN
  have optionReducible :
      IsReducibleTypeAtBounded env (LevelExpr.denote (lmaxAll [elementLevel]) env)
        (RawTerm.subst substitution (.mkGen .gen_optionCode () (.childCons element .childNil))) := by
    rw [substEq]
    exact ⟨IsStronglyNormalizing,
      ReducibleTypeStepBounded.neutral
        (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
        (show Generator.gen_optionCode ≠ Generator.gen_piTyCode by decide)
        (show Generator.gen_optionCode ≠ Generator.gen_universeCode by decide)
        (show Generator.gen_optionCode ≠ Generator.gen_emptyCode by decide)⟩
  rw [subst_universeCodeCell]
  exact universeMembershipIntroAtBounded env (lmaxAll [elementLevel]) flag bound
    (RawTerm.subst substitution (.mkGen .gen_optionCode () (.childCons element .childNil)))
    belowBound optionSN optionReducible

end FX1Poly.Typed
