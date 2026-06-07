import FX1Poly.Typed.ReducibleSemanticRules
import FX1Poly.Core.StrongNormalizationCodeFormers

/-! # FX1Poly/Typed/OptionCodeFormationUnderSubst
    — the `optionCode` data-former universe-membership under a closing substitution (GTL-13 reducibility wiring)

The under-substitution wrapper for the `optionCode` data type former, the exact lemma the fundamental theorem's
`genFormation` arm needs when `gen_optionCode` joins `typingRuleDescOf` (GTL-13).  It is the one-child twin of
`IsReducibleMemberAt.listCodeFormationUnderSubst`: under a closing `substitution`, `Option element` is a
reducible member of `Type@levelExpr` whenever the substituted element code is strongly normalizing.

The option type former is weak-head normal (no root redex — only the vacuous `rootIota` arm unifies a former
root) and root-distinct from Π / universe, so it is classified purely by strong normalization via the
ARITY-GENERIC `IsReducibleMemberAt.dataFormerInUniverse` — exactly as `listCodeFormationUnderSubst` does.  There
is NO per-former reducibility candidate and NO canonicity empty-candidate model-change: data FORMATION
reducibility is a `dataFormerInUniverse` dispatch.  Row-independent — uses only the shipped
`optionCode_isStronglyNormalizing_of_element` SN combinator, so it lands ahead of the formation row.

## Zero-axiom verification

`rw [subst_universeCodeCell]` + a `rfl` cell-substitution rewrite + the arity-generic
`IsReducibleMemberAt.dataFormerInUniverse` fed the shipped `optionCode_isStronglyNormalizing_of_element`, the
uniform weak-head-normal `cases iotaStep`, and two `nomatch` root-distinctness proofs — the exact structure of
`listCodeFormationUnderSubst`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.StepStar FX1Poly.Universe FX1Poly.Foundation

/-- **Semantic `optionCode`-former formation under a closing substitution (the `genFormation` data-former arm
for `gen_optionCode`).**  Under a closing `substitution`, the option type code `Option element` is a reducible
member of its universe `Type@levelExpr` whenever its substituted element code is strongly normalizing.  The
one-child twin of `IsReducibleMemberAt.listCodeFormationUnderSubst`, routed through the arity-generic
`IsReducibleMemberAt.dataFormerInUniverse` — no per-former reducibility candidate. -/
theorem IsReducibleMemberAt.optionCodeFormationUnderSubst {scope targetScope : Nat} {predLevel : Nat}
    {element : RawTerm scope}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (substitution : RawTermSubst scope targetScope)
    (elementNormalizing : IsStronglyNormalizing (RawTerm.subst substitution element)) :
    IsReducibleMemberAt (predLevel + 1)
      (RawTerm.subst substitution (universeCodeCell levelExpr flag))
      (RawTerm.subst substitution
        (.mkGen .gen_optionCode () (.childCons element .childNil))) := by
  rw [subst_universeCodeCell]
  have substEq :
      RawTerm.subst substitution
          (.mkGen .gen_optionCode () (.childCons element .childNil))
        = .mkGen .gen_optionCode ()
            (.childCons (RawTerm.subst substitution element) .childNil) := rfl
  rw [substEq]
  exact IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (optionCode_isStronglyNormalizing_of_element elementNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

end FX1Poly.Typed
