import FX1Poly.Typed.ReducibleSemanticRules
import FX1Poly.Core.StrongNormalizationCodeFormers

/-! # FX1Poly/Typed/ListCodeFormationUnderSubst
    — the `listCode` data-former universe-membership under a closing substitution (GTL-11 reducibility wiring)

The under-substitution wrapper for the `listCode` data type former, the exact lemma the fundamental theorem's
`genFormation` arm needs when `gen_listCode` joins `typingRuleDescOf` (GTL-11).  It is the one-child twin of
`IsReducibleMemberAt.sigmaFormationUnderSubst`: under a closing `substitution`, `List element` is a reducible
member of `Type@levelExpr` whenever the substituted element code is strongly normalizing.

This confirms the GTL-11 spike's GO verdict CONCRETELY (by construction): the list type former is weak-head
normal (no root redex — only the vacuous `rootIota` arm unifies a former root) and root-distinct from Π /
universe, so it is classified purely by strong normalization via the ARITY-GENERIC
`IsReducibleMemberAt.dataFormerInUniverse` — exactly as `sigmaFormationUnderSubst` does.  There is NO
per-former reducibility candidate, NO 2-child `FormerChildrenReducible`/`toPiMember` machinery, and NO
canonicity empty-candidate model-change (BFT-15/CON-A3): data FORMATION reducibility is a `dataFormerInUniverse`
dispatch, and the remaining GTL-11 work is routing the FT arm's non-Π formation branch through wrappers like
this one (plus the `FormationCanonicalForms` head disjunct).

## Zero-axiom verification

`rw [subst_universeCodeCell]` + a `rfl` cell-substitution rewrite + the arity-generic
`IsReducibleMemberAt.dataFormerInUniverse` fed the shipped `listCode_isStronglyNormalizing_of_element`, the
uniform weak-head-normal `cases iotaStep`, and two `nomatch` root-distinctness proofs — the exact structure of
`sigmaFormationUnderSubst`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.StepStar FX1Poly.Universe FX1Poly.Foundation

/-- **Semantic `listCode`-former formation under a closing substitution (the `genFormation` data-former arm for
`gen_listCode`).**  Under a closing `substitution`, the list type code `List element` is a reducible member of
its universe `Type@levelExpr` whenever its substituted element code is strongly normalizing.  The one-child
twin of `IsReducibleMemberAt.sigmaFormationUnderSubst`, routed through the arity-generic
`IsReducibleMemberAt.dataFormerInUniverse` — no per-former reducibility candidate. -/
theorem IsReducibleMemberAt.listCodeFormationUnderSubst {scope targetScope : Nat} {predLevel : Nat}
    {element : RawTerm scope}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (substitution : RawTermSubst scope targetScope)
    (elementNormalizing : IsStronglyNormalizing (RawTerm.subst substitution element)) :
    IsReducibleMemberAt (predLevel + 1)
      (RawTerm.subst substitution (universeCodeCell levelExpr flag))
      (RawTerm.subst substitution
        (.mkGen .gen_listCode () (.childCons element .childNil))) := by
  rw [subst_universeCodeCell]
  have substEq :
      RawTerm.subst substitution
          (.mkGen .gen_listCode () (.childCons element .childNil))
        = .mkGen .gen_listCode ()
            (.childCons (RawTerm.subst substitution element) .childNil) := rfl
  rw [substEq]
  exact IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (listCode_isStronglyNormalizing_of_element elementNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

end FX1Poly.Typed
