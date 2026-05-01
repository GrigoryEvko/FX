import LeanFX.Syntax.Reduction.CdLemmaStarWithBi

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! # `Step.par.cd_monotone` — `Term.cd` is monotone wrt `Step.par`.

The Tait-Martin-Löf workhorse for typed Church-Rosser:

  `Step.par.isBi parStep` ⟹ `Step.parStarWithBi (Term.cd source) (Term.cd target)`

where `parStep : Step.par sourceTerm targetTerm`.

Once landed, `Step.parStar.cd_monotone` (chain induction) and
`Step.parStar.cdIter_completion` (the reach lemma) follow
trivially, and `Step.parStar.confluence` (W8.3 / #885) is a
~30-line corollary.

The proof structure mirrors `cd_lemma_star_with_bi` (54 cases of
induction on `Step.par.isBi`).  This file collects the case
helpers — each helper receives the IH(s) for the case's
recursive premises and produces the case's parStarWithBi
conclusion.  The aggregator dispatches into them via a
`induction stepBi with ... | C ... => exact <helper>`.

We work in the **paired** `Step.parStarWithBi` flavour:

* The β cases need `subst0_parStarWithBi` (chain-form joint
  substitution), which is already proved zero-axiom.
* The eliminator-cong cases need `lam_target_inv` /
  `pair_target_inv` on the function/scrutinee IH to identify
  the target's developed shape — these inversions live on
  `parStarWithBi` (in `ParStarWithBi.lean`).

The plain `Step.parStar` corollary (`Step.par.cd_monotone`) is a
one-line projection via `.toParStar`. -/

/-! ## §1 — refl + trivial cong cases (10).

Constructors whose `Term.cd` arm performs no contraction:

  * `refl` — both sides are the same term, `parStarWithBi.refl`.
  * `lam`, `lamPi` — binder closures.
  * `pair` — Σ-pair.
  * `natSucc`, `listCons`, `optionSome`, `eitherInl`,
    `eitherInr` — constructor cong.
  * `idJ` cong — the proof goes through despite cd_idJ_redex
    splitting on `endpointsEqual`, because the IHs only see
    the bodies of the witness/baseCase, not the `refl`-shape
    that gates the redex firing.  The case helper falls back
    to `idJ_cong` because both sides of cd-app fail-fast
    when neither witness is `refl`. -/

/-- Discharge the `Step.par.isBi.refl` case.  Both sides are
the same term; `parStarWithBi.refl` closes. -/
theorem Step.par.cd_monotone_refl_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    (term : Term ctx termType) :
    Step.parStarWithBi (Term.cd term) (Term.cd term) :=
  Step.parStarWithBi.refl (Term.cd term)

/-- Discharge the `Step.par.isBi.lam` case.  Body IH gives
parStarWithBi between the cd's of source/target bodies; lift
through the binder via `parStarWithBi.lam_cong`. -/
theorem Step.par.cd_monotone_lam_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {sourceBody targetBody : Term (ctx.cons domainType) codomainType.weaken}
    (bodyIH : Step.parStarWithBi (Term.cd sourceBody) (Term.cd targetBody)) :
    Step.parStarWithBi
      (Term.cd (Term.lam (codomainType := codomainType) sourceBody))
      (Term.cd (Term.lam (codomainType := codomainType) targetBody)) := by
  simp only [Term.cd]
  exact Step.parStarWithBi.lam_cong bodyIH

/-- Discharge the `Step.par.isBi.lamPi` case.  Same recipe as
`lam_case` but for the Π-binder. -/
theorem Step.par.cd_monotone_lamPi_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {sourceBody targetBody : Term (ctx.cons domainType) codomainType}
    (bodyIH : Step.parStarWithBi (Term.cd sourceBody) (Term.cd targetBody)) :
    Step.parStarWithBi
      (Term.cd (Term.lamPi (domainType := domainType) sourceBody))
      (Term.cd (Term.lamPi (domainType := domainType) targetBody)) := by
  simp only [Term.cd]
  exact Step.parStarWithBi.lamPi_cong bodyIH

/-- Discharge the `Step.par.isBi.pair` case.  Both component
IHs give parStarWithBi between cd's; lift via `pair_cong`. -/
theorem Step.par.cd_monotone_pair_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {sourceFirst targetFirst : Term ctx firstType}
    {sourceSecond targetSecond : Term ctx (secondType.subst0 firstType)}
    (firstIH : Step.parStarWithBi (Term.cd sourceFirst) (Term.cd targetFirst))
    (secondIH : Step.parStarWithBi (Term.cd sourceSecond) (Term.cd targetSecond)) :
    Step.parStarWithBi
      (Term.cd (Term.pair sourceFirst sourceSecond))
      (Term.cd (Term.pair targetFirst targetSecond)) := by
  simp only [Term.cd]
  exact Step.parStarWithBi.pair_cong firstIH secondIH

/-- Discharge the `Step.par.isBi.natSucc` case. -/
theorem Step.par.cd_monotone_natSucc_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {sourcePred targetPred : Term ctx Ty.nat}
    (predIH : Step.parStarWithBi (Term.cd sourcePred) (Term.cd targetPred)) :
    Step.parStarWithBi
      (Term.cd (Term.natSucc sourcePred))
      (Term.cd (Term.natSucc targetPred)) := by
  simp only [Term.cd]
  exact Step.parStarWithBi.natSucc_cong predIH

/-- Discharge the `Step.par.isBi.listCons` case. -/
theorem Step.par.cd_monotone_listCons_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {sourceHead targetHead : Term ctx elementType}
    {sourceTail targetTail : Term ctx (Ty.list elementType)}
    (headIH : Step.parStarWithBi (Term.cd sourceHead) (Term.cd targetHead))
    (tailIH : Step.parStarWithBi (Term.cd sourceTail) (Term.cd targetTail)) :
    Step.parStarWithBi
      (Term.cd (Term.listCons sourceHead sourceTail))
      (Term.cd (Term.listCons targetHead targetTail)) := by
  simp only [Term.cd]
  exact Step.parStarWithBi.listCons_cong headIH tailIH

/-- Discharge the `Step.par.isBi.optionSome` case. -/
theorem Step.par.cd_monotone_optionSome_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {sourceValue targetValue : Term ctx elementType}
    (valueIH : Step.parStarWithBi (Term.cd sourceValue) (Term.cd targetValue)) :
    Step.parStarWithBi
      (Term.cd (Term.optionSome sourceValue))
      (Term.cd (Term.optionSome targetValue)) := by
  simp only [Term.cd]
  exact Step.parStarWithBi.optionSome_cong valueIH

/-- Discharge the `Step.par.isBi.eitherInl` case. -/
theorem Step.par.cd_monotone_eitherInl_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {sourceValue targetValue : Term ctx leftType}
    (valueIH : Step.parStarWithBi (Term.cd sourceValue) (Term.cd targetValue)) :
    Step.parStarWithBi
      (Term.cd (Term.eitherInl (rightType := rightType) sourceValue))
      (Term.cd (Term.eitherInl (rightType := rightType) targetValue)) := by
  simp only [Term.cd]
  exact Step.parStarWithBi.eitherInl_cong valueIH

/-- Discharge the `Step.par.isBi.eitherInr` case. -/
theorem Step.par.cd_monotone_eitherInr_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {sourceValue targetValue : Term ctx rightType}
    (valueIH : Step.parStarWithBi (Term.cd sourceValue) (Term.cd targetValue)) :
    Step.parStarWithBi
      (Term.cd (Term.eitherInr (leftType := leftType) sourceValue))
      (Term.cd (Term.eitherInr (leftType := leftType) targetValue)) := by
  simp only [Term.cd]
  exact Step.parStarWithBi.eitherInr_cong valueIH

end LeanFX.Syntax
