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

/-! ## §2 — eliminator-cong cases (10).

Constructors whose `Term.cd` arm contracts a redex when the
function/scrutinee is in canonical form.  We have three relevant
shape configurations on the IH `parStarWithBi (cd source) (cd target)`:

* **A. Source-fires AND target-fires.**  E.g. `cd source_f =
  Term.lam body`, `cd target_f = Term.lam body'`.  By
  `lam_target_inv` on the IH, the body is itself
  parStarWithBi-related; close with `subst0_parStarWithBi`
  (β-fired form on both sides).

* **B. Source-fires AND target-doesn't-fire.**  Impossible:
  `lam_target_inv` on the IH would derive cd target = lam X,
  contradicting the assumed non-lam `toRaw` shape.

* **C. Source-doesn't-fire AND target-fires.**  Real case.
  E.g., source is a higher-order app whose β-development
  happens at typed-cd-target time but not source time.
  Close with `app_cong` on the IH followed by snoc with
  `betaApp` (β-fire at the chain end).

* **D. Source-doesn't-fire AND target-doesn't-fire.**  Both
  sides are plain `Term.app`; `app_cong` directly on the IHs.

The proof structure for each helper is `simp only [Term.cd,
Term.cd_<elim>_redex]` then `split` on the source-side match
(26 raw-shape arms).  In the canonical-form arm: extract the
typed canonical-form via `Term.eq_<C>_of_toRaw_<C>`; cast IHs;
apply `lam_target_inv` (or `pair_target_inv`) and close per
case A (with case B contradicted by toRaw incompatibility).
In the non-canonical 25 arms: split RHS; canonical arm uses
case C, non-canonical arm uses case D. -/

/-- Discharge the `Step.par.isBi.app` constructor case.  The
non-dependent application's complete development fires β when
the developed function is a `Term.lam`.  Combines case A
(source/target both fire) via `subst0_parStarWithBi`, case C
(only target fires) via `app_cong` + snoc with `betaApp`, and
case D (neither fires) via `app_cong`. -/
theorem Step.par.cd_monotone_app_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {sourceFunction targetFunction :
      Term ctx (Ty.arrow domainType codomainType)}
    {sourceArgument targetArgument : Term ctx domainType}
    (functionIH : Step.parStarWithBi
      (Term.cd sourceFunction) (Term.cd targetFunction))
    (argumentIH : Step.parStarWithBi
      (Term.cd sourceArgument) (Term.cd targetArgument)) :
    Step.parStarWithBi
      (Term.cd (Term.app sourceFunction sourceArgument))
      (Term.cd (Term.app targetFunction targetArgument)) := by
  simp only [Term.cd, Term.cd_app_redex]
  split
  -- LHS-fires arm: source's developed function is a lam.
  case _ rawSourceBody developedSourceFunctionEq =>
    have sourceCdEq :
        Term.cd sourceFunction =
          Term.lam (Term.body_of_lam_general
            (Term.cd sourceFunction) rfl developedSourceFunctionEq) :=
      Term.eq_lam_of_toRaw_lam (Term.cd sourceFunction)
        developedSourceFunctionEq
    have functionIHcast :
        Step.parStarWithBi
          (Term.lam (Term.body_of_lam_general
            (Term.cd sourceFunction) rfl developedSourceFunctionEq))
          (Term.cd targetFunction) :=
      sourceCdEq ▸ functionIH
    obtain ⟨targetBody, targetCdEq, bodyPair⟩ :=
      Step.parStarWithBi.lam_target_inv functionIHcast
    rw [targetCdEq]
    simp only [Term.toRaw]
    -- Goal after simp: parStarWithBi
    --   (cast ▸ (extracted source body).subst0 (cd source_a))
    --   (cast ▸ targetBody.subst0 (cd target_a))
    exact Step.parStarWithBi.castBoth_chain
      (Ty.weaken_subst_singleton codomainType domainType)
      (Step.parStarWithBi.subst0_parStarWithBi bodyPair argumentIH)
  -- LHS-doesn't-fire (25 arms, all reachable depending on cd source's
  -- raw shape).  Split the target-side match.
  all_goals
    split
    -- RHS-fires arm: target's developed function is a lam.  Real case
    -- when source-f β-develops only after the cd-target reduction
    -- finishes.  Close via app_cong + snoc with betaApp at chain end —
    -- the betaApp step's target already carries the
    -- Ty.weaken_subst_singleton cast, matching the goal's RHS shape.
    case _ rawTargetBody developedTargetFunctionEq =>
      have targetCdEq :
          Term.cd targetFunction =
            Term.lam (Term.body_of_lam_general
              (Term.cd targetFunction) rfl developedTargetFunctionEq) :=
        Term.eq_lam_of_toRaw_lam (Term.cd targetFunction)
          developedTargetFunctionEq
      rw [targetCdEq] at functionIH
      -- functionIH : parStarWithBi (cd source_f) (Term.lam (extracted target body))
      exact Step.parStarWithBi.snoc
        (Step.parStarWithBi.app_cong functionIH argumentIH)
        (Step.par.isBi.betaApp (Step.par.isBi.refl _)
                               (Step.par.isBi.refl _))
    -- RHS-doesn't-fire: both sides are plain Term.app.  app_cong.
    all_goals
      exact Step.parStarWithBi.app_cong functionIH argumentIH

end LeanFX.Syntax
