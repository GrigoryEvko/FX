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

/-- Discharge the `Step.par.isBi.appPi` constructor case.  Same
template as `cd_monotone_app_case` but for the Π-binder; uses
`lamPi_target_inv`, `appPi_cong`, and `Step.par.isBi.betaAppPi`.
The `Ty.weaken_subst_singleton` cast does not appear here since
`cd_appPi_redex`'s lam-arm output type is already
`codomainType.subst0 domainType`. -/
theorem Step.par.cd_monotone_appPi_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {sourceFunction targetFunction :
      Term ctx (Ty.piTy domainType codomainType)}
    {sourceArgument targetArgument : Term ctx domainType}
    (functionIH : Step.parStarWithBi
      (Term.cd sourceFunction) (Term.cd targetFunction))
    (argumentIH : Step.parStarWithBi
      (Term.cd sourceArgument) (Term.cd targetArgument)) :
    Step.parStarWithBi
      (Term.cd (Term.appPi sourceFunction sourceArgument))
      (Term.cd (Term.appPi targetFunction targetArgument)) := by
  simp only [Term.cd, Term.cd_appPi_redex]
  split
  case _ rawSourceBody developedSourceFunctionEq =>
    have sourceCdEq :
        Term.cd sourceFunction =
          Term.lamPi (Term.body_of_lamPi_general
            (Term.cd sourceFunction) rfl developedSourceFunctionEq) :=
      Term.eq_lamPi_of_toRaw_lam (Term.cd sourceFunction)
        developedSourceFunctionEq
    have functionIHcast :
        Step.parStarWithBi
          (Term.lamPi (Term.body_of_lamPi_general
            (Term.cd sourceFunction) rfl developedSourceFunctionEq))
          (Term.cd targetFunction) :=
      sourceCdEq ▸ functionIH
    obtain ⟨targetBody, targetCdEq, bodyPair⟩ :=
      Step.parStarWithBi.lamPi_target_inv functionIHcast
    rw [targetCdEq]
    simp only [Term.toRaw]
    exact Step.parStarWithBi.subst0_parStarWithBi bodyPair argumentIH
  all_goals
    split
    case _ rawTargetBody developedTargetFunctionEq =>
      have targetCdEq :
          Term.cd targetFunction =
            Term.lamPi (Term.body_of_lamPi_general
              (Term.cd targetFunction) rfl developedTargetFunctionEq) :=
        Term.eq_lamPi_of_toRaw_lam (Term.cd targetFunction)
          developedTargetFunctionEq
      rw [targetCdEq] at functionIH
      exact Step.parStarWithBi.snoc
        (Step.parStarWithBi.appPi_cong functionIH argumentIH)
        (Step.par.isBi.betaAppPi (Step.par.isBi.refl _)
                                  (Step.par.isBi.refl _))
    all_goals
      exact Step.parStarWithBi.appPi_cong functionIH argumentIH

/-- Discharge the `Step.par.isBi.fst` constructor case.  The
Σ first-projection `Term.fst (Term.pair a b)` β-reduces to `a`.
`cd_fst_redex` matches the pair-shape on the developed pair via
`toRaw`.  Three IH configurations:

* Pair-on-both: extract first components via `pair_target_inv`,
  return the firstIH.
* Source-pair, target-not-pair: impossible (pair_target_inv).
* Source-not-pair, target-pair: snoc with `betaFstPair` redex
  contraction.
* Neither pair: `fst_cong` directly. -/
theorem Step.par.cd_monotone_fst_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {sourcePair targetPair :
      Term ctx (Ty.sigmaTy firstType secondType)}
    (pairIH : Step.parStarWithBi
      (Term.cd sourcePair) (Term.cd targetPair)) :
    Step.parStarWithBi
      (Term.cd (Term.fst sourcePair)) (Term.cd (Term.fst targetPair)) := by
  simp only [Term.cd, Term.cd_fst_redex]
  split
  case _ rawSourceFirst rawSourceSecond developedSourcePairEq =>
    have sourceCdEq :
        Term.cd sourcePair =
          Term.pair
            (Term.firstVal_of_pair_general
              (Term.cd sourcePair) rfl developedSourcePairEq)
            (Term.secondVal_of_pair_general
              (Term.cd sourcePair) rfl developedSourcePairEq) :=
      Term.eq_pair_of_toRaw_pair (Term.cd sourcePair)
        developedSourcePairEq
    have pairIHcast :
        Step.parStarWithBi
          (Term.pair
            (Term.firstVal_of_pair_general
              (Term.cd sourcePair) rfl developedSourcePairEq)
            (Term.secondVal_of_pair_general
              (Term.cd sourcePair) rfl developedSourcePairEq))
          (Term.cd targetPair) :=
      sourceCdEq ▸ pairIH
    obtain ⟨targetFirst, targetSecond, targetCdEq, firstPair, _secondPair⟩ :=
      Step.parStarWithBi.pair_target_inv pairIHcast
    rw [targetCdEq]
    simp only [Term.toRaw]
    exact firstPair
  all_goals
    split
    case _ rawTargetFirst rawTargetSecond developedTargetPairEq =>
      have targetCdEq :
          Term.cd targetPair =
            Term.pair
              (Term.firstVal_of_pair_general
                (Term.cd targetPair) rfl developedTargetPairEq)
              (Term.secondVal_of_pair_general
                (Term.cd targetPair) rfl developedTargetPairEq) :=
        Term.eq_pair_of_toRaw_pair (Term.cd targetPair)
          developedTargetPairEq
      rw [targetCdEq] at pairIH
      exact Step.parStarWithBi.snoc
        (Step.parStarWithBi.fst_cong pairIH)
        (Step.par.isBi.betaFstPair (Step.par.isBi.refl _))
    all_goals
      exact Step.parStarWithBi.fst_cong pairIH

/-- Discharge the `Step.par.isBi.boolElim` constructor case.
The boolean ι-rule fires when the developed scrutinee is
`boolTrue` (yields `thenBranch`) or `boolFalse` (yields
`elseBranch`).  Three IH configurations on the scrutinee:

* Scrutinee canonical-on-both: source preservation
  (`parStar.boolTrue_source_inv` / `boolFalse_source_inv`)
  forces target to match; close with `thenIH` / `elseIH`.
* Source not canonical, target canonical: snoc with
  `iotaBoolElim<True/False>` redex contraction.
* Source canonical, target not: impossible (would contradict
  the source-preservation conclusion).
* Neither canonical: `boolElim_cong` directly.

The "source canonical, target not" case is auto-discharged by
the `rw [targetCdEq]` that aligns the RHS match with the
canonical form. -/
theorem Step.par.cd_monotone_boolElim_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {sourceScrutinee targetScrutinee : Term ctx Ty.bool}
    {sourceThen targetThen : Term ctx resultType}
    {sourceElse targetElse : Term ctx resultType}
    (scrutineeIH : Step.parStarWithBi
      (Term.cd sourceScrutinee) (Term.cd targetScrutinee))
    (thenIH : Step.parStarWithBi
      (Term.cd sourceThen) (Term.cd targetThen))
    (elseIH : Step.parStarWithBi
      (Term.cd sourceElse) (Term.cd targetElse)) :
    Step.parStarWithBi
      (Term.cd (Term.boolElim sourceScrutinee sourceThen sourceElse))
      (Term.cd (Term.boolElim targetScrutinee targetThen targetElse)) := by
  simp only [Term.cd, Term.cd_boolElim_redex]
  split
  -- LHS-boolTrue.
  case _ developedSourceScrutEq =>
    have sourceCdEq : Term.cd sourceScrutinee = Term.boolTrue :=
      Term.eq_boolTrue_of_toRaw_boolTrue _ developedSourceScrutEq
    have scrutineeIHcast :
        Step.parStarWithBi Term.boolTrue (Term.cd targetScrutinee) :=
      sourceCdEq ▸ scrutineeIH
    have targetCdEq : Term.cd targetScrutinee = Term.boolTrue :=
      Step.parStar.boolTrue_source_inv scrutineeIHcast.toParStar
    rw [targetCdEq]
    simp only [Term.toRaw]
    exact thenIH
  -- LHS-boolFalse.
  case _ developedSourceScrutEq =>
    have sourceCdEq : Term.cd sourceScrutinee = Term.boolFalse :=
      Term.eq_boolFalse_of_toRaw_boolFalse _ developedSourceScrutEq
    have scrutineeIHcast :
        Step.parStarWithBi Term.boolFalse (Term.cd targetScrutinee) :=
      sourceCdEq ▸ scrutineeIH
    have targetCdEq : Term.cd targetScrutinee = Term.boolFalse :=
      Step.parStar.boolFalse_source_inv scrutineeIHcast.toParStar
    rw [targetCdEq]
    simp only [Term.toRaw]
    exact elseIH
  -- LHS-wildcard (24 arms).
  all_goals
    split
    -- RHS-boolTrue.
    case _ developedTargetScrutEq =>
      have targetCdEq : Term.cd targetScrutinee = Term.boolTrue :=
        Term.eq_boolTrue_of_toRaw_boolTrue _ developedTargetScrutEq
      rw [targetCdEq] at scrutineeIH
      exact Step.parStarWithBi.snoc
        (Step.parStarWithBi.boolElim_cong scrutineeIH thenIH elseIH)
        (Step.par.isBi.iotaBoolElimTrue _ (Step.par.isBi.refl _))
    -- RHS-boolFalse.
    case _ developedTargetScrutEq =>
      have targetCdEq : Term.cd targetScrutinee = Term.boolFalse :=
        Term.eq_boolFalse_of_toRaw_boolFalse _ developedTargetScrutEq
      rw [targetCdEq] at scrutineeIH
      exact Step.parStarWithBi.snoc
        (Step.parStarWithBi.boolElim_cong scrutineeIH thenIH elseIH)
        (Step.par.isBi.iotaBoolElimFalse _ (Step.par.isBi.refl _))
    -- RHS-wildcard.
    all_goals
      exact Step.parStarWithBi.boolElim_cong scrutineeIH thenIH elseIH

/-- Discharge the `Step.par.isBi.natElim` constructor case.
Same template as `boolElim` with three split arms (natZero,
natSucc, wildcard).  The natSucc arm fires `Term.app
developedSucc predecessor`; both-fire case extracts predecessors
via `natSucc_source_inv` and closes with `app_cong` on succIH
and the predecessor pair. -/
theorem Step.par.cd_monotone_natElim_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {sourceScrutinee targetScrutinee : Term ctx Ty.nat}
    {sourceZero targetZero : Term ctx resultType}
    {sourceSucc targetSucc : Term ctx (Ty.arrow Ty.nat resultType)}
    (scrutineeIH : Step.parStarWithBi
      (Term.cd sourceScrutinee) (Term.cd targetScrutinee))
    (zeroIH : Step.parStarWithBi
      (Term.cd sourceZero) (Term.cd targetZero))
    (succIH : Step.parStarWithBi
      (Term.cd sourceSucc) (Term.cd targetSucc)) :
    Step.parStarWithBi
      (Term.cd (Term.natElim sourceScrutinee sourceZero sourceSucc))
      (Term.cd (Term.natElim targetScrutinee targetZero targetSucc)) := by
  simp only [Term.cd, Term.cd_natElim_redex]
  split
  case _ developedSourceScrutEq =>
    have sourceCdEq : Term.cd sourceScrutinee = Term.natZero :=
      Term.eq_natZero_of_toRaw_natZero _ developedSourceScrutEq
    have scrutineeIHcast :
        Step.parStarWithBi Term.natZero (Term.cd targetScrutinee) :=
      sourceCdEq ▸ scrutineeIH
    have targetCdEq : Term.cd targetScrutinee = Term.natZero :=
      Step.parStar.natZero_source_inv scrutineeIHcast.toParStar
    rw [targetCdEq]
    simp only [Term.toRaw]
    exact zeroIH
  case _ rawSourcePred developedSourceScrutEq =>
    have sourceCdEq :
        Term.cd sourceScrutinee =
          Term.natSucc (Term.predecessor_of_natSucc_general
            (Term.cd sourceScrutinee) rfl developedSourceScrutEq) :=
      Term.eq_natSucc_of_toRaw_natSucc _ developedSourceScrutEq
    have scrutineeIHcast :
        Step.parStarWithBi
          (Term.natSucc (Term.predecessor_of_natSucc_general
            (Term.cd sourceScrutinee) rfl developedSourceScrutEq))
          (Term.cd targetScrutinee) :=
      sourceCdEq ▸ scrutineeIH
    obtain ⟨targetPred, targetCdEq, predPair⟩ :=
      Step.parStarWithBi.natSucc_source_inv scrutineeIHcast
    rw [targetCdEq]
    simp only [Term.toRaw]
    exact Step.parStarWithBi.app_cong succIH predPair
  all_goals
    split
    case _ developedTargetScrutEq =>
      have targetCdEq : Term.cd targetScrutinee = Term.natZero :=
        Term.eq_natZero_of_toRaw_natZero _ developedTargetScrutEq
      rw [targetCdEq] at scrutineeIH
      exact Step.parStarWithBi.snoc
        (Step.parStarWithBi.natElim_cong scrutineeIH zeroIH succIH)
        (Step.par.isBi.iotaNatElimZero _ (Step.par.isBi.refl _))
    case _ rawTargetPred developedTargetScrutEq =>
      have targetCdEq :
          Term.cd targetScrutinee =
            Term.natSucc (Term.predecessor_of_natSucc_general
              (Term.cd targetScrutinee) rfl developedTargetScrutEq) :=
        Term.eq_natSucc_of_toRaw_natSucc _ developedTargetScrutEq
      rw [targetCdEq] at scrutineeIH
      exact Step.parStarWithBi.snoc
        (Step.parStarWithBi.natElim_cong scrutineeIH zeroIH succIH)
        (Step.par.isBi.iotaNatElimSucc _ (Step.par.isBi.refl _)
                                        (Step.par.isBi.refl _))
    all_goals
      exact Step.parStarWithBi.natElim_cong scrutineeIH zeroIH succIH

/-- Discharge the `Step.par.isBi.natRec` constructor case.
Similar to `natElim` but with the recursive-call structure in
the natSucc arm: `app (app developedSucc pred) (natRec pred
developedZero developedSucc)`. -/
theorem Step.par.cd_monotone_natRec_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {sourceScrutinee targetScrutinee : Term ctx Ty.nat}
    {sourceZero targetZero : Term ctx resultType}
    {sourceSucc targetSucc : Term ctx
      (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (scrutineeIH : Step.parStarWithBi
      (Term.cd sourceScrutinee) (Term.cd targetScrutinee))
    (zeroIH : Step.parStarWithBi
      (Term.cd sourceZero) (Term.cd targetZero))
    (succIH : Step.parStarWithBi
      (Term.cd sourceSucc) (Term.cd targetSucc)) :
    Step.parStarWithBi
      (Term.cd (Term.natRec sourceScrutinee sourceZero sourceSucc))
      (Term.cd (Term.natRec targetScrutinee targetZero targetSucc)) := by
  simp only [Term.cd, Term.cd_natRec_redex]
  split
  case _ developedSourceScrutEq =>
    have sourceCdEq : Term.cd sourceScrutinee = Term.natZero :=
      Term.eq_natZero_of_toRaw_natZero _ developedSourceScrutEq
    have scrutineeIHcast :
        Step.parStarWithBi Term.natZero (Term.cd targetScrutinee) :=
      sourceCdEq ▸ scrutineeIH
    have targetCdEq : Term.cd targetScrutinee = Term.natZero :=
      Step.parStar.natZero_source_inv scrutineeIHcast.toParStar
    rw [targetCdEq]
    simp only [Term.toRaw]
    exact zeroIH
  case _ rawSourcePred developedSourceScrutEq =>
    have sourceCdEq :
        Term.cd sourceScrutinee =
          Term.natSucc (Term.predecessor_of_natSucc_general
            (Term.cd sourceScrutinee) rfl developedSourceScrutEq) :=
      Term.eq_natSucc_of_toRaw_natSucc _ developedSourceScrutEq
    have scrutineeIHcast :
        Step.parStarWithBi
          (Term.natSucc (Term.predecessor_of_natSucc_general
            (Term.cd sourceScrutinee) rfl developedSourceScrutEq))
          (Term.cd targetScrutinee) :=
      sourceCdEq ▸ scrutineeIH
    obtain ⟨targetPred, targetCdEq, predPair⟩ :=
      Step.parStarWithBi.natSucc_source_inv scrutineeIHcast
    rw [targetCdEq]
    simp only [Term.toRaw]
    exact Step.parStarWithBi.app_cong
      (Step.parStarWithBi.app_cong succIH predPair)
      (Step.parStarWithBi.natRec_cong predPair zeroIH succIH)
  all_goals
    split
    case _ developedTargetScrutEq =>
      have targetCdEq : Term.cd targetScrutinee = Term.natZero :=
        Term.eq_natZero_of_toRaw_natZero _ developedTargetScrutEq
      rw [targetCdEq] at scrutineeIH
      exact Step.parStarWithBi.snoc
        (Step.parStarWithBi.natRec_cong scrutineeIH zeroIH succIH)
        (Step.par.isBi.iotaNatRecZero _ (Step.par.isBi.refl _))
    case _ rawTargetPred developedTargetScrutEq =>
      have targetCdEq :
          Term.cd targetScrutinee =
            Term.natSucc (Term.predecessor_of_natSucc_general
              (Term.cd targetScrutinee) rfl developedTargetScrutEq) :=
        Term.eq_natSucc_of_toRaw_natSucc _ developedTargetScrutEq
      rw [targetCdEq] at scrutineeIH
      exact Step.parStarWithBi.snoc
        (Step.parStarWithBi.natRec_cong scrutineeIH zeroIH succIH)
        (Step.par.isBi.iotaNatRecSucc (Step.par.isBi.refl _)
          (Step.par.isBi.refl _) (Step.par.isBi.refl _))
    all_goals
      exact Step.parStarWithBi.natRec_cong scrutineeIH zeroIH succIH

/-- Discharge the `Step.par.isBi.listElim` constructor case.
listNil/listCons/wildcard split.  listCons fires
`app (app developedCons head) tail`. -/
theorem Step.par.cd_monotone_listElim_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope} {resultType : Ty level scope}
    {sourceScrutinee targetScrutinee : Term ctx (Ty.list elementType)}
    {sourceNil targetNil : Term ctx resultType}
    {sourceCons targetCons :
      Term ctx (Ty.arrow elementType
        (Ty.arrow (Ty.list elementType) resultType))}
    (scrutineeIH : Step.parStarWithBi
      (Term.cd sourceScrutinee) (Term.cd targetScrutinee))
    (nilIH : Step.parStarWithBi
      (Term.cd sourceNil) (Term.cd targetNil))
    (consIH : Step.parStarWithBi
      (Term.cd sourceCons) (Term.cd targetCons)) :
    Step.parStarWithBi
      (Term.cd (Term.listElim sourceScrutinee sourceNil sourceCons))
      (Term.cd (Term.listElim targetScrutinee targetNil targetCons)) := by
  simp only [Term.cd, Term.cd_listElim_redex]
  split
  case _ developedSourceScrutEq =>
    have sourceCdEq : Term.cd sourceScrutinee = Term.listNil :=
      Term.eq_listNil_of_toRaw_listNil _ developedSourceScrutEq
    have scrutineeIHcast :
        Step.parStarWithBi Term.listNil (Term.cd targetScrutinee) :=
      sourceCdEq ▸ scrutineeIH
    have targetCdEq : Term.cd targetScrutinee = Term.listNil :=
      Step.parStar.listNil_source_inv scrutineeIHcast.toParStar
    rw [targetCdEq]
    simp only [Term.toRaw]
    exact nilIH
  case _ rawSourceHead rawSourceTail developedSourceScrutEq =>
    have sourceCdEq :
        Term.cd sourceScrutinee =
          Term.listCons
            (Term.head_of_listCons_general
              (Term.cd sourceScrutinee) rfl developedSourceScrutEq)
            (Term.tail_of_listCons_general
              (Term.cd sourceScrutinee) rfl developedSourceScrutEq) :=
      Term.eq_listCons_of_toRaw_listCons _ developedSourceScrutEq
    have scrutineeIHcast :
        Step.parStarWithBi
          (Term.listCons
            (Term.head_of_listCons_general
              (Term.cd sourceScrutinee) rfl developedSourceScrutEq)
            (Term.tail_of_listCons_general
              (Term.cd sourceScrutinee) rfl developedSourceScrutEq))
          (Term.cd targetScrutinee) :=
      sourceCdEq ▸ scrutineeIH
    obtain ⟨targetHead, targetTail, targetCdEq, headPair, tailPair⟩ :=
      Step.parStarWithBi.listCons_source_inv scrutineeIHcast
    rw [targetCdEq]
    simp only [Term.toRaw]
    exact Step.parStarWithBi.app_cong
      (Step.parStarWithBi.app_cong consIH headPair)
      tailPair
  all_goals
    split
    case _ developedTargetScrutEq =>
      have targetCdEq : Term.cd targetScrutinee = Term.listNil :=
        Term.eq_listNil_of_toRaw_listNil _ developedTargetScrutEq
      rw [targetCdEq] at scrutineeIH
      exact Step.parStarWithBi.snoc
        (Step.parStarWithBi.listElim_cong scrutineeIH nilIH consIH)
        (Step.par.isBi.iotaListElimNil _ (Step.par.isBi.refl _))
    case _ rawTargetHead rawTargetTail developedTargetScrutEq =>
      have targetCdEq :
          Term.cd targetScrutinee =
            Term.listCons
              (Term.head_of_listCons_general
                (Term.cd targetScrutinee) rfl developedTargetScrutEq)
              (Term.tail_of_listCons_general
                (Term.cd targetScrutinee) rfl developedTargetScrutEq) :=
        Term.eq_listCons_of_toRaw_listCons _ developedTargetScrutEq
      rw [targetCdEq] at scrutineeIH
      exact Step.parStarWithBi.snoc
        (Step.parStarWithBi.listElim_cong scrutineeIH nilIH consIH)
        (Step.par.isBi.iotaListElimCons _ (Step.par.isBi.refl _)
          (Step.par.isBi.refl _) (Step.par.isBi.refl _))
    all_goals
      exact Step.parStarWithBi.listElim_cong scrutineeIH nilIH consIH

/-- Discharge the `Step.par.isBi.optionMatch` constructor case.
optionNone/optionSome/wildcard split.  optionSome fires
`app developedSome value`. -/
theorem Step.par.cd_monotone_optionMatch_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope} {resultType : Ty level scope}
    {sourceScrutinee targetScrutinee :
      Term ctx (Ty.option elementType)}
    {sourceNone targetNone : Term ctx resultType}
    {sourceSome targetSome : Term ctx (Ty.arrow elementType resultType)}
    (scrutineeIH : Step.parStarWithBi
      (Term.cd sourceScrutinee) (Term.cd targetScrutinee))
    (noneIH : Step.parStarWithBi
      (Term.cd sourceNone) (Term.cd targetNone))
    (someIH : Step.parStarWithBi
      (Term.cd sourceSome) (Term.cd targetSome)) :
    Step.parStarWithBi
      (Term.cd (Term.optionMatch sourceScrutinee sourceNone sourceSome))
      (Term.cd (Term.optionMatch targetScrutinee targetNone targetSome)) := by
  simp only [Term.cd, Term.cd_optionMatch_redex]
  split
  case _ developedSourceScrutEq =>
    have sourceCdEq : Term.cd sourceScrutinee = Term.optionNone :=
      Term.eq_optionNone_of_toRaw_optionNone _ developedSourceScrutEq
    have scrutineeIHcast :
        Step.parStarWithBi Term.optionNone (Term.cd targetScrutinee) :=
      sourceCdEq ▸ scrutineeIH
    have targetCdEq : Term.cd targetScrutinee = Term.optionNone :=
      Step.parStar.optionNone_source_inv scrutineeIHcast.toParStar
    rw [targetCdEq]
    simp only [Term.toRaw]
    exact noneIH
  case _ rawSourceValue developedSourceScrutEq =>
    have sourceCdEq :
        Term.cd sourceScrutinee =
          Term.optionSome (Term.value_of_optionSome_general
            (Term.cd sourceScrutinee) rfl developedSourceScrutEq) :=
      Term.eq_optionSome_of_toRaw_optionSome _ developedSourceScrutEq
    have scrutineeIHcast :
        Step.parStarWithBi
          (Term.optionSome (Term.value_of_optionSome_general
            (Term.cd sourceScrutinee) rfl developedSourceScrutEq))
          (Term.cd targetScrutinee) :=
      sourceCdEq ▸ scrutineeIH
    obtain ⟨targetValue, targetCdEq, valuePair⟩ :=
      Step.parStarWithBi.optionSome_source_inv scrutineeIHcast
    rw [targetCdEq]
    simp only [Term.toRaw]
    exact Step.parStarWithBi.app_cong someIH valuePair
  all_goals
    split
    case _ developedTargetScrutEq =>
      have targetCdEq : Term.cd targetScrutinee = Term.optionNone :=
        Term.eq_optionNone_of_toRaw_optionNone _ developedTargetScrutEq
      rw [targetCdEq] at scrutineeIH
      exact Step.parStarWithBi.snoc
        (Step.parStarWithBi.optionMatch_cong scrutineeIH noneIH someIH)
        (Step.par.isBi.iotaOptionMatchNone _ (Step.par.isBi.refl _))
    case _ rawTargetValue developedTargetScrutEq =>
      have targetCdEq :
          Term.cd targetScrutinee =
            Term.optionSome (Term.value_of_optionSome_general
              (Term.cd targetScrutinee) rfl developedTargetScrutEq) :=
        Term.eq_optionSome_of_toRaw_optionSome _ developedTargetScrutEq
      rw [targetCdEq] at scrutineeIH
      exact Step.parStarWithBi.snoc
        (Step.parStarWithBi.optionMatch_cong scrutineeIH noneIH someIH)
        (Step.par.isBi.iotaOptionMatchSome _ (Step.par.isBi.refl _)
          (Step.par.isBi.refl _))
    all_goals
      exact Step.parStarWithBi.optionMatch_cong scrutineeIH noneIH someIH

/-- Discharge the `Step.par.isBi.eitherMatch` constructor case.
eitherInl/eitherInr/wildcard split.  Each fires
`app developed<L/R>Branch value`. -/
theorem Step.par.cd_monotone_eitherMatch_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope} {resultType : Ty level scope}
    {sourceScrutinee targetScrutinee :
      Term ctx (Ty.either leftType rightType)}
    {sourceLeft targetLeft : Term ctx (Ty.arrow leftType resultType)}
    {sourceRight targetRight : Term ctx (Ty.arrow rightType resultType)}
    (scrutineeIH : Step.parStarWithBi
      (Term.cd sourceScrutinee) (Term.cd targetScrutinee))
    (leftIH : Step.parStarWithBi
      (Term.cd sourceLeft) (Term.cd targetLeft))
    (rightIH : Step.parStarWithBi
      (Term.cd sourceRight) (Term.cd targetRight)) :
    Step.parStarWithBi
      (Term.cd (Term.eitherMatch sourceScrutinee sourceLeft sourceRight))
      (Term.cd (Term.eitherMatch targetScrutinee targetLeft targetRight)) := by
  simp only [Term.cd, Term.cd_eitherMatch_redex]
  split
  case _ rawSourceValue developedSourceScrutEq =>
    have sourceCdEq :
        Term.cd sourceScrutinee =
          Term.eitherInl (Term.value_of_eitherInl_general
            (Term.cd sourceScrutinee) rfl developedSourceScrutEq) :=
      Term.eq_eitherInl_of_toRaw_eitherInl _ developedSourceScrutEq
    have scrutineeIHcast :
        Step.parStarWithBi
          (Term.eitherInl (Term.value_of_eitherInl_general
            (Term.cd sourceScrutinee) rfl developedSourceScrutEq))
          (Term.cd targetScrutinee) :=
      sourceCdEq ▸ scrutineeIH
    obtain ⟨targetValue, targetCdEq, valuePair⟩ :=
      Step.parStarWithBi.eitherInl_source_inv scrutineeIHcast
    rw [targetCdEq]
    simp only [Term.toRaw]
    exact Step.parStarWithBi.app_cong leftIH valuePair
  case _ rawSourceValue developedSourceScrutEq =>
    have sourceCdEq :
        Term.cd sourceScrutinee =
          Term.eitherInr (Term.value_of_eitherInr_general
            (Term.cd sourceScrutinee) rfl developedSourceScrutEq) :=
      Term.eq_eitherInr_of_toRaw_eitherInr _ developedSourceScrutEq
    have scrutineeIHcast :
        Step.parStarWithBi
          (Term.eitherInr (Term.value_of_eitherInr_general
            (Term.cd sourceScrutinee) rfl developedSourceScrutEq))
          (Term.cd targetScrutinee) :=
      sourceCdEq ▸ scrutineeIH
    obtain ⟨targetValue, targetCdEq, valuePair⟩ :=
      Step.parStarWithBi.eitherInr_source_inv scrutineeIHcast
    rw [targetCdEq]
    simp only [Term.toRaw]
    exact Step.parStarWithBi.app_cong rightIH valuePair
  all_goals
    split
    case _ rawTargetValue developedTargetScrutEq =>
      have targetCdEq :
          Term.cd targetScrutinee =
            Term.eitherInl (Term.value_of_eitherInl_general
              (Term.cd targetScrutinee) rfl developedTargetScrutEq) :=
        Term.eq_eitherInl_of_toRaw_eitherInl _ developedTargetScrutEq
      rw [targetCdEq] at scrutineeIH
      exact Step.parStarWithBi.snoc
        (Step.parStarWithBi.eitherMatch_cong scrutineeIH leftIH rightIH)
        (Step.par.isBi.iotaEitherMatchInl _ (Step.par.isBi.refl _)
          (Step.par.isBi.refl _))
    case _ rawTargetValue developedTargetScrutEq =>
      have targetCdEq :
          Term.cd targetScrutinee =
            Term.eitherInr (Term.value_of_eitherInr_general
              (Term.cd targetScrutinee) rfl developedTargetScrutEq) :=
        Term.eq_eitherInr_of_toRaw_eitherInr _ developedTargetScrutEq
      rw [targetCdEq] at scrutineeIH
      exact Step.parStarWithBi.snoc
        (Step.parStarWithBi.eitherMatch_cong scrutineeIH leftIH rightIH)
        (Step.par.isBi.iotaEitherMatchInr _ (Step.par.isBi.refl _)
          (Step.par.isBi.refl _))
    all_goals
      exact Step.parStarWithBi.eitherMatch_cong scrutineeIH leftIH rightIH

/-- Discharge the `Step.par.isBi.snd` constructor case.  Same as
`cd_monotone_fst_case` but extracting the secondVal.  Note: the
β-fired form `Term.snd (Term.pair a b) → b` carries a
`Ty.weaken_subst_singleton`-flavour cast on `secondType.subst0
firstType` because the second element's type depends on the
first via `secondType`. -/
theorem Step.par.cd_monotone_snd_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {sourcePair targetPair :
      Term ctx (Ty.sigmaTy firstType secondType)}
    (pairIH : Step.parStarWithBi
      (Term.cd sourcePair) (Term.cd targetPair)) :
    Step.parStarWithBi
      (Term.cd (Term.snd sourcePair)) (Term.cd (Term.snd targetPair)) := by
  simp only [Term.cd, Term.cd_snd_redex]
  split
  case _ rawSourceFirst rawSourceSecond developedSourcePairEq =>
    have sourceCdEq :
        Term.cd sourcePair =
          Term.pair
            (Term.firstVal_of_pair_general
              (Term.cd sourcePair) rfl developedSourcePairEq)
            (Term.secondVal_of_pair_general
              (Term.cd sourcePair) rfl developedSourcePairEq) :=
      Term.eq_pair_of_toRaw_pair (Term.cd sourcePair)
        developedSourcePairEq
    have pairIHcast :
        Step.parStarWithBi
          (Term.pair
            (Term.firstVal_of_pair_general
              (Term.cd sourcePair) rfl developedSourcePairEq)
            (Term.secondVal_of_pair_general
              (Term.cd sourcePair) rfl developedSourcePairEq))
          (Term.cd targetPair) :=
      sourceCdEq ▸ pairIH
    obtain ⟨targetFirst, targetSecond, targetCdEq, _firstPair, secondPair⟩ :=
      Step.parStarWithBi.pair_target_inv pairIHcast
    rw [targetCdEq]
    simp only [Term.toRaw]
    exact secondPair
  all_goals
    split
    case _ rawTargetFirst rawTargetSecond developedTargetPairEq =>
      have targetCdEq :
          Term.cd targetPair =
            Term.pair
              (Term.firstVal_of_pair_general
                (Term.cd targetPair) rfl developedTargetPairEq)
              (Term.secondVal_of_pair_general
                (Term.cd targetPair) rfl developedTargetPairEq) :=
        Term.eq_pair_of_toRaw_pair (Term.cd targetPair)
          developedTargetPairEq
      rw [targetCdEq] at pairIH
      exact Step.parStarWithBi.snoc
        (Step.parStarWithBi.snd_cong pairIH)
        (Step.par.isBi.betaSndPair (Step.par.isBi.refl _))
    all_goals
      exact Step.parStarWithBi.snd_cong pairIH

end LeanFX.Syntax
