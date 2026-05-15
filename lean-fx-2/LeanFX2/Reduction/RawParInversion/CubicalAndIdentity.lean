import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParRename

/-! # LeanFX2.Reduction.RawParInversion.CubicalAndIdentity

Inversion lemmas for `RawStep.par` on D1.6 / D3.6 cubical and
identity-type ctors plus the equivalence-introduction / application
ctors.

Covered families:

* Interval algebra: `interval0`, `interval1`, `intervalOpp`,
  `intervalMeet`, `intervalJoin`
* Path lambdas / app / cubical β: `pathLam`, `pathApp`
* D3.6 univalence machinery: `uaToEquiv`, `pathCompose`, `idToEquiv`
  (5-way β), `oeqTrans`, `equivCompose`
* Glue: `glueIntro`, `glueElim`
* Transp: `transp` (7-way β across `transpReflBeta`, `uaBeta`,
  `transpCompose` and their `Deep` variants)
* Hcomp: `hcomp`
* Observational equality: `oeqRefl`, `oeqJ`, `oeqFunext`
* Strict id: `idStrictRefl`, `idStrictRec`
* Equivalence intro / app: `equivIntro`, `equivApp`

## Root status

Layer 2 raw parallel-step inversion helper.  Zero axioms. -/

namespace LeanFX2

/-! ## D1.6 inversion lemmas — 27 new ctors.

Each inversion follows the same skeleton as the existing ctors: `cases`
on the parallel-step, `refl` arm uses the source unchanged, every cong
arm yields the matching reduced shape.  Trivial nullary canonical ctors
(interval0, interval1) just say `target = ctor`.

These are needed by deep-rule cases in cd_lemma when β/ι rules for the
new ctors land at D2.5–D2.7. -/

/-- `RawStep.par interval0 target → target = interval0`. -/
theorem RawStep.par.interval0_inv {scope : Nat}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.interval0 : RawTerm scope) target) :
    target = RawTerm.interval0 := by
  cases parallelStep
  case refl _ => rfl

/-- `RawStep.par interval1 target → target = interval1`. -/
theorem RawStep.par.interval1_inv {scope : Nat}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.interval1 : RawTerm scope) target) :
    target = RawTerm.interval1 := by
  cases parallelStep
  case refl _ => rfl

/-- `RawStep.par (intervalOpp t) target → target = intervalOpp t' ∧ par t t'`. -/
theorem RawStep.par.intervalOpp_inv {scope : Nat}
    {intervalTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.intervalOpp intervalTerm) target) :
    ∃ intervalTarget, target = RawTerm.intervalOpp intervalTarget ∧
      RawStep.par intervalTerm intervalTarget := by
  cases parallelStep with
  | refl _ => exact ⟨intervalTerm, rfl, RawStep.par.refl _⟩
  | intervalOppCong intervalStep => exact ⟨_, rfl, intervalStep⟩

/-- `RawStep.par (intervalMeet l r) target → target = intervalMeet l' r' ∧ pars`. -/
theorem RawStep.par.intervalMeet_inv {scope : Nat}
    {leftInterval rightInterval : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.intervalMeet leftInterval rightInterval) target) :
    ∃ leftTarget rightTarget,
      target = RawTerm.intervalMeet leftTarget rightTarget ∧
        RawStep.par leftInterval leftTarget ∧
        RawStep.par rightInterval rightTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨leftInterval, rightInterval, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | intervalMeetCong leftStep rightStep =>
      exact ⟨_, _, rfl, leftStep, rightStep⟩

/-- `RawStep.par (intervalJoin l r) target → target = intervalJoin l' r' ∧ pars`. -/
theorem RawStep.par.intervalJoin_inv {scope : Nat}
    {leftInterval rightInterval : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.intervalJoin leftInterval rightInterval) target) :
    ∃ leftTarget rightTarget,
      target = RawTerm.intervalJoin leftTarget rightTarget ∧
        RawStep.par leftInterval leftTarget ∧
        RawStep.par rightInterval rightTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨leftInterval, rightInterval, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | intervalJoinCong leftStep rightStep =>
      exact ⟨_, _, rfl, leftStep, rightStep⟩

/-- `RawStep.par (pathLam body) target → target = pathLam body' ∧ par`. -/
theorem RawStep.par.pathLam_inv {scope : Nat}
    {body : RawTerm (scope + 1)} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.pathLam body) target) :
    ∃ bodyTarget, target = RawTerm.pathLam bodyTarget ∧
      RawStep.par body bodyTarget := by
  cases parallelStep with
  | refl _ => exact ⟨body, rfl, RawStep.par.refl _⟩
  | pathLamCong bodyStep => exact ⟨_, rfl, bodyStep⟩

/-- D3.6-S1 `RawStep.par (uaToEquiv proof) target → target =
uaToEquiv proof' ∧ par proof proof'`.  Required by `RawCdLemma`'s
`uaBetaDeep` arm and `cdTranspCase` activation: a parallel step
landing at `uaToEquiv X` admits only the `uaToEquivCong` rule (or
`refl`), so the target is `uaToEquiv` of an inner par-target. -/
theorem RawStep.par.uaToEquiv_inv {scope : Nat}
    {proof : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.uaToEquiv proof) target) :
    ∃ proofTarget, target = RawTerm.uaToEquiv proofTarget ∧
      RawStep.par proof proofTarget := by
  cases parallelStep with
  | refl _ => exact ⟨proof, rfl, RawStep.par.refl _⟩
  | uaToEquivCong proofStep => exact ⟨_, rfl, proofStep⟩

/-- D3.6-S3 `RawStep.par (pathCompose left right) target → target =
pathCompose left' right' ∧ par left left' ∧ par right right'`.  Required
by `RawCdLemma`'s `transpComposeDeep` arm and `cdTranspCase`
activation: a parallel step landing at `pathCompose X Y` admits only
the `pathComposeCong` rule (or `refl`), so the target is `pathCompose`
of inner par-targets. -/
theorem RawStep.par.pathCompose_inv {scope : Nat}
    {leftPath rightPath : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.pathCompose leftPath rightPath) target) :
    ∃ leftTarget rightTarget,
      target = RawTerm.pathCompose leftTarget rightTarget ∧
      RawStep.par leftPath leftTarget ∧
      RawStep.par rightPath rightTarget := by
  cases parallelStep with
  | refl _ => exact ⟨leftPath, rightPath, rfl, RawStep.par.refl _, RawStep.par.refl _⟩
  | pathComposeCong leftStep rightStep => exact ⟨_, _, rfl, leftStep, rightStep⟩

/-- D3.6-S4/S5 `RawStep.par (idToEquiv proofSource) target` admits five
disjunctive arms: a congruent `idToEquiv` (cong arm), shallow
identity-β when the proof is syntactically a `refl witness` head
(idToEquivRefl arm), deep identity-β when the proof develops to
`refl witness` (idToEquivReflDeep arm), shallow compose-β when the
proof is syntactically an `oeqTrans first second` head
(idToEquivCompose arm), or deep compose-β when the proof develops to
`oeqTrans ...` (idToEquivComposeDeep arm).  Required by `RawCdLemma`'s
β arms and the cdIdToEquivCase activation. -/
theorem RawStep.par.idToEquiv_inv {scope : Nat}
    {proofSource : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.idToEquiv proofSource) target) :
    (∃ proofTarget,
        target = RawTerm.idToEquiv proofTarget ∧
        RawStep.par proofSource proofTarget) ∨
    (∃ (witnessSource witnessTarget : RawTerm scope),
        proofSource = RawTerm.refl witnessSource ∧
        target = RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var (Fin.mk 0 (Nat.zero_lt_succ _))))
          (RawTerm.lam (RawTerm.var (Fin.mk 0 (Nat.zero_lt_succ _)))) ∧
        RawStep.par witnessSource witnessTarget) ∨
    (∃ (witnessTarget : RawTerm scope),
        target = RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var (Fin.mk 0 (Nat.zero_lt_succ _))))
          (RawTerm.lam (RawTerm.var (Fin.mk 0 (Nat.zero_lt_succ _)))) ∧
        RawStep.par proofSource (RawTerm.refl witnessTarget)) ∨
    (∃ (firstSource secondSource firstTarget secondTarget : RawTerm scope),
        proofSource = RawTerm.oeqTrans firstSource secondSource ∧
        target = RawTerm.equivCompose
          (RawTerm.idToEquiv firstTarget)
          (RawTerm.idToEquiv secondTarget) ∧
        RawStep.par firstSource firstTarget ∧
        RawStep.par secondSource secondTarget) ∨
    (∃ (firstTarget secondTarget : RawTerm scope),
        target = RawTerm.equivCompose
          (RawTerm.idToEquiv firstTarget)
          (RawTerm.idToEquiv secondTarget) ∧
        RawStep.par proofSource (RawTerm.oeqTrans firstTarget secondTarget)) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨proofSource, rfl, RawStep.par.refl _⟩
  | idToEquivCong proofStep =>
      exact Or.inl ⟨_, rfl, proofStep⟩
  | @idToEquivRefl _ witnessSource witnessTarget witnessStep =>
      exact Or.inr (Or.inl ⟨witnessSource, witnessTarget, rfl, rfl, witnessStep⟩)
  | @idToEquivReflDeep _ _ witnessTarget proofStep =>
      exact Or.inr (Or.inr (Or.inl ⟨witnessTarget, rfl, proofStep⟩))
  | @idToEquivCompose _ firstSource firstTarget secondSource secondTarget firstStep secondStep =>
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨firstSource, secondSource, firstTarget, secondTarget,
         rfl, rfl, firstStep, secondStep⟩)))
  | @idToEquivComposeDeep _ _ firstTarget secondTarget proofStep =>
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨firstTarget, secondTarget, rfl, proofStep⟩)))

/-- D3.6-S5 `RawStep.par (oeqTrans first second) target → target =
oeqTrans first' second' ∧ par first first' ∧ par second second'`.
Required by `cd_lemma`'s `idToEquivCompose`/`idToEquivComposeDeep`
arms and the cdIdToEquivCase activation: a parallel step landing at
`oeqTrans X Y` admits only the `oeqTransCong` rule (or `refl`). -/
theorem RawStep.par.oeqTrans_inv {scope : Nat}
    {firstProof secondProof : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.oeqTrans firstProof secondProof) target) :
    ∃ firstTarget secondTarget,
      target = RawTerm.oeqTrans firstTarget secondTarget ∧
      RawStep.par firstProof firstTarget ∧
      RawStep.par secondProof secondTarget := by
  cases parallelStep with
  | refl _ => exact ⟨firstProof, secondProof, rfl, RawStep.par.refl _, RawStep.par.refl _⟩
  | oeqTransCong firstStep secondStep => exact ⟨_, _, rfl, firstStep, secondStep⟩

/-- D3.6-S5 `RawStep.par (equivCompose first second) target → target =
equivCompose first' second' ∧ par first first' ∧ par second second'`.
Mirror of `oeqTrans_inv` for the equivalence-composition ctor. -/
theorem RawStep.par.equivCompose_inv {scope : Nat}
    {firstEquiv secondEquiv : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.equivCompose firstEquiv secondEquiv) target) :
    ∃ firstTarget secondTarget,
      target = RawTerm.equivCompose firstTarget secondTarget ∧
      RawStep.par firstEquiv firstTarget ∧
      RawStep.par secondEquiv secondTarget := by
  cases parallelStep with
  | refl _ => exact ⟨firstEquiv, secondEquiv, rfl, RawStep.par.refl _, RawStep.par.refl _⟩
  | equivComposeCong firstStep secondStep => exact ⟨_, _, rfl, firstStep, secondStep⟩

/-- `RawStep.par (pathApp p i) target` either stays a congruent
`pathApp`, or fires cubical path β after the path develops to a
`pathLam`. -/
theorem RawStep.par.pathApp_inv {scope : Nat}
    {pathTerm intervalArg : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.pathApp pathTerm intervalArg) target) :
    (∃ pathTarget intervalTarget,
      target = RawTerm.pathApp pathTarget intervalTarget ∧
        RawStep.par pathTerm pathTarget ∧
        RawStep.par intervalArg intervalTarget) ∨
    (∃ bodyTarget intervalTarget,
      target = bodyTarget.subst0 intervalTarget ∧
        RawStep.par pathTerm (RawTerm.pathLam bodyTarget) ∧
        RawStep.par intervalArg intervalTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨pathTerm, intervalArg, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | pathAppCong pathStep intervalStep =>
      exact Or.inl ⟨_, _, rfl, pathStep, intervalStep⟩
  | betaPathApp bodyStep intervalStep =>
      exact Or.inr ⟨_, _, rfl, RawStep.par.pathLamCong bodyStep, intervalStep⟩
  | betaPathAppDeep pathStep intervalStep =>
      exact Or.inr ⟨_, _, rfl, pathStep, intervalStep⟩
  | betaPathReflApp valueStep intervalStep =>
      -- Source: pathApp (pathLam valueSource.weaken) intervalArg.
      -- valueStep : par <valueSource> target (where target is the header's
      -- target, and the constructor's valueRawTarget unifies with it).
      -- intervalStep : par intervalArg <intervalRawTarget>.
      -- Reuse branch 2 (β-fired) with bodyTarget = target.weaken,
      -- intervalTarget := the constructor's intervalRawTarget.
      -- The equation `target = target.weaken.subst0 intervalRawTarget`
      -- holds via `RawTerm.weaken_subst_singleton`.
      refine Or.inr ⟨target.weaken, _, ?_, ?_, intervalStep⟩
      · exact (RawTerm.weaken_subst_singleton target _).symm
      · exact RawStep.par.pathLamCong
          (RawStep.par.rename (RawRenaming.weaken (scope := _)) valueStep)

/-- `RawStep.par (glueIntro b p) target → target = glueIntro b' p' ∧ pars`. -/
theorem RawStep.par.glueIntro_inv {scope : Nat}
    {baseValue partialValue : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.glueIntro baseValue partialValue) target) :
    ∃ baseTarget partialTarget,
      target = RawTerm.glueIntro baseTarget partialTarget ∧
        RawStep.par baseValue baseTarget ∧
        RawStep.par partialValue partialTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨baseValue, partialValue, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | glueIntroCong baseStep partialStep =>
      exact ⟨_, _, rfl, baseStep, partialStep⟩

/-- `RawStep.par (glueElim g) target` either stays a congruent
`glueElim`, or fires Glue β after the glued value develops to a
`glueIntro`. -/
theorem RawStep.par.glueElim_inv {scope : Nat}
    {gluedValue : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.glueElim gluedValue) target) :
    (∃ gluedTarget, target = RawTerm.glueElim gluedTarget ∧
      RawStep.par gluedValue gluedTarget) ∨
    (∃ baseTarget partialTarget,
      target = baseTarget ∧
        RawStep.par gluedValue
          (RawTerm.glueIntro baseTarget partialTarget)) := by
  cases parallelStep with
  | refl _ => exact Or.inl ⟨gluedValue, rfl, RawStep.par.refl _⟩
  | betaGlueElimIntro baseStep partialStep =>
      exact Or.inr ⟨_, _, rfl,
        RawStep.par.glueIntroCong baseStep partialStep⟩
  | betaGlueElimIntroDeep gluedStep =>
      exact Or.inr ⟨_, _, rfl, gluedStep⟩
  | glueElimCong gluedStep => exact Or.inl ⟨_, rfl, gluedStep⟩

/-- Inversion of `RawStep.par` on a `transp` head: either the target
is again a `transp` (refl / transpCong cases), the LHS path was a
constant `pathLam typeRaw.weaken` and the rule fired through
`transpReflBeta`, the path develops to a constant pathLam-weaken via
parallel step (deep-β `transpReflBetaDeep`), the LHS path was a
`uaToEquiv proofRaw` head and the rule fired through `uaBeta`
(D3.6-S1), the path develops to `uaToEquiv proofRawTarget` via
parallel step (deep ua-β `uaBetaDeep`), the LHS path was a
`pathCompose left right` head and the rule fired through
`transpCompose` (D3.6-S3), or the path develops to a `pathCompose`
shape via parallel step (deep compose-β `transpComposeDeep`). -/
theorem RawStep.par.transp_inv {scope : Nat}
    {pathTerm sourceTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.transp pathTerm sourceTerm) target) :
    (∃ pathTarget sourceTarget,
        target = RawTerm.transp pathTarget sourceTarget ∧
          RawStep.par pathTerm pathTarget ∧
          RawStep.par sourceTerm sourceTarget) ∨
    (∃ (typeRawSource : RawTerm scope) (sourceTarget : RawTerm scope),
        pathTerm = RawTerm.pathLam typeRawSource.weaken ∧
        target = sourceTarget ∧
        RawStep.par sourceTerm sourceTarget) ∨
    (∃ (typeRawTarget : RawTerm scope) (sourceTarget : RawTerm scope),
        target = sourceTarget ∧
        RawStep.par pathTerm (RawTerm.pathLam typeRawTarget.weaken) ∧
        RawStep.par sourceTerm sourceTarget) ∨
    (∃ (proofRawSource proofRawTarget sourceTarget : RawTerm scope),
        pathTerm = RawTerm.uaToEquiv proofRawSource ∧
        target = RawTerm.equivApply (RawTerm.uaToEquiv proofRawTarget)
                                     sourceTarget ∧
        RawStep.par proofRawSource proofRawTarget ∧
        RawStep.par sourceTerm sourceTarget) ∨
    (∃ (proofRawTarget sourceTarget : RawTerm scope),
        target = RawTerm.equivApply (RawTerm.uaToEquiv proofRawTarget)
                                     sourceTarget ∧
        RawStep.par pathTerm (RawTerm.uaToEquiv proofRawTarget) ∧
        RawStep.par sourceTerm sourceTarget) ∨
    (∃ (leftRawSource leftRawTarget rightRawSource rightRawTarget
        sourceTarget : RawTerm scope),
        pathTerm = RawTerm.pathCompose leftRawSource rightRawSource ∧
        target = RawTerm.transp rightRawTarget
                                (RawTerm.transp leftRawTarget sourceTarget) ∧
        RawStep.par leftRawSource leftRawTarget ∧
        RawStep.par rightRawSource rightRawTarget ∧
        RawStep.par sourceTerm sourceTarget) ∨
    (∃ (leftRawTarget rightRawTarget sourceTarget : RawTerm scope),
        target = RawTerm.transp rightRawTarget
                                (RawTerm.transp leftRawTarget sourceTarget) ∧
        RawStep.par pathTerm (RawTerm.pathCompose leftRawTarget rightRawTarget) ∧
        RawStep.par sourceTerm sourceTarget) ∨
    -- D2.5.5 shallow transpPi-β: LHS was literally
    -- `pathLam (piTyCode innerDomain.weaken codomainCodeSource)`; target
    -- is the contractum on `codomainCodeTarget` with a par step both on
    -- the codomain (bi-cong) and the source argument.
    (∃ (innerDomain : RawTerm scope)
       (codomainCodeSource codomainCodeTarget : RawTerm (scope + 2))
       (sourceTarget : RawTerm scope),
        pathTerm = RawTerm.pathLam
          (RawTerm.piTyCode innerDomain.weaken codomainCodeSource) ∧
        target = RawTerm.transpPiBetaContractum codomainCodeTarget sourceTarget ∧
        RawStep.par codomainCodeSource codomainCodeTarget ∧
        RawStep.par sourceTerm sourceTarget) ∨
    -- D2.5.5 deep transpPi-β: path develops via parallel step to
    -- `pathLam (piTyCode innerDomain.weaken codomainCodeMid)`; target is
    -- the contractum on `codomainCodeTarget` (a further par-step on the
    -- codomain from `codomainCodeMid`).
    (∃ (innerDomain : RawTerm scope)
       (codomainCodeMid codomainCodeTarget : RawTerm (scope + 2))
       (sourceTarget : RawTerm scope),
        target = RawTerm.transpPiBetaContractum codomainCodeTarget sourceTarget ∧
        RawStep.par pathTerm
          (RawTerm.pathLam
            (RawTerm.piTyCode innerDomain.weaken codomainCodeMid)) ∧
        RawStep.par codomainCodeMid codomainCodeTarget ∧
        RawStep.par sourceTerm sourceTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨pathTerm, sourceTerm, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | transpCong pathStep sourceStep =>
      exact Or.inl ⟨_, _, rfl, pathStep, sourceStep⟩
  | @transpReflBeta _ typeRawSource _ _ _ _ sourceStep =>
      exact Or.inr (Or.inl ⟨typeRawSource, _, rfl, rfl, sourceStep⟩)
  | @transpReflBetaDeep _ _ typeRawTarget _ _ pathStep sourceStep =>
      exact Or.inr (Or.inr (Or.inl
        ⟨typeRawTarget, _, rfl, pathStep, sourceStep⟩))
  | @uaBeta _ proofRawSource proofRawTarget _ _ proofStep sourceStep =>
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨proofRawSource, proofRawTarget, _, rfl, rfl, proofStep, sourceStep⟩)))
  | @uaBetaDeep _ _ proofRawTarget _ _ pathStep sourceStep =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨proofRawTarget, _, rfl, pathStep, sourceStep⟩))))
  | @transpCompose _ leftRawSource leftRawTarget rightRawSource rightRawTarget
                   _ _ leftStep rightStep sourceStep =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨leftRawSource, leftRawTarget, rightRawSource, rightRawTarget, _,
         rfl, rfl, leftStep, rightStep, sourceStep⟩)))))
  | @transpComposeDeep _ _ leftRawTarget rightRawTarget _ _ pathStep sourceStep =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨leftRawTarget, rightRawTarget, _, rfl, pathStep, sourceStep⟩))))))
  | @transpPiBeta _ innerDomain codomainCodeSource codomainCodeTarget _ _
                  codomainStep sourceStep =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨innerDomain, codomainCodeSource, codomainCodeTarget, _,
         rfl, rfl, codomainStep, sourceStep⟩)))))))
  | @transpPiBetaDeep _ _ innerDomain codomainCodeMid codomainCodeTarget _ _
                      pathStep codomainStep sourceStep =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨innerDomain, codomainCodeMid, codomainCodeTarget, _,
         rfl, pathStep, codomainStep, sourceStep⟩)))))))

/-- Inversion of `RawStep.par` on an `hcomp` head: either the target
is again a `hcomp` (refl / hcompCong cases), the LHS sides was a
constant `pathLam pathBodyRawSource.weaken` and the rule fired through
`hcompBeta` (D2.5.2, shallow constant-path β; the cap reduces to the
target), or the sides develops to a constant pathLam-weaken via
parallel step (deep `hcompBetaDeep`).  In both β arms,
`pathBodyRawSource`/`pathBodyRawTarget` is INDEPENDENT of the cap
target — the raw rule fires for any constant-path body and returns
the cap's reduct.  This mirrors `transp_inv`'s transpReflBeta shape. -/
theorem RawStep.par.hcomp_inv {scope : Nat}
    {sidesTerm capTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.hcomp sidesTerm capTerm) target) :
    (∃ sidesTarget capTarget,
        target = RawTerm.hcomp sidesTarget capTarget ∧
          RawStep.par sidesTerm sidesTarget ∧
          RawStep.par capTerm capTarget) ∨
    (∃ (pathBodyRawSource capTarget : RawTerm scope),
        sidesTerm = RawTerm.pathLam pathBodyRawSource.weaken ∧
        target = capTarget ∧
        RawStep.par capTerm capTarget) ∨
    (∃ (pathBodyRawTarget capTarget : RawTerm scope),
        target = capTarget ∧
        RawStep.par sidesTerm (RawTerm.pathLam pathBodyRawTarget.weaken) ∧
        RawStep.par capTerm capTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨sidesTerm, capTerm, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | hcompCong sidesStep capStep =>
      exact Or.inl ⟨_, _, rfl, sidesStep, capStep⟩
  | hcompBeta _ capStep =>
      exact Or.inr (Or.inl ⟨_, _, rfl, rfl, capStep⟩)
  | hcompBetaDeep sidesStep capStep =>
      exact Or.inr (Or.inr ⟨_, _, rfl, sidesStep, capStep⟩)

/-- `RawStep.par (oeqRefl w) target → target = oeqRefl w' ∧ par w w'`. -/
theorem RawStep.par.oeqRefl_inv {scope : Nat}
    {witness : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.oeqRefl witness) target) :
    ∃ witnessTarget, target = RawTerm.oeqRefl witnessTarget ∧
      RawStep.par witness witnessTarget := by
  cases parallelStep with
  | refl _ => exact ⟨witness, rfl, RawStep.par.refl _⟩
  | oeqReflCong witnessStep => exact ⟨_, rfl, witnessStep⟩

/-- `RawStep.par (oeqJ b w) target → target = oeqJ b' w' ∧ pars`. -/
theorem RawStep.par.oeqJ_inv {scope : Nat}
    {baseCase witness : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.oeqJ baseCase witness) target) :
    ∃ baseTarget witnessTarget,
      target = RawTerm.oeqJ baseTarget witnessTarget ∧
        RawStep.par baseCase baseTarget ∧
        RawStep.par witness witnessTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨baseCase, witness, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | oeqJCong baseStep witnessStep =>
      exact ⟨_, _, rfl, baseStep, witnessStep⟩

/-- `RawStep.par (oeqFunext p) target → target = oeqFunext p' ∧ par`. -/
theorem RawStep.par.oeqFunext_inv {scope : Nat}
    {pointwiseEquality : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.oeqFunext pointwiseEquality) target) :
    ∃ pointwiseTarget, target = RawTerm.oeqFunext pointwiseTarget ∧
      RawStep.par pointwiseEquality pointwiseTarget := by
  cases parallelStep with
  | refl _ => exact ⟨pointwiseEquality, rfl, RawStep.par.refl _⟩
  | oeqFunextCong pointwiseStep => exact ⟨_, rfl, pointwiseStep⟩

/-- `RawStep.par (idStrictRefl w) target → target = idStrictRefl w' ∧ par`. -/
theorem RawStep.par.idStrictRefl_inv {scope : Nat}
    {witness : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.idStrictRefl witness) target) :
    ∃ witnessTarget, target = RawTerm.idStrictRefl witnessTarget ∧
      RawStep.par witness witnessTarget := by
  cases parallelStep with
  | refl _ => exact ⟨witness, rfl, RawStep.par.refl _⟩
  | idStrictReflCong witnessStep => exact ⟨_, rfl, witnessStep⟩

/-- `RawStep.par (idStrictRec b w) target` either remains a strict recursor
or fires the strict-id ι rule. -/
theorem RawStep.par.idStrictRec_inv {scope : Nat}
    {baseCase witness : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.idStrictRec baseCase witness) target) :
    (∃ baseTarget witnessTarget,
      target = RawTerm.idStrictRec baseTarget witnessTarget ∧
        RawStep.par baseCase baseTarget ∧
        RawStep.par witness witnessTarget) ∨
    (∃ reflRawArgument baseTarget,
      target = baseTarget ∧
        RawStep.par witness (RawTerm.idStrictRefl reflRawArgument) ∧
        RawStep.par baseCase baseTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨baseCase, witness, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | idStrictRecCong baseStep witnessStep =>
      exact Or.inl ⟨_, _, rfl, baseStep, witnessStep⟩
  | iotaIdStrictRecRefl witnessRaw baseStep =>
      exact Or.inr ⟨witnessRaw, _, rfl, RawStep.par.refl _, baseStep⟩
  | iotaIdStrictRecReflDeep witnessStep baseStep =>
      exact Or.inr ⟨_, _, rfl, witnessStep, baseStep⟩

/-- `RawStep.par (equivIntro f b) target → target = equivIntro f' b' ∧ pars`. -/
theorem RawStep.par.equivIntro_inv {scope : Nat}
    {forwardFn backwardFn : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.equivIntro forwardFn backwardFn) target) :
    ∃ forwardTarget backwardTarget,
      target = RawTerm.equivIntro forwardTarget backwardTarget ∧
        RawStep.par forwardFn forwardTarget ∧
        RawStep.par backwardFn backwardTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨forwardFn, backwardFn, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | equivIntroCong forwardStep backwardStep =>
      exact ⟨_, _, rfl, forwardStep, backwardStep⟩

/-- `RawStep.par (equivApp e a) target → target = equivApp e' a' ∧ pars`. -/
theorem RawStep.par.equivApp_inv {scope : Nat}
    {equivTerm argument : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.equivApp equivTerm argument) target) :
    ∃ equivTarget argumentTarget,
      target = RawTerm.equivApp equivTarget argumentTarget ∧
        RawStep.par equivTerm equivTarget ∧
        RawStep.par argument argumentTarget := by
  cases parallelStep with
  | refl _ =>
      exact ⟨equivTerm, argument, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | equivAppCong equivStep argumentStep =>
      exact ⟨_, _, rfl, equivStep, argumentStep⟩

end LeanFX2
