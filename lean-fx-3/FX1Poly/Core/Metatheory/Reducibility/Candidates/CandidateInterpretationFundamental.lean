import FX1Poly.Core.Metatheory.Reducibility.Candidates.CandidateReducibleSubst
import FX1Poly.Core.Metatheory.Reducibility.Candidates.ArrowCandidateMembership
import FX1Poly.Core.Rewriting.Reduction.Preservation.SubstPreservationProbes
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationLeaves
import FX1Poly.Core.Rewriting.Reduction.Preservation.CompoundSubstPreservation
import FX1Poly.Tier0.Term.Subst.RawTermSubstConsCommute
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CandidateInterpretationSubst
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationConstructors
import FX1Poly.Core.Eliminators.Nat.NatElimNeutralScrutineeMember
import FX1Poly.Core.Eliminators.List.ListElimNeutralScrutineeMember
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationNatElim
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationListElim
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.BoolElimStrongNormalization
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationIotaRedexes
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.IdentityEliminatorStrongNormalization

/-! # FX1Poly/Core/CandidateInterpretationFundamental
    — the fundamental-theorem cases under a closing substitution, over the choice-free interpretation

The Girard-Tait fundamental theorem is an induction over the typing derivation, each arm producing
"the closed subject lies in the closed classifier's candidate".  Over the candidate-environment
interpretation `InterpretsType` (`CandidateInterpretation`) — which is CHOICE-FREE (the Π codomain is
interpreted in a candidate ENVIRONMENT extended by the domain's candidate, never an `∀ argument ∃
candidate` family) — the candidate-level operations are all shipped (`IsArrowReducible.application` /
`.abstraction`, `ReducibleSubst`, `InterpretsType.rename` / `.subst` / `.isReducibilityCandidate` /
`.headExpansionClosed`).  This file assembles the LEAF + ELIMINATION spine of that induction as
standalone closed-substitution cases — the `var`, arrow-`piElim`, and `universeFormation` arms — each a
thin composition of the shipped operations through the cell-substitution reductions.

  * `fundamentalVariable` (the `var` arm) — a reducible closing substitution sends a variable to a
    member of that variable's candidate.  `subst ρ (var i) = ρ i` (`subst_var_reduces`) and
    `ReducibleSubst` supplies `varCandidates i (ρ i)`.
  * `fundamentalArrowApplication` (the `piElim` / app arm, non-dependent arrow) — a closed function in
    the arrow candidate, applied to a closed reducible argument, lands in the codomain candidate.  The
    closing substitution pushes through the application cell (rfl), then `IsArrowReducible.application`
    discharges it.  The choice-free dependent-elimination payoff at the candidate level.
  * `fundamentalUniverseFormation` (the `universeFormation` arm) — a universe code is a member of the
    universe's candidate, which (a universe code is a weak-head-normal non-Π leaf) is strong
    normalization; the code is a normal leaf (`noStep_universeCode`), so it is strongly normalizing.

## Zero-axiom verification

Each case is a composition of shipped lemmas through `subst_var_reduces` (rfl), the rfl
application-cell substitution, and a `dsimp only [fold]` + `dif_neg` reduction of the childless
universe-code substitution (NOT `unfold`, which pulls `Quot.sound`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by `#audit_namespace
FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Tier0.Syntax FX1Poly.Universe
open StepStar

/-- **The `var` case of the fundamental theorem under a closing substitution.**  A reducible closing
substitution `substitution` (each variable's substituent lies in that variable's candidate,
`ReducibleSubst`) sends the variable `index` to a member of `index`'s candidate: `subst substitution
(var index) = substitution index` (`subst_var_reduces`) which `ReducibleSubst` places in `varCandidates
index`.  The leaf case turning the theorem into the closed-term corollary at `reducibleSubst_identity`.
The type-code side is the `InterpretsType.typeVariable` constructor (the variable interprets to its
environment candidate). -/
theorem InterpretsType.fundamentalVariable {scope targetScope : Nat}
    {varCandidates : CandidateEnv scope targetScope}
    {substitution : RawTermSubst scope targetScope}
    (reducibleSubst : ReducibleSubst varCandidates substitution) (index : Fin scope) :
    varCandidates index
      (RawTerm.subst substitution (.mkGen .gen_var index .childNil)) := by
  rw [RawTerm.subst_var_reduces]
  exact reducibleSubst index

/-- **The `piElim` (application) case of the fundamental theorem under a closing substitution**, at the
non-dependent arrow candidate `InterpretsType.piType` produces.  Given a closed function that is a member
of the arrow candidate `IsArrowReducible domainCandidate codomainCandidate` and a closed argument that is
a member of the domain candidate, the closed application is a member of the codomain candidate.  The
closing substitution pushes through the application cell (`subst (app f a) = app (subst f) (subst a)`,
rfl), and `IsArrowReducible.application` discharges the result — the choice-free dependent-elimination
payoff.  The `functionReducible` / `argumentReducible` premises are the function's and argument's
fundamental-theorem induction hypotheses, already closed by the same substitution. -/
theorem InterpretsType.fundamentalArrowApplication {scope targetScope : Nat}
    {domainCandidate codomainCandidate : RawTerm targetScope → Prop}
    {functionTerm argument : RawTerm scope}
    (substitution : RawTermSubst scope targetScope)
    (functionReducible : IsArrowReducible domainCandidate codomainCandidate
      (RawTerm.subst substitution functionTerm))
    (argumentReducible : domainCandidate (RawTerm.subst substitution argument)) :
    codomainCandidate
      (RawTerm.subst substitution
        (.mkGen .gen_app () (.childCons functionTerm (.childCons argument .childNil)))) :=
  IsArrowReducible.application functionReducible argumentReducible

/-- **The `universeFormation` case of the fundamental theorem under a closing substitution.**  A universe
code is a member of the universe's candidate, which — a universe code being a weak-head-normal non-Π leaf
— `InterpretsType.baseType` makes the strong-normalization candidate; the closed universe code is a
normal leaf (`noStep_universeCode`), hence strongly normalizing.  The closing substitution leaves the
childless universe code unchanged (the non-variable fold branch rebuilds the same cell, reduced by
`dsimp only [fold]` + `dif_neg`). -/
theorem InterpretsType.fundamentalUniverseFormation {scope targetScope : Nat}
    (substitution : RawTermSubst scope targetScope)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (RawTerm.subst substitution
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil)) := by
  have substEquation :
      RawTerm.subst substitution
          (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        = .mkGen .gen_universeCode (levelExpr, flag) .childNil := by
    show fold GenAlgebra.canonical substitution
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil) = _
    dsimp only [fold]
    rw [dif_neg (fun isEq => Generator.noConfusion isEq :
        Generator.gen_universeCode ≠ Generator.gen_var)]
    rfl
  rw [substEquation]
  exact isStronglyNormalizing_of_noStep
    (fun _target step => noStep_universeCode (levelExpr, flag) step)

/-- **The `piIntro` (λ) case of the fundamental theorem under a closing substitution** — the classical hard
Tait case, at the non-dependent arrow candidate.  Given the body's fundamental-theorem induction hypothesis
`bodyReducible` (for every `domainCandidate`-reducible argument, the body — closed under the LIFTED closing
substitution and then β-substituted by the argument — lies in `codomainCandidate`), the domain candidate's
CR1 (`domainArgumentsSN`: domain members are strongly normalizing), and the codomain's head-expansion
closure, the closed `λ body` is a member of the arrow candidate.  The closing substitution pushes through
the lam cell (`subst substitution (lam body) = lam (subst (lift substitution) body)`,
`RawTerm.subst_lam_reduces`, rfl — the binder lifts the substitution), and `IsArrowReducible.abstraction`
discharges the abstraction: the β-redex `app (λ (subst (lift substitution) body)) argument` head-expands to
`subst0 (subst (lift substitution) body) argument`, across which `codomainCandidate`'s closure carries
membership back.  No choice — the codomain candidate is argument-independent (the choice-free
`CandidateInterpretation` no-large-elimination fact), so `bodyReducible` is a single argument-indexed family
into ONE `codomainCandidate`, never an `∀ argument ∃ candidate`.  This is the binder arm completing the
simply-typed introduction spine (var leaf, app elim, λ intro, universe formation) of the fundamental theorem
over the choice-free interpretation. -/
theorem InterpretsType.fundamentalArrowAbstraction {scope targetScope : Nat}
    {domainCandidate codomainCandidate : RawTerm targetScope → Prop}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    (substitution : RawTermSubst scope targetScope)
    (domainAnnSN : IsStronglyNormalizing (RawTerm.subst substitution domainAnn))
    (domainArgumentsSN : ∀ argument : RawTerm targetScope, domainCandidate argument →
      IsStronglyNormalizing argument)
    (codomainClosed : HeadExpansionClosed codomainCandidate)
    (bodyReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      codomainCandidate
        (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) body) argument)) :
    IsArrowReducible domainCandidate codomainCandidate
      (RawTerm.subst substitution
        (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))) := by
  rw [RawTerm.subst_lam_reduces]
  exact IsArrowReducible.abstraction domainAnnSN domainArgumentsSN codomainClosed bodyReducible

/-- **The `piIntro` (λ) fundamental-theorem arm in the form the closure induction supplies it** — the
binder arm packaged for direct dispatch by the `HasTypeDescPi` fundamental-theorem induction.  When the
induction reaches `λ body : Π domain codomain`, the body's induction hypothesis is taken at the
binder-EXTENDED closing environment: the substitution extended by the argument, `RawTermSubst.cons argument
substitution` — so the IH delivers `codomainCandidate (subst (cons argument substitution) body)` for every
`domainCandidate`-reducible argument (`bodyReducible` here, the cons-substitution form).  But
`fundamentalArrowAbstraction` / `IsArrowReducible.abstraction` consume the β-redex form `subst0 (subst (lift
substitution) body) argument`.  The binder-split keystone `RawTerm.subst_cons_eq_subst0_lift` is exactly the
bridge — `subst (cons argument substitution) body = subst0 (subst (lift substitution) body) argument` — so a
single rewrite reshapes the IH into the abstraction premise.  This is the precise glue the closure induction
calls in its piIntro arm: no further substitution reasoning needed at the induction site, just this lemma. -/
theorem InterpretsType.fundamentalArrowAbstractionConsForm {scope targetScope : Nat}
    {domainCandidate codomainCandidate : RawTerm targetScope → Prop}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    (substitution : RawTermSubst scope targetScope)
    (domainAnnSN : IsStronglyNormalizing (RawTerm.subst substitution domainAnn))
    (domainArgumentsSN : ∀ argument : RawTerm targetScope, domainCandidate argument →
      IsStronglyNormalizing argument)
    (codomainClosed : HeadExpansionClosed codomainCandidate)
    (bodyReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      codomainCandidate
        (RawTerm.subst (RawTermSubst.cons argument substitution) body)) :
    IsArrowReducible domainCandidate codomainCandidate
      (RawTerm.subst substitution
        (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))) := by
  apply InterpretsType.fundamentalArrowAbstraction substitution domainAnnSN domainArgumentsSN
    codomainClosed
  intro argument argumentInDomain
  rw [← RawTerm.subst_cons_eq_subst0_lift]
  exact bodyReducible argument argumentInDomain

/-- **The dependent `piElim` (application) classifier conversion** — the elimination-side counterpart of
`fundamentalArrowAbstractionConsForm`, the precise glue the closure induction's piElim arm calls.  In the
`HasTypeDescPi` engine, applying `functionTerm : Π domainCode. codomainCode` to `argument : domainCode`
yields the DEPENDENT classifier `subst0 codomainCode argument` (the codomain instantiated at the actual
argument — `piElim`'s motive-dependent output).  But the function's induction hypothesis interprets its Π
classifier as `IsArrowReducible domainCandidate codomainCandidate`, where `codomainCandidate` is the codomain
interpreted in the env EXTENDED by the domain's candidate (`InterpretsType (env.cons domainCandidate)
codomainCode codomainCandidate`).  This lemma reconciles the two: the substituted codomain `subst0
codomainCode argument` interprets, under the BASE env, to the SAME `codomainCandidate` — provided the
argument, viewed as a type-code, interprets to the domain's candidate (`argumentInterprets`, the
no-large-elimination premise — the codomain's candidate depends only on the argument's candidate, never its
value).  It is the singleton-substitution instance of the general semantic substitution lemma
`InterpretsType.subst`: the variable-0 substituent is `argument` (interpreting to `domainCandidate`), every
higher variable `k+1` maps to `var k` (interpreting to `env k` by `typeVariable`), and `subst0 codomainCode
argument = subst (singleton argument) codomainCode` definitionally.  With this, the closure's piElim arm
reads off `codomainCandidate (subst σ (appCell functionTerm argument))` from `fundamentalArrowApplication`
and rewrites the classifier to `subst0 codomainCode argument` — no substitution reasoning at the arm. -/
theorem InterpretsType.codomainAfterApplication {scope targetScope : Nat}
    {env : CandidateEnv scope targetScope}
    {domainCandidate codomainCandidate : RawTerm targetScope → Prop}
    {codomainCode : RawTerm (scope + 1)} {argument : RawTerm scope}
    (codomainInterprets :
      InterpretsType (CandidateEnv.cons domainCandidate env) codomainCode codomainCandidate)
    (argumentInterprets : InterpretsType env argument domainCandidate) :
    InterpretsType env (RawTerm.subst0 codomainCode argument) codomainCandidate := by
  apply codomainInterprets.subst (RawTermSubst.singleton argument)
  intro index
  match index with
  | ⟨0, _⟩ => exact argumentInterprets
  | ⟨priorValue + 1, hBound⟩ =>
      exact InterpretsType.typeVariable env ⟨priorValue, Nat.lt_of_succ_lt_succ hBound⟩

/-- **The Π-former `genFormationPi` case of the fundamental theorem under a closing substitution.**  A
Π-type code `Π domain. codomain` is a member of its universe `Type@e`'s candidate — which (the universe
code being a non-Π weak-head-normal leaf) `InterpretsType.baseType` makes the strong-normalization
candidate — so membership is exactly strong normalization of the (substituted) former.  The closing
substitution distributes over the Π cell by `rfl` (domain by the substitution, codomain by the lift), and
`piTyCode_isStronglyNormalizing_of_domain_codomain` builds the former's SN from its children's SN — the
children's fundamental-theorem induction hypotheses, each a member of its own universe's SN candidate.
The level-free counterpart of the stratified `IsReducibleMemberAt.piFormationUnderSubst`: over the
opaque-universe interpretation a type former inhabits its universe purely by strong normalization, with no
fuel and no per-former arrow candidate (the arrow candidate is what `InterpretsType.piType` supplies when
the Π is used as a TYPE, not when it is a member of `Type@e`). -/
theorem InterpretsType.fundamentalPiFormation {scope targetScope : Nat}
    (substitution : RawTermSubst scope targetScope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainNormalizing : IsStronglyNormalizing (RawTerm.subst substitution domain))
    (codomainNormalizing :
      IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) codomain)) :
    IsStronglyNormalizing
      (RawTerm.subst substitution
        (.mkGen .gen_piTyCode () (.childCons domain (.childCons codomain .childNil)))) := by
  have substEquation :
      RawTerm.subst substitution
          (.mkGen .gen_piTyCode () (.childCons domain (.childCons codomain .childNil)))
        = .mkGen .gen_piTyCode ()
            (.childCons (RawTerm.subst substitution domain)
              (.childCons (RawTerm.subst (RawTermSubst.lift substitution) codomain) .childNil)) := rfl
  rw [substEquation]
  exact piTyCode_isStronglyNormalizing_of_domain_codomain domainNormalizing codomainNormalizing

/-- **The Σ-former `genFormationPi` case of the fundamental theorem under a closing substitution.**  The
Σ twin of `fundamentalPiFormation`: a Σ-type code `Σ domain. codomain` is a member of its universe
`Type@e`'s strong-normalization candidate, built from its children's SN by
`sigmaTyCode_isStronglyNormalizing_of_domain_codomain`.  Together with `fundamentalPiFormation` and
`fundamentalUniverseFormation` this discharges every `typingRuleDescOf` formation generator's
universe-membership over the choice-free interpretation. -/
theorem InterpretsType.fundamentalSigmaFormation {scope targetScope : Nat}
    (substitution : RawTermSubst scope targetScope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainNormalizing : IsStronglyNormalizing (RawTerm.subst substitution domain))
    (codomainNormalizing :
      IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) codomain)) :
    IsStronglyNormalizing
      (RawTerm.subst substitution
        (.mkGen .gen_sigmaTyCode () (.childCons domain (.childCons codomain .childNil)))) := by
  have substEquation :
      RawTerm.subst substitution
          (.mkGen .gen_sigmaTyCode () (.childCons domain (.childCons codomain .childNil)))
        = .mkGen .gen_sigmaTyCode ()
            (.childCons (RawTerm.subst substitution domain)
              (.childCons (RawTerm.subst (RawTermSubst.lift substitution) codomain) .childNil)) := rfl
  rw [substEquation]
  exact sigmaTyCode_isStronglyNormalizing_of_domain_codomain domainNormalizing codomainNormalizing

/-- **The `natElim` (recursive eliminator) case of the fundamental theorem under a closing
substitution**, at a BASE result type — small elimination, where the result candidate is the
strong-normalization candidate `InterpretsType.baseType` produces.  A `natElim` cell whose motive,
scrutinee, and branches are strongly normalizing under the closing substitution — and whose successor
ι-contractum (the recursive call substituted into the successor branch, the Phase-Z succ-ι being a
SUBSTITUTION) is strongly normalizing for every strongly-normalizing predecessor — is itself strongly
normalizing.  The closing substitution distributes over the four-child `natElim` cell by `rfl` (the
motive under one binder via `RawTermSubst.lift`, the successor branch under two binders via the double
lift, the two same-scope children plainly — `RawTerm.subst_natElim_reduces`), and
`natElim_isStronglyNormalizing_of_strongly_normalizing_branches` builds the cell's SN from the
substituted children's SN plus the substituted successor-contractum obligation.  This is the
data-eliminator extension of the choice-free fundamental theorem's arm family
(var/app/λ/Π/Σ/universe), covering the no-large-elimination fragment `CandidateInterpretation` is sound
for: at a base result type the result candidate IS `IsStronglyNormalizing`, so membership is exactly
strong normalization.  Large elimination (a type-valued motive, whose result candidate is
`IsArrowReducible` or a variable candidate) needs the value-tracking interpretation refinement flagged
in `CandidateInterpretation`'s soundness scope — additive, deferred.  The recursion-closure obligation
`succContractumTerminates` is a premise (as every formation arm takes its children's SN as premises);
its discharge from the successor branch's induction hypothesis is the self-contained value-member
descent `natElimValueMemberSelfContained` (FTGEN-11.1). -/
theorem InterpretsType.fundamentalNatElim {scope targetScope : Nat}
    (substitution : RawTermSubst scope targetScope)
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (motiveNormalizing :
      IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) motive))
    (scrutineeNormalizing : IsStronglyNormalizing (RawTerm.subst substitution scrutinee))
    (zeroBranchNormalizing : IsStronglyNormalizing (RawTerm.subst substitution zeroBranch))
    (succBranchNormalizing :
      IsStronglyNormalizing
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranch))
    (succContractumTerminates :
      ∀ (currentMotive : RawTerm (targetScope + 1)) (currentSucc : RawTerm (targetScope + 2))
        (predecessor currentZero : RawTerm targetScope), IsStronglyNormalizing predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons
              (natElimCellSpine currentMotive predecessor currentZero currentSucc)
              (RawTermSubst.singleton predecessor))
            currentSucc)) :
    IsStronglyNormalizing
      (RawTerm.subst substitution
        (natElimCellSpine motive scrutinee zeroBranch succBranch)) := by
  have substEquation :
      RawTerm.subst substitution (natElimCellSpine motive scrutinee zeroBranch succBranch)
        = natElimCellSpine (RawTerm.subst (RawTermSubst.lift substitution) motive)
            (RawTerm.subst substitution scrutinee)
            (RawTerm.subst substitution zeroBranch)
            (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranch) := rfl
  rw [substEquation]
  exact natElim_isStronglyNormalizing_of_strongly_normalizing_branches
    succContractumTerminates scrutineeNormalizing motiveNormalizing zeroBranchNormalizing
    succBranchNormalizing

/-- **The `natRec` (dependent recursive eliminator) case of the fundamental theorem under a closing
substitution** — the dependent-recursor twin of `fundamentalNatElim`.  `gen_natRec` shares
`gen_natElim`'s four-child Phase-Z shape and its SUBSTITUTING successor ι, so the arm is the
`gen_natElim → gen_natRec` clone: the same `rfl` cell-substitution distribution
(`RawTerm.subst_natRec_reduces`) feeding
`natRec_isStronglyNormalizing_of_strongly_normalizing_branches`.  Same no-large-elimination soundness
scope. -/
theorem InterpretsType.fundamentalNatRec {scope targetScope : Nat}
    (substitution : RawTermSubst scope targetScope)
    {motive : RawTerm (scope + 1)} {scrutinee zeroBranch : RawTerm scope}
    {succBranch : RawTerm (scope + 2)}
    (motiveNormalizing :
      IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) motive))
    (scrutineeNormalizing : IsStronglyNormalizing (RawTerm.subst substitution scrutinee))
    (zeroBranchNormalizing : IsStronglyNormalizing (RawTerm.subst substitution zeroBranch))
    (succBranchNormalizing :
      IsStronglyNormalizing
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranch))
    (succContractumTerminates :
      ∀ (currentMotive : RawTerm (targetScope + 1)) (currentSucc : RawTerm (targetScope + 2))
        (predecessor currentZero : RawTerm targetScope), IsStronglyNormalizing predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons
              (natRecCellSpine currentMotive predecessor currentZero currentSucc)
              (RawTermSubst.singleton predecessor))
            currentSucc)) :
    IsStronglyNormalizing
      (RawTerm.subst substitution
        (natRecCellSpine motive scrutinee zeroBranch succBranch)) := by
  have substEquation :
      RawTerm.subst substitution (natRecCellSpine motive scrutinee zeroBranch succBranch)
        = natRecCellSpine (RawTerm.subst (RawTermSubst.lift substitution) motive)
            (RawTerm.subst substitution scrutinee)
            (RawTerm.subst substitution zeroBranch)
            (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) succBranch) := rfl
  rw [substEquation]
  exact natRec_isStronglyNormalizing_of_strongly_normalizing_branches
    succContractumTerminates scrutineeNormalizing motiveNormalizing zeroBranchNormalizing
    succBranchNormalizing

/-- **The `listElim` (list recursor) case of the fundamental theorem under a closing substitution**,
at a BASE result type.  The list twin of `fundamentalNatElim` with one structural difference: the cons
ι-contractum is an APP-CHAIN, not a substitution — `app (app (app consBranch head) tail) (listElim
motive nilBranch consBranch tail)` — so `consContractumTerminates` quantifies over the cons head and
tail (each strongly normalizing) and asserts the application-chain reduct strongly normalizing, the
recursive `listElim` call threaded through.  The closing substitution distributes over the four-child
`listElim` cell by `rfl` (binder shifts `[1, 0, 0, 0]` — only the motive lifts), and
`listElim_isStronglyNormalizing_of_strongly_normalizing_branches` builds the cell's SN.  Same
no-large-elimination soundness scope as the nat recursors. -/
theorem InterpretsType.fundamentalListElim {scope targetScope : Nat}
    (substitution : RawTermSubst scope targetScope)
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch : RawTerm scope}
    (motiveNormalizing :
      IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) motive))
    (scrutineeNormalizing : IsStronglyNormalizing (RawTerm.subst substitution scrutinee))
    (nilBranchNormalizing : IsStronglyNormalizing (RawTerm.subst substitution nilBranch))
    (consBranchNormalizing : IsStronglyNormalizing (RawTerm.subst substitution consBranch))
    (consContractumTerminates :
      ∀ head tail : RawTerm targetScope,
        IsStronglyNormalizing head → IsStronglyNormalizing tail →
        IsStronglyNormalizing
          (.mkGen .gen_app ()
            (.childCons
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_app ()
                    (.childCons (RawTerm.subst substitution consBranch)
                      (.childCons head .childNil)))
                  (.childCons tail .childNil)))
              (.childCons
                (listElimCellSpine (RawTerm.subst (RawTermSubst.lift substitution) motive)
                  tail (RawTerm.subst substitution nilBranch)
                  (RawTerm.subst substitution consBranch))
                .childNil)))) :
    IsStronglyNormalizing
      (RawTerm.subst substitution
        (listElimCellSpine motive scrutinee nilBranch consBranch)) := by
  have substEquation :
      RawTerm.subst substitution (listElimCellSpine motive scrutinee nilBranch consBranch)
        = listElimCellSpine (RawTerm.subst (RawTermSubst.lift substitution) motive)
            (RawTerm.subst substitution scrutinee)
            (RawTerm.subst substitution nilBranch)
            (RawTerm.subst substitution consBranch) := rfl
  rw [substEquation]
  exact listElim_isStronglyNormalizing_of_strongly_normalizing_branches
    consContractumTerminates scrutineeNormalizing motiveNormalizing nilBranchNormalizing
    consBranchNormalizing

/-- **The `boolElim` (case / match) case of the fundamental theorem under a closing substitution.**  The
NON-recursive eliminator: both ι-contractums are the branches themselves (no substitution, no recursion),
so a `boolElim` cell whose motive, scrutinee, and both branches are strongly normalizing under the closing
substitution is itself strongly normalizing.  The closing substitution distributes over the four-child
`boolElim` cell by `rfl` (motive under one binder via `RawTermSubst.lift`, the rest plainly —
`RawTerm.subst_boolElim_reduces`), and `boolElim_isStronglyNormalizing_of_strongly_normalizing_branches`
discharges the cell's SN with no recursion-closure obligation.  The match-eliminator representative of the
choice-free fundamental theorem's data-eliminator family; same base-result soundness scope as the
recursors. -/
theorem InterpretsType.fundamentalBoolElim {scope targetScope : Nat}
    (substitution : RawTermSubst scope targetScope)
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch : RawTerm scope}
    (motiveNormalizing :
      IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) motive))
    (scrutineeNormalizing : IsStronglyNormalizing (RawTerm.subst substitution scrutinee))
    (thenBranchNormalizing : IsStronglyNormalizing (RawTerm.subst substitution thenBranch))
    (elseBranchNormalizing : IsStronglyNormalizing (RawTerm.subst substitution elseBranch)) :
    IsStronglyNormalizing
      (RawTerm.subst substitution
        (.mkGen .gen_boolElim ()
          (.childCons motive
            (.childCons thenBranch
              (.childCons elseBranch (.childCons scrutinee .childNil)))))) := by
  have substEquation :
      RawTerm.subst substitution
          (.mkGen .gen_boolElim ()
            (.childCons motive
              (.childCons thenBranch
                (.childCons elseBranch (.childCons scrutinee .childNil)))))
        = .mkGen .gen_boolElim ()
            (.childCons (RawTerm.subst (RawTermSubst.lift substitution) motive)
              (.childCons (RawTerm.subst substitution thenBranch)
                (.childCons (RawTerm.subst substitution elseBranch)
                  (.childCons (RawTerm.subst substitution scrutinee) .childNil)))) := rfl
  rw [substEquation]
  exact boolElim_isStronglyNormalizing_of_strongly_normalizing_branches
    scrutineeNormalizing motiveNormalizing thenBranchNormalizing elseBranchNormalizing

/-- **The `fst` (first projection) case of the fundamental theorem under a closing substitution.**  The
projection eliminator for pairs: `fst (pair a b) ↝ a`, the contractum a sub-term of the argument, so the
single-child `fst` cell is strongly normalizing whenever its argument is.  The closing substitution
distributes over the childless-binder `fst` cell by `rfl` (`RawTerm.subst_fst_reduces`), and
`fst_isStronglyNormalizing_of_argument` discharges the cell's SN. -/
theorem InterpretsType.fundamentalFst {scope targetScope : Nat}
    (substitution : RawTermSubst scope targetScope)
    {argument : RawTerm scope}
    (argumentNormalizing : IsStronglyNormalizing (RawTerm.subst substitution argument)) :
    IsStronglyNormalizing
      (RawTerm.subst substitution
        (.mkGen .gen_fst () (.childCons argument .childNil))) := by
  have substEquation :
      RawTerm.subst substitution (.mkGen .gen_fst () (.childCons argument .childNil))
        = .mkGen .gen_fst () (.childCons (RawTerm.subst substitution argument) .childNil) := rfl
  rw [substEquation]
  exact fst_isStronglyNormalizing_of_argument argumentNormalizing

/-- **The `snd` (second projection) case of the fundamental theorem under a closing substitution** — the
`fst` twin, `snd (pair a b) ↝ b`, discharged by `snd_isStronglyNormalizing_of_argument`. -/
theorem InterpretsType.fundamentalSnd {scope targetScope : Nat}
    (substitution : RawTermSubst scope targetScope)
    {argument : RawTerm scope}
    (argumentNormalizing : IsStronglyNormalizing (RawTerm.subst substitution argument)) :
    IsStronglyNormalizing
      (RawTerm.subst substitution
        (.mkGen .gen_snd () (.childCons argument .childNil))) := by
  have substEquation :
      RawTerm.subst substitution (.mkGen .gen_snd () (.childCons argument .childNil))
        = .mkGen .gen_snd () (.childCons (RawTerm.subst substitution argument) .childNil) := rfl
  rw [substEquation]
  exact snd_isStronglyNormalizing_of_argument argumentNormalizing

/-- **The `idJ` (identity / J eliminator) case of the fundamental theorem under a closing substitution.**
The Martin-Löf J eliminator: `idJ motive base (refl w) ↝ base`, the contractum the (passive) base child.
An `idJ` cell whose motive, base, and witness are strongly normalizing under the closing substitution is
itself strongly normalizing.  The closing substitution distributes over the three-child `idJ` cell by
`rfl` (the motive under TWO binders via the double `RawTermSubst.lift`, base and witness plainly —
`RawTerm.subst_idJ_reduces`), and `idJ_isStronglyNormalizing_of_strongly_normalizing_base` discharges the
cell's SN.  The identity-eliminator member of the choice-free fundamental theorem's data-eliminator
family. -/
theorem InterpretsType.fundamentalIdJ {scope targetScope : Nat}
    (substitution : RawTermSubst scope targetScope)
    {motive : RawTerm (scope + 2)} {baseCase witness : RawTerm scope}
    (motiveNormalizing :
      IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) motive))
    (baseCaseNormalizing : IsStronglyNormalizing (RawTerm.subst substitution baseCase))
    (witnessNormalizing : IsStronglyNormalizing (RawTerm.subst substitution witness)) :
    IsStronglyNormalizing
      (RawTerm.subst substitution
        (.mkGen .gen_idJ ()
          (.childCons motive
            (.childCons baseCase (.childCons witness .childNil))))) := by
  have substEquation :
      RawTerm.subst substitution
          (.mkGen .gen_idJ ()
            (.childCons motive
              (.childCons baseCase (.childCons witness .childNil))))
        = .mkGen .gen_idJ ()
            (.childCons
              (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift substitution)) motive)
              (.childCons (RawTerm.subst substitution baseCase)
                (.childCons (RawTerm.subst substitution witness) .childNil))) := rfl
  rw [substEquation]
  exact idJ_isStronglyNormalizing_of_strongly_normalizing_base
    motiveNormalizing baseCaseNormalizing witnessNormalizing

end FX1Poly.Core
