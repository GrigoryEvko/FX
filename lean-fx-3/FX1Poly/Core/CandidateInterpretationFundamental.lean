import FX1Poly.Core.CandidateReducibleSubst
import FX1Poly.Core.ArrowCandidateMembership
import FX1Poly.Core.SubstPreservationProbes
import FX1Poly.Core.StrongNormalizationLeaves
import FX1Poly.Core.CompoundSubstPreservation
import FX1Poly.Core.RawTermSubstConsCommute
import FX1Poly.Core.CandidateInterpretationSubst
import FX1Poly.Core.StrongNormalizationConstructors

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
open FX1Poly.Foundation FX1Poly.Universe
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
    rw [dif_neg (by decide : Generator.gen_universeCode ≠ Generator.gen_var)]
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

end FX1Poly.Core
