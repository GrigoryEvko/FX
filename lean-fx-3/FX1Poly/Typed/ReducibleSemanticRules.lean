import FX1Poly.Core.StratifiedReducibleMember
import FX1Poly.Core.StratifiedReducibleMemberNonDependent
import FX1Poly.Core.StratifiedReducibleUniverseDecode
import FX1Poly.Core.StrongNormalizationConstructors
import FX1Poly.Core.ConvSubstRename
import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeDescPiSubstitution

/-! # FX1Poly/Typed/ReducibleSemanticRules
    — the fundamental theorem's semantic typing rules under a closing substitution (#425)

The Girard-Tait fundamental theorem over `HasTypeDescPi` is a thin induction on the derivation whose
arms dispatch to SEMANTIC TYPING RULES "under a closing substitution `γ`": each rule takes the induction
hypotheses (the premises' reducibility, already closed by `γ`) and produces the conclusion's reducibility
(also closed by `γ`).  This file accumulates those rules — one per `HasTypeDescPi` constructor — lifting
the shipped raw membership rules (`IsReducibleMemberAt.application` / `.castAlongConv` / `.abstraction`,
and `ReducibleEnvAt.lookupReducible`) through the substitution-commutation lemmas that re-express
`subst γ (cell …)` as `cell (subst γ …)`.

## The application (`piElim`) arm — shipped here

`HasTypeDescPi.piElim` types `appCell functionTerm argument : subst0 codomainCode argument` from
`functionTerm : Π domainCode. codomainCode` and `argument : domainCode`.  Its semantic counterpart takes
the γ-closed reducibility of the function and argument and produces the γ-closed reducibility of the
application at the γ-closed dependent output.  The technical crux is the β-substitution commutation
`RawTerm.subst0_subst_commute`: `subst γ (subst0 codomainCode argument)` is exactly
`subst0 (subst (lift γ) codomainCode) (subst γ argument)` — the dependent output of the substituted
function/argument — so the raw `IsReducibleMemberAt.application` (over the substituted domain/codomain
candidates) lands precisely at the γ-closed classifier.  `subst_appCell` / `subst_piTyCodeCell` (both
`rfl`) re-express the application and Π cells; `iterateLiftRaw γ 1 ≡ RawTermSubst.lift γ` by `rfl`.

This is the literal body of the fundamental theorem's `piElim` arm, threaded at a FIXED `level` — the
elimination rule introduces no universe nesting, so the level rides straight through (the level decrease
is confined to the universe/formation arms).

## Zero-axiom verification

Two `rfl` rewrites (`subst_appCell`, `subst_piTyCodeCell`) + the β-commutation `RawTerm.subst0_subst_commute`
+ the shipped `IsReducibleMemberAt.application` (defeq-unified through `iterateLiftRaw γ 1 ≡ lift γ`).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.StepStar FX1Poly.Universe FX1Poly.Foundation

/-- **Semantic Π elimination under a closing substitution (the `piElim` arm of the fundamental theorem).**
Given that a closing substitution `substitution` sends `functionTerm` to a reducible member of the closed
Π-type `subst (piTyCodeCell domainCode codomainCode)` and `argument` to a reducible member of the closed
domain, it sends `appCell functionTerm argument` to a reducible member of the closed dependent output
`subst (subst0 codomainCode argument)`.

The β-substitution commutation `RawTerm.subst0_subst_commute` re-expresses that closed output as
`subst0 (subst (lift substitution) codomainCode) (subst substitution argument)` — the dependent output of
the substituted pieces — so the shipped raw `IsReducibleMemberAt.application` applies directly (`subst_appCell`
/ `subst_piTyCodeCell` re-express the cells, both `rfl`; `iterateLiftRaw substitution 1 ≡ lift substitution`
by `rfl`).  The `level` is threaded unchanged — elimination introduces no universe nesting. -/
theorem IsReducibleMemberAt.applicationUnderSubst {scope targetScope : Nat} {level : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {functionTerm argument : RawTerm scope}
    (substitution : RawTermSubst scope targetScope)
    (functionReducible : IsReducibleMemberAt level
      (RawTerm.subst substitution (piTyCodeCell domainCode codomainCode))
      (RawTerm.subst substitution functionTerm))
    (argumentReducible : IsReducibleMemberAt level
      (RawTerm.subst substitution domainCode)
      (RawTerm.subst substitution argument)) :
    IsReducibleMemberAt level
      (RawTerm.subst substitution (RawTerm.subst0 codomainCode argument))
      (RawTerm.subst substitution (appCell functionTerm argument)) := by
  rw [subst_piTyCodeCell] at functionReducible
  rw [subst_appCell, RawTerm.subst0_subst_commute]
  exact IsReducibleMemberAt.application functionReducible argumentReducible

/-- **Semantic conversion under a closing substitution (the `conv` arm of the fundamental theorem).**
Given that a closing `substitution` sends `subject` to a reducible member of the closed `classifier`, and
that the closed `reclassifier` is itself a reducible type at `level` — which the fundamental theorem obtains
by `tarskiDecode`-ing the `reclassifier : Type@e` premise's induction hypothesis taken at `level + 1` — it
sends `subject` to a reducible member of the closed `reclassifier`.  The membership transports across the
SUBSTITUTED conversion `Conv.subst substitution converts` via the shipped `IsReducibleMemberAt.castAlongConv`.
The `level` is threaded unchanged — conversion introduces no universe nesting. -/
theorem IsReducibleMemberAt.castAlongConvUnderSubst {scope targetScope : Nat} {level : Nat}
    {classifier reclassifier subject : RawTerm scope}
    {candidateRight : RawTerm targetScope → Prop}
    (substitution : RawTermSubst scope targetScope)
    (subjectReducible : IsReducibleMemberAt level
      (RawTerm.subst substitution classifier) (RawTerm.subst substitution subject))
    (reclassifierReducible : ReducibleTypeAt level
      (RawTerm.subst substitution reclassifier) candidateRight)
    (converts : Conv classifier reclassifier) :
    IsReducibleMemberAt level
      (RawTerm.subst substitution reclassifier) (RawTerm.subst substitution subject) :=
  IsReducibleMemberAt.castAlongConv subjectReducible reclassifierReducible
    (Conv.subst substitution converts)

/-- **Semantic non-dependent Π introduction under a closing substitution (the simply-typed `piIntro` arm of
the fundamental theorem).**  Given that a closing `substitution` makes the domain `domainCode` and the
codomain `codomainCodeBase` reducible types at `level` (the type premises' γ-closed induction hypotheses),
that every domain-reducible argument is strongly normalizing (the domain CR1), and that `body` — under the
lifted substitution — lands in the codomain candidate for every reducible argument (the body's γ-closed IH
at the binder-extended environment), it sends `lamCell body` to a reducible member of the closed SIMPLE
arrow `A → B` (code `piTyCodeCell domainCode (weaken codomainCodeBase)`).

The closed cells re-express by the substitution-commutations: `subst_lamCell` (`rfl`) pushes the
substitution under the λ binder (as `iterateLiftRaw substitution 1 ≡ RawTermSubst.lift substitution`);
`subst_piTyCodeCell` (`rfl`) splits the Π; and the codomain's weakening commutes OUT through the lift by
`subst_lift_weaken_commute` (`subst (lift γ) (weaken B) = weaken (subst γ B)` — `RawTerm.weaken` is
`RawTerm.rename RawRenaming.weaken` definitionally, so the lemma — stated on `rename weaken` — applies),
exposing the γ-closed simple arrow exactly in the shape the shipped raw
`IsReducibleMemberAt.abstractionNonDependent` consumes.  The `level` is threaded unchanged — introduction
introduces no universe nesting.  This is the binder arm of the SIMPLY-TYPED fundamental theorem; the
DEPENDENT `piIntro` (per-argument codomain) belongs to the large-elimination lane. -/
theorem IsReducibleMemberAt.abstractionNonDependentUnderSubst {scope targetScope : Nat} {level : Nat}
    {domainCode codomainCodeBase : RawTerm scope} {body : RawTerm (scope + 1)}
    {domainCandidate codomainCandidate : RawTerm targetScope → Prop}
    (substitution : RawTermSubst scope targetScope)
    (domainReducible : ReducibleTypeAt level
      (RawTerm.subst substitution domainCode) domainCandidate)
    (domainArgumentsSN : ∀ argument : RawTerm targetScope, domainCandidate argument →
      IsStronglyNormalizing argument)
    (codomainReducible : ReducibleTypeAt level
      (RawTerm.subst substitution codomainCodeBase) codomainCandidate)
    (bodyReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      codomainCandidate
        (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) body) argument)) :
    IsReducibleMemberAt level
      (RawTerm.subst substitution (piTyCodeCell domainCode (RawTerm.weaken codomainCodeBase)))
      (RawTerm.subst substitution (lamCell body)) := by
  have typeEq :
      RawTerm.subst substitution (piTyCodeCell domainCode (RawTerm.weaken codomainCodeBase))
        = piTyCodeCell (RawTerm.subst substitution domainCode)
            (RawTerm.weaken (RawTerm.subst substitution codomainCodeBase)) := by
    rw [subst_piTyCodeCell]
    exact congrArg (piTyCodeCell (RawTerm.subst substitution domainCode))
      (subst_lift_weaken_commute substitution codomainCodeBase)
  rw [typeEq, subst_lamCell]
  exact IsReducibleMemberAt.abstractionNonDependent
    domainReducible domainArgumentsSN codomainReducible bodyReducible

/-- **Semantic DEPENDENT Π introduction under a closing substitution (the dependent `piIntro` arm).**  The
dependent twin of `abstractionNonDependentUnderSubst`: the codomain candidate `codomainCandidate argument`
is a PER-ARGUMENT family (the codomain code `codomainCode : RawTerm (scope + 1)` genuinely varies with the
bound variable), so this is the introduction arm the FULL (large-elimination) fundamental theorem consumes
once the recursive type-interpretation supplies the per-argument candidates.

As a SEMANTIC RULE it is choice-free and shippable now — it merely lifts the shipped raw
`IsReducibleMemberAt.abstraction`, which TAKES the per-argument candidate as given; the candidate-congruence
choice obstruction lives in the FT ASSEMBLY (constructing the candidate from `∀ argument ∃ candidate`), not
here.  It is also CLEANER than the non-dependent arm: the dependent codomain stays in the extended scope, so
only the `rfl` cell-substitutions `subst_piTyCodeCell` / `subst_lamCell` are needed (which push the closing
substitution under the binder as `iterateLiftRaw substitution 1 ≡ RawTermSubst.lift substitution`) — NO
weakening-commutation.  The `level` is threaded unchanged. -/
theorem IsReducibleMemberAt.abstractionUnderSubst {scope targetScope : Nat} {level : Nat}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainCandidate : RawTerm targetScope → Prop}
    {codomainCandidate : RawTerm targetScope → (RawTerm targetScope → Prop)}
    (substitution : RawTermSubst scope targetScope)
    (domainReducible : ReducibleTypeAt level
      (RawTerm.subst substitution domainCode) domainCandidate)
    (domainArgumentsSN : ∀ argument : RawTerm targetScope, domainCandidate argument →
      IsStronglyNormalizing argument)
    (codomainReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      ReducibleTypeAt level
        (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) argument)
        (codomainCandidate argument))
    (bodyReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      codomainCandidate argument
        (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) body) argument)) :
    IsReducibleMemberAt level
      (RawTerm.subst substitution (piTyCodeCell domainCode codomainCode))
      (RawTerm.subst substitution (lamCell body)) := by
  rw [subst_piTyCodeCell, subst_lamCell]
  exact IsReducibleMemberAt.abstraction
    domainReducible domainArgumentsSN codomainReducible bodyReducible

/-- **Semantic non-dependent (simply-typed) Π formation under a closing substitution (the simple-arrow
`Π`-formation arm).**  `gen_piTyCode (A, weaken B)` is a reducible TYPE at the non-dependent arrow candidate
`IsArrowReducible domainCandidate codomainCandidate` under a closing `substitution`, from the γ-closed
reducibility of the domain `A` and the codomain `B`.  Lifts the shipped raw `ReducibleTypeAt.arrowType`
through the SAME `typeEq` re-expression as `abstractionNonDependentUnderSubst` (`subst_piTyCodeCell` rfl +
`subst_lift_weaken_commute` for the codomain weakening through the binder lift).  The type-former companion
to the simply-typed `piIntro` arm; the `level` rides through unchanged. -/
theorem ReducibleTypeAt.arrowTypeUnderSubst {scope targetScope : Nat} {level : Nat}
    {domainCode codomainCodeBase : RawTerm scope}
    {domainCandidate codomainCandidate : RawTerm targetScope → Prop}
    (substitution : RawTermSubst scope targetScope)
    (domainReducible : ReducibleTypeAt level
      (RawTerm.subst substitution domainCode) domainCandidate)
    (codomainReducible : ReducibleTypeAt level
      (RawTerm.subst substitution codomainCodeBase) codomainCandidate) :
    ReducibleTypeAt level
      (RawTerm.subst substitution (piTyCodeCell domainCode (RawTerm.weaken codomainCodeBase)))
      (IsArrowReducible domainCandidate codomainCandidate) := by
  have typeEq :
      RawTerm.subst substitution (piTyCodeCell domainCode (RawTerm.weaken codomainCodeBase))
        = piTyCodeCell (RawTerm.subst substitution domainCode)
            (RawTerm.weaken (RawTerm.subst substitution codomainCodeBase)) := by
    rw [subst_piTyCodeCell]
    exact congrArg (piTyCodeCell (RawTerm.subst substitution domainCode))
      (subst_lift_weaken_commute substitution codomainCodeBase)
  rw [typeEq]
  exact ReducibleTypeAt.arrowType domainReducible codomainReducible

/-- **Semantic DEPENDENT Π formation under a closing substitution (the dependent `Π`-formation arm).**  The
dependent twin of `arrowTypeUnderSubst`: `gen_piTyCode (A, codomainCode)` with a genuinely dependent codomain
`codomainCode : RawTerm (scope + 1)` is a reducible TYPE at the dependent-arrow candidate
`IsDependentArrowReducible domainCandidate codomainCandidate` under a closing `substitution`.  Lifts the
shipped raw `ReducibleTypeAt.piType`; like `abstractionUnderSubst` it needs ONLY the `rfl` cell-substitution
`subst_piTyCodeCell` (the dependent codomain stays in the extended scope — no weakening-commutation), so the
per-argument codomain reducibility carries straight through.  The formation arm of the full
(large-elimination) fundamental theorem; choice-free as a semantic rule (the per-argument candidate is
given). -/
theorem ReducibleTypeAt.piTypeUnderSubst {scope targetScope : Nat} {level : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainCandidate : RawTerm targetScope → Prop}
    {codomainCandidate : RawTerm targetScope → (RawTerm targetScope → Prop)}
    (substitution : RawTermSubst scope targetScope)
    (domainReducible : ReducibleTypeAt level
      (RawTerm.subst substitution domainCode) domainCandidate)
    (codomainReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      ReducibleTypeAt level
        (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) argument)
        (codomainCandidate argument)) :
    ReducibleTypeAt level
      (RawTerm.subst substitution (piTyCodeCell domainCode codomainCode))
      (IsDependentArrowReducible domainCandidate codomainCandidate) := by
  rw [subst_piTyCodeCell]
  exact ReducibleTypeAt.piType codomainCandidate domainReducible codomainReducible

/-- **CHOICE-FREE dependent Π formation under a closing substitution.**  The canonical-codomain twin of
`piTypeUnderSubst`: feeds the FIXED codomain function `fun argument => IsReducibleMemberAt level (subst0
(subst (lift substitution) codomainCode) argument)`, so the per-argument codomain premise is discharged from
mere per-argument EXISTENCE (`codomainExists`) by `ReducibleTypeAt.piTypeCanonical`.  No per-argument
candidate is chosen — this is the under-substitution Π-FORMATION arm of the dependent fundamental theorem
that actually dissolves the choice wall (unlike `piTypeUnderSubst`, which takes the candidate as given). -/
theorem ReducibleTypeAt.piTypeCanonicalUnderSubst {scope targetScope : Nat} {level : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainCandidate : RawTerm targetScope → Prop}
    (substitution : RawTermSubst scope targetScope)
    (domainReducible : ReducibleTypeAt level
      (RawTerm.subst substitution domainCode) domainCandidate)
    (codomainExists : ∀ argument : RawTerm targetScope, domainCandidate argument →
      IsReducibleTypeAt level
        (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) argument)) :
    ReducibleTypeAt level
      (RawTerm.subst substitution (piTyCodeCell domainCode codomainCode))
      (IsDependentArrowReducible domainCandidate
        (fun argument => IsReducibleMemberAt level
          (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) argument))) := by
  rw [subst_piTyCodeCell]
  exact ReducibleTypeAt.piTypeCanonical domainReducible codomainExists

/-- **CHOICE-FREE dependent Π introduction under a closing substitution (the dependent `piIntro` FT arm).**
The canonical-codomain twin of `abstractionUnderSubst`: the body's fundamental-theorem IH lands it in
`IsReducibleMemberAt level (subst0 (subst (lift substitution) codomainCode) argument)` for every reducible
argument, and the codomain-reducibility premise is discharged from existence by
`IsReducibleMemberAt.abstractionCanonical`.  This is the choice-free dependent generalization of
`abstractionNonDependentUnderSubst`; the binder arm of the dependent fundamental theorem. -/
theorem IsReducibleMemberAt.abstractionCanonicalUnderSubst {scope targetScope : Nat} {level : Nat}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {domainCandidate : RawTerm targetScope → Prop}
    (substitution : RawTermSubst scope targetScope)
    (domainReducible : ReducibleTypeAt level
      (RawTerm.subst substitution domainCode) domainCandidate)
    (domainArgumentsSN : ∀ argument : RawTerm targetScope, domainCandidate argument →
      IsStronglyNormalizing argument)
    (codomainExists : ∀ argument : RawTerm targetScope, domainCandidate argument →
      IsReducibleTypeAt level
        (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) argument))
    (bodyReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      IsReducibleMemberAt level
        (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) argument)
        (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) body) argument)) :
    IsReducibleMemberAt level
      (RawTerm.subst substitution (piTyCodeCell domainCode codomainCode))
      (RawTerm.subst substitution (lamCell body)) := by
  rw [subst_piTyCodeCell, subst_lamCell]
  exact IsReducibleMemberAt.abstractionCanonical
    domainReducible domainArgumentsSN codomainExists bodyReducible

/-- **A formation generator's cell admits no weak-head step (the `genFormationPi` arm's weak-head-normality
obligation).**  The grown engine's sole formation arm `HasTypeDescPi.genFormationPi` is generic over
`typingRuleDescOf generator = some rule`; that table is `some` for EXACTLY `gen_piTyCode` and
`gen_sigmaTyCode` (the two dependent type-formers), both of which are weak-head normal — a type former is
neither a β-redex (root `gen_app`) nor an ι-redex (an eliminator applied to a constructor), so the only
weak-head arm whose subject unifies is `rootIota`, and no `IotaHeadStep` fires on a former root.  This
discharges the weak-head-normality hypothesis of `ReducibleTypeAt.reducibleOfWeakHeadNormalFormer` for the
non-Π formation formers (`gen_sigmaTyCode` and any future data former added as a `typingRuleDescOf` row),
so the fundamental theorem's `genFormationPi` arm classifies the substituted former by strong normalization
in the Tarski universe with no per-former weak-head-normality proof at the induction site.  The `gen_piTyCode`
case is handled separately (the arrow candidate via `piTypeCanonicalUnderSubst`); this lemma covers the
weak-head-normality both share.  Proof: the formation generator is `gen_piTyCode` or `gen_sigmaTyCode` (else
`typingRuleDescOf` is `none`, contradicting `isFormation`), and each is weak-head normal by
`cases` on the step leaving only the vacuous `rootIota`/`IotaHeadStep`. -/
theorem formationGenerator_noWeakHeadStep {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    {rule : TypingRuleDesc} (isFormation : typingRuleDescOf generator = some rule) :
    ∀ reduct : RawTerm scope,
      ¬ WeakHeadStep (.mkGen generator payload children) reduct := by
  by_cases isPiFormer : generator = .gen_piTyCode
  · subst isPiFormer
    intro _reduct weakHeadStep
    cases weakHeadStep with
    | rootIota iotaStep => cases iotaStep
  · by_cases isSigmaFormer : generator = .gen_sigmaTyCode
    · subst isSigmaFormer
      intro _reduct weakHeadStep
      cases weakHeadStep with
      | rootIota iotaStep => cases iotaStep
    · simp only [typingRuleDescOf, if_neg isPiFormer, if_neg isSigmaFormer] at isFormation
      nomatch isFormation

/-- **Semantic Σ-former formation under a closing substitution (the `genFormationPi` data-former arm for
`gen_sigmaTyCode`).**  Under a closing `substitution`, the Σ-type code `Σ domain. codomain` is a reducible
member of its universe `Type@levelExpr` whenever its substituted domain and under-binder codomain are
strongly normalizing (the telescope's γ-closed strong-normalization induction hypotheses).  The substituted
former is strongly normalizing (`sigmaTyCode_isStronglyNormalizing_of_domain_codomain` over the substituted
children — the substitution distributes over the Σ cell by `rfl`, domain by `substitution`, codomain by the
lift) and a reducible TYPE classified by strong normalization in the Tarski universe
(`IsReducibleMemberAt.dataFormerInUniverse`: weak-head normal — only the vacuous `rootIota` arm unifies a
Σ root — and root-distinct from Π / universe); `subst_universeCodeCell` (`rfl`) leaves the universe
classifier fixed.  Together with `piTypeCanonicalUnderSubst` (the `gen_piTyCode` arm) and
`formationGenerator_noWeakHeadStep` (the weak-head-normality common to both formation generators), this
discharges the fundamental theorem's `genFormationPi` arm entirely by dispatch over the two
`typingRuleDescOf` formers — no per-former development remains at the induction site. -/
theorem IsReducibleMemberAt.sigmaFormationUnderSubst {scope targetScope : Nat} {predLevel : Nat}
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (substitution : RawTermSubst scope targetScope)
    (domainNormalizing : IsStronglyNormalizing (RawTerm.subst substitution domain))
    (codomainNormalizing :
      IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) codomain)) :
    IsReducibleMemberAt (predLevel + 1)
      (RawTerm.subst substitution (universeCodeCell levelExpr flag))
      (RawTerm.subst substitution
        (.mkGen .gen_sigmaTyCode () (.childCons domain (.childCons codomain .childNil)))) := by
  rw [subst_universeCodeCell]
  have substEq :
      RawTerm.subst substitution
          (.mkGen .gen_sigmaTyCode () (.childCons domain (.childCons codomain .childNil)))
        = .mkGen .gen_sigmaTyCode ()
            (.childCons (RawTerm.subst substitution domain)
              (.childCons (RawTerm.subst (RawTermSubst.lift substitution) codomain) .childNil)) := rfl
  rw [substEq]
  exact IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (sigmaTyCode_isStronglyNormalizing_of_domain_codomain domainNormalizing codomainNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

/-- **Semantic Π-former formation under a closing substitution (the `genFormationPi` arm for
`gen_piTyCode`).**  Under a closing `substitution`, the Π-type code `Π domain. codomain` is a reducible
member of its universe `Type@levelExpr` from: the domain's γ-closed reducibility + per-argument codomain
existence (the dependent-Π formation data), plus strong normalization of the substituted domain and
under-binder codomain.  Unlike the Σ / data-former arm (`sigmaFormationUnderSubst`, routed through
`dataFormerInUniverse` whose `reducibleOfWeakHeadNormalFormer` core EXCLUDES Π roots), the Π former is NOT
classified by the bare strong-normalization candidate — it is a reducible TYPE at the genuine
(dependent-)arrow candidate.  So membership in the universe is `tarskiEncode` of: strong normalization of
the substituted Π former (`piTyCode_isStronglyNormalizing_of_domain_codomain` over the substituted children,
the cell distributing by `subst_piTyCodeCell`/`rfl`) AND its reducibility-as-a-type
(`piTypeCanonicalUnderSubst`, the choice-free dependent Π-formation, packaged existentially).
`subst_universeCodeCell` (`rfl`) leaves the universe classifier fixed.  Together with
`sigmaFormationUnderSubst` (the Σ / data-former arm) and `formationGenerator_noWeakHeadStep` (the
weak-head-normality the formers share), this completes the universe-membership half of the fundamental
theorem's `genFormationPi` arm for BOTH `typingRuleDescOf` formers — no per-former development remains at the
induction site. -/
theorem IsReducibleMemberAt.piFormationUnderSubst {scope targetScope : Nat} {predLevel : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {domainCandidate : RawTerm targetScope → Prop}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (substitution : RawTermSubst scope targetScope)
    (domainReducible : ReducibleTypeAt predLevel
      (RawTerm.subst substitution domainCode) domainCandidate)
    (domainNormalizing : IsStronglyNormalizing (RawTerm.subst substitution domainCode))
    (codomainNormalizing :
      IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift substitution) codomainCode))
    (codomainExists : ∀ argument : RawTerm targetScope, domainCandidate argument →
      IsReducibleTypeAt predLevel
        (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) argument)) :
    IsReducibleMemberAt (predLevel + 1)
      (RawTerm.subst substitution (universeCodeCell levelExpr flag))
      (RawTerm.subst substitution (piTyCodeCell domainCode codomainCode)) := by
  rw [subst_universeCodeCell]
  have formerNormalizing :
      IsStronglyNormalizing (RawTerm.subst substitution (piTyCodeCell domainCode codomainCode)) := by
    rw [subst_piTyCodeCell]
    exact piTyCode_isStronglyNormalizing_of_domain_codomain domainNormalizing codomainNormalizing
  exact IsReducibleMemberAt.tarskiEncode formerNormalizing
    ⟨_, ReducibleTypeAt.piTypeCanonicalUnderSubst substitution domainReducible codomainExists⟩

end FX1Poly.Typed
