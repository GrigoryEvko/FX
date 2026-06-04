import FX1Poly.Typed.HasTypeDescPiConsistency
import FX1Poly.Core.RawConfluence

/-! # FX1Poly/Typed/HasTypeDescPiAppInversion — Π-ELIMINATION (app) inversion for the GROWN engine
    (the OUTER inversion general β-subject-reduction needs; TY-INVN #454/#769, dual of invertLam)

For an `appCell functionTerm argument` SUBJECT typed in the grown engine `HasTypeDescPi`, this file
recovers the piElim premises: the function is typed at a Π-code `piTyCodeCell domainCode codomainCode`,
the argument is typed at the domain, and the classifier is convertible to the dependent output
`RawTerm.subst0 codomainCode argument`.  Together with `HasTypeDescPi.invertLam` (the Π-introduction
inversion) this is everything fully-general β-subject-reduction (TY-SR-beta, #474) consumes:
`app (lam b) a : T` ⟹ invertApp gives `lam b : Π dom cod`, `a : dom`, `T Conv subst0 cod a`; invertLam
gives `b : cod'` under `cons dom'` with `Π dom cod Conv Π dom' cod'`; injecting that Π-`Conv` aligns
domain/codomain and the substitution lemma (#457) retypes `subst0 b a`.

## Why the `Conv` conjunct survives (same reason as invertLam)

Raw `Conv` is an UNCONDITIONAL equivalence relation (`Conv.trans` / `Conv.sym`, harvested from raw
confluence #420/#714), so the `conv` arm composes `converts.sym` with the recursive `Conv` — no
`toHasType`, no `IsType`, no `WfContext`.

## The recipe (propext-free, the dual of invertLam)

Subject-generalised structural recursion (`subject = appCell functionTerm argument` threaded as an `Eq`):

  * `ofFormation` — the FORMATION engine cannot type an application (`HasTypeDesc.subjectRootGenerator`
    pins its root to a type-code/variable root, never `gen_app`) — refuted by `Generator.noConfusion`.
  * `conv` — recurse on the typed premise (same subject), then re-thread the classifier `Conv` by
    `Conv.trans converts.sym recursiveConv`.
  * `piIntro` — the subject is `lamCell`; `congrArg headGenerator` clashes `gen_lam` against `gen_app`.
  * `piElim` — the MATCH: `injection` the two-child `appCell` cell equality (mkGen then childCons twice,
    via the `nlication` drilling pattern) to identify the function and argument, return the arm's
    function/argument typings with `Conv.refl` for the classifier (it IS the dependent output).
  * `genFormationPi` — the subject is a former cell; `congrArg headGenerator` pins the generator to
    `gen_app`, but `typingRuleDescOf gen_app = none` contradicts the `isFormation` witness.

## Zero-axiom verification

Subject-generalised structural recursion + `HasTypeDesc.subjectRootGenerator` + the unconditional
`Conv.trans` / `Conv.sym` / `Conv.refl` + the `mkGen`/`childCons` `injection` drilling + the
`headGenerator` / `Generator.noConfusion` refutations + the `typingRuleDescOf gen_app = none` reduction.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- Subject-generalised recursive workhorse for grown Π-elimination inversion: any grown derivation
whose subject is an `appCell functionTerm argument` exposes the piElim premises (function at a Π-code,
argument at the domain) modulo a classifier `Conv` to the dependent output `subst0 codomainCode
argument`.  The `conv` arm re-threads the conversion through the unconditional raw `Conv.trans`. -/
theorem HasTypeDescPi.invertAppGeneral {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject classifier : RawTerm generalScope}
    (derivation : HasTypeDescPi profile generalContext subject classifier) :
    ∀ {functionTerm argument : RawTerm generalScope}, subject = appCell functionTerm argument →
      ∃ (domainCode : RawTerm generalScope) (codomainCode : RawTerm (generalScope + 1)),
        HasTypeDescPi profile generalContext functionTerm (piTyCodeCell domainCode codomainCode) ∧
          HasTypeDescPi profile generalContext argument domainCode ∧
          Conv classifier (RawTerm.subst0 codomainCode argument) :=
  fun {functionTermImplicit argumentImplicit} =>
    match derivation with
    | .ofFormation formationTyped => fun subjectEq => by
        have rootIsApp : subject.rootGenerator = Generator.gen_app := by
          rw [subjectEq]; rfl
        rcases formationTyped.subjectRootGenerator with isRoot | isRoot | isRoot | isRoot <;>
          · rw [rootIsApp] at isRoot
            exact Generator.noConfusion isRoot
    | .conv _levelExpr _flag typedPremise converts _reclassifierTyped => fun subjectEq => by
        obtain ⟨domainCode, codomainCode, functionTyped, argumentTyped, recursiveConv⟩ :=
          HasTypeDescPi.invertAppGeneral typedPremise subjectEq
        exact ⟨domainCode, codomainCode, functionTyped, argumentTyped,
          Conv.trans converts.sym recursiveConv⟩
    | .piIntro _domainLevel _codomainLevel _flag _domainTyped _codomainTyped _bodyTyped =>
        fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_lam = Generator.gen_app)
    | .piElim functionTyped argumentTyped => fun subjectEq => by
        injection subjectEq with _scopeEq _generatorEq _payloadEq childrenSpineEq
        injection childrenSpineEq with _ _ _ functionTermEq tailSpineEq
        injection tailSpineEq with _ _ _ argumentEq _
        subst functionTermEq
        subst argumentEq
        exact ⟨_, _, functionTyped, argumentTyped, Conv.refl _⟩
    | .genFormationPi _armContext armGenerator _armPayload _armChildren _armLevels _armFlag
        armRule armIsFormation _armPremises => fun subjectEq => by
        have generatorIsApp : armGenerator = Generator.gen_app :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorIsApp
        rw [show typingRuleDescOf Generator.gen_app = none from rfl] at armIsFormation
        nomatch armIsFormation

/-- **Π-elimination (app) inversion for the grown engine.**  An `appCell functionTerm argument` typed
at `classifier` in the grown engine has the function typed at a Π-code `piTyCodeCell domainCode
codomainCode`, the argument typed at the domain, and `classifier` convertible to the dependent output
`RawTerm.subst0 codomainCode argument`.  The clean corollary of `invertAppGeneral` at `subject =
appCell functionTerm argument` (`rfl`); the OUTER inversion fully-general β-subject-reduction consumes
(with `invertLam` for the function). -/
theorem HasTypeDescPi.invertApp {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm argument : RawTerm scope} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (appCell functionTerm argument) classifier) :
    ∃ (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)),
      HasTypeDescPi profile context functionTerm (piTyCodeCell domainCode codomainCode) ∧
        HasTypeDescPi profile context argument domainCode ∧
        Conv classifier (RawTerm.subst0 codomainCode argument) :=
  HasTypeDescPi.invertAppGeneral typed rfl

end FX1Poly.Typed
