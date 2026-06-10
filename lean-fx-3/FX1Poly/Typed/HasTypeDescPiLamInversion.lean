import FX1Poly.Typed.HasTypeDescPiConsistency
import FX1Poly.Typed.HasTypeDescPiRootGeneric
import FX1Poly.Core.RawConfluence

/-! # FX1Poly/Typed/HasTypeDescPiLamInversion — Π-INTRODUCTION (λ) inversion for the GROWN engine
    (the inversion general β-subject-reduction explicitly needs)

For a Church-style `lamCell domainAnn body` SUBJECT typed in the grown engine `HasTypeDescPi`, this
file recovers the piIntro premises modulo the conv arm: the classifier is convertible to a Π-code
`piTyCodeCell domainAnn codomainCode` whose domain is the SYNTACTIC ANNOTATION `domainAnn` (the T2
Church-style pin — the annotation IS the rule's domain, so the recovered Π domain coincides with the
annotation), the domain and codomain are grown types at a shared universe flag, and the body is typed
at the codomain under the domain binder.  This is the grown analogue of the simply-typed fragment's
`SimplyTypedTermLF.nbda`, and the lemma `HasTypeDescPi.lean`'s β-SR docstring names as the missing
ingredient for fully-general subject reduction ("the fully-general inverted SR … additionally needs
Π-arm inversion").

## Why the `Conv` conjunct survives here (where the type-code inversions dropped it)

`HasTypeDescPiInversion.lean` (the Π/Σ-CODE component inversions) returns only the component
type-hoods, DROPPING the classifier-`Conv` conjunct.  Here the `Conv` is recovered WITHOUT any
typed-middle obligation: raw `Conv` is an UNCONDITIONAL equivalence relation (`Conv.trans` /
`Conv.sym`, harvested from raw confluence), so the `conv` arm just composes `converts.sym` with the
recursive `Conv` — no well-formedness premise.

## The recipe (propext-free, per the equation-motive cell-index inversion)

Subject-generalised structural recursion (`subject = lamCell domainAnn body` threaded as an `Eq`),
one arm per grown constructor:

  * `ofFormation` — the FORMATION engine cannot type a λ (`HasTypeDesc.subjectRootGenerator` pins its
    root to `gen_var` / `gen_universeCode` / `gen_piTyCode` / `gen_sigmaTyCode`), so the `subject =
    lamCell domainAnn body` equation forces `gen_lam` into that set — refuted by `Generator.noConfusion`.
  * `conv` — recurse on the typed premise (same subject), then re-thread the classifier `Conv` by
    `Conv.trans converts.sym recursiveConv`.
  * `piIntro` — the MATCH: `injection` the two-child `lamCell` cell equality (DOMAIN annotation first,
    then body) to identify the domain annotation and body — the annotation IS the piIntro rule's
    `domainCode`, so the recovered Π domain coincides with it — return the arm's domain/codomain/body
    typings with `Conv.refl` for the classifier (it IS the Π-code).
  * `piElim` — the subject is `appCell`; `congrArg headGenerator` clashes `gen_app` against `gen_lam`,
    refuted by `Generator.noConfusion`.
  * `genFormationPi` — the subject is a former cell; `congrArg headGenerator` pins the generator to
    `gen_lam`, but `typingRuleDescOf gen_lam = none` contradicts the `isFormation` witness.

## Zero-axiom verification

Subject-generalised structural recursion + `HasTypeDesc.subjectRootGenerator` + the unconditional
`Conv.trans` / `Conv.sym` / `Conv.refl` + `injection` + the `headGenerator` / `Generator.noConfusion`
refutations + the `typingRuleDescOf gen_lam = none` reduction.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- Subject-generalised recursive workhorse for grown Π-introduction inversion: any grown derivation
whose subject is a Church-style `lamCell domainAnn body` exposes the piIntro premises modulo a
classifier `Conv` to the Π-code whose DOMAIN IS THE SYNTACTIC ANNOTATION `domainAnn` (the T2 pin).
The `conv` arm re-threads the conversion through the unconditional raw `Conv.trans`. -/
theorem HasTypeDescPi.invertLamGeneral {profile : PolyProfile}
    {generalScope : Nat} {generalContext : TypingContext profile generalScope}
    {subject classifier : RawTerm generalScope}
    (derivation : HasTypeDescPi profile generalContext subject classifier) :
    ∀ {domainAnn : RawTerm generalScope} {body : RawTerm (generalScope + 1)},
      subject = lamCell domainAnn body →
      ∃ (codomainCode : RawTerm (generalScope + 1))
        (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
        Conv classifier (piTyCodeCell domainAnn codomainCode) ∧
          HasTypeDescPi profile generalContext domainAnn (universeCodeCell domainLevel flag) ∧
          HasTypeDescPi profile (generalContext.cons domainAnn) codomainCode
            (universeCodeCell codomainLevel flag) ∧
          HasTypeDescPi profile (generalContext.cons domainAnn) body codomainCode :=
  fun {domainAnnImplicit bodyImplicit} =>
    match derivation with
    | .ofFormation formationTyped => fun subjectEq => by
        have rootIsLam : subject.rootGenerator = Generator.gen_lam := by
          rw [subjectEq]; rfl
        rcases formationTyped.subjectRootGeneratorGeneric with isRoot | isRoot | ⟨_rule, isFormer⟩
        · rw [rootIsLam] at isRoot
          exact Generator.noConfusion isRoot
        · rw [rootIsLam] at isRoot
          exact Generator.noConfusion isRoot
        · -- the root carries a formation rule, but `gen_lam` has `typingRuleDescOf = none`
          rw [rootIsLam] at isFormer
          cases isFormer
    | .conv _levelExpr _flag typedPremise converts _reclassifierTyped => fun subjectEq => by
        obtain ⟨codomainCode, domainLevel, codomainLevel, flag,
            recursiveConv, domainTyped, codomainTyped, bodyTyped⟩ :=
          HasTypeDescPi.invertLamGeneral typedPremise subjectEq
        exact ⟨codomainCode, domainLevel, codomainLevel, flag,
          Conv.trans converts.sym recursiveConv, domainTyped, codomainTyped, bodyTyped⟩
    | .piIntro domainLevel codomainLevel flag domainTyped codomainTyped bodyTyped =>
        fun subjectEq => by
        dsimp only [lamCell] at subjectEq
        injection subjectEq with _scopeEq _generatorEq _payloadEq childrenSpineEq
        injection childrenSpineEq with _ _ _ domainAnnEq tailSpineEq
        injection tailSpineEq with _ _ _ bodyEq _
        subst_vars
        exact ⟨_, domainLevel, codomainLevel, flag, Conv.refl _,
          domainTyped, codomainTyped, bodyTyped⟩
    | .piElim _functionTyped _argumentTyped => fun subjectEq =>
        Generator.noConfusion
          (congrArg RawTerm.headGenerator subjectEq :
            Generator.gen_app = Generator.gen_lam)
    | .genFormationPi _armContext armGenerator _armPayload _armChildren _armLevels _armFlag
        armRule armIsFormation _armPremises => fun subjectEq => by
        have generatorIsLam : armGenerator = Generator.gen_lam :=
          congrArg RawTerm.headGenerator subjectEq
        subst generatorIsLam
        rw [show typingRuleDescOf Generator.gen_lam = none from rfl] at armIsFormation
        nomatch armIsFormation

/-- **Π-introduction (λ) inversion for the grown engine.**  A Church-style `lamCell domainAnn body`
typed at `classifier` in the grown engine has `classifier` convertible to a Π-code `piTyCodeCell
domainAnn codomainCode` whose domain IS THE SYNTACTIC ANNOTATION `domainAnn` (the T2 pin: no domain
existential — the annotation already fixes it), with the domain and codomain grown types at a shared
universe flag and the body typed at the codomain under the domain binder.  The clean corollary of
`invertLamGeneral` at `subject = lamCell domainAnn body` (`rfl`); the inversion fully-general
β-subject-reduction consumes (with `invertApp` for the outer application). -/
theorem HasTypeDescPi.invertLam {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)} {classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (lamCell domainAnn body) classifier) :
    ∃ (codomainCode : RawTerm (scope + 1))
      (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag),
      Conv classifier (piTyCodeCell domainAnn codomainCode) ∧
        HasTypeDescPi profile context domainAnn (universeCodeCell domainLevel flag) ∧
        HasTypeDescPi profile (context.cons domainAnn) codomainCode
          (universeCodeCell codomainLevel flag) ∧
        HasTypeDescPi profile (context.cons domainAnn) body codomainCode :=
  HasTypeDescPi.invertLamGeneral typed rfl

end FX1Poly.Typed
