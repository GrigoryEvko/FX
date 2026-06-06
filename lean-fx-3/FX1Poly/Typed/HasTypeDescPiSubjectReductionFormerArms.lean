import FX1Poly.Typed.HasTypeDescPiFormerCongruence
import FX1Poly.Typed.WfContextDescPi
import FX1Poly.Core.StepInversion

/-! # FX1Poly/Typed/HasTypeDescPiSubjectReductionFormerArms
    — the Π/Σ-FORMER routing arms of the grown-engine subject-reduction dispatcher (SN-055)

The companion of `HasTypeDescPiSubjectReductionArms` (λ + application) for the FORMER positions.  A Π/Σ-former
heads no redex, so `Step.from_piTyCode` / `from_sigmaTyCode` expose a 2-way congruence: the DOMAIN steps or the
CODOMAIN steps.  Each routes to the matching congruence arm:

  * **codomain congruence** → `congPiCodomain` / `congSigmaCodomain` (UNCONDITIONAL): the domain is fixed, the
    codomain re-types in place.
  * **domain congruence** → `congPiDomain` / `congSigmaDomain`, which need `codomainReTyping` — the codomain,
    typed under `cons domainCode`, re-typed under `cons domainReduct`.  This is the grown context-conversion
    (#814); it is threaded here as a hypothesis PARAMETERIZED over the domain step.  The dispatcher discharges
    it via `formationCodomainReTyping` for a FORMATION codomain (unconditional) and via the mutual bundle for a
    GROWN codomain (deferred).

These are the dispatcher's `genFormationPi` (and `ofFormation`-former) cases, taking the children's SR + the
codomain re-typing as recursive / contextual hypotheses.

## Zero-axiom verification

`Step.from_piTyCode` / `from_sigmaTyCode` + the shipped former congruence arms.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **SR routing arm at a Π-former.**  `Step (piTyCodeCell domainCode codomainCode) reduct` is domain
congruence (→ `congPiDomain`, with the domain's SR and the codomain re-typing under the stepped domain) or
codomain congruence (→ `congPiCodomain`, with the codomain's SR).  The dispatcher's Π-formation case. -/
theorem HasTypeDescPi.subjectReductionAtPiFormer {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {reduct classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (piTyCodeCell domainCode codomainCode) classifier)
    (step : Step (piTyCodeCell domainCode codomainCode) reduct)
    (domainPreserves : ∀ {domainReduct domainClassifier : RawTerm scope},
      Step domainCode domainReduct →
        HasTypeDescPi profile context domainCode domainClassifier →
          HasTypeDescPi profile context domainReduct domainClassifier)
    (codomainPreserves :
      ∀ {bindingType : RawTerm scope} {codomainReduct codomainClassifier : RawTerm (scope + 1)},
      Step codomainCode codomainReduct →
        HasTypeDescPi profile (context.cons bindingType) codomainCode codomainClassifier →
          HasTypeDescPi profile (context.cons bindingType) codomainReduct codomainClassifier)
    (codomainReTyping : ∀ {domainReduct : RawTerm scope},
      Step domainCode domainReduct →
        ∀ {codomainLevel : LevelExpr} {codomainFlag : UniverseFlag},
          HasTypeDescPi profile (context.cons domainCode) codomainCode
              (universeCodeCell codomainLevel codomainFlag) →
            HasTypeDescPi profile (context.cons domainReduct) codomainCode
              (universeCodeCell codomainLevel codomainFlag))
    (wellFormed : WfContextDescPi context) :
    HasTypeDescPi profile context reduct classifier := by
  rcases Step.from_piTyCode step with ⟨domainAfter, reductEq, domainStep⟩ |
      ⟨codomainAfter, reductEq, codomainStep⟩
  · subst reductEq
    exact HasTypeDescPi.congPiDomain typed
      (fun domainTyped => domainPreserves domainStep domainTyped)
      (codomainReTyping domainStep) wellFormed
  · subst reductEq
    exact HasTypeDescPi.congPiCodomain typed
      (fun codomainTyped => codomainPreserves codomainStep codomainTyped) wellFormed

/-- **SR routing arm at a Σ-former** — the Σ dual of `subjectReductionAtPiFormer`, via `Step.from_sigmaTyCode`
+ `congSigmaDomain` / `congSigmaCodomain`. -/
theorem HasTypeDescPi.subjectReductionAtSigmaFormer {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {reduct classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (sigmaTyCodeCell domainCode codomainCode) classifier)
    (step : Step (sigmaTyCodeCell domainCode codomainCode) reduct)
    (domainPreserves : ∀ {domainReduct domainClassifier : RawTerm scope},
      Step domainCode domainReduct →
        HasTypeDescPi profile context domainCode domainClassifier →
          HasTypeDescPi profile context domainReduct domainClassifier)
    (codomainPreserves :
      ∀ {bindingType : RawTerm scope} {codomainReduct codomainClassifier : RawTerm (scope + 1)},
      Step codomainCode codomainReduct →
        HasTypeDescPi profile (context.cons bindingType) codomainCode codomainClassifier →
          HasTypeDescPi profile (context.cons bindingType) codomainReduct codomainClassifier)
    (codomainReTyping : ∀ {domainReduct : RawTerm scope},
      Step domainCode domainReduct →
        ∀ {codomainLevel : LevelExpr} {codomainFlag : UniverseFlag},
          HasTypeDescPi profile (context.cons domainCode) codomainCode
              (universeCodeCell codomainLevel codomainFlag) →
            HasTypeDescPi profile (context.cons domainReduct) codomainCode
              (universeCodeCell codomainLevel codomainFlag))
    (wellFormed : WfContextDescPi context) :
    HasTypeDescPi profile context reduct classifier := by
  rcases Step.from_sigmaTyCode step with ⟨domainAfter, reductEq, domainStep⟩ |
      ⟨codomainAfter, reductEq, codomainStep⟩
  · subst reductEq
    exact HasTypeDescPi.congSigmaDomain typed
      (fun domainTyped => domainPreserves domainStep domainTyped)
      (codomainReTyping domainStep) wellFormed
  · subst reductEq
    exact HasTypeDescPi.congSigmaCodomain typed
      (fun codomainTyped => codomainPreserves codomainStep codomainTyped) wellFormed

end FX1Poly.Typed
