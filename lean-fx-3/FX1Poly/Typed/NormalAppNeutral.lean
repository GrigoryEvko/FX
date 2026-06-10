import FX1Poly.Typed.NeutralClassifierUnique
import FX1Poly.Typed.PinnedReflectionPiElimDispatcher

/-! # FX1Poly/Typed/NormalAppNeutral — a normal grown-typed application is neutral
     (route-H reflection, E2.7 app-arm closure — UNCONDITIONAL)

`HasTypeDescPi.normalAppIsNeutral`: the application's function is normal
(`appNormal_functionNormal`) and Π-typed (`invertApp`), so it is λ-or-neutral by the wf-free
canonical forms (`normalFunctionIsLambdaOrNeutralOfTyping`); a λ function would make the whole
application a β-redex (`not_isStepNormalForm_beta_smoke`), contradicting normality — so the
application is neutral (`IsNeutral.app`).

`HasTypeDescPi.normalAppClassifierUnique`: classifier-class uniqueness therefore extends from
neutrals (`neutralClassifierUnique`) to ALL normal applications.  Both wf-free.

With this, same-subject classifier/universe-classification uniqueness covers: variables,
neutrals, normal applications, universe codes (`inversionUniverseCode` + rigidity), and λs are
ruled out at universe classifiers (`lam_notTypedAtUniverseCode`) — leaving the row-bearing
FORMER arm (telescope determinism by child recursion) as E2.7's remaining open piece.

## Zero-axiom verification

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

theorem HasTypeDescPi.normalAppIsNeutral {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {functionTerm argument classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (appCell functionTerm argument) classifier)
    (normal : RawTerm.isStepNormalForm (appCell functionTerm argument)) :
    IsNeutral (appCell functionTerm argument) := by
  obtain ⟨domainCode, codomainCode, functionTyped, _argumentTyped, _classifierConv⟩ :=
    HasTypeDescPi.invertApp typed
  have functionNormal : RawTerm.isStepNormalForm functionTerm :=
    appNormal_functionNormal functionTerm argument normal
  rcases HasTypeDescPi.normalFunctionIsLambdaOrNeutralOfTyping functionTyped functionNormal with
    ⟨domainAnn, body, bodyEq⟩ | functionNeutral
  · rw [bodyEq] at normal
    exact (RawTerm.not_isStepNormalForm_beta_smoke domainAnn body argument normal).elim
  · exact IsNeutral.app functionNeutral

theorem HasTypeDescPi.normalAppClassifierUnique {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {functionTerm argument : RawTerm scope}
    {firstClassifier secondClassifier : RawTerm scope}
    (normal : RawTerm.isStepNormalForm (appCell functionTerm argument))
    (firstTyped : HasTypeDescPi profile context (appCell functionTerm argument) firstClassifier)
    (secondTyped :
      HasTypeDescPi profile context (appCell functionTerm argument) secondClassifier) :
    Conv firstClassifier secondClassifier :=
  HasTypeDescPi.neutralClassifierUnique
    (HasTypeDescPi.normalAppIsNeutral firstTyped normal) firstTyped secondTyped

end FX1Poly.Typed

