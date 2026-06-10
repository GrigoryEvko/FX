import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeDescWeakening
import FX1Poly.Typed.CellRenaming
import FX1Poly.Core.StepEta

/-! # FX1Poly/Typed/HasTypeDescPiEtaCoherence
    — η-coherence for formation-component functions (the η-twin of `betaCoherence_formationBody`, PAR-2)

`HasTypeDescPi.betaCoherence_formationBody` (in `HasTypeDescPi.lean`) ships the FIRST non-vacuous β
subject-reduction fact for the grown engine: a β-redex built from FORMATION components and its β-reduct both
type at the same classifier.  This file ships the η counterpart — the analogous PRESERVATION fact for the η
direction, built FORWARD (no inversion, no grown strengthening): a function `f : Π D C` whose components type in
the formation engine produces an η-redex `λ. (weaken f @ var 0)` (= `RawTerm.etaLamSource f`) that types at the
SAME `Π D C` as `f` itself.  This is the η-direction's analogue of the β-coherence and the first step of the
grown-engine η subject-reduction arc.

Two declarations:

  * **`RawTerm.subst0_iterateLiftWeaken_newestVar`** — THE η identity (the load-bearing substrate lemma):
    lifting a codomain `C` past a fresh binder (`rename (iterateLiftRaw weaken 1) C`, the exact shape
    `rename_piTyCodeCell` produces for the weakened function type's codomain) and then instantiating de-Bruijn-0
    with the newest variable returns `C` unchanged.  Proof: `subst0` unfolds to `subst (singleton newestVar)`;
    `rename_subst_commute` fuses the `subst`-after-`rename` into one substitution; that composite is
    pointwise the identity substitution (var 0 ↦ var 0 via `singleton`'s zero arm; var (k+1) ↦ var (k+1)
    because the lift shifted it to var (k+2) which `singleton`'s successor arm sends back to var (k+1)); close
    with `subst_identity_apply`.  This is the de Bruijn law that makes η typecheck and is reusable by any
    η-typing work.

  * **`HasTypeDescPi.etaCoherence_formationFunction`** — the η-coherence proper.  Given the formation typings of
    `D` (`domainFormationTyped`), `C` (`codomainFormationTyped`, under `context.cons D`), and `f`
    (`functionFormationTyped : f : piTyCodeCell D C`), BOTH the η-redex `etaLamSource f` AND its η-reduct `f`
    type (in the grown engine) at `piTyCodeCell D C`.  The reduct half is `ofFormation functionFormationTyped`.
    The redex half builds `λ. (weaken f @ var 0)` via `piIntro` over the formation-embedded domain/codomain, with
    the body `weaken f @ var 0` typed via `piElim`: `weaken f` is `f`'s typing weakened under the binder
    (`weakenUnderBinding` + `rename_piTyCodeCell`, both definitional), `var 0` types at `weaken D`
    (`HasTypeDesc.var`, classifier = `lookup_cons_zero` definitionally), and the application's result classifier
    `subst0 (rename (iterateLiftRaw weaken 1) C) newestVar` collapses to `C` by the η identity — exactly the
    codomain the `piIntro` binder body requires.

Scope: PRESERVATION for formation-component η-redexes, mirroring `betaCoherence_formationBody`'s scope.  The
fully-general inverted η subject reduction (arbitrary grown derivation, η-contracting under `conv`) additionally
needs grown-engine STRENGTHENING (the inverse of the shipped `weakenUnderBinding`), which does not yet exist; the
forward direction here needs none.  Genuinely non-vacuous — the η-redex actually η-reduces and the reduct
re-types at the identical Π classifier.

## Zero-axiom verification

The η identity: `subst0` def + `rename_subst_commute` + `subst_pointwise` (pointwise-identity, per-position
`rfl`) + `subst_identity_apply`.  The coherence: `weakenUnderBinding` + `rename_piTyCodeCell` (defeq) +
`HasTypeDesc.var` + `lookup_cons_zero` (defeq) + the η identity + `piIntro`/`piElim`/`ofFormation`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The η identity** (load-bearing substrate lemma).  Lifting a codomain past a fresh binder
(`rename (iterateLiftRaw weaken 1) codomain` — the shape `rename_piTyCodeCell` produces) then instantiating
de-Bruijn-0 with the newest variable returns the codomain unchanged.  The composite `subst`-after-`rename` is
pointwise the identity substitution.  This is the de Bruijn law that makes function η typecheck. -/
theorem RawTerm.subst0_iterateLiftWeaken_newestVar {scope : Nat} (codomain : RawTerm (scope + 1)) :
    RawTerm.subst0 (RawTerm.rename (iterateLiftRaw RawRenaming.weaken 1) codomain)
      RawTerm.newestVar = codomain := by
  dsimp only [RawTerm.subst0]
  rw [RawTerm.rename_subst_commute]
  have hpointwise :
      RawTerm.subst
          (RawRenaming.thenSubst (iterateLiftRaw RawRenaming.weaken 1)
            (RawTermSubst.singleton RawTerm.newestVar))
          codomain
        = RawTerm.subst RawTermSubst.identity codomain := by
    apply RawTerm.subst_pointwise
    intro position
    cases position with
    | mk positionValue positionBound =>
        cases positionValue with
        | zero => rfl
        | succ priorPosition => rfl
  rw [hpointwise, RawTerm.subst_identity_apply]

/-- **η-coherence for formation-component functions** (the η-twin of `betaCoherence_formationBody`).  From the
formation typings of the domain code `D`, the codomain code `C` (under `context.cons D`), and the function `f`
(at `piTyCodeCell D C`), BOTH the η-redex `etaLamSource f = λ. (weaken f @ var 0)` and its η-reduct `f` type in
the grown engine at the SAME `piTyCodeCell D C`.  Forward construction: the reduct is `ofFormation` of `f`'s
formation typing; the redex is `piIntro` over the formation-embedded `D`/`C` with the body `weaken f @ var 0`
typed by `piElim` (the weakened function via `weakenUnderBinding` + `rename_piTyCodeCell`, the newest variable
via `HasTypeDesc.var`, and the application's result classifier collapsed to `C` by the η identity). -/
theorem HasTypeDescPi.etaCoherence_formationFunction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (domainFormationTyped :
      HasTypeDesc profile context domainCode (universeCodeCell domainLevel flag))
    (codomainFormationTyped :
      HasTypeDesc profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (functionFormationTyped :
      HasTypeDesc profile context functionTerm (piTyCodeCell domainCode codomainCode)) :
    HasTypeDescPi profile context (RawTerm.etaLamSource domainCode functionTerm)
        (piTyCodeCell domainCode codomainCode)
      ∧ HasTypeDescPi profile context functionTerm (piTyCodeCell domainCode codomainCode) := by
  refine ⟨?_, HasTypeDescPi.ofFormation functionFormationTyped⟩
  have functionWeakened :
      HasTypeDesc profile (context.cons domainCode)
        (RawTerm.rename RawRenaming.weaken functionTerm)
        (piTyCodeCell (RawTerm.rename RawRenaming.weaken domainCode)
          (RawTerm.rename (iterateLiftRaw RawRenaming.weaken 1) codomainCode)) := by
    have hWeak := HasTypeDesc.weakenUnderBinding domainCode functionFormationTyped
    rw [rename_piTyCodeCell] at hWeak
    exact hWeak
  have newestVarTyped :
      HasTypeDesc profile (context.cons domainCode) RawTerm.newestVar
        (RawTerm.rename RawRenaming.weaken domainCode) :=
    HasTypeDesc.var (context.cons domainCode) ⟨0, Nat.zero_lt_succ scope⟩
  have bodyTyped :
      HasTypeDescPi profile (context.cons domainCode)
        (appCell (RawTerm.rename RawRenaming.weaken functionTerm) RawTerm.newestVar) codomainCode := by
    have hElim := HasTypeDescPi.piElim (HasTypeDescPi.ofFormation functionWeakened)
      (HasTypeDescPi.ofFormation newestVarTyped)
    rw [RawTerm.subst0_iterateLiftWeaken_newestVar] at hElim
    exact hElim
  exact HasTypeDescPi.piIntro domainLevel codomainLevel flag
    (HasTypeDescPi.ofFormation domainFormationTyped)
    (HasTypeDescPi.ofFormation codomainFormationTyped)
    bodyTyped

end FX1Poly.Typed
