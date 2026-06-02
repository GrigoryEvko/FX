import FX1Poly.Typed.AbstractionNonDependentUnderSubstLevelFree
import FX1Poly.Typed.SimplyTypedTypeExprReducibleLevelFree
import FX1Poly.Typed.ReducibleEnv
import FX1Poly.Core.SubstPreservationProbes

/-! # FX1Poly/Typed/SimplyTypedTermFundamentalLevelFree
    — the LEVEL-FREE simply-typed term fundamental theorem (and its strong-normalization corollary)

The capstone of the level-free simply-typed line: a term judgment + the Girard-Tait fundamental theorem +
strong normalization for closed simply-typed terms.  This is the wall-free analogue, for the simply-typed
fragment, of the dependent fundamental theorem (which is blocked at the universe-domain wall): it closes
because the lambda binder extends the level-free `ReducibleEnv` from a SINGLE member (no all-levels universe
wall — see `AbstractionNonDependentUnderSubstLevelFree`), and the domain types are directly reducible (no
type-variable leaves — see `SimplyTypedTypeExprReducibleLevelFree`).

`SimplyTypedTermLF` is the well-scoped simply-typed term judgment over a context: variable, application
(non-dependent — the function's arrow codomain IS the result type), and lambda (whose domain and codomain
are directly-reducible type expressions, `IsReducibleTypeExprLF`).

`SimplyTypedTermLF.reducibleUnderSubst` is the fundamental theorem: every such term, closed by a reducible
substitution, is a reducible member of its closed type.  The three arms dispatch to the assembled keystones:

  * `var` — `RawTerm.subst_var_reduces` + `ReducibleEnv.lookupReducible` (the looked-up reducible member).
  * `app` — `IsReducibleMember.applicationUnderSubst` (piElim) on the two induction hypotheses; the
    non-dependent output classifier `subst σ (subst0 (weaken codomainBase) argument)` collapses to
    `subst σ codomainBase` (`RawTerm.weaken_subst_singleton`).
  * `lam` — `IsReducibleMember.abstractionNonDependentUnderSubst` (piIntro): domain reducibility +
    CR1-SN from `IsReducibleTypeExprLF.reducibleUnderSubst`, codomain reducibility likewise, and the body
    membership from the induction hypothesis at the `ReducibleEnv.cons`-extended environment, reshaped by
    `RawTerm.weaken_subst_cons` (codomain) and `RawTerm.subst_cons_eq_subst0_lift` (body).

The target scope is `targetScope + 1` so the arrow CR1 (`IsReducibleMember.stronglyNormalizing`) has a fresh
variable — the same convention as the stratified `fundamentalPiIntroNonDependentAtAll`.

`stronglyNormalizingUnderSubst`, `reducibleClosed`, and `stronglyNormalizingClosed` are the corollaries: the
membership feeds CR1 to give STRONG NORMALIZATION of every closed simply-typed term (the tangible payoff —
SN-for-well-typed restricted to the simply-typed fragment, wall-free).

## Zero-axiom verification

`induction` on the term judgment with the three dispatches above; the corollaries are `IsReducibleMember`
projections (`.stronglyNormalizing`) at the empty environment (`ReducibleEnv.empty`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **A level-free simply-typed term over a context** (well-scoped var / app / lambda).  The lambda's domain
and codomain are directly-reducible type expressions (`IsReducibleTypeExprLF`); application is non-dependent
(the function's arrow codomain is the result type). -/
inductive SimplyTypedTermLF {profile : PolyProfile} :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop
  | var {scope : Nat} {context : TypingContext profile scope} (index : Fin scope) :
      SimplyTypedTermLF context (variableCell index) (context.lookup index)
  | app {scope : Nat} {context : TypingContext profile scope}
      {functionTerm argument domainCode codomainBase : RawTerm scope}
      (functionTyped : SimplyTypedTermLF context functionTerm
        (piTyCodeCell domainCode (RawTerm.weaken codomainBase)))
      (argumentTyped : SimplyTypedTermLF context argument domainCode) :
      SimplyTypedTermLF context (appCell functionTerm argument) codomainBase
  | lam {scope : Nat} {context : TypingContext profile scope}
      {body : RawTerm (scope + 1)} {domainCode codomainBase : RawTerm scope}
      (domainExpr : IsReducibleTypeExprLF domainCode)
      (codomainExpr : IsReducibleTypeExprLF codomainBase)
      (bodyTyped : SimplyTypedTermLF (context.cons domainCode) body (RawTerm.weaken codomainBase)) :
      SimplyTypedTermLF context (lamCell body) (piTyCodeCell domainCode (RawTerm.weaken codomainBase))

/-- **The level-free simply-typed term fundamental theorem.**  Every simply-typed term, closed by a reducible
substitution, is a reducible member of its (closed) type.  The three arms dispatch `var` to
`ReducibleEnv.lookupReducible`, `app` to `IsReducibleMember.applicationUnderSubst` (codomain collapse via
`weaken_subst_singleton`), and `lam` to `IsReducibleMember.abstractionNonDependentUnderSubst` (domain/codomain
reducibility from `IsReducibleTypeExprLF.reducibleUnderSubst`, body IH at the `ReducibleEnv.cons`-extended
environment reshaped by `weaken_subst_cons` + `subst_cons_eq_subst0_lift`).  Target scope `targetScope + 1` so
the arrow CR1 has a fresh variable. -/
theorem SimplyTypedTermLF.reducibleUnderSubst {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {term type : RawTerm scope}
    (typed : SimplyTypedTermLF context term type) :
    ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
      ReducibleEnv context substitution →
      IsReducibleMember (RawTerm.subst substitution type) (RawTerm.subst substitution term) := by
  induction typed with
  | var index =>
      intro targetScope substitution env
      rw [show RawTerm.subst substitution (variableCell index) = substitution index
          from RawTerm.subst_var_reduces substitution index]
      exact env index
  | @app scope context functionTerm argument domainCode codomainBase
        _functionTyped _argumentTyped functionIH argumentIH =>
      intro targetScope substitution env
      have functionMember := functionIH substitution env
      have argumentMember := argumentIH substitution env
      have result := IsReducibleMember.applicationUnderSubst substitution functionMember argumentMember
      rw [show RawTerm.subst substitution (RawTerm.subst0 (RawTerm.weaken codomainBase) argument)
            = RawTerm.subst substitution codomainBase
          from congrArg (RawTerm.subst substitution)
            (RawTerm.weaken_subst_singleton codomainBase argument)] at result
      exact result
  | @lam scope context body domainCode codomainBase domainExpr codomainExpr _bodyTyped bodyIH =>
      intro targetScope substitution env
      obtain ⟨domainCandidate, domainReducible⟩ :=
        domainExpr.reducibleUnderSubst (substitution := substitution)
      exact IsReducibleMember.abstractionNonDependentUnderSubst substitution domainReducible
        (fun _argument argumentInDomain =>
          domainReducible.isReducibilityCandidate.stronglyNormalizing argumentInDomain)
        (codomainExpr.reducibleUnderSubst)
        (fun argument argumentInDomain => by
          have headReducible : IsReducibleMember (RawTerm.subst substitution domainCode) argument :=
            ⟨domainCandidate, domainReducible, argumentInDomain⟩
          have bodyMember := bodyIH (RawTermSubst.cons argument substitution)
            (ReducibleEnv.cons env headReducible)
          rw [show RawTerm.subst (RawTermSubst.cons argument substitution) (RawTerm.weaken codomainBase)
                = RawTerm.subst substitution codomainBase
              from RawTerm.weaken_subst_cons codomainBase argument substitution,
            RawTerm.subst_cons_eq_subst0_lift body argument substitution] at bodyMember
          exact bodyMember)

/-- **Strong normalization of simply-typed terms under a reducible substitution.**  CR1 applied to the
fundamental theorem: a simply-typed term closed by a reducible substitution strongly normalizes. -/
theorem SimplyTypedTermLF.stronglyNormalizingUnderSubst {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {term type : RawTerm scope}
    (typed : SimplyTypedTermLF context term type) {targetScope : Nat}
    (substitution : RawTermSubst scope (targetScope + 1))
    (envReducible : ReducibleEnv context substitution) :
    IsStronglyNormalizing (RawTerm.subst substitution term) :=
  (typed.reducibleUnderSubst substitution envReducible).stronglyNormalizing

/-- **Closed-term reducibility.**  A closed simply-typed term (empty context) is a reducible member of its
type under any substitution into a non-empty scope (the environment is vacuously reducible). -/
theorem SimplyTypedTermLF.reducibleClosed {profile : PolyProfile}
    {term type : RawTerm 0} (typed : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type)
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1)) :
    IsReducibleMember (RawTerm.subst substitution type) (RawTerm.subst substitution term) :=
  typed.reducibleUnderSubst substitution (ReducibleEnv.empty substitution)

/-- **Strong normalization of closed simply-typed terms.**  The tangible payoff: every closed simply-typed
term strongly normalizes — SN-for-well-typed restricted to the wall-free simply-typed fragment. -/
theorem SimplyTypedTermLF.stronglyNormalizingClosed {profile : PolyProfile}
    {term type : RawTerm 0} (typed : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type)
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1)) :
    IsStronglyNormalizing (RawTerm.subst substitution term) :=
  (typed.reducibleClosed substitution).stronglyNormalizing

end FX1Poly.Typed
