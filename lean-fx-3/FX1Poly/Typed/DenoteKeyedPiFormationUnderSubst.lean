import FX1Poly.Typed.DenoteKeyedPiFormationFromExistence
import FX1Poly.Core.RawTermSubstConsCommute

/-! # FX1Poly/Typed/DenoteKeyedPiFormationUnderSubst
    — the denote fundamental theorem's Π-FORMATION arm under a closing substitution (denote #493)

The first genuine fundamental-theorem binder arm over the denote relation: given a closing substitution
`substitution`, the substituted DOMAIN reducible-with-a-uniform-candidate at every level, and the CODOMAIN
reducible-at-all-levels under the `cons`-extended substitution (the shape the FT's codomain induction
hypothesis delivers — it closes the codomain by `cons argument substitution`), the substituted Π code
`subst substitution (Π domainCode codomainCode)` is denote-reducible at every level.

It composes two shipped pieces with no new induction:
  * `subst` distributes over the Π cell DEFINITIONALLY (`subst σ (Π A B) = Π (subst σ A) (subst (lift σ) B)`,
    by `rfl` — the second child carries a binder shift of 1, so it gets `lift σ`), reducing the goal to the
    distributed form;
  * `uniformDomainPi_reducibleFromCodomainExistence` discharges the distributed Π from the domain candidate +
    codomain existence, with the per-argument codomain obligation `subst0 (subst (lift σ) codomainCode)
    argument` rewritten to the IH's `subst (cons argument substitution) codomainCode` via the binder-split
    keystone `RawTerm.subst_cons_eq_subst0_lift`.

The denote analogue of the fuel `FundamentalWithTypeValueCandidates` Π-formation arm (#493), but choice-free
and at the denote relation — the codomain candidate is the canonical member-predicate (inside
`uniformDomainPi_reducibleFromCodomainExistence`), never a `Classical.choice` selection.  This arm consumes a
domain with a UNIFORM candidate (neutral / type-variable domains — the common FT case); the universe-domain
binder arm routes through `universeDomainPi_reducibleFromCodomainExistence` instead.

## Zero-axiom verification

`show` to the distributed Π form (definitional), then a single application of
`uniformDomainPi_reducibleFromCodomainExistence` with the codomain premise rewritten by
`RawTerm.subst_cons_eq_subst0_lift` (a substitution-pointwise equality, no `funext`/`Quot.sound`).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The denote Π-formation fundamental-theorem arm under a closing substitution.**  From a uniform domain
candidate for `subst substitution domainCode` (at every level) and the codomain reducible-at-all-levels under
the `cons`-extended substitution, the substituted Π code is denote-reducible at every level.  The codomain
IH-shape `subst (cons argument substitution) codomainCode` is bridged to the from-existence arm's
`subst0 (subst (lift substitution) codomainCode) argument` by `RawTerm.subst_cons_eq_subst0_lift`. -/
theorem piFormationUnderClosingSubstitution {scope targetScope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {substitution : RawTermSubst scope targetScope}
    (domainCandidate : RawTerm targetScope → Prop)
    (domainReducible : ∀ level : Nat,
      ReducibleTypeAtDenote env level (RawTerm.subst substitution domainCode) domainCandidate)
    (codomainReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      IsReducibleTypeAtAllDenoteLevels env
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode)) :
    IsReducibleTypeAtAllDenoteLevels env
      (RawTerm.subst substitution
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))) := by
  show IsReducibleTypeAtAllDenoteLevels env
    (.mkGen .gen_piTyCode ()
      (.childCons (RawTerm.subst substitution domainCode)
        (.childCons (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) .childNil)))
  refine uniformDomainPi_reducibleFromCodomainExistence env domainCandidate domainReducible
    (fun argument argumentInDomain => ?_)
  rw [← RawTerm.subst_cons_eq_subst0_lift codomainCode argument substitution]
  exact codomainReducible argument argumentInDomain

/-- **The denote universe-domain Π-formation fundamental-theorem arm under a closing substitution (the
impredicative twin).**  For an impredicative-polymorphic Π whose domain is a closed universe code
`Type@levelExpr`, the substituted Π code `subst substitution (Π (Type@levelExpr) codomainCode)` is
denote-reducible at every level given the codomain reducible-at-all-levels under the `cons`-extended
substitution for every universe member.  The domain is closed (`childNil`), so `subst substitution` leaves it
fixed and the Π distribution lands the codomain under `lift substitution` definitionally; the arm routes
through `universeDomainPi_reducibleFromCodomainExistence` (threshold-split inside), the codomain IH bridged by
`RawTerm.subst_cons_eq_subst0_lift`.  Completes the binder-arm-under-substitution family across all domain
shapes (uniform / neutral / universe). -/
theorem universeDomainPiFormationUnderClosingSubstitution {scope targetScope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) {codomainCode : RawTerm (scope + 1)}
    {substitution : RawTermSubst scope targetScope}
    (codomainReducible : ∀ argument : RawTerm targetScope,
      (IsStronglyNormalizing argument ∧
        IsReducibleTypeAtDenote env (LevelExpr.denote levelExpr env) argument) →
      IsReducibleTypeAtAllDenoteLevels env
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode)) :
    IsReducibleTypeAtAllDenoteLevels env
      (RawTerm.subst substitution
        (.mkGen .gen_piTyCode ()
          (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
            (.childCons codomainCode .childNil)))) := by
  show IsReducibleTypeAtAllDenoteLevels env
    (.mkGen .gen_piTyCode ()
      (.childCons (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
        (.childCons (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) .childNil)))
  refine universeDomainPi_reducibleFromCodomainExistence env levelExpr flag
    (fun argument argumentInUniverse => ?_)
  rw [← RawTerm.subst_cons_eq_subst0_lift codomainCode argument substitution]
  exact codomainReducible argument argumentInUniverse

end FX1Poly.Typed
