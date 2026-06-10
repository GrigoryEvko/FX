import FX1Poly.Typed.DenoteKeyedAbstractionMember
import FX1Poly.Core.RawTermSubstConsCommute

/-! # FX1Poly/Typed/DenoteKeyedAbstractionUnderSubst
    — the denote fundamental theorem's Π-INTRODUCTION (λ) member arm under a closing substitution (SN-D3)

The FT-shaped (under closing substitution) twin of `abstractionMemberAtDenote` (SN-D2), the introduction
counterpart of the shipped `applicationMemberUnderClosingSubstitution` and `piFormationUnderClosingSubstitution`.
Given a closing substitution `substitution`, the substituted `λ body` is a denote-reducible MEMBER of the
substituted `Π domainCode codomainCode`.

It composes `abstractionMemberAtDenote` with the binder-split keystone, no new induction:
  * `subst` distributes over the Π cell and the λ cell DEFINITIONALLY: `subst σ (Π A B) = Π (subst σ A)
    (subst (lift σ) B)` and `subst σ (λ body) = λ (subst (lift σ) body)` — both children that cross the binder
    carry a shift of 1, so they get `lift σ` (established by `show` to the distributed form);
  * the codomain and body premises arrive in the FT IH shape (closed by `cons argument substitution`, the way
    the codomain/body induction hypotheses deliver them) and are bridged to the `subst0 … (lift σ)` shape
    `abstractionMemberAtDenote` consumes by `RawTerm.subst_cons_eq_subst0_lift`
    (`subst (cons argument σ) t = subst0 (subst (lift σ) t) argument`), applied once to `codomainCode` and once
    to `body`.

This is the candidate-explicit under-substitution port of SN-D2; the domain/codomain candidates are supplied by
the caller (the fundamental theorem, SN-D5, extracts them choice-free via the canonical member-predicate
engine).  `domainArgumentsSN` (domain CR1) stays an explicit premise, deferring bounded denote CR1 to BRICK 5.

## Zero-axiom verification

`show` to the distributed Π/λ form (definitional), then a single `abstractionMemberAtDenote` with the
`codomainCandidate` pinned explicitly (it is existentially packaged in the conclusion so the elaborator cannot
infer it from the goal) and the two per-argument premises rewritten by `RawTerm.subst_cons_eq_subst0_lift` (a
substitution-pointwise equality — no `funext`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The denote Π-introduction (λ) member arm under a closing substitution (the fundamental-theorem shape).**
From the substituted domain reducible with candidate `domainCandidate`, the codomain reducible under the
`cons`-extended substitution per reducible argument (the codomain IH), the domain candidate's members SN
(domain CR1, explicit — discharged by the FT at the ambient classifier level), and each body instance under the
`cons`-extended substitution in the codomain candidate (the body IH), the substituted `λ body` is a
denote-reducible member of the substituted `Π domainCode codomainCode`.  `subst` distributes over Π/λ
definitionally; the two IH-shaped premises bridge to `abstractionMemberAtDenote`'s `subst0 … (lift σ)` shape via
`RawTerm.subst_cons_eq_subst0_lift`. -/
theorem abstractionMemberUnderClosingSubstitution {scope targetScope : Nat} (env : Nat → Nat) (level : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {body : RawTerm (scope + 1)} {substitution : RawTermSubst scope targetScope}
    {domainCandidate : RawTerm targetScope → Prop}
    {codomainCandidate : RawTerm targetScope → (RawTerm targetScope → Prop)}
    (domainReducible :
      ReducibleTypeAtDenote env level (RawTerm.subst substitution domainCode) domainCandidate)
    (domainAnnSN : IsStronglyNormalizing (RawTerm.subst substitution domainCode))
    (codomainReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      ReducibleTypeAtDenote env level
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode)
        (codomainCandidate argument))
    (domainArgumentsSN : ∀ argument : RawTerm targetScope, domainCandidate argument →
      IsStronglyNormalizing argument)
    (bodyReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      codomainCandidate argument
        (RawTerm.subst (RawTermSubst.cons argument substitution) body)) :
    IsReducibleMemberAtDenote env level
      (RawTerm.subst substitution
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
      (RawTerm.subst substitution
        (.mkGen .gen_lam () (.childCons domainCode (.childCons body .childNil)))) := by
  show IsReducibleMemberAtDenote env level
    (.mkGen .gen_piTyCode ()
      (.childCons (RawTerm.subst substitution domainCode)
        (.childCons (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) .childNil)))
    (.mkGen .gen_lam ()
      (.childCons (RawTerm.subst substitution domainCode)
        (.childCons (RawTerm.subst (RawTermSubst.lift substitution) body) .childNil)))
  refine abstractionMemberAtDenote (codomainCandidate := codomainCandidate) env level
    domainReducible domainAnnSN
    (fun argument argumentInDomain => ?_) domainArgumentsSN
    (fun argument argumentInDomain => ?_)
  · rw [← RawTerm.subst_cons_eq_subst0_lift codomainCode argument substitution]
    exact codomainReducible argument argumentInDomain
  · rw [← RawTerm.subst_cons_eq_subst0_lift body argument substitution]
    exact bodyReducible argument argumentInDomain

end FX1Poly.Typed
