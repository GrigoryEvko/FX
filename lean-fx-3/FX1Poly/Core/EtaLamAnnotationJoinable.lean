import FX1Poly.Core.StepStarConfluence

/-! # FX1Poly/Core/EtaLamAnnotationJoinable
    — the weakened Nederpelt guard: annotation JOINABILITY at a lambda eta root.

`EtaLamAnnotationJoinable domainAnn innerFunction` says: IF the eta-expanded inner function is
itself an annotated lambda, its domain annotation joins the eta binder's annotation
`domainAnn` at a common beta+iota reduct (`StepStar.Join`, the bespoke β/ι reflexive-transitive
join).  Strictly weaker than the syntactic EQUALITY guard `EtaLamAnnotationDiagonal`, and
exactly what typing supplies — typed eta sources have CONVERTIBLE annotations and `Conv` IS
`StepStar.Join`.

It is a pure β/ι (`StepStar.Join`) + term-shape predicate — it mentions no eta relation.  It
previously lived inside the bespoke `Step.eta` joinable-confluence cluster
(`StepBetaEtaJoinableConfluence`); it is relocated here to a bespoke-`Step.eta`-free home so the
native table beta-eta confluence (the canonical `StepTableBetaEtaRoot` Church-Rosser) and its
typed annotation-joinability extraction can consume it without importing — and thus keeping
alive — the bespoke cluster.

## Zero-axiom verification

A plain `Prop`-valued definition over `StepStar.Join`; no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditCoreTerminationOrders.lean`. -/

namespace FX1Poly.Core

namespace BetaEtaPairJoin

/-- **The weakened Nederpelt guard: annotation JOINABILITY.**  IF the eta-expanded function is
itself an annotated lambda, its annotation joins the eta binder's annotation at a common
beta+iota reduct.  Strictly weaker than `EtaLamAnnotationDiagonal` (equality), and exactly
what typing supplies — typed eta sources have CONVERTIBLE annotations, and `Conv` IS
`StepStar.Join`. -/
def EtaLamAnnotationJoinable {scope : Nat}
    (domainAnn innerFunction : RawTerm scope) : Prop :=
  ∀ (innerDomainAnn : RawTerm scope) (innerBody : RawTerm (scope + 1)),
    innerFunction =
      .mkGen .gen_lam ()
        (.childCons innerDomainAnn (.childCons innerBody .childNil)) →
    StepStar.Join innerDomainAnn domainAnn

end BetaEtaPairJoin

end FX1Poly.Core
