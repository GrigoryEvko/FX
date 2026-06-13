import FX1Poly.Core.WeakHeadStepCommute

/-! # FX1Poly/Core/StepLamDomainCong
    — replay a beta+iota reduction chain through a lambda's domain annotation.

`StepStar.lamDomainCong` lifts a `StepStar` (beta+iota) chain on a lambda's DOMAIN
annotation up through the `gen_lam` cell, leaving the body fixed — the one-hole-context
instance of `StepStar.congAt` at the `gen_lam` head child (shift `0`, rest shifts `[1]`).

It is a pure `Step` / `StepStar` congruence fact — it mentions no eta relation at all.
It previously lived inside the bespoke `Step.eta` confluence cluster
(`StepBetaEtaJoinableConfluence`); it is relocated here to a bespoke-`Step.eta`-free home
so the native table beta-eta confluence (the canonical `StepTableBetaEtaRoot` Church-Rosser)
can consume it without importing — and thus without keeping alive — the bespoke cluster.

The annotation-replay is exactly what the eta-lambda-versus-beta critical pair needs: when
the inner beta fires under an eta-expanded lambda, the two reducts `lam A b` and `lam B b`
join at `lam C b` by replaying the convertible annotations `A ↝* C ↜* B` through THIS
congruence (root-only eta chains would not lift into the domain child — beta+iota chains do).

## Zero-axiom verification

A single `StepStar.congAt` instance; no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCoreTerminationOrders.lean`. -/

namespace FX1Poly.Core

/-- Replay a beta+iota `StepStar` chain on a lambda's domain annotation through the lambda
cell (body fixed) — the one-hole-context instance of `StepStar.congAt` at the `gen_lam` head
child (shift `0`, rest shifts `[1]`). -/
theorem StepStar.lamDomainCong {scope : Nat} (body : RawTerm (scope + 1))
    {domainStart domainEnd : RawTerm scope}
    (annotationChain : StepStar domainStart domainEnd) :
    StepStar
      (RawTerm.mkGen .gen_lam ()
        (.childCons domainStart (.childCons body .childNil)))
      (RawTerm.mkGen .gen_lam ()
        (.childCons domainEnd (.childCons body .childNil))) :=
  StepStar.congAt
    (fun annotation =>
      RawTerm.mkGen .gen_lam () (.childCons annotation (.childCons body .childNil)))
    (fun annotationStep =>
      Step.cong .gen_lam ()
        (StepChildren.here (parentScope := scope) (headShift := 0) (restShifts := [1])
          (.childCons body .childNil) annotationStep))
    annotationChain

end FX1Poly.Core
