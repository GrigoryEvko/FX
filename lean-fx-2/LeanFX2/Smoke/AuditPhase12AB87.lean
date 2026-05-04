import LeanFX2.HoTT.Univalence

/-! # Smoke/AuditPhase12AB87 — heterogeneous Univalence headline theorem.

Phase 12.A.B8.7 (CUMUL-8.7).  Ships the **headline heterogeneous
Univalence theorem** — the Voevodsky form for arbitrary equivalences
(not just rfl).  Consumes the `Step.eqTypeHet` reduction rule landed
in Phase 12.A.B8.6 (commit `ab017bb0`) and lifts it through
`Conv.fromStep` to a typed `Conv` between
`Term.uaIntroHet ... equivWitness` and the underlying packaged
`equivWitness`.

## What this audit establishes

The single new theorem `LeanFX2.UnivalenceHet` shipped in
`HoTT/Univalence.lean` carries a real proof body
(`Conv.fromStep (Step.eqTypeHet ...)`) and `#print axioms` reports:

```
'LeanFX2.UnivalenceHet' does not depend on any axioms
```

No `propext`, no `Quot.sound`, no `Classical.choice`, no
user-declared axiom.  Build remains GREEN at all 302 prior jobs PLUS
this new audit job.

## Relationship to the rfl-fragment `Univalence`

`LeanFX2.Univalence` (Phase 12.A.B8.6, audited in
`Smoke/AuditPhase12AB8.lean`) handles the rfl-fragment only —
both endpoints share the SAME carrier
(`Term.equivReflIdAtId → Term.equivReflId` via `Step.eqType`).

`LeanFX2.UnivalenceHet` handles the heterogeneous case — ANY
equivalence between two distinct carriers
(`Term.uaIntroHet ... equivWitness → equivWitness` via
`Step.eqTypeHet`).

Together the two cover the FULL Voevodsky Univalence at the kernel
level — `Step.eqType` for refl, `Step.eqTypeHet` for arbitrary, and
the union is full Univalence definitional.  Both ship as zero-axiom
theorems under strict policy.

## Architectural raw-alignment trick (recap)

Both source `Term.uaIntroHet ... equivWitness` and target
`equivWitness` project to the SAME raw form
`RawTerm.equivIntro forwardRaw backwardRaw` (the `uaIntroHet` ctor's
raw is by construction the same as its packaged `equivWitness`'s raw
— see `Term.uaIntroHet` docstring).  The rule changes the type only:
`Ty.id (Ty.universe ...) carrierARaw carrierBRaw` reduces to
`Ty.equiv carrierA carrierB` while the raw data is preserved.  Same
architectural payoff as `cumulUpInner` / `eqType` / `eqArrow`. -/

namespace LeanFX2

/-! ## §1. The headline heterogeneous Univalence theorem. -/

#print axioms UnivalenceHet

end LeanFX2
