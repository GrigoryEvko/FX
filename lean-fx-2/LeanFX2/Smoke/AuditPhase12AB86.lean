import LeanFX2.Term
import LeanFX2.Reduction.Step
import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.Cumul
import LeanFX2.Reduction.ConvBridge
import LeanFX2.Bridge

/-! # Smoke/AuditPhase12AB86 — heterogeneous Univalence reduction.

Phase 12.A.B8.6 (heterogeneous Univalence reduction).  Adds the
`Step.eqTypeHet` reduction rule that makes heterogeneous Univalence
DEFINITIONAL: the canonical heterogeneous-carrier path-from-equivalence
proof at the universe (`Term.uaIntroHet ... equivWitness`) reduces in
one step to the underlying packaged equivalence (`equivWitness`).

Builds on Phase 12.A.B8.5 (`Term.equivIntroHet`) and Phase 12.A.B8.5b
(`Term.uaIntroHet`).  Together with `Step.eqType` (rfl-fragment, B8.1)
and `Step.eqArrow` (funext rfl-fragment, B8.2), the kernel now hosts
the full heterogeneous Univalence schema as a definitional reduction.

## Architectural raw-alignment trick

Both source `Term.uaIntroHet (context := context) innerLevel
innerLevelLt carrierARaw carrierBRaw equivWitness` and target
`equivWitness` project to the SAME raw form
`RawTerm.equivIntro forwardRaw backwardRaw` (the `uaIntroHet` ctor's
raw is by construction the same as its packaged equivWitness's raw —
see `Term.uaIntroHet` docstring).  The `Step.par.toRawBridge` arm
therefore collapses to `RawStep.par.refl _` — no new
`RawStep.par.eqTypeHet` ctor is needed at the raw level, raw
confluence inherits the rule for free.  Same architectural payoff as
`cumulUpInnerCong` / `eqType` / `eqArrow`.

## Cascade summary

5 files extended, 1 new audit file.  All zero-axiom under strict
policy.  Audit gates:

* **Reduction (Layer 2):**
  - `Step.eqTypeHet` — the headline reduction rule
  - `Step.par.eqTypeHet` — parallel-reduction analog
  - `Step.toPar` — extended with the eqTypeHet arm

* **Bridge (Layer 4):**
  - `Step.par.toRawBridge` — extended with the eqTypeHet arm
    (collapses to `RawStep.par.refl _` via raw alignment)

* **Cumul (Layer 2):**
  - `ConvCumul.iotaEqTypeHetCumul` — ConvCumul lift for eqTypeHet,
    mirror of `iotaEqTypeCumul` / `iotaEqArrowCumul`
  - `Step.toConvCumul` — extended with the eqTypeHet arm

## What this audit establishes

`#print axioms` over EVERY new declaration reports:

```
'<DeclName>' does not depend on any axioms
```

No `propext`, no `Quot.sound`, no `Classical.choice`, no user-declared
axiom.  Build remains GREEN at all 301 prior jobs PLUS this new audit
job.

## Univalence-as-theorem (now fully heterogeneous)

The downstream theorem

```lean
theorem UnivalenceHet
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    (equivWitness : Term context (Ty.equiv carrierA carrierB)
                                 (RawTerm.equivIntro forwardRaw backwardRaw)) :
    Conv (Term.uaIntroHet (context := context)
                          innerLevel innerLevelLt
                          carrierARaw carrierBRaw equivWitness)
         equivWitness :=
  Conv.fromStep (Step.eqTypeHet innerLevel innerLevelLt
                                carrierARaw carrierBRaw equivWitness)
```

is `Conv.fromStep Step.eqTypeHet` — zero axioms — exactly as the
rfl-fragment Univalence theorem is `Conv.fromStep Step.eqType`.  The
theorem itself is shipped in `HoTT/Univalence.lean` (or its successor)
once the headline-theorem layer is wired to consume `Step.eqTypeHet`. -/

namespace LeanFX2

/-! ## §1. The Step constructor itself. -/

#print axioms Step.eqTypeHet

/-! ## §2. Parallel-reduction lift. -/

#print axioms Step.par.eqTypeHet

/-! ## §3. Step → Par lift (extended with the new arm). -/

#print axioms Step.toPar

/-! ## §4. Bridge cascade — typed→raw projection (extended). -/

#print axioms Step.par.toRawBridge

/-! ## §5. ConvCumul cascade — ConvCumul ctor + Step→ConvCumul lift. -/

#print axioms ConvCumul.iotaEqTypeHetCumul
#print axioms Step.toConvCumul

end LeanFX2
