import LeanFX2.Term
import LeanFX2.Term.Rename
import LeanFX2.Term.Subst
import LeanFX2.Term.SubstHet
import LeanFX2.Term.Pointwise
import LeanFX2.Algo.Eval
import LeanFX2.Algo.WHNF
import LeanFX2.Algo.Soundness
import LeanFX2.Reduction.Cumul
import LeanFX2.Reduction.CumulSubstCompat
import LeanFX2.Reduction.ParRed
import LeanFX2.Bridge

/-! # Smoke/AuditPhase12AB85b — heterogeneous-carrier uaIntroHet audit.

Phase 12.A.B8.5b (heterogeneous Univalence prerequisite, second half).
Adds `Term.uaIntroHet` — the heterogeneous-carrier path-from-equivalence
ctor at type `Ty.id (Ty.universe innerLevel ...) carrierARaw carrierBRaw`,
packaging an arbitrary `equivWitness : Term context (Ty.equiv carrierA
carrierB) (RawTerm.equivIntro forwardRaw backwardRaw)`.  Generalizes
`Term.equivReflIdAtId` (rfl-fragment / homogeneous carriers only) so
the future `Step.eqTypeHet` reduction (heterogeneous Univalence) can
fire from arbitrary equivalences between distinct type-codes.

## Architectural raw-alignment trick

`Term.uaIntroHet`'s raw projection is the SAME as its packaged
`equivWitness`'s raw — `RawTerm.equivIntro forwardRaw backwardRaw` —
exactly mirroring how `Term.equivReflIdAtId` shares its raw with
`Term.equivReflId`.  This pre-aligns the source/target raws for a
future `Step.eqTypeHet` rule so that `Step.par.toRawBridge` collapses
to `RawStep.par.refl _` (same architectural payoff as `cumulUpInner`,
`eqType`, `eqArrow`).

For the IMMEDIATE `Step.par.uaIntroHetCong` cong rule, source and
target raws DO differ (they package different equivWitness raws), so
the bridge collapses to the equivWitness's IH directly — which IS a
raw-level parallel step from `RawTerm.equivIntro forwardRawSource
backwardRawSource` to `RawTerm.equivIntro forwardRawTarget
backwardRawTarget`.  No `RawStep.par.uaIntroCong` ctor needed — we
reuse the equivWitness's raw step via the IH.

## Cascade summary

11 files extended, 1 new audit file.  All zero-axiom under strict
policy.  Audit gates:

* **Term ctor (Layer 1):**
  - `Term.uaIntroHet` — heterogeneous-carrier path-from-equivalence

* **Term cascade (Layer 1):**
  - `Term.rename` — recursion arm
  - `Term.subst` — recursion arm
  - `Term.substHet` — recursion arm (uses `Nat.le_trans` for level
    cumulativity, mirror of `equivReflIdAtId` substHet arm)
  - `Term.subst_pointwise` — recursion arm

* **Algo cascade (Layer 9):**
  - `Term.headStep?` — value (returns `none`)
  - `Term.HeadCtor` — enum entry
  - `Term.headCtor` — projection arm
  - `Term.isWHNF` — value (returns `true`)
  - `Term.headStep?_sound` + 5 inversion-lemma branches in WHNF.lean
    (11 nomatch arms total: 5 inversion lemmas plus payload-existence
    cascade)

* **Reduction cascade (Layer 2):**
  - `Step.par.uaIntroHetCong` — single-subterm parallel-cong rule

* **Confluence cascade (Layer 4 bridge):**
  - `Step.par.toRawBridge` arm — collapses to the equivWitness IH
    (the source/target raws are exactly the equivWitness's raws)

* **Cumul cascade (Layer 2):**
  - `ConvCumul.uaIntroHetCong` — single-subterm cong rule
  - `ConvCumul.subst_compatible_uaIntroHet_allais` — Allais arm
  - `ConvCumul.subst_compatible_paired_allais` dispatch arm

## What this audit establishes

`#print axioms` over EVERY new declaration reports:

```
'<DeclName>' does not depend on any axioms
```

No `propext`, no `Quot.sound`, no `Classical.choice`, no user-declared
axiom.  Build remains GREEN at all 300 prior jobs PLUS new audit job.

## Honest scope

`Term.uaIntroHet` is the SHAPE — it carries an arbitrary equivWitness
but does NOT yet enforce that the equivalence is "actually" the path
proof at the universe (that's the future `Step.eqTypeHet` rule, to be
added once heterogeneous Univalence reduction is wired in).  The
structural cascade (rename / subst / substHet / pointwise / Algo /
Reduction / Confluence / Cumul) is complete and zero-axiom.

This unblocks the SECOND half of heterogeneous Univalence.  Combined
with `Term.equivIntroHet` (Phase 12.A.B8.5), the kernel can now host:

* heterogeneous-carrier equivalence values (`equivIntroHet` —
  Phase 12.A.B8.5)
* heterogeneous-carrier path-from-equivalence values (`uaIntroHet` —
  this phase, B8.5b)

The remaining work for full heterogeneous Univalence is the
`Step.eqTypeHet` reduction rule:

```
| eqTypeHet : Step (Term.uaIntroHet ... equivWitness)
                   (Term.equivIntroHet forward backward)
```

deferred to a future phase. -/

namespace LeanFX2

/-! ## §1. The Term constructor itself. -/

#print axioms Term.uaIntroHet

/-! ## §2. Term cascade — rename / subst / substHet / pointwise. -/

#print axioms Term.rename
#print axioms Term.subst
#print axioms Term.substHet
#print axioms Term.subst_pointwise

/-! ## §3. Algo cascade — Eval, WHNF, Soundness. -/

#print axioms Term.headStep?
#print axioms Term.HeadCtor
#print axioms Term.headCtor
#print axioms Term.isWHNF
#print axioms Term.headStep?_sound

/-! ## §4. Reduction cascade — Step.par cong rule. -/

#print axioms Step.par.uaIntroHetCong

/-! ## §5. Bridge cascade — typed→raw projection. -/

#print axioms Step.par.toRawBridge

/-! ## §6. Cumul cascade — ConvCumul cong + Allais arm + dispatch. -/

#print axioms ConvCumul.uaIntroHetCong
#print axioms ConvCumul.subst_compatible_uaIntroHet_allais
#print axioms ConvCumul.subst_compatible_paired_allais

end LeanFX2
