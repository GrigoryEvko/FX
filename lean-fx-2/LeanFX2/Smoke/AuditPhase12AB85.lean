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

/-! # Smoke/AuditPhase12AB85 — heterogeneous-carrier equivIntroHet audit.

Phase 12.A.B8.5 (heterogeneous Univalence prerequisite).  Adds
`Term.equivIntroHet` — the general heterogeneous-carrier equivalence
introduction at type `Ty.equiv carrierA carrierB` packaging forward +
backward functions plus left/right inverse proof functions.  Generalizes
`Term.equivReflId` (which only ships the rfl-fragment at homogeneous
carriers).

## Cascade summary

11 files extended, all zero-axiom.  Audit gates:

* **Term ctor (Layer 1):**
  - `Term.equivIntroHet` — heterogeneous-carrier equivalence intro

* **Term cascade (Layer 1):**
  - `Term.rename` — recursion arm
  - `Term.subst` — recursion arm
  - `Term.substHet` — recursion arm
  - `Term.subst_pointwise` — recursion arm

* **Algo cascade (Layer 9):**
  - `Term.headStep?` — value (returns `none`)
  - `Term.HeadCtor` — enum entry
  - `Term.headCtor` — projection arm
  - `Term.isWHNF` — value (returns `true`)
  - `Term.headStep?_sound` + 5 inversion-lemma branches in WHNF.lean

* **Reduction cascade (Layer 2):**
  - `Step.par.equivIntroHetCong` — two-subterm parallel-cong rule

* **Confluence cascade (Layer 4 bridge):**
  - `Step.par.toRawBridge` arm — collapses to `RawStep.par.equivIntroCong`

* **Cumul cascade (Layer 2):**
  - `ConvCumul.equivIntroHetCong` — two-subterm cong rule
  - `ConvCumul.subst_compatible_equivIntroHet_allais` — Allais arm
  - `ConvCumul.subst_compatible_paired_allais` dispatch arm

## What this audit establishes

`#print axioms` over EVERY new declaration reports:

```
'<DeclName>' does not depend on any axioms
```

No `propext`, no `Quot.sound`, no `Classical.choice`, no user-declared
axiom.  Build remains GREEN at all 299 prior jobs PLUS new jobs.

## Honest scope

`Term.equivIntroHet` now enforces the bi-inverse shape: a forward map,
a backward map, and proof functions for `backward (forward x) = x` and
`forward (backward y) = y`.  This still inherits the current `Ty.id`
raw-endpoint limitation, so the endpoint typing debt is tracked by the
separate Ty raw-endpoint gate.  The structural cascade (rename / subst /
substHet / pointwise / Algo / Reduction / Confluence / Cumul) is
complete and zero-axiom.

This unblocks heterogeneous Univalence: the cascade pieces needed to
extend `Step.eqType` to A ≠ B are now in place — the remaining work
is the general heterogeneous Step rule and the broader endpoint-typing
repair, deferred to a future phase. -/

namespace LeanFX2

/-! ## §1. The Term constructor itself. -/

#print axioms Term.equivIntroHet

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

#print axioms Step.par.equivIntroHetCong

/-! ## §5. Bridge cascade — typed→raw projection. -/

#print axioms Step.par.toRawBridge

/-! ## §6. Cumul cascade — ConvCumul cong + Allais arm. -/

#print axioms ConvCumul.equivIntroHetCong
#print axioms ConvCumul.subst_compatible_equivIntroHet_allais
#print axioms ConvCumul.subst_compatible_paired_allais

end LeanFX2
