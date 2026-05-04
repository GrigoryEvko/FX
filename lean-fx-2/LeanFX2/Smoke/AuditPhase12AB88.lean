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
import LeanFX2.HoTT.Univalence
import LeanFX2.HoTT.Funext

/-! # Smoke/AuditPhase12AB88 — heterogeneous-carrier funextIntroHet audit.

Phase 12.A.B8.8 (heterogeneous Funext prerequisite).  Adds
`Term.funextIntroHet` — the heterogeneous-carrier funext-introduction
ctor at type `Ty.id (Ty.arrow domainType codomainType) (RawTerm.lam
applyARaw) (RawTerm.lam applyBRaw)`, witnessing a path between two
DISTINCT lambda-shaped raw functions at an arrow type.  Generalizes
`Term.funextReflAtId` (rfl-fragment / single applyRaw, witnessing
`f = f`) to the heterogeneous case (two distinct apply-payloads
witnessing arbitrary `f = g`).

## Why funextIntroHet is a VALUE ctor (no typed subterms)

Unlike `uaIntroHet` (which packages a typed `equivWitness`
subterm), `funextIntroHet` carries only schematic data:
`domainType`, `codomainType`, `applyARaw`, `applyBRaw` — all
either `Ty` or `RawTerm` indices, no typed `Term` subterm.
This is the SAME architectural shape as `funextReflAtId` (which
also has no typed subterm) and PROPER VALUE ctors (`unit`,
`boolTrue`, ...).  Consequence: NO cong rules needed in
`ConvCumul` / `Step.par` (a la lines 217-218 of `Cumul.lean`:
"Pure-data ctors ... don't need cong — `ConvCumul.refl` covers
them").  NO arm needed in `Step.par.toRawBridge` (no new
`Step.par` ctor was added).  Only the substitution-compatibility
helper + dispatch arm in `CumulSubstCompat.lean` is required —
and it discharges via `ConvCumul.refl _`.

## Architectural raw-alignment trick

`Term.funextIntroHet`'s raw projection is `RawTerm.lam (RawTerm.refl
applyARaw)` — IDENTICAL to `Term.funextReflAtId domainType
codomainType applyARaw`'s raw.  This pre-aligns the source for a
future `Step.eqArrowHet` rule that will reduce
`Term.funextIntroHet ... applyARaw applyBRaw` to a
heterogeneous-funext witness, with `Step.par.toRawBridge`
collapsing to `RawStep.par.refl _` (same architectural payoff as
`Step.eqType` / `Step.eqArrow` / `Step.eqTypeHet`).

## Cascade summary

8 files extended, 1 new audit file.  All zero-axiom under strict
policy.  Audit gates:

* **Term ctor (Layer 1):**
  - `Term.funextIntroHet` — heterogeneous-carrier funext-introduction
    at Id-of-arrow

* **Term cascade (Layer 1):**
  - `Term.rename` — recursion arm
  - `Term.subst` — recursion arm
  - `Term.substHet` — recursion arm
  - `Term.subst_pointwise` — recursion arm (rfl: VALUE ctor, both
    sides definitionally identical given same `sigma`)

* **Algo cascade (Layer 9):**
  - `Term.headStep?` — value (returns `none`)
  - `Term.HeadCtor` — enum entry
  - `Term.headCtor` — projection arm
  - `Term.isWHNF` — value (returns `true`)
  - `Term.headStep?_sound` + 5 inversion-lemma branches in
    WHNF.lean (11 nomatch arms total: 5 inversion lemmas plus
    payload-existence cascade)

* **Cumul cascade (Layer 2):**
  - `ConvCumul.subst_compatible_funextIntroHet_allais` — Allais
    arm (VALUE ctor: discharges via `ConvCumul.refl _`)
  - `ConvCumul.subst_compatible_paired_allais` dispatch arm
    (delegates to the helper above)

* **Reduction / Confluence:** NO new arms.  No new `Step.par`
  ctor (no typed subterm to recurse on).  No new `ConvCumul`
  cong rule (`ConvCumul.refl` covers the VALUE-ctor case via
  the dispatch arm in `CumulSubstCompat.lean`).  No new
  `Step.par.toRawBridge` arm.  Phase 4 base infrastructure
  (Cd / CdLemma / Diamond / ChurchRosser / CanonicalForm)
  cascades transparently.

## What this audit establishes

`#print axioms` over EVERY new declaration reports:

```
'<DeclName>' does not depend on any axioms
```

No `propext`, no `Quot.sound`, no `Classical.choice`, no
user-declared axiom.  Build remains GREEN at all 318 prior jobs
PLUS this new audit job.

## Headliner regression

The CUMUL-1.7 substitution-compatibility headliners
(`ConvCumul.subst_compatible_paired_allais`,
`ConvCumulHomo.subst_compatible_paired_allais`,
`ConvCumul.subst_compatible`) MUST remain zero-axiom after this
extension.  The audit re-prints axioms over each headliner.

## Honest scope

`Term.funextIntroHet` is the SHAPE — it carries arbitrary
applyARaw / applyBRaw raws but does NOT yet enforce a "real"
heterogeneous-funext rewriting (that's the future
`Step.eqArrowHet` rule, to be added once heterogeneous Funext
reduction is wired in).  The structural cascade
(rename / subst / substHet / pointwise / Algo / Cumul) is
complete and zero-axiom.

This unblocks the SECOND half of heterogeneous Funext.  Combined
with `Term.funextReflAtId` (Phase 12.A.B8.2 / refl-only) and
`Term.uaIntroHet` (Phase 12.A.B8.5b), the kernel can now host:

* heterogeneous-carrier equivalence values (`equivIntroHet` —
  Phase 12.A.B8.5)
* heterogeneous-carrier path-from-equivalence values
  (`uaIntroHet` — Phase 12.A.B8.5b)
* heterogeneous-carrier funext-introduction values
  (`funextIntroHet` — this phase, B8.8)

The remaining work for full heterogeneous Funext is the
`Step.eqArrowHet` reduction rule:

```
| eqArrowHet : Step (Term.funextIntroHet ... applyARaw applyBRaw)
                    (Term.funextRefl ... applyARaw)
```

deferred to a future phase (Z8.B). -/

namespace LeanFX2

/-! ## §1. The Term constructor itself. -/

#print axioms Term.funextIntroHet

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

/-! ## §4. Cumul cascade — Allais arm + dispatch (no cong rule needed). -/

#print axioms ConvCumul.subst_compatible_funextIntroHet_allais
#print axioms Term.subst_compatible_pointwise_allais
#print axioms ConvCumul.subst_compatible_paired_allais

/-! ## §5. Headliner regression — CUMUL-1.7 zero-axiom check. -/

#print axioms ConvCumulHomo.subst_compatible_paired_allais
#print axioms ConvCumul.subst_compatible

end LeanFX2

/-! ## §6. Pattern-3 + W8 + heterogeneous Univalence regression. -/

#print axioms LeanFX2.Univalence
#print axioms LeanFX2.UnivalenceHet
#print axioms LeanFX2.funext
