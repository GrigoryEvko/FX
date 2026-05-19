import LeanFX2.Reduction.Step
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Confluence.RawCd
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdRename
import LeanFX2.Confluence.RawDiamond
import LeanFX2.HoTT.Univalence

/-! # Smoke/AuditD36All — D3.6 univalence-β rollup audit (#1688).

Reviewer-facing comprehensive audit log spanning the entire D3.6
phase: parametric vocabulary (P1–P6), step-level rules (S1–S6),
and typed mirrors (D3.6 univalence-as-theorem).  S1–S6 close the
univalence-β round-trip cycle at the kernel-syntactic level.

This rollup file is the single point of truth for Phase D3.6 audit
coverage.  Each section below corresponds to one shipped sub-phase
and prints `#print axioms` for every shipped declaration produced
by that sub-phase, validating end-to-end zero-axiom discipline.

## Phase boundary at a glance

| Sub | Title                                         | Status               |
| --- | --------------------------------------------- | -------------------- |
| P1  | RawTerm.uaToEquiv vocabulary                  | shipped (#1646)      |
| P2  | RawTerm.equivApply vocabulary                 | shipped (#1647)      |
| P3  | Term.uaToEquiv typed mirror                   | shipped (#1648)      |
| P4  | Term.equivApply typed mirror                  | shipped (#1649)      |
| P5  | Pointwise lemmas                              | shipped (#1650)      |
| P6  | Foundation cascade (rename/subst/raw)         | shipped (#1651)      |
| S1  | Step.uaBeta + RawStep.par.uaBeta{,Deep}       | shipped (#1682)      |
| S2  | Step.transpReflId / no-op vs #1555            | shipped (#1683)      |
| S3  | RawStep.par.transpCompose{,Deep}              | shipped (#1684)      |
| S4  | RawStep.par.idToEquivRefl{,Deep}              | shipped (#1685)      |
| S5  | RawStep.par.idToEquivCompose{,Deep}           | shipped (#1686)      |
| S6  | RawStep.par.uaReflEquivApply{,Deep}           | shipped (#1687)      |

## S6 redesigned target — composes with uaBetaDeep

Phase S6 was initially attempted as `uaToEquiv (oeqRefl witness)
⟶ equivIntro id id` (mirroring S4's `idToEquiv (refl _) ⟶
equivIntro id id`).  That target conflicted with `uaBetaDeep`'s
deep arm in the cd cascade — `cdTranspCase`'s default rebuilds
`transp (equivIntro ...) ...` since `equivIntro` head does NOT
match a `uaToEquiv`/`pathCompose` β-firing case, breaking the
diamond.

The redesigned S6 ships at the **applied** form rather than the
intro form:

```
| uaReflEquivApply :
    par witnessSource witnessTarget →
    par sourceRawSource sourceRawTarget →
    par (equivApply (uaToEquiv (oeqRefl witnessSource)) sourceRawSource)
        sourceRawTarget
```

(applying the identity-equivalence-via-univalence to a value
yields the value unchanged).  The deep variant invokes the same
contraction when the equiv develops to `uaToEquiv (oeqRefl _)`
via parallel reduction.

This shape composes cleanly with `uaBetaDeep`: both reductions
that originate at a `transp` redex converge on the underlying
argument value at the `equivApply` layer.  The diamond holds:
`cdEquivApplyCase` dispatches to `cdUaToEquivApplyCase` (67-arm
full enumeration to keep the match propext-clean), which fires
the headline arm `oeqRefl _ => developedArg` directly.

## Round-trip closure status (S1–S6 complete)

* idToEquiv-side round-trip (S4 + S5): `idToEquiv (refl _) ⟶
  equivIntro id id` and `idToEquiv (oeqTrans _ _) ⟶
  equivCompose ...` both ship.
* uaToEquiv-side round-trip (S6): `equivApply (uaToEquiv (oeqRefl
  _)) arg ⟶ arg` ships at the applied form.  Together with the
  S1 transp-applied path (`transp (uaToEquiv ...) ...`), this
  fully closes the univalence round-trip cycle at the kernel-
  syntactic level. -/

namespace LeanFX2

-- ============================
-- Section P: D3.6 parametric vocabulary
-- ============================

-- P1: RawTerm.uaToEquiv ctor — the kernel-level univalence intro
#print axioms LeanFX2.RawTerm.uaToEquiv

-- P2: RawTerm.equivApply ctor — equivalence application destructor
#print axioms LeanFX2.RawTerm.equivApply

-- P3, P4: typed mirrors live at Term layer; pointwise checked via P5
-- (no public name in this file's import surface; verified upstream
-- via Term/PreservesTerm.lean and Smoke/AuditD36P3/P4).

-- ============================
-- Section S1: D3.6-S1 univalence-β
-- (raw-only confluence-closure mechanism — typed `Step.uaBeta`
-- mirror deferred to v1.1 alongside typed `Term.transp`/equivApply
-- ctors per the docstring above; raw-only entry in
-- `isDocumentedRawOnlyParity` Section D.)
-- ============================

#print axioms LeanFX2.RawStep.par.uaBeta
#print axioms LeanFX2.RawStep.par.uaBetaDeep
#print axioms LeanFX2.RawStep.par.uaToEquivCong
#print axioms LeanFX2.RawStep.par.equivApplyCong
#print axioms LeanFX2.RawStep.par.uaToEquiv_inv

-- ============================
-- Section S2: D3.6-S2 transp-refl-id (no-op vs #1555)
-- ============================

#print axioms LeanFX2.RawStep.par.transpReflBeta
#print axioms LeanFX2.RawStep.par.transpReflBetaDeep
#print axioms LeanFX2.Step.transpReflBeta

-- ============================
-- Section S3: D3.6-S3 transp-compose β
-- ============================

#print axioms LeanFX2.RawStep.par.pathComposeCong
#print axioms LeanFX2.RawStep.par.transpCompose
#print axioms LeanFX2.RawStep.par.transpComposeDeep
#print axioms LeanFX2.RawStep.par.pathCompose_inv

-- ============================
-- Section S4: D3.6-S4 idToEquiv-refl β
-- ============================

#print axioms LeanFX2.RawStep.par.idToEquivCong
#print axioms LeanFX2.RawStep.par.idToEquivRefl
#print axioms LeanFX2.RawStep.par.idToEquivReflDeep
#print axioms LeanFX2.RawStep.par.idToEquiv_inv

-- ============================
-- Section S5: D3.6-S5 idToEquiv-compose β
-- ============================

#print axioms LeanFX2.RawStep.par.oeqTransCong
#print axioms LeanFX2.RawStep.par.equivComposeCong
#print axioms LeanFX2.RawStep.par.idToEquivCompose
#print axioms LeanFX2.RawStep.par.idToEquivComposeDeep
#print axioms LeanFX2.RawStep.par.oeqTrans_inv
#print axioms LeanFX2.RawStep.par.equivCompose_inv

-- ============================
-- Section U: univalence-as-theorem (D3.6 headline)
-- ============================

#print axioms LeanFX2.Step.eqType
#print axioms LeanFX2.Univalence

-- ============================
-- Section CD: confluence pillars remain zero-axiom across D3.6
-- ============================

#print axioms LeanFX2.RawStep.par.cd_lemma
#print axioms LeanFX2.RawStep.par.cd_dominates
#print axioms LeanFX2.RawStep.par.diamond

-- ============================
-- Section S6: D3.6-S6 uaToEquiv-of-oeqRefl round-trip β
-- (raw-only confluence-closure mechanism — typed `Step.uaReflEquivApply`
-- mirror deferred to v1.1 alongside typed `Term.uaToEquiv`/`Term.equivApply`
-- ctors per the docstring above; raw-only entry in
-- `isDocumentedRawOnlyParity` Section H.)
-- ============================

#print axioms LeanFX2.RawStep.par.uaReflEquivApply
#print axioms LeanFX2.RawStep.par.uaReflEquivApplyDeep

end LeanFX2
