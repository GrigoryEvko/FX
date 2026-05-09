import LeanFX2.Reduction.Step
import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.RawParRename
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Confluence.RawCd
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawCdRename
import LeanFX2.Confluence.RawDiamond
import LeanFX2.HoTT.Univalence

/-! # Smoke/AuditD36All — D3.6 univalence-β rollup audit (#1688).

Reviewer-facing comprehensive audit log spanning the entire D3.6
phase: parametric vocabulary (P1–P6), step-level rules (S1–S5),
typed mirrors (D3.6 univalence-as-theorem), and the structural
deferral note for S6.

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
| S6  | uaToEquiv-of-oeqRefl round-trip               | DEFERRED v1.1 (#1687) |

## S6 structural deferral note

Phase S6 (`uaToEquiv (oeqRefl witness) ⟶ equivIntro id id`) was
investigated as a standalone shallow + deep β cascade following
S4's mold (`idToEquiv (refl _) ⟶ equivIntro id id`).  The
shallow rule and its four cascade arms (RawPar / RawParCompatible /
RawParRename / RawParWeakenInv) ship structurally without trouble.

The blocker is in the **cd cascade**.  The existing `uaBetaDeep`
rule

```
par pathRawSource (uaToEquiv proofRawTarget) →
par sourceRawSource sourceRawTarget →
par (transp pathRawSource sourceRawSource)
    (equivApply (uaToEquiv proofRawTarget) sourceRawTarget)
```

asserts a parallel-reduction step from a `transp` redex to an
`equivApply (uaToEquiv ...)` head.  When `proofRawTarget` happens
to be `oeqRefl _`, the new S6 rule `uaToEquivOfRefl` fires on
the inner `uaToEquiv (oeqRefl _)` head producing `equivIntro id
id`.  The parallel-development closure `cd` must commit BOTH
reductions at once: the maximal cd of `uaToEquiv (oeqRefl X)` is
the closed identity-equiv `equivIntro id id`, NOT `uaToEquiv
(oeqRefl (cd X))`.

This means `cd pathRawSource = equivIntro ...` (after
`cdUaToEquivCase`'s `oeqRefl` arm fires), and `cdTranspCase`'s
default arm rebuilds `transp (equivIntro ...) (cd sourceRawSource)`
since `equivIntro` does NOT match the `uaToEquiv`/`pathCompose`
β-firing cases.  But `uaBetaDeep`'s cd_lemma proof obligation
becomes:

```
par (equivApply (uaToEquiv (oeqRefl proofRawTarget)) sourceRawTarget)
    (transp (equivIntro ...) (cd sourceRawSource))
```

Different head ctors (`equivApply` vs `transp`) on each side of
the par-step — structurally false, with no realizable single
parallel-reduction rule connecting them.  The cd cascade is
broken.

The fix requires adding a NEW joint reduction rule like

```
| transpUaOfReflBeta {scope : Nat} {pathRawSource ...} :
    par pathRawSource (uaToEquiv (oeqRefl _)) →
    par sourceRawSource sourceRawTarget →
    par (transp pathRawSource sourceRawSource) sourceRawTarget
```

(transport along the identity equivalence is the identity), plus
a corresponding `cdTranspCase` extension recognizing the joint
firing.  This is a multi-rule cascade extension (~250+ lines per
the `cd_cascade_inversion_blocker` memory entry) — beyond a
single-atom ship boundary and properly belongs to the v1.1
follow-up that will land typed mirrors `Term.{idToEquiv,oeqRefl,
oeqTrans,equivCompose,uaToEquiv}` together with a unified
univalence-of-refl + transport-along-identity treatment.

Investigation work documented inline; no axioms, no wrapper
files, no hypothesis-as-postulate placeholder.  S6 stays open
on the issue tracker (#1687) with status DEFERRED v1.1, blocking
on D3.10-UNIVALENCE-COMPOSITION-CLOSURE / cd-cascade-extension
co-design.  No decl of the S6 rule lives in the kernel — the
existing S1 cascade (where `uaToEquiv proof` reduces via
`uaBeta` when applied as a path under transp) is the ONLY way
the round-trip semantics fire today, and that is sound.

## Round-trip closure status WITH S6 deferred

* idToEquiv-side round-trip (S4 + S5): `idToEquiv (refl _) ⟶
  equivIntro id id` and `idToEquiv (oeqTrans _ _) ⟶
  equivCompose ...` both ship.
* uaToEquiv-side round-trip (S6): NOT YET — `uaToEquiv (oeqRefl
  _) ⟶ equivIntro id id` is the missing dual.
* The asymmetry is real but bounded: `idToEquiv` round-trips
  fully at the raw layer; `uaToEquiv` round-trips only via the
  S1 transp-applied path.  Closure under v1.1 will eliminate
  the asymmetry. -/

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
-- Section S6 (DEFERRED v1.1): no kernel decls; structural blocker
-- documented in the docstring above.  No `#print axioms` here —
-- there is nothing to print, by design.  When S6 ships in v1.1
-- as part of D3.10-UNIVALENCE-COMPOSITION-CLOSURE, this section
-- will gain `#print axioms LeanFX2.RawStep.par.uaToEquivOfRefl`
-- and `#print axioms LeanFX2.RawStep.par.uaToEquivOfReflDeep`
-- alongside the joint `transpUaOfReflBeta` cd-cascade extension.
-- ============================

end LeanFX2
