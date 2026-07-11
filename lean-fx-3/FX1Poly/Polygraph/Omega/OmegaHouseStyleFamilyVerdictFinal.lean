import FX1Poly.Polygraph.Omega.OmegaHouseStyleFamilyLedger
import FX1Poly.Polygraph.Omega.NotSpuriousTrioOverQuotientAdjudication
import FX1Poly.Polygraph.Omega.FrobeniusFourCountBlindAdjudication
import FX1Poly.Polygraph.Omega.ComonadOpDualOverQuotientAdjudication

/-! # Polygraph/Omega/OmegaHouseStyleFamilyVerdictFinal — the finalized family over-quotient verdict
(OMEGA SWEEP r2 — the residual-models round, B4)

★ **The family audit completes.**  The r4 `OmegaHouseStyleFamilyLedger` shipped THREE machine-confirmed
over-quotients (monad / strong / distlaw), deferred the not-spurious trio as UNRESOLVED-predicted-clean, named
Frobenius / the op-duals / the Fubini isolations in the r4-bill, and flagged the walking equivalence as the
positive example.  This sweep RESOLVES the residual models: the trio OVER-QUOTIENTS (B1), the walking comonad
op-dual OVER-QUOTIENTS (B3), and the Frobenius latent rows are MODEL-INVISIBLE (B2, no claim, ledger correct).
This file consolidates the finalized per-walker verdict and ships the superseding markers additively — the r4
ledger's markers are LEFT INTACT as the historical record (they recorded a genuine pre-model state), exactly as
the r3 bunched flag was left intact and "made good" by the monad adjudication.

## The finalized per-walker verdict table

  * walking monad — OVER-QUOTIENT (3 bare-whisker rows, r4 `Mat(N)`-monoid, sound sub-theory restored).
  * walking strong monad — OVER-QUOTIENT (3 T-monad rows, r4).
  * walking distributive law — OVER-QUOTIENT (6 monad-internal rows, r4).
  * **walking involution `sss`** — OVER-QUOTIENT (B1, was "predicted clean").
  * **walking cyclic-3 `ssss` / `sssss`** — OVER-QUOTIENT (B1, was "predicted clean").
  * **walking idempotent semigroup `eee`** — OVER-QUOTIENT + restored soundness (B1, `M`-mediated assoc).
  * **walking comonad `counitCounit` / `leftCounitCoassoc` / `rightCounitCoassoc`** — OVER-QUOTIENT (B3,
    transpose model; convertibility free via `opConvWithId`).
  * **walking Frobenius monad (6 latent rows)** — MODEL-INVISIBLE (B2: four-count blind + cheap `Mat(N)` breaks
    F1; no over-quotient claim, deferred pending planar-2Cob — the ledger got this right).
  * KZ / co-KZ — census free-riders on the monad / comonad (B3).
  * idempotent comonad = op(idempotent semigroup) — transports identically to the comonad (name-only free-rider;
    the idempotent-transpose separation mirrors B1's `eee` separation, not separately shipped this round).
  * walking equivalence — CLEAN positive example (shape ABSENT, r4).

## The correction, stated under BOTH semantics (Risk 1 — no "wrong monoid" claim)

Under the family's dim-2-congruence + free-2-category (`Mat(N)`) semantics — THE SAME standard that condemns
the monad — the trio and the comonad OVER-QUOTIENT (distinct 2-cells identified).  Under the delooped-monoid
semantics the presented 1-dimensional monoids (`Z/2`, `Z/3`, idempotent) remain CORRECT; only the Squier
2-cell / syzygy information is lost.  This is uniformly the monad-vs-Delta situation; the ledger's ASYMMETRY
(monad broken, trio clean) — rooted in the category error of reading `rho` / `R` / `M` as a 1-level torsion
equation rather than a non-invertible 2-cell — is what is retracted.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin.
Purely a consolidation layer: every fact is re-exported from B1 / B2 / B3; no new machine content. -/

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # B4 — THE FINALIZED FAMILY OVER-QUOTIENT BUNDLE (the trio + the comonad, one machine fact)
    # ========================================================================================= -/

/-- ★★ **THE FINALIZED RESIDUAL-MODEL OVER-QUOTIENT BUNDLE.**  The SEVEN residual leg-pairs this sweep resolved
— involution `sss`, cyclic-3 `ssss` / `sssss`, idempotent `eee`, and the three op'd comonad rows — are EACH an
over-quotient witness: convertible under their r1 base relation yet `Mat(N)`-separated (the trio by the monoid
model, the comonad by its transpose).  One conjunction, all seven components machine-checked and zero-axiom. -/
theorem omegaHouseStyleTrioComonadOverQuotientBundle :
    (SaturatedConvOverWithId involutionOmegaComputad involutionBaseRel
        involutionLeftLeg involutionRightLeg
      ∧ involutionOmegaEvalCell involutionLeftLeg ≠ involutionOmegaEvalCell involutionRightLeg)
    ∧ (SaturatedConvOverWithId cyclicThreeOmegaComputad cyclicThreeOmegaBaseRel
        cyclicThreeOmegaSsssLeftLeg cyclicThreeOmegaSsssRightLeg
      ∧ cyclicThreeOmegaEvalCell cyclicThreeOmegaSsssLeftLeg
        ≠ cyclicThreeOmegaEvalCell cyclicThreeOmegaSsssRightLeg)
    ∧ (SaturatedConvOverWithId cyclicThreeOmegaComputad cyclicThreeOmegaBaseRel
        cyclicThreeOmegaSssssLeftLeg cyclicThreeOmegaSssssRightLeg
      ∧ cyclicThreeOmegaEvalCell cyclicThreeOmegaSssssLeftLeg
        ≠ cyclicThreeOmegaEvalCell cyclicThreeOmegaSssssRightLeg)
    ∧ (SaturatedConvOverWithId idempotentSemigroupOmegaComputad idempotentSemigroupOmegaBaseRel
        idempotentSemigroupOmegaEeeLeftLeg idempotentSemigroupOmegaEeeRightLeg
      ∧ idempotentSemigroupOmegaEvalCell idempotentSemigroupOmegaEeeLeftLeg
        ≠ idempotentSemigroupOmegaEvalCell idempotentSemigroupOmegaEeeRightLeg)
    ∧ (SaturatedConvOverWithId monadOmegaComputad (opCellRelOver monadOmegaBaseRel)
        (opCellExpr monadOmegaUnitUnitLeftLeg) (opCellExpr monadOmegaUnitUnitRightLeg)
      ∧ comonadOmegaEvalCell (opCellExpr monadOmegaUnitUnitLeftLeg)
        ≠ comonadOmegaEvalCell (opCellExpr monadOmegaUnitUnitRightLeg))
    ∧ (SaturatedConvOverWithId monadOmegaComputad (opCellRelOver monadOmegaBaseRel)
        (opCellExpr monadOmegaLeftUnitAssocLeftLeg) (opCellExpr monadOmegaLeftUnitAssocRightLeg)
      ∧ comonadOmegaEvalCell (opCellExpr monadOmegaLeftUnitAssocLeftLeg)
        ≠ comonadOmegaEvalCell (opCellExpr monadOmegaLeftUnitAssocRightLeg))
    ∧ (SaturatedConvOverWithId monadOmegaComputad (opCellRelOver monadOmegaBaseRel)
        (opCellExpr monadOmegaRightUnitAssocLeftLeg) (opCellExpr monadOmegaRightUnitAssocRightLeg)
      ∧ comonadOmegaEvalCell (opCellExpr monadOmegaRightUnitAssocLeftLeg)
        ≠ comonadOmegaEvalCell (opCellExpr monadOmegaRightUnitAssocRightLeg)) :=
  ⟨involutionOmegaBaseRelOverQuotientsSss,
    cyclicThreeOmegaBaseRelOverQuotientsSsss, cyclicThreeOmegaBaseRelOverQuotientsSssss,
    idempotentSemigroupOmegaBaseRelOverQuotientsEee,
    comonadOmegaBaseRelOverQuotientsUnitUnit, comonadOmegaBaseRelOverQuotientsLeftUnitAssoc,
    comonadOmegaBaseRelOverQuotientsRightUnitAssoc⟩

/-! # =========================================================================================
    # B4 — THE FINALIZED VERDICT MARKERS (superseding the r4 ledger additively)
    # ========================================================================================= -/

/-- ★★ **THE NOT-SPURIOUS TRIO OVER-QUOTIENTS — SUPERSEDES the r4 UNRESOLVED marker.**  `= true` records the
resolution of `fxOmegaHouseStyle_notSpuriousTrioShapeMatchesOverQuotientUnresolved`: all four trio leg-pairs
(involution `sss`, cyclic-3 `ssss` / `sssss`, idempotent `eee`) are r1-convertible yet `Mat(N)`-separated (the
B1 witnesses), so the ledger's "PREDICTED CLEAN by torsion" is REFUTED.  Under the family's dim-2 semantics the
trio over-quotients like the monad; under the delooped-monoid semantics the presented monoids stay correct and
only distinct 2-cells collapse.  The r4 marker is left intact as the historical pre-model state. -/
def fxOmegaHouseStyle_trioOverQuotientConfirmedMatNSeparated : Bool := true

/-- ★★ **THE DISCRIMINANT RESOLVES POSITIVE FOR THE TRIO — corrects the r4 discriminant.**  `= true` records
the correction to `fxOmegaHouseStyle_shapeIsNecessaryNotSufficientFaithfulModelDecides`'s trio prediction:
"over-quotient = shape present AND faithful model separates" is TRUE for the trio, because `Mat(N)` IS a
faithful (legitimate strict-2-category) model of the 2-polygraph — the rewrite rule `rho` / `R` / `M` is a
non-invertible 2-cell GENERATOR, not a 1-level torsion equation, so the "delooped group identifies" branch was
a category error (retracted in B1's `fxOmegaHouseStyle_trioTorsionModelCategoryErrorRetracted`).  The
discriminant itself stands; only its trio outcome flips from "unresolved / predicted identify" to
"separates". -/
def fxOmegaHouseStyle_familyDiscriminantCorrectedTrioSeparates : Bool := true

/-- ★★ **THE WALKING COMONAD OP-DUAL OVER-QUOTIENTS — the r4-bill op-dual item RESOLVED.**  `= true` records
`comonadOmegaBaseRelOverQuotients{UnitUnit,LeftUnitAssoc,RightUnitAssoc}` (B3): the three op'd bare-whisker rows
are op-convertible (free `opConvWithId`) yet transpose-separated by a comonad model sound on the genuine
comonad laws.  The idempotent comonad = op(idempotent semigroup) transports identically (name-only free-rider);
KZ / co-KZ ride the monad / comonad.  Resolves the ledger's r4-bill "walking co-monad / co-KZ op-duals" item. -/
def fxOmegaHouseStyle_opDualComonadOverQuotientConfirmed : Bool := true

/-- ★ **THE FROBENIUS LATENT ROWS STAY MODEL-INVISIBLE — the r4-bill Frobenius item CONFIRMED, not resolved.**
`= true` records that B2 (`fxFrob_ledgerFrobeniusEntryConfirmedCorrect`) makes GOOD the ledger's r4-bill
Frobenius entry: the six latent rows are four-count BLIND and the cheap `Mat(N)` bimonoid breaks F1 (invalid
model), so no shipped model decides them — they stay honestly deferred pending planar-2Cob.  Unlike the trio,
this item is NOT resolved; it is now UNDERSTOOD as model-invisible (not merely unbuilt). -/
def fxOmegaHouseStyle_frobeniusModelInvisibleLedgerCorrect : Bool := true

/-- ★ **THE FINALIZED r4-BILL — trio + op-duals RESOLVED, three item-classes remain.**  `= true` records the
shrunk census: the r4-bill `fxOmegaHouseStyle_censusedBillFrobeniusTrioModelsOpDualsFubini` had five open item
classes; this sweep RESOLVES two — (2) the not-spurious trio's faithful models (B1: `Mat(N)` IS faithful, they
over-quotient) and (3) the walking co-monad / co-KZ op-duals (B3: transported).  Item (1) Frobenius is CONFIRMED
model-invisible (B2), still deferred pending planar-2Cob.  The remaining open item classes are: Frobenius
planar-2Cob, (4) the full `StrictAxiomRel union SoundRow` Fubini isolations per walker, (5) the spider
matrix-completeness per walker — each still NAMED at its node. -/
def fxOmegaHouseStyle_censusedBillResolvedTrioAndOpDuals : Bool := true

/-- ★★ **ESTABLISHED (B4) — the family over-quotient census FINALIZED.**  `= true` records the completed family
audit: the residual models are resolved — the not-spurious trio (involution / cyclic-3 / idempotent) and the
walking comonad OVER-QUOTIENT (B1 / B3, `omegaHouseStyleTrioComonadOverQuotientBundle`), correcting the r4
ledger's trio prediction and its torsion-model category error; the Frobenius latent rows are MODEL-INVISIBLE
(B2, ledger correct, deferred); KZ / co-KZ and the idempotent comonad are census free-riders; the walking
equivalence remains the clean positive example; the r4-bill shrinks to Frobenius-2Cob + the Fubini isolations +
the spider completeness.  Every over-quotient is under the family's dim-2 semantics (the presented monoids stay
correct under the delooped-monoid reading — no "wrong monoid" claim); every wall NAMED at its node. -/
def fxOmegaHouseStyle_familyOverQuotientCensusFinalized : Bool := true

end FX1Poly.Polygraph.Omega
