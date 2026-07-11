import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidMatrixSemantics
import FX1Poly.Polygraph.Omega.FrobeniusMonadPresentation

/-! # Polygraph/Omega/FrobeniusFourCountBlindAdjudication — the walking Frobenius monad's latent rows are
MODEL-INVISIBLE, adjudicated (OMEGA SWEEP r2 — the residual-models round, B2)

★ **The Frobenius crux: the six latent bare-whisker rows are FOUR-COUNT-BLIND, and the only cheap `Mat(N)`
matrix model is UNFAITHFUL (breaks the Frobenius law F1) — so NO shipped model can currently decide these
rows.  The r4 family ledger's r4-bill entry for Frobenius (`Mat(N)` unverified for F1/F2, imposes
commutativity) is CONFIRMED CORRECT — unlike the trio (whose "predicted clean" this sweep refutes).**

The six latent rows (the bare-single-whisker ones, `isBareGenWhisker = true`) are the monad / comonad
bare-whisker rows carried inside the Frobenius presentation: `monadUnitUnit`, `monadLeftUnitAssoc`,
`monadRightUnitAssoc`, `counitCounit`, `leftCounitCoassoc`, `rightCounitCoassoc`.  If any faithful model
separated their legs, the Frobenius walker would over-quotient exactly like the monad.  This file shows that
neither shipped invariant can even see the question.

## Why the FOUR-COUNT is BLIND (the crux — machine-shipped already, formalized here)

The shipped four-count `frobMonadOmegaGeneratorFourCount` `(#mu, #eta, #delta, #eps)` DROPS the whiskering
1-cell and counts only the generators inside a cell.  Each latent row's two legs carry exactly ONE generator,
differing only in whisker POSITION (`op |> x` vs `x <| op`) — which the four-count forgets.  So the four-count
is EQUAL on both legs of every latent row (`rfl`, below).  The shipped `frobMonadOmegaFourCountAbsorbs` already
proves this at the whole-relation level (its `ofRelation` arms for the six latent rows are `rfl`), so the
four-count CANNOT separate them: it is a SOUND invariant that identifies the very legs an over-quotient audit
would need to tell apart.  Four-count-blind = model-invisible-to-the-four-count.

## Why the cheap `Mat(N)` model is UNFAITHFUL (breaks F1 — the recon's r1-BI fact, machine-shipped here)

The bicommutative-bimonoid `Mat(N)` (`mu = [[1,1]]`, `eta = [[]]`, `delta = [[1],[1]]`, `eps = []`) evaluates
the Frobenius F1 LEFT leg `(s <| delta).(mu |> s)` to `[[1,1],[0,1]]` but the shared middle `mu . delta` to
`[[1,1],[1,1]]` — DIFFERENT at entry `(1,0)` (`0` vs `1`).  But F1 is a GENUINE Frobenius LAW
(`FrobMonadCriticalRow.frobLeft`, the shipped 3-cell `frobMonadOmegaFrobLeftThreeCell` makes the two legs
convertible), so a model that separates them is NOT a valid model: `Mat(N)` imposes the bialgebra /
commutativity relation `mu.delta = delta.mu` on a NON-commutative Frobenius walker (the r1-BI "Frobenius !=
bialgebra" fact — the four-count separation `(1,0,1,0)` vs `(2,0,2,0)` there).  So a `Mat(N)` separation of the
Frobenius latent rows would be WORTHLESS — it comes from a model that already violates a Frobenius law.

## The honest classification: MODEL-INVISIBLE pending planar 2Cob

Four-count BLIND + no valid cheap matrix model (breaks F1/F2) means the latent Frobenius rows are
model-invisible with the shipped machinery.  Deciding them needs a GENUINE Frobenius model — the planar-2Cob /
partition-with-genus invariant walled at the `TwoCategory/Frobenius` bridge at TWO named nodes
(non-commutativity = the open `BRAUER-BREACH`, and genus = `fxFrob_has2CobGenus = false`).  This file ships the
BLINDNESS + the unfaithfulness + the planar-2Cob wall; it makes NO over-quotient claim for Frobenius (contra
the trio), confirming the ledger's r4-bill Frobenius entry.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin.
The four-count is REUSED from `FrobeniusMonadPresentation`; the `Mat(N)` carrier / ops from
`WalkingBunchedBimonoidMatrixSemantics`; only the Frobenius bimonoid generator table and fold are new. -/

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # B2 — THE FOUR-COUNT IS BLIND TO THE SIX LATENT ROWS (both legs share the four-count, `rfl`)
    # ========================================================================================= -/

/-- The `monadUnitUnit` latent legs share the four-count (both carry one `eta`) — four-count-BLIND. -/
theorem frobMonadOmegaMonadUnitUnitFourCountBlind :
    frobMonadOmegaGeneratorFourCount frobMonadOmegaMonadUnitUnitLeftLeg
      = frobMonadOmegaGeneratorFourCount frobMonadOmegaMonadUnitUnitRightLeg := rfl

/-- The `monadLeftUnitAssoc` latent legs share the four-count (both carry one `mu`). -/
theorem frobMonadOmegaMonadLeftUnitAssocFourCountBlind :
    frobMonadOmegaGeneratorFourCount frobMonadOmegaMonadLeftUnitAssocLeftLeg
      = frobMonadOmegaGeneratorFourCount frobMonadOmegaMonadLeftUnitAssocRightLeg := rfl

/-- The `monadRightUnitAssoc` latent legs share the four-count (both carry one `eta`). -/
theorem frobMonadOmegaMonadRightUnitAssocFourCountBlind :
    frobMonadOmegaGeneratorFourCount frobMonadOmegaMonadRightUnitAssocLeftLeg
      = frobMonadOmegaGeneratorFourCount frobMonadOmegaMonadRightUnitAssocRightLeg := rfl

/-- The `counitCounit` latent legs share the four-count (both carry one `eps`). -/
theorem frobMonadOmegaCounitCounitFourCountBlind :
    frobMonadOmegaGeneratorFourCount frobMonadOmegaCounitCounitLeftLeg
      = frobMonadOmegaGeneratorFourCount frobMonadOmegaCounitCounitRightLeg := rfl

/-- The `leftCounitCoassoc` latent legs share the four-count (both carry one `delta`). -/
theorem frobMonadOmegaLeftCounitCoassocFourCountBlind :
    frobMonadOmegaGeneratorFourCount frobMonadOmegaLeftCounitCoassocLeftLeg
      = frobMonadOmegaGeneratorFourCount frobMonadOmegaLeftCounitCoassocRightLeg := rfl

/-- The `rightCounitCoassoc` latent legs share the four-count (both carry one `eps`). -/
theorem frobMonadOmegaRightCounitCoassocFourCountBlind :
    frobMonadOmegaGeneratorFourCount frobMonadOmegaRightCounitCoassocLeftLeg
      = frobMonadOmegaGeneratorFourCount frobMonadOmegaRightCounitCoassocRightLeg := rfl

/-- ★★ **THE FOUR-COUNT IS BLIND TO ALL SIX LATENT ROWS.**  Every latent bare-whisker row's two legs share the
four-count (both legs one generator, differing only in whisker position which the fold drops), so the shipped
sound invariant `frobMonadOmegaGeneratorFourCount` CANNOT separate them — the Frobenius latent defect is
four-count-invisible.  The bundle of the six per-row blindness facts. -/
theorem frobMonadOmegaLatentRowsFourCountBlind :
    (frobMonadOmegaGeneratorFourCount frobMonadOmegaMonadUnitUnitLeftLeg
        = frobMonadOmegaGeneratorFourCount frobMonadOmegaMonadUnitUnitRightLeg)
      ∧ (frobMonadOmegaGeneratorFourCount frobMonadOmegaMonadLeftUnitAssocLeftLeg
        = frobMonadOmegaGeneratorFourCount frobMonadOmegaMonadLeftUnitAssocRightLeg)
      ∧ (frobMonadOmegaGeneratorFourCount frobMonadOmegaMonadRightUnitAssocLeftLeg
        = frobMonadOmegaGeneratorFourCount frobMonadOmegaMonadRightUnitAssocRightLeg)
      ∧ (frobMonadOmegaGeneratorFourCount frobMonadOmegaCounitCounitLeftLeg
        = frobMonadOmegaGeneratorFourCount frobMonadOmegaCounitCounitRightLeg)
      ∧ (frobMonadOmegaGeneratorFourCount frobMonadOmegaLeftCounitCoassocLeftLeg
        = frobMonadOmegaGeneratorFourCount frobMonadOmegaLeftCounitCoassocRightLeg)
      ∧ (frobMonadOmegaGeneratorFourCount frobMonadOmegaRightCounitCoassocLeftLeg
        = frobMonadOmegaGeneratorFourCount frobMonadOmegaRightCounitCoassocRightLeg) :=
  ⟨frobMonadOmegaMonadUnitUnitFourCountBlind, frobMonadOmegaMonadLeftUnitAssocFourCountBlind,
    frobMonadOmegaMonadRightUnitAssocFourCountBlind, frobMonadOmegaCounitCounitFourCountBlind,
    frobMonadOmegaLeftCounitCoassocFourCountBlind, frobMonadOmegaRightCounitCoassocFourCountBlind⟩

/-! # =========================================================================================
    # B2 — THE CHEAP `Mat(N)` BIMONOID MODEL IS UNFAITHFUL: it breaks the Frobenius law F1
    # ========================================================================================= -/

/-- The **Frobenius bimonoid generator matrix table** — the bicommutative-bimonoid `Mat(N)` map: `s |-> ` width
1; `mu = [[1,1]] : 1x2`, `eta = [[]] : 1x0`, `delta = [[1],[1]] : 2x1`, `eps = [] : 0x1`.  Full six-arm split on
the five labels (`sEndo` a total width-1 default; it never appears at label-dimension 1) — propext-clean. -/
def frobMonadOmegaBimonoidEvalGen : (labelDim : Nat) → FrobMonadGenLabel →
    BunchedBimonoidEvalCarrier labelDim → BunchedBimonoidEvalCarrier labelDim →
    BunchedBimonoidEvalCarrier (labelDim + 1)
  | 0, _, _, _ => (1 : Nat)
  | 1, .sEndo, _, _ => bunchedBimonoidIdentityMat 1
  | 1, .muMult, _, _ => { rows := 1, cols := 2, entries := [[1, 1]] }
  | 1, .etaUnit, _, _ => { rows := 1, cols := 0, entries := [[]] }
  | 1, .deltaComult, _, _ => { rows := 2, cols := 1, entries := [[1], [1]] }
  | 1, .epsCounit, _, _ => { rows := 0, cols := 1, entries := [] }
  | _ + 2, _, _, _ => ()

/-- ★ **The Frobenius bimonoid matrix evaluation** — the bicommutative-bimonoid functor into `Mat(N)`, the
identical fold as `monadOmegaEvalCell` with the Frobenius generator table.  Propext-clean. -/
def frobMonadOmegaBimonoidEvalCell : {dim : Nat} → CellExpr frobMonadOmegaComputad dim →
    BunchedBimonoidEvalCarrier dim
  | _, .ofMode _ => ()
  | _, .gen (dim := labelDim) label source target =>
      frobMonadOmegaBimonoidEvalGen labelDim label
        (frobMonadOmegaBimonoidEvalCell source) (frobMonadOmegaBimonoidEvalCell target)
  | _, .id (dim := d) cell => bunchedBimonoidEvalId d (frobMonadOmegaBimonoidEvalCell cell)
  | _, .vcomp (dim := d) leftCell rightCell =>
      bunchedBimonoidEvalVcomp d (frobMonadOmegaBimonoidEvalCell leftCell)
        (frobMonadOmegaBimonoidEvalCell rightCell)
  | _, .whiskerLeft (dim := d) whiskerCell cell =>
      bunchedBimonoidEvalWhiskerLeft d (frobMonadOmegaBimonoidEvalCell whiskerCell)
        (frobMonadOmegaBimonoidEvalCell cell)
  | _, .whiskerRight (dim := d) cell whiskerCell =>
      bunchedBimonoidEvalWhiskerRight d (frobMonadOmegaBimonoidEvalCell cell)
        (frobMonadOmegaBimonoidEvalCell whiskerCell)

/-- ★ **THE CHEAP `Mat(N)` MODEL BREAKS FROBENIUS F1.**  The F1 left leg `(s <| delta).(mu |> s)` evaluates to
`[[1,1],[0,1]]` but the shared middle `mu . delta` to `[[1,1],[1,1]]` — DIFFERENT at entry `(1,0)` (`0` vs `1`).
So the bicommutative-bimonoid `Mat(N)` does NOT respect the Frobenius law F1. -/
theorem frobMonadOmegaBimonoidBreaksFrobeniusF1 :
    frobMonadOmegaBimonoidEvalCell frobMonadOmegaFrobLeftLeg
      ≠ frobMonadOmegaBimonoidEvalCell frobMonadOmegaFrobMiddle :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 1 0) hmatrix)

/-- ★★ **THE `Mat(N)` BIMONOID IS AN INVALID MODEL OF THE FROBENIUS WALKER.**  The F1 legs ARE convertible
under the Frobenius base relation (the shipped genuine-law 3-cell `frobMonadOmegaFrobLeftThreeCell`) yet the
bimonoid `Mat(N)` SEPARATES them — so `Mat(N)` violates a genuine Frobenius law (it imposes the bialgebra /
commutativity relation `mu.delta = delta.mu` on the non-commutative walker).  A separation of the latent rows
by this model would therefore be WORTHLESS.  The pair `(genuine-law-convertibility, model-separation)` — the
model's own unsoundness witness. -/
theorem frobMonadOmegaBimonoidIsInvalidModel :
    SaturatedConvOverWithId frobMonadOmegaComputad frobMonadOmegaBaseRel
        frobMonadOmegaFrobLeftLeg frobMonadOmegaFrobMiddle
      ∧ frobMonadOmegaBimonoidEvalCell frobMonadOmegaFrobLeftLeg
        ≠ frobMonadOmegaBimonoidEvalCell frobMonadOmegaFrobMiddle :=
  ⟨frobMonadOmegaFrobLeftThreeCell, frobMonadOmegaBimonoidBreaksFrobeniusF1⟩

/-! # =========================================================================================
    # B2 — THE VERDICT MARKERS (the ledger's Frobenius r4-bill entry CONFIRMED CORRECT)
    # ========================================================================================= -/

/-- ★★ **THE FROBENIUS FOUR-COUNT IS BLIND TO THE SIX LATENT ROWS (machine-confirmed).**  `= true` records
`frobMonadOmegaLatentRowsFourCountBlind`: each of the six latent bare-whisker rows' two legs shares the shipped
four-count (differing only in whisker position, which the fold drops), so the four-count CANNOT separate them.
The crux: the Frobenius latent defect is four-count-invisible. -/
def fxFrob_fourCountBlindToSixLatentRows : Bool := true

/-- ★★ **THE CHEAP `Mat(N)` BIMONOID MODEL IS UNFAITHFUL — it breaks Frobenius F1 (machine-confirmed).**
`= false` records `frobMonadOmegaBimonoidIsInvalidModel`: the only cheap matrix model separates the genuine-law
F1 legs (`[[1,1],[0,1]]` vs `[[1,1],[1,1]]`), so it violates a Frobenius law and is an INVALID separator (it
imposes bialgebra / commutativity on the non-commutative walker).  So — unlike the monad and the trio — there is
NO valid cheap `Mat(N)` separation for the Frobenius latent rows. -/
def fxFrob_matNBimonoidBreaksF1Unfaithful : Bool := false

/-- ★★ **THE FROBENIUS LATENT ROWS ARE MODEL-INVISIBLE PENDING PLANAR 2Cob (honest).**  `= false` records the
crux conclusion: four-count BLIND (`fxFrob_fourCountBlindToSixLatentRows`) + no valid cheap matrix model
(`fxFrob_matNBimonoidBreaksF1Unfaithful`) means NO shipped model can currently decide whether the six latent
rows over-quotient.  Deciding them needs a GENUINE Frobenius model — the planar-2Cob / partition-with-genus
invariant, walled at the `TwoCategory/Frobenius` bridge at two named nodes (non-commutativity = the open
`BRAUER-BREACH`; genus = `fxFrob_has2CobGenus = false`).  NO over-quotient claim is made for Frobenius. -/
def fxFrob_latentRowsModelInvisiblePending2Cob : Bool := false

/-- ★ **THE r4 LEDGER'S FROBENIUS r4-BILL ENTRY IS CONFIRMED CORRECT.**  `= true` records that — UNLIKE the
not-spurious trio (whose "predicted clean" this sweep REFUTES) — the ledger's r4-bill Frobenius entry (`Mat(N)`
unverified for the Frobenius laws F1/F2, imposes commutativity, so a `Mat(N)` separation would be worthless)
is machine-CONFIRMED: the four-count is blind and the cheap `Mat(N)` model breaks F1.  The Frobenius rows stay
honestly deferred pending the planar-2Cob model; the ledger got this one right. -/
def fxFrob_ledgerFrobeniusEntryConfirmedCorrect : Bool := true

/-! ## The B2 truth-probe outputs (the F1 break + the four-count blindness) -/

#eval (frobMonadOmegaBimonoidEvalCell frobMonadOmegaFrobLeftLeg).entries
#eval (frobMonadOmegaBimonoidEvalCell frobMonadOmegaFrobMiddle).entries
#eval frobMonadOmegaGeneratorFourCount frobMonadOmegaMonadUnitUnitLeftLeg
#eval frobMonadOmegaGeneratorFourCount frobMonadOmegaMonadUnitUnitRightLeg

end FX1Poly.Polygraph.Omega
