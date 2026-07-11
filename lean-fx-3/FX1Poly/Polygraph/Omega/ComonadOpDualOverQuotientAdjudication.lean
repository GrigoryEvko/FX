import FX1Poly.Polygraph.Omega.WalkingMonadOverQuotientAdjudication
import FX1Poly.Polygraph.Omega.PresentationOpDualityWithId

/-! # Polygraph/Omega/ComonadOpDualOverQuotientAdjudication — the walking comonad's latent over-quotient,
transported from the monad (OMEGA SWEEP r2 — the residual-models round, B3)

★ **The op-dual over-quotient transports cheaply: convertibility is FREE (the shipped generic `opConvWithId`),
separation is a fresh TRANSPOSE eval.**  The walking comonad is the walking monad's presentation read backwards
(`opCellRelOver monadOmegaBaseRel`, over the same `monadOmegaComputad`, via `opCellExpr`).  Its coherent
presentation already ships (`comonadWalkerCoherentPresentation` in `PresentationOpDualityWithId`), so the r1
convertibility of the op'd bare-whisker legs is the shipped `comonadOmega{UnitUnit,LeftUnitAssoc,
RightUnitAssoc}Resolved.legsConvertible`.  This file supplies the SEPARATION half with a DIRECT comonad
`Mat(N)` model — the natural TRANSPOSE of the monad's (`delta = mu^T = [[1],[1]]`, `eps = eta^T = []`) — and
pairs the two into the op-dual over-quotient witnesses.

## Why a DIRECT transpose eval, not the transported monad eval (the recon's variance adjudication)

The monad's own `monadOmegaEvalCell` applied to the op'd legs happens to separate (the transpose of the
originals), but it is LABEL-keyed and `op` preserves labels while reversing boundaries, so
`monadOmegaEvalCell . op` is not a priori a SOUND invariant of the op'd genuine comonad laws.  The DIRECT
comonad eval `comonadOmegaEvalCell` (`eta`-label `|-> eps`, `mu`-label `|-> delta` — the natural transpose)
IS a sound invariant of the genuine comonad laws (it respects the op'd genuine monad laws ON THE NOSE — the
op'd counit / coassociativity rows evaluate equal, machine-checked `rfl` below) AND separates the op'd
bare-whisker legs by the same entry-check.  This is the transpose of the monad's soundness picture; the full
comonad restored-soundness FOLD over `opCellRelOver MonadOmegaSoundRow` is the NAMED transpose-involutivity
wall (the `op`-image inversion the recInto arms need), the exact transpose of the monad's Fubini wall.

## KZ / co-KZ ride the monad / comonad (census free-rider caveat, per the r3 docstring)

The KZ (lax-idempotent) and co-KZ walkers are the monad / comonad presentation with the DIRECTED (2-cell
ordering) structure forgotten, so their bare-whisker over-quotient RIDES the monad / comonad over-quotient
verbatim — no separate transport.  Recorded as a census free-rider marker, not a fresh adjudication (matching
`fxOmega4_squierFamilyTwoGenuineOpDualsShippedR3`'s free-rider caveat).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin.
The op involution / transport, the shipped comonad resolutions, the `Mat(N)` carrier / ops / helpers are all
REUSED; only the direct comonad transpose generator table and fold are new. -/

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # B3 — THE DIRECT COMONAD TRANSPOSE `Mat(N)` MODEL (delta = mu^T = [[1],[1]], eps = eta^T = [])
    # ========================================================================================= -/

/-- The **comonad generator matrix table** — the natural TRANSPOSE of the monad's: at label-dimension 0 the
1-generator `t` is a single strand (width 1); at label-dimension 1 the counit `eps` (label `false`, = `op eta`)
is the empty coproduct `[] : 0x1` and the comultiplication `delta` (label `true`, = `op mu`) is the copy
`[[1],[1]] : 2x1`.  `Unit` above.  The label family is the constant `Bool` (`monadOmegaComputad.genLabel`), so
the arm splits on the `Bool` at label-dimension 1 — full-enum, propext-clean. -/
def comonadOmegaEvalGen : (labelDim : Nat) → Bool →
    BunchedBimonoidEvalCarrier labelDim → BunchedBimonoidEvalCarrier labelDim →
    BunchedBimonoidEvalCarrier (labelDim + 1)
  | 0, _, _, _ => (1 : Nat)
  | 1, false, _, _ => { rows := 0, cols := 1, entries := [] }
  | 1, true, _, _ => { rows := 2, cols := 1, entries := [[1], [1]] }
  | _ + 2, _, _, _ => ()

/-- ★ **The comonad matrix evaluation** `comonadOmegaEvalCell : CellExpr monadOmegaComputad dim -> EvalCarrier
dim` — the comonoid functor into `Mat(N)`, the identical fold as `monadOmegaEvalCell` with the transpose
generator table.  Applied to the OP'd monad legs (which are cells over the SAME `monadOmegaComputad`, boundaries
reversed by `op`), it evaluates the comonad's bare-whisker legs.  Propext-clean. -/
def comonadOmegaEvalCell : {dim : Nat} → CellExpr monadOmegaComputad dim →
    BunchedBimonoidEvalCarrier dim
  | _, .ofMode _ => ()
  | _, .gen (dim := labelDim) label source target =>
      comonadOmegaEvalGen labelDim label (comonadOmegaEvalCell source) (comonadOmegaEvalCell target)
  | _, .id (dim := d) cell => bunchedBimonoidEvalId d (comonadOmegaEvalCell cell)
  | _, .vcomp (dim := d) leftCell rightCell =>
      bunchedBimonoidEvalVcomp d (comonadOmegaEvalCell leftCell) (comonadOmegaEvalCell rightCell)
  | _, .whiskerLeft (dim := d) whiskerCell cell =>
      bunchedBimonoidEvalWhiskerLeft d (comonadOmegaEvalCell whiskerCell) (comonadOmegaEvalCell cell)
  | _, .whiskerRight (dim := d) cell whiskerCell =>
      bunchedBimonoidEvalWhiskerRight d (comonadOmegaEvalCell cell) (comonadOmegaEvalCell whiskerCell)

/-! ## The direct comonad model RESPECTS the op'd genuine comonad laws (the SOUND-model evidence) -/

/-- The op'd genuine left-counit law is respected: `op ((eta |> t).mu)` and `op id_t` both evaluate to `[[1]]`
under the comonad model.  The transpose of `monadOmegaMatrixRespectsGenuineLeftUnit`. -/
theorem comonadOmegaMatrixRespectsGenuineCounit :
    comonadOmegaEvalCell (opCellExpr monadOmegaGenuineLeftUnitLeftLeg)
      = comonadOmegaEvalCell (opCellExpr monadOmegaGenuineLeftUnitRightLeg) := rfl

/-- The op'd genuine right-counit law is respected (both `[[1]]`). -/
theorem comonadOmegaMatrixRespectsGenuineCounitRight :
    comonadOmegaEvalCell (opCellExpr monadOmegaGenuineRightUnitLeftLeg)
      = comonadOmegaEvalCell (opCellExpr monadOmegaGenuineRightUnitRightLeg) := rfl

/-- The op'd genuine coassociativity law is respected: both legs evaluate to `[[1],[1],[1]]` (the transpose of
the monad's `[[1,1,1]]`).  So the comonad model is SOUND on the genuine comonad laws. -/
theorem comonadOmegaMatrixRespectsGenuineCoassoc :
    comonadOmegaEvalCell (opCellExpr monadOmegaGenuineAssocLeftLeg)
      = comonadOmegaEvalCell (opCellExpr monadOmegaGenuineAssocRightLeg) := rfl

/-! ## The three op'd bare-whisker legs SEPARATE under the comonad model -/

/-- ★ The op'd `unitUnit` (`counitCounit`) legs are DIFFERENT: `[[1,0]]` vs `[[0,1]]`; entry `(0,0)` is `1` vs
`0`.  The transpose of `monadOmegaMatrixSeparatesUnitUnit`. -/
theorem comonadOmegaMatSeparatesUnitUnit :
    comonadOmegaEvalCell (opCellExpr monadOmegaUnitUnitLeftLeg)
      ≠ comonadOmegaEvalCell (opCellExpr monadOmegaUnitUnitRightLeg) :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-- ★ The op'd `leftUnitAssoc` (`leftCounitCoassoc`) legs are DIFFERENT: `[[1,0],[0,1],[0,1]]` vs
`[[1,0],[1,0],[0,1]]`; entry `(1,0)` is `0` vs `1`. -/
theorem comonadOmegaMatSeparatesLeftUnitAssoc :
    comonadOmegaEvalCell (opCellExpr monadOmegaLeftUnitAssocLeftLeg)
      ≠ comonadOmegaEvalCell (opCellExpr monadOmegaLeftUnitAssocRightLeg) :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 1 0) hmatrix)

/-- ★ The op'd `rightUnitAssoc` (`rightCounitCoassoc`) legs are DIFFERENT: `[[1,0,0],[0,1,0]]` vs
`[[0,1,0],[0,0,1]]`; entry `(0,0)` is `1` vs `0`. -/
theorem comonadOmegaMatSeparatesRightUnitAssoc :
    comonadOmegaEvalCell (opCellExpr monadOmegaRightUnitAssocLeftLeg)
      ≠ comonadOmegaEvalCell (opCellExpr monadOmegaRightUnitAssocRightLeg) :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-! # =========================================================================================
    # B3 — THE OP-DUAL OVER-QUOTIENT WITNESSES (shipped convertibility + transpose separation)
    # ========================================================================================= -/

/-- ★★ **THE COMONAD `counitCounit` OVER-QUOTIENT WITNESS.**  The op'd legs are convertible under the op'd base
relation `opCellRelOver monadOmegaBaseRel` (the shipped `comonadOmegaUnitUnitResolved.legsConvertible`, = the
generic `opConvWithId` transport of the monad's 3-cell) yet evaluate to DISTINCT comonad-model maps.  The pair
`(shipped-convertibility, transpose-separation)`. -/
theorem comonadOmegaBaseRelOverQuotientsUnitUnit :
    SaturatedConvOverWithId monadOmegaComputad (opCellRelOver monadOmegaBaseRel)
        (opCellExpr monadOmegaUnitUnitLeftLeg) (opCellExpr monadOmegaUnitUnitRightLeg)
      ∧ comonadOmegaEvalCell (opCellExpr monadOmegaUnitUnitLeftLeg)
        ≠ comonadOmegaEvalCell (opCellExpr monadOmegaUnitUnitRightLeg) :=
  ⟨comonadOmegaUnitUnitResolved.legsConvertible, comonadOmegaMatSeparatesUnitUnit⟩

/-- ★★ **THE COMONAD `leftCounitCoassoc` OVER-QUOTIENT WITNESS.** -/
theorem comonadOmegaBaseRelOverQuotientsLeftUnitAssoc :
    SaturatedConvOverWithId monadOmegaComputad (opCellRelOver monadOmegaBaseRel)
        (opCellExpr monadOmegaLeftUnitAssocLeftLeg) (opCellExpr monadOmegaLeftUnitAssocRightLeg)
      ∧ comonadOmegaEvalCell (opCellExpr monadOmegaLeftUnitAssocLeftLeg)
        ≠ comonadOmegaEvalCell (opCellExpr monadOmegaLeftUnitAssocRightLeg) :=
  ⟨comonadOmegaLeftUnitAssocResolved.legsConvertible, comonadOmegaMatSeparatesLeftUnitAssoc⟩

/-- ★★ **THE COMONAD `rightCounitCoassoc` OVER-QUOTIENT WITNESS.** -/
theorem comonadOmegaBaseRelOverQuotientsRightUnitAssoc :
    SaturatedConvOverWithId monadOmegaComputad (opCellRelOver monadOmegaBaseRel)
        (opCellExpr monadOmegaRightUnitAssocLeftLeg) (opCellExpr monadOmegaRightUnitAssocRightLeg)
      ∧ comonadOmegaEvalCell (opCellExpr monadOmegaRightUnitAssocLeftLeg)
        ≠ comonadOmegaEvalCell (opCellExpr monadOmegaRightUnitAssocRightLeg) :=
  ⟨comonadOmegaRightUnitAssocResolved.legsConvertible, comonadOmegaMatSeparatesRightUnitAssoc⟩

/-- ★★ **THE GENUINE COMONAD LAWS ARE MODELLED YET THE BARE ROW IS SEPARATED.**  The comonad model respects the
genuine coassociativity (`[[1],[1],[1]]` both legs) AND separates the `counitCounit` legs — so it is a SOUND
model of the genuine comonad that refutes the bare-whisker row.  The transpose of
`monadOmegaGenuineLawModelledRowSeparated`; the op-dual has NO braiding repair either (the comonad carries no
`sigma`). -/
theorem comonadOmegaGenuineLawRespectedRowSeparated :
    (comonadOmegaEvalCell (opCellExpr monadOmegaGenuineAssocLeftLeg)
        = comonadOmegaEvalCell (opCellExpr monadOmegaGenuineAssocRightLeg))
      ∧ (comonadOmegaEvalCell (opCellExpr monadOmegaUnitUnitLeftLeg)
        ≠ comonadOmegaEvalCell (opCellExpr monadOmegaUnitUnitRightLeg)) :=
  ⟨comonadOmegaMatrixRespectsGenuineCoassoc, comonadOmegaMatSeparatesUnitUnit⟩

/-! # =========================================================================================
    # B3 — THE VERDICT MARKERS + THE KZ / co-KZ FREE-RIDER CENSUS
    # ========================================================================================= -/

/-- ★★ **THE WALKING COMONAD OVER-QUOTIENTS ON THREE BARE-WHISKER ROWS — machine-transported.**  `= true`
records `comonadOmegaBaseRelOverQuotients{UnitUnit,LeftUnitAssoc,RightUnitAssoc}`: the op'd base relation
identifies the three op'd bare-whisker legs (`counitCounit` / `leftCounitCoassoc` / `rightCounitCoassoc`) that
the direct TRANSPOSE comonad model separates.  The over-quotient transports from the monad exactly as the r1
convertibility does — convertibility FREE (shipped `opConvWithId`), separation the transpose eval. -/
def fxOmegaHouseStyle_comonadOverQuotientConfirmedTransposeSeparated : Bool := true

/-- ★ **THE COMONAD TRANSPOSE MODEL IS SOUND ON THE GENUINE COMONAD LAWS.**  `= true` records
`comonadOmegaMatrixRespectsGenuine{Counit,CounitRight,Coassoc}` and
`comonadOmegaGenuineLawRespectedRowSeparated`: the direct comonad `Mat(N)` model (the natural transpose,
`delta = mu^T`, `eps = eta^T`) respects the op'd genuine comonad laws ON THE NOSE (`rfl`, both `[[1]]` / both
`[[1],[1],[1]]`) while separating the bare-whisker legs — so it is a legitimate sound separator, not a
label-blind accident.  This is the recon's variance adjudication (a DIRECT comonad eval, not the transported
monad eval). -/
def fxOmegaHouseStyle_comonadEvalSoundOnGenuineComonadLaws : Bool := true

/-- ★ **KZ / co-KZ RIDE THE MONAD / COMONAD (census free-rider caveat).**  `= true` records that the KZ
(lax-idempotent) and co-KZ walkers are the monad / comonad presentation with the directed 2-cell ordering
forgotten, so their bare-whisker over-quotient RIDES the monad / comonad over-quotient verbatim — no separate
transport is needed or performed.  A census free-rider entry, matching the r3
`fxOmega4_squierFamilyTwoGenuineOpDualsShippedR3` caveat (two genuine op-transports; KZ / co-KZ ride them). -/
def fxOmegaHouseStyle_kzCoKzRideMonadComonadFreeRiders : Bool := true

/-- ★ **WALL (honest) — the FULL comonad restored-soundness fold is the transpose-involutivity wall.**
`= false` records that lifting the comonad model's soundness from the specific genuine-law rows (the `rfl`
checks above) to a full `IsSaturatedCongruenceWithId` fold over `opCellRelOver MonadOmegaSoundRow` requires the
`op`-image inversion the `recInto` `ofRelation` arms need (casing `MonadOmegaSoundRow (op a) (op b)` against
the fixed genuine-law legs), the exact TRANSPOSE of the monad's finite-sum Fubini wall
(`fxOmegaHouseStyle_monadFullIsolationNeedsStrictLawFubiniKit`).  The over-quotient witnesses (convertibility +
separation + sound-on-the-rows) are shipped and decisive regardless; only the full fold is walled. -/
def fxOmegaHouseStyle_comonadFullSoundnessTransposeFubiniWalled : Bool := false

/-- ★ **ESTABLISHED (B3) — the comonad op-dual over-quotient adjudication.**  `= true` records the scoreboard:
the walking comonad over-quotients on its three bare-whisker rows (`counitCounit` / `leftCounitCoassoc` /
`rightCounitCoassoc`), each op'd-convertible (shipped `opConvWithId` transport) yet separated by the direct
transpose comonad model, which is SOUND on the genuine comonad laws (`rfl`); KZ / co-KZ ride the monad /
comonad as census free-riders; the full comonad restored-soundness fold is the NAMED transpose-involutivity
wall.  The op-dual transports cheaply — it does NOT defer. -/
def fxOmegaHouseStyle_comonadOpDualOverQuotientAdjudicationShipped : Bool := true

/-! ## The B3 truth-probe outputs (the transpose separations + the genuine-comonad-law model) -/

#eval (comonadOmegaEvalCell (opCellExpr monadOmegaUnitUnitLeftLeg)).entries
#eval (comonadOmegaEvalCell (opCellExpr monadOmegaUnitUnitRightLeg)).entries
#eval (comonadOmegaEvalCell (opCellExpr monadOmegaLeftUnitAssocLeftLeg)).entries
#eval (comonadOmegaEvalCell (opCellExpr monadOmegaLeftUnitAssocRightLeg)).entries
#eval (comonadOmegaEvalCell (opCellExpr monadOmegaGenuineAssocLeftLeg)).entries
#eval (comonadOmegaEvalCell (opCellExpr monadOmegaGenuineAssocRightLeg)).entries

end FX1Poly.Polygraph.Omega
