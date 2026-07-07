import FX1Poly.Polygraph.Computad.ModeComputad
import FX1Poly.Tier0.Mode.ModeSignatureSpectrum

/-! # Tier0/Mode/ModeComputadRichness — carrier-computed richness from a finite `ModeComputad`

The v2 slice (`ModeSignatureSpectrum.lean` A3) threaded richness as hand-supplied
`ModeSignatureRichness` evidence because the semantic `ModeSignature` carrier is not finitely readable.
This leaf reads the SAME rung classifier off the FINITE `ModeComputad` carrier — `rungOfComputad` matches
directly on `modeCount` (`Nat.ble modeCount 1` is the grade / mode band split) and on the two generator
`List`s.  It then lands positions in the shipped `GradedSpectrum` (`richnessOfComputad := rungPos o
rungOfComputad`) and proves:

  * the CROSSOVER carrier-computed — the same classifier sends the one-object semiring computad (grade
    band, R2) strictly below the two-object adjunction computad (mode band, R5), the decision reading
    `modeCount 1 vs 2`;
  * the GAP-CLOSURE — the carrier-computed richness EQUALS the v2 hand-supplied evidence
    (`adjunctionSeedRichness` / `singleObjectSemiringRichness`), so the threaded evidence was the
    computad's computed richness all along.

No shipped decl is edited; the mode carrier is only READ; no fifth axis; fibrancy stays the ONE
`geometric` property.  This supersedes the evidence-threaded crossover
(`crossover_semiring_strictly_below_adjunctionSeed`) with a carrier-computed one; the genuine
`spectrumOfAdjointEdge` / `spectrumOfFibrancyKind` maps stay intact.  Raw Lean 4 + Init, propext-free
(full-enum matches; `rfl` where definitional; `Nat.blt`-decidable `by decide` only over `Nat` / `Bool`).
-/

namespace FX1Poly.Tier0
open FX1Poly.Polygraph

/-! ## The carrier-computed rung classifier -/

/-- The **rung read-off from the finite carrier** (total, full-enum, propext-free).  ONE object
(`Nat.ble modeCount 1`) => grade band R1-R3 (2-generators => R3, a 1-generator => R2, else R1); MANY
objects => mode band R4/R5 (2-generators / adjoint strings => R5, else R4).  This is the exact analogue of
the v2 `richnessRungOfModeSignature`, but reading the carrier's `List`s instead of threaded evidence. -/
def rungOfComputad (computad : ModeComputad) : SpectrumRung :=
  match Nat.ble computad.modeCount 1 with
  | true =>
    match computad.twoCellGenerators with
    | _ :: _ => .r3
    | [] =>
      match computad.modalityGenerators with
      | _ :: _ => .r2
      | [] => .r1
  | false =>
    match computad.twoCellGenerators with
    | _ :: _ => .r5
    | [] => .r4

/-- The **carrier-computed richness position** — the finite computad's rung, landed on the shipped
`GradedSpectrum` rung diagonal.  Reads `modeCount` + generator-list lengths; lands as a `GradedSpectrum`
position. -/
def richnessOfComputad (computad : ModeComputad) : GradedSpectrum :=
  rungPos (rungOfComputad computad)

/-- The **scalar richness** of a computad — the numeric shadow of its position
(`GradedSpectrum.richnessOf` of the landed rung).  Monotone: a higher rung is a strictly larger scalar. -/
def richnessScalarOfComputad (computad : ModeComputad) : Nat :=
  (richnessOfComputad computad).richnessOf

/-- The landed position classifies back to the rung it came from (`rungOfSpectrum o richnessOfComputad =
rungOfComputad`), via the shipped `rungOfSpectrum_rungPos`. -/
theorem rungOfSpectrum_richnessOfComputad (computad : ModeComputad) :
    rungOfSpectrum (richnessOfComputad computad) = rungOfComputad computad :=
  rungOfSpectrum_rungPos (rungOfComputad computad)

/-! ## The concrete rung read-offs -/

/-- The single-object semiring computad reads off as R2 (one object, one endo-generator, no 2-cells). -/
theorem singleObjectSemiringComputad_rung_r2 :
    rungOfComputad singleObjectSemiringComputad = SpectrumRung.r2 := rfl

/-- The adjunction computad reads off as R5 (two objects, generators, unit/counit 2-cells). -/
theorem adjunctionComputad_rung_r5 :
    rungOfComputad adjunctionComputad = SpectrumRung.r5 := rfl

/-! ## ★★★ CENTERPIECE — the crossover, CARRIER-COMPUTED, reading modeCount 1 vs 2 -/

/-- ★★★ The **grade->mode crossover as a carrier-computed theorem**: the SAME classifier `rungOfComputad`
sends the one-object semiring computad (grade band, R2) strictly below the two-object adjunction computad
(mode band, R5).  Unlike the v2 centerpiece (which read threaded evidence), this reads the FINITE carrier —
the `modeCount 1 vs 2` decision IS the grade->mode seam.  Reduces: LHS `r2` (rank 1), RHS `r5` (rank 4),
`Nat.blt 1 4 = true`. -/
theorem crossover_computad_semiring_below_adjunction :
    SpectrumRung.lt
      (rungOfComputad singleObjectSemiringComputad)
      (rungOfComputad adjunctionComputad) = true := by decide

/-- The crossover DECISION is literally the modeCount read: the semiring computad's `modeCount` puts it in
the grade band (`Nat.ble modeCount 1 = true`), the adjunction's puts it in the mode band (`= false`). -/
theorem crossover_reads_modeCount :
    Nat.ble singleObjectSemiringComputad.modeCount 1 = true
      ∧ Nat.ble adjunctionComputad.modeCount 1 = false :=
  ⟨rfl, rfl⟩

/-- The scalar richness strictly increases across the crossover too. -/
theorem crossover_computad_scalar_strictMono :
    richnessScalarOfComputad singleObjectSemiringComputad
      < richnessScalarOfComputad adjunctionComputad := by decide

/-! ## The GAP-CLOSURE — carrier-computed richness EQUALS the v2 threaded evidence -/

/-- ★ **Gap-closure, adjunction**: the carrier-computed rung equals the rung the v2 slice obtained from the
HAND-SUPPLIED `adjunctionSeedRichness` evidence.  The threaded evidence was the computad's computed richness
all along. -/
theorem adjunctionComputad_matches_evidence :
    rungOfComputad adjunctionComputad
      = richnessRungOfModeSignature adjunctionModeSignature adjunctionSeedRichness := rfl

/-- ★ **Gap-closure, semiring**: the same, for the single-object case vs `singleObjectSemiringRichness`. -/
theorem singleObjectSemiringComputad_matches_evidence :
    rungOfComputad singleObjectSemiringComputad
      = richnessRungOfModeSignature singleObjectSemiringSignature singleObjectSemiringRichness := rfl

/-- ★ **The evidence triple is now COMPUTED** — the `(modeCount, hasGeneratingModality,
hasGeneratingTwoCell)` that `adjunctionSeedRichness` hand-supplied is exactly
`adjunctionComputad.richnessEvidence`. -/
theorem adjunctionComputad_richnessEvidence_matches :
    adjunctionComputad.richnessEvidence
      = (adjunctionSeedRichness.modeCount,
         adjunctionSeedRichness.hasGeneratingModality,
         adjunctionSeedRichness.hasGeneratingTwoCell) := rfl

/-! ## Honesty marker -/

/-- ★ **Honesty marker — richness is now CARRIER-COMPUTED from the finite `ModeComputad`.**
`rungOfComputad` reads `modeCount` + generator-list lengths; `richnessOfComputad` lands on the shipped
`GradedSpectrum` diagonal; the CENTERPIECE `crossover_computad_semiring_below_adjunction` proves R2 < R5
over the finite carrier with the decision reading `modeCount 1 vs 2`; and the GAP-CLOSURE theorems prove
the computed richness EQUALS the v2 hand-supplied evidence.  `= true`. -/
def fxMode_hasComputadRichness : Bool := true

end FX1Poly.Tier0
