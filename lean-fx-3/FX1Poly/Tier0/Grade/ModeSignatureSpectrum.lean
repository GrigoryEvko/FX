import FX1Poly.Tier0.Grade.GradedSpectrum
import FX1Poly.Tier0.Mode.AdjointModeSignature

/-! # ModeSignatureSpectrum — wiring the Polygraph mode carrier INTO the grade↔mode spectrum

The v2 WIRING leaf: the maps FROM the Polygraph / MATT mode structures (`ModeSignature`,
`AdjointModeSignature.classOf`, `FibrancyKind`, `adjunctionModeSignature`) INTO the shipped
`GradedSpectrum` (`Tier0/Mode/GradedSpectrum.lean`), plus additive sharpenings of the v1 slice.

Everything here is a NEW declaration.  No shipped decl in `GradedSpectrum.lean` /
`FibrancyFeatures.lean` / `AdjointModeSignature.lean` is edited; the mode carrier
(`Polygraph/Computad`) is only READ, never redefined; NO fifth axis; fibrancy stays the ONE
`geometric` mode property.  Imports are only the two strictly-lower siblings (`GradedSpectrum`
+ `AdjointModeSignature`, which pulls `Polygraph/Computad/{Signature,AdjunctionSeed}`
transitively) — no `WalkingAdjunction/**`, no `Typed/*`.

## §7 rulings upheld (`grade-mode-spectrum.md` §7)

  * **§7.3** (mode axis = grade-of-grades; read the carrier, don't move it; no fifth axis):
    `spectrumOfAdjointEdge` / `richnessRungOfModeSignature` READ the shipped `classOf` API and
    finite-presentation evidence off a signature, lift into the shipped `GradedSpectrum`, and
    apply the shipped `rungOfSpectrum`.  No new judgment index / ω-category; carrier untouched.
  * **§7.2** (fibrancy is ONE mode property): `spectrumOfFibrancyKind` routes through the shipped
    `featuresOfFibrancyKind` into the single `geometric` field.
  * **§7.1** (grade = R1–R3 / mode = R4+, seam = decategorification): the centerpiece proves the
    SAME classifier separates a one-object semiring signature (grade band, R2) strictly below the
    walking-adjunction seed (mode band, R5); B4 proves the seam collapse is genuinely lossy.

Raw Lean 4 + Init, ASCII-only, propext-free (`rfl` / `by decide` / full-enum `cases`).
-/

namespace FX1Poly.Modal

/-- The **usage-grade rank** — `zero < one < omega` as a `Nat`.  (Declared under `FX1Poly.Modal`, the
home namespace of `UsageGrade`, so dot-projection `resource.rank` resolves.) -/
def UsageGrade.rank : UsageGrade → Nat
  | .zero => 0
  | .one => 1
  | .omega => 2

/-- The usage-grade rank is monotone along the usage order. -/
theorem UsageGrade.rank_le_of_le {lower upper : UsageGrade}
    (isBelow : lower.le upper = true) : lower.rank ≤ upper.rank := by
  cases lower <;> cases upper <;> revert isBelow <;> decide

end FX1Poly.Modal

namespace FX1Poly.Tier0
open FX1Poly.Modal
open FX1Poly.Polygraph

/-! ## PART A — wiring the Polygraph structures into the spectrum -/

/-! ### A0. A rung strict-order (`SpectrumRung` ships only `.next` + `DecidableEq`) -/

/-- The **rung rank** — the position of a rung on the R1–R7 ladder as a `Nat`. -/
def SpectrumRung.rank : SpectrumRung → Nat
  | .r1 => 0
  | .r2 => 1
  | .r3 => 2
  | .r4 => 3
  | .r5 => 4
  | .r6 => 5
  | .r7 => 6

/-- The **rung strict order** — `lower < upper` on the ladder, via `Nat.blt` on the rank. -/
def SpectrumRung.lt (lower upper : SpectrumRung) : Bool := Nat.blt lower.rank upper.rank

/-! ### A1. `spectrumOfAdjointEdge` — fold `AdjointClass` into the modal coordinate (mode-2 read) -/

/-- ★ The **MATT class of an adjoint-mode edge, lifted to a spectrum position** — the modal coordinate
only, every other coordinate `bottom`, so the shipped modal poles are hit on the nose (§7.2/§7.3).
Modal-only (NOT geometric-coupled) so `.left ↦ sinisterPole` and `.right ↦ tanglePole` land by `rfl`
(both poles are `{bottom with modal := …}`).  The geometric coupling already ships as `geometricOfModal`. -/
def spectrumOfAdjointEdge (signature : AdjointModeSignature)
    {sourceMode targetMode : signature.base.graph.Mode}
    (edge : signature.base.graph.Modality sourceMode targetMode) : GradedSpectrum :=
  { GradedSpectrum.bottom with modal := signature.classOf edge }

/-! ### A2. `spectrumOfFibrancyKind` — fold `FibrancyKind` into the geometric coordinate (φ read) -/

/-- ★ A **fibrancy mode → its geometric-coordinate position** (the φ property at higher resolution,
§7.2), routed through the shipped `featuresOfFibrancyKind` into the single `geometric` field. -/
def spectrumOfFibrancyKind (kind : FibrancyKind) : GradedSpectrum :=
  { GradedSpectrum.bottom with geometric := featuresOfFibrancyKind kind }

/-! ### A3. `richnessRungOfModeSignature` — the computational mode-2 rung certificate

`Mode : Type` carries no `Fintype`; `twoCell : … → Type` inhabitation is undecidable — so the three
§1 richness dials (objects × 1-cell-algebra × dimension) are threaded as decidable evidence per
signature (the honest, recon-confirmed gap-closure: Mode-cardinality and twoCell-inhabitation are not
readable off the bare carrier). -/

/-- Finite-presentation richness evidence (`grade-mode-spectrum.md` §1: richness = objects ×
1-cell-algebra × categorical dimension).  Supplied per signature because Mode-cardinality and
twoCell-inhabitation are not readable off the bare carrier. -/
structure ModeSignatureRichness (signature : ModeSignature) where
  /-- `|Mode|` — the object count. -/
  modeCount : Nat
  /-- Is a non-identity 1-cell present (the 1-cell algebra)? -/
  hasGeneratingModality : Bool
  /-- Is the twoCell family inhabited (the categorical dimension)? -/
  hasGeneratingTwoCell : Bool

/-- ★ The **rung read-off** (total, full-enum, propext-free).  One object ⇒ grade band R1–R3
(2-cells ⇒ R3, endo-1-cell ⇒ R2, else R1); many objects ⇒ mode band R4/R5 (2-cells / adjoint
strings ⇒ R5).  R6/R7 need ω / self-index — unreachable from a finite presentation (documented cap
at R5). -/
def richnessRungOfModeSignature (signature : ModeSignature)
    (richness : ModeSignatureRichness signature) : SpectrumRung :=
  match Nat.ble richness.modeCount 1 with
  | true =>
    match richness.hasGeneratingTwoCell with
    | true => .r3
    | false =>
      match richness.hasGeneratingModality with
      | true => .r2
      | false => .r1
  | false =>
    match richness.hasGeneratingTwoCell with
    | true => .r5
    | false => .r4

/-! ### A4. Evidence for the shipped seed + a one-object semiring signature -/

/-- The **walking-adjunction seed** richness: 2 modes (base, tip), left/right generators, unit+counit
2-cells inhabited ⇒ rung R5. -/
def adjunctionSeedRichness : ModeSignatureRichness adjunctionModeSignature := ⟨2, true, true⟩

/-- A genuine **single-object semiring** mode: one object `carrier`. -/
inductive SemiringMode where
  /-- The single carrier object. -/
  | carrier
  deriving DecidableEq

/-- The **single-object semiring** 1-cell generators: one endo-generator (the product). -/
inductive SemiringModality : SemiringMode → SemiringMode → Type where
  /-- The multiplication endo-generator `carrier ⟶ carrier`. -/
  | multiply : SemiringModality .carrier .carrier

/-- The single-object semiring quiver: one object, one endo-generator. -/
def semiringModeGraph : ModeGraph := { Mode := SemiringMode, Modality := SemiringModality }

/-- The **single-object semiring signature** — one object, one endo-generator, no 2-cells. -/
def singleObjectSemiringSignature : ModeSignature :=
  { graph := semiringModeGraph, twoCell := fun _ _ => Empty }

/-- The single-object semiring richness: one object, one endo-generator, no 2-cells ⇒ rung R2. -/
def singleObjectSemiringRichness : ModeSignatureRichness singleObjectSemiringSignature :=
  ⟨1, true, false⟩

/-! ### A5. The adjunction seed as ONE spectrum point (signature → richness → rung → position) -/

/-- ★ The **adjunction seed as one spectrum position** — signature ↦ richness ↦ rung ↦ diagonal
point (`rungPos r5`). -/
def spectrumOfAdjunctionSeed : GradedSpectrum :=
  rungPos (richnessRungOfModeSignature adjunctionModeSignature adjunctionSeedRichness)

/-! ### Pole-landing theorems -/

/-- `left` (sinister) lifts to the sinister pole. -/
theorem spectrumOfAdjointEdge_adjunctionLeft :
    spectrumOfAdjointEdge adjunctionAdjointModeSignature AdjunctionModality.left = sinisterPole := rfl

/-- `right` (tangible) lifts to the tangible pole. -/
theorem spectrumOfAdjointEdge_adjunctionRight :
    spectrumOfAdjointEdge adjunctionAdjointModeSignature AdjunctionModality.right = tanglePole := rfl

/-- The fibrancy inclusion `ι` (sinister) lifts to the sinister pole. -/
theorem spectrumOfAdjointEdge_fibrancyInclusion :
    spectrumOfAdjointEdge fibrancyAdjointModeSignature FibrancyModalityAdj.inclusion = sinisterPole := rfl

/-- The fibrancy right adjoint `ι†` (tangible) lifts to the tangible pole. -/
theorem spectrumOfAdjointEdge_fibrancyInclusionAdj :
    spectrumOfAdjointEdge fibrancyAdjointModeSignature FibrancyModalityAdj.inclusionAdj = tanglePole := rfl

/-- The fibrant mode's φ-position is the groupoidal pole. -/
theorem spectrumOfFibrancyKind_fibrant :
    spectrumOfFibrancyKind FibrancyKind.fibrant = groupoidalPole := rfl

/-- The exotype mode's φ-position is the strict pole. -/
theorem spectrumOfFibrancyKind_exotype :
    spectrumOfFibrancyKind FibrancyKind.exotype = strictPole := rfl

/-- The adjunction-seed position classifies back to R5. -/
theorem rungOfSpectrum_adjunctionSeed :
    rungOfSpectrum spectrumOfAdjunctionSeed = SpectrumRung.r5 :=
  rungOfSpectrum_rungPos SpectrumRung.r5

/-- The adjunction-seed richness reads off as R5. -/
theorem adjunctionSeed_richnessRung_r5 :
    richnessRungOfModeSignature adjunctionModeSignature adjunctionSeedRichness = SpectrumRung.r5 := rfl

/-- The single-object semiring richness reads off as R2. -/
theorem singleObjectSemiring_richnessRung_r2 :
    richnessRungOfModeSignature singleObjectSemiringSignature singleObjectSemiringRichness
      = SpectrumRung.r2 := rfl

/-! ### ★★★ CENTERPIECE — the R2 < R5 crossover made computational -/

/-- ★★★ The **grade→mode crossover as a theorem**: the SAME classifier `richnessRungOfModeSignature`
sends a one-object semiring signature (grade band, R2 — "how much") strictly below the
walking-adjunction seed (mode band, R5 — adjoint strings).  `grade-mode-spectrum.md` §7.1's grade/mode
seam and §1's "R3→R4: one object becomes many; grade becomes mode; quantity becoming place", executable
over the shipped `adjunctionModeSignature` carrier.  Reduces: LHS `r2` (rank 1), RHS `r5` (rank 4),
`Nat.blt 1 4 = true`. -/
theorem crossover_semiring_strictly_below_adjunctionSeed :
    SpectrumRung.lt
      (richnessRungOfModeSignature singleObjectSemiringSignature singleObjectSemiringRichness)
      (richnessRungOfModeSignature adjunctionModeSignature adjunctionSeedRichness) = true := by decide

/-! ## PART B — additive sharpenings of the v1 slice -/

/-! ### Bool-conjunction elimination helpers (propext-free; `&&` is left-associative) -/

/-- From `(x && y) = true`, the left conjunct is `true`.  Manual (avoids `Bool.and_eq_true`, a
`Prop = Prop` equality that would pull `propext`). -/
private theorem boolAndElimLeft {leftFlag rightFlag : Bool}
    (bothHold : (leftFlag && rightFlag) = true) : leftFlag = true := by
  cases leftFlag with
  | true => rfl
  | false => exact Bool.noConfusion bothHold

/-- From `(x && y) = true`, the right conjunct is `true`. -/
private theorem boolAndElimRight {leftFlag rightFlag : Bool}
    (bothHold : (leftFlag && rightFlag) = true) : rightFlag = true := by
  cases leftFlag with
  | true => exact bothHold
  | false => exact Bool.noConfusion bothHold

/-! ### B1. Coordinate-computed richness gradient — resolves the "accumulate character" caveat -/

/-- The **character count** of a φ-cube point — how many of the three fibrancy characters it carries. -/
def FibrancyFeatures.characterCount (features : FibrancyFeatures) : Nat :=
  Bool.toNat features.hasInvertibility + Bool.toNat features.hasDirection
    + Bool.toNat features.hasRelationality

/-- The **AdjointClass fan rank** — the ambient `tangible` is `0`; the three distinguished atoms are
`1` each (they are incomparable, so the rank collapses their fan to one level above the bottom). -/
def AdjointClass.fanRank : AdjointClass → Nat
  | .tangible => 0
  | .sharp => 1
  | .transparent => 1
  | .sinister => 1

/-- ★ The **numeric richness** of a spectrum position — the sum of the six coordinate ranks.  The
scalar shadow of the product position (`grade-mode-spectrum.md` §6.4). -/
def GradedSpectrum.richnessOf (position : GradedSpectrum) : Nat :=
  position.geometric.characterCount + position.size + position.depth
    + position.resource.rank + position.modal.fanRank + position.epistemic.rank

/-- The φ character count is monotone along the cube order (64-arm full enumeration). -/
theorem FibrancyFeatures.characterCount_le_of_le {lower upper : FibrancyFeatures}
    (isBelow : lower.le upper = true) : lower.characterCount ≤ upper.characterCount := by
  obtain ⟨lowInv, lowDir, lowRel⟩ := lower
  obtain ⟨upInv, upDir, upRel⟩ := upper
  cases lowInv <;> cases lowDir <;> cases lowRel <;>
    cases upInv <;> cases upDir <;> cases upRel <;> revert isBelow <;> decide

/-- The AdjointClass fan rank is monotone along the fan order. -/
theorem AdjointClass.fanRank_le_of_le {lower upper : AdjointClass}
    (isBelow : lower.le upper = true) : lower.fanRank ≤ upper.fanRank := by
  cases lower <;> cases upper <;> revert isBelow <;> decide

/-- ★ THE tie: any `le`-ascending chain is richness-non-decreasing — the accumulate caveat as a
theorem (the sum of the six coordinate monotonicities). -/
theorem GradedSpectrum.richnessOf_monotone {lower upper : GradedSpectrum}
    (isBelow : lower.le upper = true) : lower.richnessOf ≤ upper.richnessOf := by
  dsimp only [GradedSpectrum.le] at isBelow
  have epiLe := boolAndElimRight isBelow
  have rest5 := boolAndElimLeft isBelow
  have modalLe := boolAndElimRight rest5
  have rest4 := boolAndElimLeft rest5
  have resLe := boolAndElimRight rest4
  have rest3 := boolAndElimLeft rest4
  have depthLe := boolAndElimRight rest3
  have rest2 := boolAndElimLeft rest3
  have sizeLe := boolAndElimRight rest2
  have geoLe := boolAndElimLeft rest2
  dsimp only [GradedSpectrum.richnessOf]
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (FibrancyFeatures.characterCount_le_of_le geoLe)
            (Nat.le_of_ble_eq_true sizeLe))
          (Nat.le_of_ble_eq_true depthLe))
        (UsageGrade.rank_le_of_le resLe))
      (AdjointClass.fanRank_le_of_le modalLe))
    (Nat.le_of_ble_eq_true epiLe)

/-- ★ The diagonal is a STRICT numeric gradient (upgrades `monotone_rungs` from `le`-only). -/
theorem richnessOf_rungPos_strictMono (rung : SpectrumRung) (isNotTop : rung ≠ SpectrumRung.r7) :
    (rungPos rung).richnessOf < (rungPos rung.next).richnessOf := by
  cases rung <;> first | decide | exact absurd rfl isNotTop

/-! ### B2. `geometricOfModal` is an ORDER EMBEDDING -/

/-- The φ image of the MATT MODE row is an order embedding: `featuresOfAdjointClass` reflects the fan
order into the cube order on the nose (16-case). -/
theorem featuresOfAdjointClass_le_iff (lower upper : AdjointClass) :
    FibrancyFeatures.le (featuresOfAdjointClass lower) (featuresOfAdjointClass upper)
      = AdjointClass.le lower upper := by
  cases lower <;> cases upper <;> decide

/-- `geometricOfModal` is an order embedding — its φ-coordinate `le` equals the fan order. -/
theorem geometricOfModal_le_iff (lower upper : AdjointClass) :
    (geometricOfModal lower).le (geometricOfModal upper) = AdjointClass.le lower upper := by
  cases lower <;> cases upper <;> decide

/-! ### B3. The R3→R4 crossover as a coordinate theorem -/

/-- The **R3→R4 crossover** carried by BOTH the geometric bit gaining `hasDirection` AND the modal
coordinate flipping `tangible → sinister` (`grade-mode-spectrum.md` §1: quantity becoming place). -/
theorem crossover_r3_r4 :
    (rungPos SpectrumRung.r3).geometric.hasDirection = false
      ∧ (rungPos SpectrumRung.r4).geometric.hasDirection = true
      ∧ (rungPos SpectrumRung.r3).modal.isSinister = false
      ∧ (rungPos SpectrumRung.r4).modal.isSinister = true := by decide

/-! ### B4. Decategorification is lossy — `rungOfSpectrum` non-injective -/

/-- The cross-family interior `interiorBlend` classifies to R2 (its resource is `one`). -/
theorem rungOfSpectrum_interiorBlend : rungOfSpectrum interiorBlend = SpectrumRung.r2 := by decide

/-- ★ **The decategorification shadow is lossy** — `rungOfSpectrum` is NOT injective: the shipped
interior `interiorBlend` and the diagonal point `rungPos r2` share the rung R2 yet differ (§6/§7.3
"grade = π₀(mode)" has non-trivial fibers). -/
theorem rungOfSpectrum_not_injective :
    ∃ lower upper, rungOfSpectrum lower = rungOfSpectrum upper ∧ lower ≠ upper :=
  ⟨interiorBlend, rungPos SpectrumRung.r2, by decide, by decide⟩

/-! ### B5. Extremal `bottom` uniqueness -/

/-- ★ **`bottom` is the unique minimum** — anything below `bottom` equals `bottom` (from the shipped
`le_antisymm` + `bottom_le`). -/
theorem GradedSpectrum.bottom_unique {position : GradedSpectrum}
    (isBelowBottom : position.le GradedSpectrum.bottom = true) : position = GradedSpectrum.bottom :=
  GradedSpectrum.le_antisymm isBelowBottom (GradedSpectrum.bottom_le position)

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the Polygraph → spectrum wiring ships, genuinely inhabited.**  The maps FROM
the mode carrier (`spectrumOfAdjointEdge` reading `AdjointModeSignature.classOf`,
`spectrumOfFibrancyKind` reading `featuresOfFibrancyKind`, `richnessRungOfModeSignature` reading
finite-presentation evidence) land the shipped modal / φ poles by `rfl`, and the CENTERPIECE
`crossover_semiring_strictly_below_adjunctionSeed` proves the SAME classifier separates a one-object
semiring signature (R2, grade) strictly below the walking-adjunction seed (R5, mode) over the real
`adjunctionModeSignature` carrier.  Additive v1 sharpenings: the strict numeric richness gradient
(`richnessOf_rungPos_strictMono`), the `geometricOfModal` order embedding, the R3→R4 crossover, the
lossy-decategorification non-injectivity, and `bottom` uniqueness.  `= true`. -/
def fxMode_hasSpectrumPolygraphWiring : Bool := true

end FX1Poly.Tier0
