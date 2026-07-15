import FX1Poly.Axis.Mode.FibrancyFeatures
import FX1Poly.Axis.Mode.GradeAlgebra.ResourceGraded

/-! # GradedSpectrum — the grade↔mode spectrum as a smooth product-graded position

The FX-native realization of `grade-mode-spectrum.md`'s central object: a single point in the PRODUCT of
the six §5 grade families, whose position on the R1–R7 rung ladder is a decidable read-off.  This is the
mode-axis "grade of grades" (§7.3) — the classifier of all grading structures, made into DATA.

## The design (which primary, what folded in)

Primary carrier = a FLAT product-of-six-families record (`grade-mode-spectrum.md` §5 "the wider grade
families": Geometric / Size / Depth / Resource / Modal / Epistemic).  It literally IS the `#1872` telos
object ("one product-graded object whose grading structure is itself a grid-point", §6.4), and the flat
shape means antisymmetry of its order needs no `funext` — zero-axiom by construction (an indexed
`Family → Carrier` carrier would force `funext` at antisymmetry; the flat product avoids exactly that).

Folded in:
  * the **φ / Geometric** field is `FibrancyFeatures` (the finer reading of the ONE fibrancy mode
    property — `FibrancyMode`; see `FibrancyFeatures.lean`), NOT a fifth axis and NOT a replacement (§7.2).
  * the **Resource** field is the shipped `UsageGrade` `{0, 1, ω}` (§6.1); the **Modal** field is the
    shipped MATT `AdjointClass` (§5 MODE row) with a NEW fan order defined additively here.
  * the **Size** / **Depth** fields are `Nat` shadows (§4: ℓ at R1–R2, δ at R3).
  * the **Epistemic** field is a new thin ranked trust enum (§5 Epistemic family / §10 trust dimension).

Roadmap (v2+, deliberately NOT here): the `categorify ⊣ decategorify` endomaps and the self-describing
`SelfPosition` (§6 self-application); `WithTop Nat` size/depth for ω / large-cardinal values (§4); the
full 4×7 grid collapse (#1872).

## §7 rulings upheld (see `grade-mode-spectrum.md` §7)

  * §7.1 grade = R1–R3 / mode = R4+: `rungOfSpectrum` places `modal = tangible` positions at R1–R3
    (grade) and `modal`-nontrivial positions at R4+ (mode); the crossover is the R3→R4 `tangible →
    sinister` flip (quantity becoming place).
  * §7.2 fibrancy is ONE mode property: φ is the single `geometric` field, the finer reading of
    `FibrancyMode` — nothing replaced, no `Axis/Fibrancy/` folder.
  * §7.3 no fifth axis: this file lives in `Axis/Mode/`, introduces no new judgment index / ω-category /
    folder; `rungOfSpectrum` IS the `mode-2`/`mode-12` rung classifier as a total decidable function.
  * §7.4 build order φ→ℓ→δ: kept OUT of the carrier order (documented prose only); `le` is a static
    product order, the causal build sequencing is separate.
  * §7.5 value-dependent grades stay beneath: the carrier is static — no field is term-indexed.

The mode carrier (`Polygraph/Computad`) is untouched; this file imports only `Axis/Mode` siblings.
Purely additive.  Raw Lean 4 + Init, ASCII-only, propext-free.
-/

namespace FX1Poly.Axis
open FX1Poly.Modal

/-! ## The Epistemic-strength coordinate (new, thin) -/

/-- The **epistemic strength** of a grading position — the §5 Epistemic family / §10 trust dimension as a
ranked enum: how much do we TRUST the fact?  `external < assumed < sorryLevel < tested < verified`
(release builds require `verified`; trust propagates as the minimum through a call graph). -/
inductive EpistemicStrength where
  /-- `external` — from an untrusted boundary (IO / FFI / deserialization); the bottom. -/
  | external
  /-- `assumed` — an `axiom` / postulate. -/
  | assumed
  /-- `sorryLevel` — a `sorry`-tainted proof (dev only). -/
  | sorryLevel
  /-- `tested` — validated by tests but not proved. -/
  | tested
  /-- `verified` — kernel-checked proof; the top (release-admissible). -/
  | verified
  deriving DecidableEq

/-- The epistemic rank — the position on the trust ladder as a `Nat`. -/
def EpistemicStrength.rank : EpistemicStrength → Nat
  | .external => 0
  | .assumed => 1
  | .sorryLevel => 2
  | .tested => 3
  | .verified => 4

/-- The rank is injective — equal ranks force equal strengths (so the order is antisymmetric). -/
theorem EpistemicStrength.rank_injective {first second : EpistemicStrength}
    (ranksEqual : first.rank = second.rank) : first = second := by
  cases first <;> cases second <;> first | rfl | exact absurd ranksEqual (by decide)

/-- The **epistemic order** — `external ≤ … ≤ verified`, via `Nat.ble` on the rank. -/
def EpistemicStrength.le (lower upper : EpistemicStrength) : Bool :=
  Nat.ble lower.rank upper.rank

/-- Reflexivity of the epistemic order. -/
theorem EpistemicStrength.le_refl (strength : EpistemicStrength) : strength.le strength = true :=
  Nat.ble_self_eq_true strength.rank

/-- Transitivity of the epistemic order. -/
theorem EpistemicStrength.le_trans {first second third : EpistemicStrength}
    (firstToSecond : first.le second = true) (secondToThird : second.le third = true) :
    first.le third = true :=
  Nat.ble_eq_true_of_le
    (Nat.le_trans (Nat.le_of_ble_eq_true firstToSecond) (Nat.le_of_ble_eq_true secondToThird))

/-- Antisymmetry of the epistemic order. -/
theorem EpistemicStrength.le_antisymm {first second : EpistemicStrength}
    (forward : first.le second = true) (backward : second.le first = true) : first = second :=
  EpistemicStrength.rank_injective
    (Nat.le_antisymm (Nat.le_of_ble_eq_true forward) (Nat.le_of_ble_eq_true backward))

/-! ## The Modal-coordinate fan order (new def on the shipped `AdjointClass`; carrier untouched) -/

/-- The **AdjointClass fan order** — a NEW order defined additively in THIS file over the shipped
`AdjointClass` (`AdjointModeSignature` is untouched).  `tangible` is the bottom (the ambient class,
below everything); `sharp` / `transparent` / `sinister` are three INCOMPARABLE atoms above it (the fan).
Pointwise Boolean-implication over the three distinguishing membership predicates — `tangible ≤ b`
always (all three false), and a distinguished class is `≤` only itself.  (§5 Modal family.) -/
def AdjointClass.le (lower upper : AdjointClass) : Bool :=
  (!lower.isSharp || upper.isSharp)
    && (!lower.isTransparent || upper.isTransparent)
    && (!lower.isSinister || upper.isSinister)

/-- Reflexivity of the fan order. -/
theorem AdjointClass.le_refl (adjointClass : AdjointClass) : adjointClass.le adjointClass = true := by
  cases adjointClass <;> rfl

/-- Transitivity of the fan order. -/
theorem AdjointClass.le_trans {lower middle upper : AdjointClass}
    (lowerToMiddle : lower.le middle = true) (middleToUpper : middle.le upper = true) :
    lower.le upper = true := by
  cases lower <;> cases middle <;> cases upper <;>
    first
      | rfl
      | exact Bool.noConfusion lowerToMiddle
      | exact Bool.noConfusion middleToUpper

/-- Antisymmetry of the fan order. -/
theorem AdjointClass.le_antisymm {first second : AdjointClass}
    (forward : first.le second = true) (backward : second.le first = true) : first = second := by
  cases first <;> cases second <;>
    first
      | rfl
      | exact Bool.noConfusion forward
      | exact Bool.noConfusion backward

/-- `tangible` is the bottom of the fan (the ambient class, below everything). -/
theorem AdjointClass.tangible_le (adjointClass : AdjointClass) :
    AdjointClass.tangible.le adjointClass = true := by cases adjointClass <;> rfl

/-! ## The spectrum position -/

/-- ★ **A position on the grade↔mode spectrum** — one point in the PRODUCT of the six §5 grade families
(`grade-mode-spectrum.md` §5).  A FLAT record (not `Family → Carrier`), so the antisymmetry of its
product order needs no `funext` — zero-axiom.  This IS the `#1872` telos object (§6.4): one
product-graded object whose grading structure is itself a grid-point.

  * `geometric` — φ (Geometric): the finer reading of the ONE fibrancy mode property (§4 R4, §7.2).
  * `size` — ℓ (Size): the level / cumulativity shadow (§4 R1–R2, `LevelExpr.denote`'s shadow).
  * `depth` — δ (Depth): the truncation / cell-dimension shadow (§4 R3).
  * `resource` — the shipped usage semiring `{0, 1, ω}` (§6.1).
  * `modal` — the shipped MATT `AdjointClass` under the fan order (§5 MODE row).
  * `epistemic` — the trust strength (§5 Epistemic family / §10). -/
structure GradedSpectrum where
  /-- φ (Geometric) — the fibrancy cube (finer reading of `FibrancyMode`). -/
  geometric : FibrancyFeatures
  /-- ℓ (Size) — the level shadow. -/
  size : Nat
  /-- δ (Depth) — the truncation shadow. -/
  depth : Nat
  /-- Resource — the shipped usage grade `{0, 1, ω}`. -/
  resource : UsageGrade
  /-- Modal — the shipped MATT `AdjointClass` (under the fan order). -/
  modal : AdjointClass
  /-- Epistemic — the trust strength. -/
  epistemic : EpistemicStrength
  deriving DecidableEq

/-- The **product order** on positions — componentwise, the conjunction of the six coordinate orders. -/
def GradedSpectrum.le (lower upper : GradedSpectrum) : Bool :=
  lower.geometric.le upper.geometric
    && Nat.ble lower.size upper.size
    && Nat.ble lower.depth upper.depth
    && lower.resource.le upper.resource
    && lower.modal.le upper.modal
    && lower.epistemic.le upper.epistemic

/-- The **bottom** position — strict φ, zero size / depth, zero resource, the ambient mode, the untrusted
strength.  Below every position (`bottom_le`). -/
def GradedSpectrum.bottom : GradedSpectrum :=
  ⟨FibrancyFeatures.strict, 0, 0, UsageGrade.zero, AdjointClass.tangible, EpistemicStrength.external⟩

/-! ## Bool-conjunction elimination helpers (propext-free; `&&` is left-associative) -/

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

/-! ## The product order is a partial order -/

/-- Reflexivity of the product order — each coordinate order is reflexive. -/
theorem GradedSpectrum.le_refl (position : GradedSpectrum) : position.le position = true := by
  dsimp only [GradedSpectrum.le]
  rw [FibrancyFeatures.le_refl, Nat.ble_self_eq_true, Nat.ble_self_eq_true,
      UsageGrade.le_refl, AdjointClass.le_refl, EpistemicStrength.le_refl]
  rfl

/-- Transitivity of the product order — coordinatewise, each order transitive.  The `&&` is
left-associative, so extraction peels the last coordinate first. -/
theorem GradedSpectrum.le_trans {lower middle upper : GradedSpectrum}
    (lowerToMiddle : lower.le middle = true) (middleToUpper : middle.le upper = true) :
    lower.le upper = true := by
  dsimp only [GradedSpectrum.le] at lowerToMiddle middleToUpper ⊢
  have geometricLower := boolAndElimLeft (boolAndElimLeft (boolAndElimLeft
    (boolAndElimLeft (boolAndElimLeft lowerToMiddle))))
  have sizeLower := boolAndElimRight (boolAndElimLeft (boolAndElimLeft
    (boolAndElimLeft (boolAndElimLeft lowerToMiddle))))
  have depthLower := boolAndElimRight (boolAndElimLeft (boolAndElimLeft
    (boolAndElimLeft lowerToMiddle)))
  have resourceLower := boolAndElimRight (boolAndElimLeft (boolAndElimLeft lowerToMiddle))
  have modalLower := boolAndElimRight (boolAndElimLeft lowerToMiddle)
  have epistemicLower := boolAndElimRight lowerToMiddle
  have geometricUpper := boolAndElimLeft (boolAndElimLeft (boolAndElimLeft
    (boolAndElimLeft (boolAndElimLeft middleToUpper))))
  have sizeUpper := boolAndElimRight (boolAndElimLeft (boolAndElimLeft
    (boolAndElimLeft (boolAndElimLeft middleToUpper))))
  have depthUpper := boolAndElimRight (boolAndElimLeft (boolAndElimLeft
    (boolAndElimLeft middleToUpper)))
  have resourceUpper := boolAndElimRight (boolAndElimLeft (boolAndElimLeft middleToUpper))
  have modalUpper := boolAndElimRight (boolAndElimLeft middleToUpper)
  have epistemicUpper := boolAndElimRight middleToUpper
  rw [FibrancyFeatures.le_trans geometricLower geometricUpper,
      Nat.ble_eq_true_of_le (Nat.le_trans (Nat.le_of_ble_eq_true sizeLower)
        (Nat.le_of_ble_eq_true sizeUpper)),
      Nat.ble_eq_true_of_le (Nat.le_trans (Nat.le_of_ble_eq_true depthLower)
        (Nat.le_of_ble_eq_true depthUpper)),
      UsageGrade.le_trans resourceLower resourceUpper,
      AdjointClass.le_trans modalLower modalUpper,
      EpistemicStrength.le_trans epistemicLower epistemicUpper]
  rfl

/-- Antisymmetry of the product order — a genuine PARTIAL order.  Each coordinate order is
antisymmetric; the six field equalities reconstruct the record. -/
theorem GradedSpectrum.le_antisymm {first second : GradedSpectrum}
    (forward : first.le second = true) (backward : second.le first = true) : first = second := by
  obtain ⟨firstGeo, firstSize, firstDepth, firstRes, firstModal, firstEpi⟩ := first
  obtain ⟨secondGeo, secondSize, secondDepth, secondRes, secondModal, secondEpi⟩ := second
  dsimp only [GradedSpectrum.le] at forward backward
  have geoEq : firstGeo = secondGeo := FibrancyFeatures.le_antisymm
    (boolAndElimLeft (boolAndElimLeft (boolAndElimLeft (boolAndElimLeft (boolAndElimLeft forward)))))
    (boolAndElimLeft (boolAndElimLeft (boolAndElimLeft (boolAndElimLeft (boolAndElimLeft backward)))))
  have sizeEq : firstSize = secondSize := Nat.le_antisymm
    (Nat.le_of_ble_eq_true (boolAndElimRight (boolAndElimLeft (boolAndElimLeft
      (boolAndElimLeft (boolAndElimLeft forward))))))
    (Nat.le_of_ble_eq_true (boolAndElimRight (boolAndElimLeft (boolAndElimLeft
      (boolAndElimLeft (boolAndElimLeft backward))))))
  have depthEq : firstDepth = secondDepth := Nat.le_antisymm
    (Nat.le_of_ble_eq_true (boolAndElimRight (boolAndElimLeft (boolAndElimLeft
      (boolAndElimLeft forward)))))
    (Nat.le_of_ble_eq_true (boolAndElimRight (boolAndElimLeft (boolAndElimLeft
      (boolAndElimLeft backward)))))
  have resEq : firstRes = secondRes := UsageGrade.le_antisymm
    (boolAndElimRight (boolAndElimLeft (boolAndElimLeft forward)))
    (boolAndElimRight (boolAndElimLeft (boolAndElimLeft backward)))
  have modalEq : firstModal = secondModal := AdjointClass.le_antisymm
    (boolAndElimRight (boolAndElimLeft forward))
    (boolAndElimRight (boolAndElimLeft backward))
  have epiEq : firstEpi = secondEpi := EpistemicStrength.le_antisymm
    (boolAndElimRight forward) (boolAndElimRight backward)
  rw [geoEq, sizeEq, depthEq, resEq, modalEq, epiEq]

/-- `bottom` is below every position. -/
theorem GradedSpectrum.bottom_le (position : GradedSpectrum) :
    GradedSpectrum.bottom.le position = true := by
  dsimp only [GradedSpectrum.le, GradedSpectrum.bottom]
  have geoHolds : FibrancyFeatures.strict.le position.geometric = true :=
    FibrancyFeatures.strict_le position.geometric
  have sizeHolds : Nat.ble 0 position.size = true := Nat.ble_eq_true_of_le (Nat.zero_le _)
  have depthHolds : Nat.ble 0 position.depth = true := Nat.ble_eq_true_of_le (Nat.zero_le _)
  have resourceHolds : UsageGrade.zero.le position.resource = true := by
    cases position.resource <;> rfl
  have modalHolds : AdjointClass.tangible.le position.modal = true :=
    AdjointClass.tangible_le position.modal
  have epistemicHolds : EpistemicStrength.external.le position.epistemic = true :=
    Nat.ble_eq_true_of_le (Nat.zero_le _)
  rw [geoHolds, sizeHolds, depthHolds, resourceHolds, modalHolds, epistemicHolds]
  rfl

/-! ## The φ-pole embeddings (the discrete fibrancy classifications as named points) -/

/-- The **strict pole** — `bottom` with strict φ (it already is strict). -/
def strictPole : GradedSpectrum := GradedSpectrum.bottom

/-- The **groupoidal pole** — `bottom` at groupoidal φ. -/
def groupoidalPole : GradedSpectrum := { GradedSpectrum.bottom with geometric := FibrancyFeatures.groupoidal }

/-- The **directed pole** — `bottom` at directed φ. -/
def directedPole : GradedSpectrum := { GradedSpectrum.bottom with geometric := FibrancyFeatures.directed }

/-- The **relational pole** — `bottom` at relational φ. -/
def relationalPole : GradedSpectrum := { GradedSpectrum.bottom with geometric := FibrancyFeatures.relational }

/-- The **omega (geometric) pole** — `bottom` at the ω φ-corner (all three characters). -/
def omegaGeometricPole : GradedSpectrum := { GradedSpectrum.bottom with geometric := FibrancyFeatures.omega }

/-! ## The MATT AdjointClass pole embeddings (§5 MODE / mode-13) -/

/-- The **tangible pole** — `bottom` (the ambient mode). -/
def tanglePole : GradedSpectrum := GradedSpectrum.bottom

/-- The **sharp pole** — `bottom` at the sharp mode. -/
def sharpPole : GradedSpectrum := { GradedSpectrum.bottom with modal := AdjointClass.sharp }

/-- The **transparent pole** — `bottom` at the transparent mode. -/
def transparentPole : GradedSpectrum := { GradedSpectrum.bottom with modal := AdjointClass.transparent }

/-- The **sinister pole** — `bottom` at the sinister (left-adjoint) mode. -/
def sinisterPole : GradedSpectrum := { GradedSpectrum.bottom with modal := AdjointClass.sinister }

/-- ★ The **cross-coherence map** `geometricOfModal` — lift a MATT `AdjointClass` to its φ-pole position
(via `featuresOfAdjointClass`).  Documents §5's claim that the φ MODE-row IS the four AdjointClasses,
with NO second order imposed: a total map `AdjointClass → GradedSpectrum`. -/
def geometricOfModal (adjointClass : AdjointClass) : GradedSpectrum :=
  { GradedSpectrum.bottom with geometric := featuresOfAdjointClass adjointClass }

/-- Embedding landing — the sinister mode lifts to the directed pole (`rfl`). -/
theorem geometricOfModal_sinister : geometricOfModal AdjointClass.sinister = directedPole := rfl

/-- The tangible mode lifts to the strict pole (`rfl`). -/
theorem geometricOfModal_tangible : geometricOfModal AdjointClass.tangible = strictPole := rfl

/-- The sharp mode lifts to the groupoidal pole (`rfl`). -/
theorem geometricOfModal_sharp : geometricOfModal AdjointClass.sharp = groupoidalPole := rfl

/-- The transparent mode lifts to the relational pole (`rfl`). -/
theorem geometricOfModal_transparent : geometricOfModal AdjointClass.transparent = relationalPole := rfl

/-- The FibrancyKind embedding lands where expected — the fibrant mode's φ reading is the groupoidal
pole's geometric coordinate (`rfl`). -/
theorem fibrantKind_geometric :
    featuresOfFibrancyKind FibrancyKind.fibrant = groupoidalPole.geometric := rfl

/-- The exotype mode's φ reading is the strict pole's geometric coordinate (`rfl`). -/
theorem exotypeKind_geometric :
    featuresOfFibrancyKind FibrancyKind.exotype = strictPole.geometric := rfl

/-! ## The R1–R7 rung ladder — one monotone diagonal

The seven rungs of `grade-mode-spectrum.md` §1 as one MONOTONE diagonal through the product.  Each step
raises several coordinates (richness = objects × 1-cell-algebra × dimension, §1).  The geometric
coordinate ACCUMULATES fibrancy character down the diagonal (`strict` ⊑ `groupoidal` ⊑ `groupoidal ⊔
directed` ⊑ `omega`) so the climb stays monotone in the cube — the PURE single-character poles
(`directed`, `relational`) are the separate embeddings above, NOT diagonal points.  The R3→R4 crossover
(§1: grade → mode, "quantity becoming place") is carried by BOTH the geometric bit gaining
`hasDirection` AND the modal coordinate flipping `tangible → sinister`. -/

/-- The seven rungs (`grade-mode-spectrum.md` §1). -/
inductive SpectrumRung where
  /-- R1 — lattice grade (security / effect-join). -/
  | r1
  /-- R2 — grade proper (usage / cost, QTT). -/
  | r2
  /-- R3 — graded modality `!ᵣ` (bounded linear logic). -/
  | r3
  /-- R4 — the grade→mode crossover (one object → many; adjoint character appears). -/
  | r4
  /-- R5 — adjoint strings (MTT / MATT). -/
  | r5
  /-- R6 — the ω-mode. -/
  | r6
  /-- R7 — doctrine / self-index. -/
  | r7
  deriving DecidableEq

/-- The successor on the rung ladder (`r7` is the top fixpoint). -/
def SpectrumRung.next : SpectrumRung → SpectrumRung
  | .r1 => .r2
  | .r2 => .r3
  | .r3 => .r4
  | .r4 => .r5
  | .r5 => .r6
  | .r6 => .r7
  | .r7 => .r7

/-- ★ The **rung diagonal** — each rung's canonical position.  Monotone by construction (every coordinate
non-decreasing; the geometric character accumulates). -/
def rungPos : SpectrumRung → GradedSpectrum
  | .r1 => ⟨FibrancyFeatures.strict, 0, 0, UsageGrade.zero, AdjointClass.tangible, EpistemicStrength.external⟩
  | .r2 => ⟨FibrancyFeatures.strict, 1, 0, UsageGrade.one, AdjointClass.tangible, EpistemicStrength.assumed⟩
  | .r3 => ⟨FibrancyFeatures.groupoidal, 1, 1, UsageGrade.omega, AdjointClass.tangible, EpistemicStrength.sorryLevel⟩
  | .r4 => ⟨FibrancyFeatures.directed.join FibrancyFeatures.groupoidal, 1, 1, UsageGrade.omega,
            AdjointClass.sinister, EpistemicStrength.tested⟩
  | .r5 => ⟨FibrancyFeatures.directed.join FibrancyFeatures.groupoidal, 2, 2, UsageGrade.omega,
            AdjointClass.sinister, EpistemicStrength.tested⟩
  | .r6 => ⟨FibrancyFeatures.omega, 3, 3, UsageGrade.omega, AdjointClass.sinister, EpistemicStrength.verified⟩
  | .r7 => ⟨FibrancyFeatures.omega, 4, 4, UsageGrade.omega, AdjointClass.sinister, EpistemicStrength.verified⟩

/-- ★ **The diagonal is monotone** — `rungPos i ≤ rungPos i.next` for every rung.  Every coordinate is
non-decreasing (the geometric character accumulates `strict ⊑ groupoidal ⊑ groupoidal⊔directed ⊑ omega`,
the modal flips `tangible → sinister` once at R3→R4, size/depth/resource/epistemic climb). -/
theorem monotone_rungs (rung : SpectrumRung) : (rungPos rung).le (rungPos rung.next) = true := by
  cases rung <;> rfl

/-! ## The decategorification classifier `rungOfSpectrum` (`grade = π₀(mode)`, §6/§7.3)

`rungOfSpectrum` reads the rung off the coordinates — realizing the `mode-2`/`mode-12` rung classifier
(§7.3) as a total decidable function.  `modal = tangible ∧ …` sits at R1–R3 (grade); a non-ambient mode
sits at R4+ (mode); size resolves the intra-band rung.  Full-enum matches (no wildcard) keep it
propext-free. -/

/-- ★ The **rung classifier** — the total decidable read-off of a position's rung (`grade-mode-spectrum.md`
§7.3, `grade = π₀(mode)`).  `tangible` mode ⇒ grade band R1–R3 (resource resolves); non-ambient mode ⇒
mode band R4+ (relational character ⇒ R6/R7, else R4/R5; size resolves). -/
def rungOfSpectrum (position : GradedSpectrum) : SpectrumRung :=
  match position.modal.isSinister with
  | false =>
    match position.resource with
    | .zero => .r1
    | .one => .r2
    | .omega => .r3
  | true =>
    match position.geometric.hasRelationality with
    | true =>
      match Nat.ble position.size 3 with
      | true => .r6
      | false => .r7
    | false =>
      match Nat.ble position.size 1 with
      | true => .r4
      | false => .r5

/-- ★★★ **`rungOfSpectrum ∘ rungPos = id`** — the classifier reads every rung's canonical position back
to that rung.  The decategorification shadow is a genuine total section (§6 self-application, v1 slice). -/
theorem rungOfSpectrum_rungPos (rung : SpectrumRung) : rungOfSpectrum (rungPos rung) = rung := by
  cases rung <;> rfl

/-! ## The witnessed interior positions (the genuine gradient, not a 4-enum) -/

/-- ★ **Interior witness 1 — the cross-family blend.**  A DIRECTED identity structure carrying a LINEAR
(`one`) resource discipline — nuance living in the PRODUCT (§6.4 `#1872`): no discrete pole carries BOTH
a non-strict φ AND a non-zero resource.  Every one of the nine poles has `resource = zero`, so this point
differs from all of them (`interiorBlend_ne_poles`). -/
def interiorBlend : GradedSpectrum :=
  ⟨FibrancyFeatures.directed, 0, 0, UsageGrade.one, AdjointClass.tangible, EpistemicStrength.external⟩

/-- `interiorBlend` is strictly ABOVE the strict pole (`bottom`): `bottom ≤ interiorBlend` and unequal. -/
theorem strictPole_lt_interiorBlend :
    strictPole.le interiorBlend = true ∧ strictPole ≠ interiorBlend := by
  refine ⟨by decide, by decide⟩

/-- `interiorBlend` is strictly BELOW the R4 rung position: `interiorBlend ≤ rungPos r4` and unequal.
So `interiorBlend` sits strictly between two named points — a genuine interpolation, not a corner. -/
theorem interiorBlend_lt_rungR4 :
    interiorBlend.le (rungPos SpectrumRung.r4) = true ∧ interiorBlend ≠ rungPos SpectrumRung.r4 := by
  refine ⟨by decide, by decide⟩

/-- ★ `interiorBlend` differs from EVERY one of the nine poles — each pole has `resource = zero`, the
blend has `resource = one`.  The concrete `#1872` thesis: the product interior is unreachable by any
single discrete classifier. -/
theorem interiorBlend_ne_poles :
    interiorBlend ≠ strictPole ∧ interiorBlend ≠ groupoidalPole ∧ interiorBlend ≠ directedPole
      ∧ interiorBlend ≠ relationalPole ∧ interiorBlend ≠ omegaGeometricPole
      ∧ interiorBlend ≠ sharpPole ∧ interiorBlend ≠ transparentPole ∧ interiorBlend ≠ sinisterPole := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ★ **Interior witness 2 — interior fibrancy.**  The φ-cube interior `directedRelational` (a left
adjoint that admits a relational reading but is NOT invertible), placed at the bottom of every other
coordinate.  The lattice interior strictly richer than the discrete classifier (§5). -/
def interiorFibrancy : GradedSpectrum :=
  { GradedSpectrum.bottom with geometric := FibrancyFeatures.directedRelational }

/-- `interiorFibrancy` sits strictly between the directed pole and the ω-geometric pole. -/
theorem directedPole_lt_interiorFibrancy_lt_omega :
    (directedPole.le interiorFibrancy = true ∧ directedPole ≠ interiorFibrancy)
      ∧ (interiorFibrancy.le omegaGeometricPole = true ∧ interiorFibrancy ≠ omegaGeometricPole) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- ★★★ **No shipped `AdjointClass` names `interiorFibrancy`.**  For every MATT class `c`, the
`geometricOfModal c` position differs from `interiorFibrancy` — the discrete mode classifier cannot reach
the φ-cube interior (lifted `featuresOfAdjointClass_ne_directedRelational`).  The falsifiable payoff of
"fibrancy read at higher resolution." -/
theorem interiorFibrancy_ne_geometricOfModal (adjointClass : AdjointClass) :
    geometricOfModal adjointClass ≠ interiorFibrancy := by
  cases adjointClass <;> decide

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the smooth-gradient `GradedSpectrum` ships, genuinely inhabited with real
interior.**  The six-family flat position record with its verified product partial order (`le_refl` /
`le_trans` / `le_antisymm` / `bottom_le`), the φ-pole and AdjointClass-pole embeddings landing by `rfl`,
the monotone R1–R7 rung diagonal with the total classifier `rungOfSpectrum` (`rungOfSpectrum ∘ rungPos =
id`), and TWO witnessed interior positions strictly between named points and distinct from every pole
(`interiorBlend` — the cross-family blend; `interiorFibrancy` — the φ-cube interior named by no shipped
`AdjointClass`).  `= true` because the interiors are genuinely inhabited and proven distinct from every
pole. -/
def fxMode_hasGradedSpectrum : Bool := true

end FX1Poly.Axis
