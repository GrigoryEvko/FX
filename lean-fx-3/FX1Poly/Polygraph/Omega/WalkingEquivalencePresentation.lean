import FX1Poly.Polygraph.Omega.CongruenceWithId
import FX1Poly.Polygraph.Omega.StrictAxioms
import FX1Poly.Polygraph.Omega.PresentationOpDualityWithId

/-! # Polygraph/Omega/WalkingEquivalencePresentation — the walking equivalence as a two-object
invertible-unit/counit presentation (WP-EQUIV r1, B1)

★ **The FIRST two-object Omega-lane walker, and the first whose 2-cell relations are literally globular on
BOTH boundaries.**  Every shipped Omega walker so far is single-mode (`modeCarrier := Unit`): the involution,
the monad, the idempotent semigroup, the distributive law.  The walking equivalence needs TWO objects — an
equivalence `f : A => B`, `g : B => A` with invertible unit and counit — so this file makes the genuine
mode-carrier upgrade to `modeCarrier := Bool` (the carrier is fully generic; only the shipped comparators had
assumed `Unit`).  A real `Bool` mode comparator and a real six-label tag comparator separate the two objects
and the six generators (unlike the single-object walkers' trivial `fun _ _ => true`).

## The presentation `<f, g | eta, etaInv, eps, epsInv | four iso-cancellations>` (NO triangles)

  * 0-cells: two objects `A` (`ofMode false`) and `B` (`ofMode true`).
  * 1-cells: two generators `f : A => B`, `g : B => A`; the two round-trips `u_A := f.g : A => A`,
    `u_B := g.f : B => B` (diagrammatic-order `vcomp`, "f then g"), plus `id A`, `id B`.
  * 2-cells: FOUR generators presenting an invertible unit and counit — `eta : id A => u_A`,
    `etaInv : u_A => id A`, `eps : u_B => id B`, `epsInv : id B => u_B`.
  * The FOUR iso-cancellation rows (the only relations — invertibility presented as generator + inverse +
    cancellation, NOT as triangle identities):
      (E1a) `eta . etaInv ~ id (id A)`   (eta after etaInv is the identity 2-cell on `id A`);
      (E1b) `etaInv . eta ~ id u_A`      (etaInv after eta is the identity 2-cell on `u_A`);
      (E2a) `eps . epsInv ~ id u_B`      (eps after epsInv is the identity 2-cell on `u_B`);
      (E2b) `epsInv . eps ~ id (id B)`   (epsInv after eps is the identity 2-cell on `id B`).

This is the free 2-category on "an equivalence without triangle identities" — the walking equivalence.

## Literally globular on BOTH boundaries (the new scope observation)

Each cancellation row relates a `vcomp` of a generator with its inverse to an `id` 2-cell; BOTH sides are
already identity-typed, so the two leg SOURCES are the LITERALLY IDENTICAL 1-cell and so are the two leg
TARGETS.  Hence every row's peak AND valley close on the nose (`refl`) — the EASIEST joins in the family.
Contrast the idempotent semigroup (half-globular: valley literal, peak modulo-strict) and the monad (three
pairs modulo-strict).  The walking equivalence is the first walker whose relations are literally globular on
both boundaries (witnessed by `walkingEquiv*Legs_literallyParallelSource/Target = true`).

## The op-duality note (B2, appended)

The equivalence is SELF-OP-DUAL up to swapping `f <-> g`, `A <-> B`, `eta <-> eps`, `etaInv <-> epsInv`: the
four cancellation rows are closed under `op` (the COOP involution), so the op-dual walker is a FREE-RIDER on
the same presentation — a positive of self-duality (unlike the adjunction, for which op yields nothing).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The two-object signature (six generator labels) -/

/-- ★ The **six generator labels** of the walking equivalence: the two 1-cell generators `f` / `g`, the unit
`eta` and its inverse `etaInv`, the counit `eps` and its inverse `epsInv`.  A finite inductive (full case
splits everywhere — the wildcard-`_ =>` propext leak is avoided). -/
inductive WalkingEquivGenLabel where
  /-- The 1-generator `f : A => B`. -/
  | colourF
  /-- The 1-generator `g : B => A`. -/
  | colourG
  /-- The unit `eta : id A => u_A`. -/
  | etaUnit
  /-- The inverse unit `etaInv : u_A => id A`. -/
  | etaInv
  /-- The counit `eps : u_B => id B`. -/
  | epsCounit
  /-- The inverse counit `epsInv : id B => u_B`. -/
  | epsInv

/-- The **integer tag** of a generator label — a full six-arm split (constant `Nat` motive, propext-free);
the label comparator compares tags. -/
def walkingEquivLabelTag : WalkingEquivGenLabel → Nat
  | .colourF => 0
  | .colourG => 1
  | .etaUnit => 2
  | .etaInv => 3
  | .epsCounit => 4
  | .epsInv => 5

/-- The **label `Bool` equality** — tags equal (`Nat.beq` on tags, propext-free); separates all six labels. -/
def walkingEquivLabelBeq (labelA labelB : WalkingEquivGenLabel) : Bool :=
  walkingEquivLabelTag labelA == walkingEquivLabelTag labelB

/-- ★ The **walking-equivalence omega-computad**: TWO objects (`Bool`), the constant six-label family
`WalkingEquivGenLabel` at every dimension.  The first non-`Unit` mode carrier in the Omega walker family. -/
def walkingEquivComputad : OmegaComputad where
  modeCarrier := Bool
  genLabel := fun _ => WalkingEquivGenLabel

/-- The **mode comparator** — genuine `Bool` equality (NOT the trivial one-object comparator: the two objects
`A` / `B` must be separated).  A full four-arm `Bool` split (no wildcard — propext-free); its result type is
`Bool -> Bool -> Bool`, defeq to `walkingEquivComputad.modeCarrier -> ... -> Bool` at the `cellBeq` call
sites. -/
def walkingEquivModeBeq : Bool → Bool → Bool
  | false, false => true
  | true, true => true
  | false, true => false
  | true, false => false

/-- The **heterogeneous generator comparator** — compares the six labels by tag (separates `f` / `g` and the
four 2-cell generators; NOT the trivial comparator the single-object walkers used). -/
def walkingEquivGenBeq :
    (dimA dimB : Nat) → walkingEquivComputad.genLabel dimA → walkingEquivComputad.genLabel dimB → Bool :=
  fun _ _ labelA labelB => walkingEquivLabelBeq labelA labelB

/-! ## The objects and the 1-cells -/

/-- The object `A` (`ofMode false`). -/
def walkingEquivObjectA : CellExpr walkingEquivComputad 0 := CellExpr.ofMode false

/-- The object `B` (`ofMode true`). -/
def walkingEquivObjectB : CellExpr walkingEquivComputad 0 := CellExpr.ofMode true

/-- The 1-generator `f : A => B`. -/
def walkingEquivFGen : CellExpr walkingEquivComputad 1 :=
  CellExpr.gen (dim := 0) WalkingEquivGenLabel.colourF walkingEquivObjectA walkingEquivObjectB

/-- The 1-generator `g : B => A`. -/
def walkingEquivGGen : CellExpr walkingEquivComputad 1 :=
  CellExpr.gen (dim := 0) WalkingEquivGenLabel.colourG walkingEquivObjectB walkingEquivObjectA

/-- The round-trip `u_A := f.g : A => A` (the unit's target, diagrammatic order "f then g"). -/
def walkingEquivUnitA : CellExpr walkingEquivComputad 1 :=
  CellExpr.vcomp walkingEquivFGen walkingEquivGGen

/-- The round-trip `u_B := g.f : B => B` (the counit's source). -/
def walkingEquivUnitB : CellExpr walkingEquivComputad 1 :=
  CellExpr.vcomp walkingEquivGGen walkingEquivFGen

/-- The identity 1-cell `id A` (the unit's source). -/
def walkingEquivIdA : CellExpr walkingEquivComputad 1 := CellExpr.id walkingEquivObjectA

/-- The identity 1-cell `id B` (the counit's target). -/
def walkingEquivIdB : CellExpr walkingEquivComputad 1 := CellExpr.id walkingEquivObjectB

/-! ## The four invertible unit/counit 2-generators -/

/-- ★ The **unit** `eta : id A => u_A` (label `etaUnit`).  Globular: both `id A` and `u_A` are `A => A`. -/
def walkingEquivEtaGen : CellExpr walkingEquivComputad 2 :=
  CellExpr.gen (dim := 1) WalkingEquivGenLabel.etaUnit walkingEquivIdA walkingEquivUnitA

/-- ★ The **inverse unit** `etaInv : u_A => id A` (label `etaInv`). -/
def walkingEquivEtaInvGen : CellExpr walkingEquivComputad 2 :=
  CellExpr.gen (dim := 1) WalkingEquivGenLabel.etaInv walkingEquivUnitA walkingEquivIdA

/-- ★ The **counit** `eps : u_B => id B` (label `epsCounit`).  Globular: both `u_B` and `id B` are `B => B`. -/
def walkingEquivEpsGen : CellExpr walkingEquivComputad 2 :=
  CellExpr.gen (dim := 1) WalkingEquivGenLabel.epsCounit walkingEquivUnitB walkingEquivIdB

/-- ★ The **inverse counit** `epsInv : id B => u_B` (label `epsInv`). -/
def walkingEquivEpsInvGen : CellExpr walkingEquivComputad 2 :=
  CellExpr.gen (dim := 1) WalkingEquivGenLabel.epsInv walkingEquivIdB walkingEquivUnitB

/-! ## The four cancellation cells (the B1 truth-probe: the rows type-check on concrete words) -/

/-- `eta . etaInv : id A => id A` — the forward unit round-trip (E1a left side). -/
def walkingEquivEtaEtaInv : CellExpr walkingEquivComputad 2 :=
  CellExpr.vcomp walkingEquivEtaGen walkingEquivEtaInvGen

/-- `id (id A) : id A => id A` — the identity 2-cell on `id A` (E1a right side). -/
def walkingEquivIdIdA : CellExpr walkingEquivComputad 2 := CellExpr.id walkingEquivIdA

/-- `etaInv . eta : u_A => u_A` — the backward unit round-trip (E1b left side). -/
def walkingEquivEtaInvEta : CellExpr walkingEquivComputad 2 :=
  CellExpr.vcomp walkingEquivEtaInvGen walkingEquivEtaGen

/-- `id u_A : u_A => u_A` — the identity 2-cell on `u_A` (E1b right side). -/
def walkingEquivIdUnitA : CellExpr walkingEquivComputad 2 := CellExpr.id walkingEquivUnitA

/-- `eps . epsInv : u_B => u_B` — the forward counit round-trip (E2a left side). -/
def walkingEquivEpsEpsInv : CellExpr walkingEquivComputad 2 :=
  CellExpr.vcomp walkingEquivEpsGen walkingEquivEpsInvGen

/-- `id u_B : u_B => u_B` — the identity 2-cell on `u_B` (E2a right side). -/
def walkingEquivIdUnitB : CellExpr walkingEquivComputad 2 := CellExpr.id walkingEquivUnitB

/-- `epsInv . eps : id B => id B` — the backward counit round-trip (E2b left side). -/
def walkingEquivEpsInvEps : CellExpr walkingEquivComputad 2 :=
  CellExpr.vcomp walkingEquivEpsInvGen walkingEquivEpsGen

/-- `id (id B) : id B => id B` — the identity 2-cell on `id B` (E2b right side). -/
def walkingEquivIdIdB : CellExpr walkingEquivComputad 2 := CellExpr.id walkingEquivIdB

/-! ## The literal-globularity boundary checks (both boundaries identity-typed on the nose) -/

/-- The forward unit round-trip's source boundary is `id A` (literal). -/
theorem walkingEquivEtaEtaInv_boundarySource :
    boundarySource walkingEquivEtaEtaInv = walkingEquivIdA := rfl

/-- The forward unit round-trip's target boundary is `id A` (literal) — so both boundaries of E1a agree with
`id (id A)`'s on the nose. -/
theorem walkingEquivEtaEtaInv_boundaryTarget :
    boundaryTarget walkingEquivEtaEtaInv = walkingEquivIdA := rfl

/-- The backward unit round-trip's source boundary is `u_A` (literal). -/
theorem walkingEquivEtaInvEta_boundarySource :
    boundarySource walkingEquivEtaInvEta = walkingEquivUnitA := rfl

/-- The backward unit round-trip's target boundary is `u_A` (literal). -/
theorem walkingEquivEtaInvEta_boundaryTarget :
    boundaryTarget walkingEquivEtaInvEta = walkingEquivUnitA := rfl

/-! ## The four cancellation rows and the base relation -/

/-- ★ The **four walking-equivalence cancellation rows** — a `CellRelOver` firing on the two sides of each
iso-cancellation.  These four are the ONLY relations of the walking equivalence: invertibility presented as
generator + inverse + cancellation (NO triangle identities). -/
inductive WalkingEquivCancellationRow :
    {d : Nat} → CellExpr walkingEquivComputad d → CellExpr walkingEquivComputad d → Prop where
  /-- (E1a) `eta . etaInv ~ id (id A)`. -/
  | unitCancelForward : WalkingEquivCancellationRow walkingEquivEtaEtaInv walkingEquivIdIdA
  /-- (E1b) `etaInv . eta ~ id u_A`. -/
  | unitCancelBackward : WalkingEquivCancellationRow walkingEquivEtaInvEta walkingEquivIdUnitA
  /-- (E2a) `eps . epsInv ~ id u_B`. -/
  | counitCancelForward : WalkingEquivCancellationRow walkingEquivEpsEpsInv walkingEquivIdUnitB
  /-- (E2b) `epsInv . eps ~ id (id B)`. -/
  | counitCancelBackward : WalkingEquivCancellationRow walkingEquivEpsInvEps walkingEquivIdIdB

/-- The base relation the 3-cells resolve: the strict omega laws united with the four cancellation rows. -/
def walkingEquivBaseRel : CellRelOver walkingEquivComputad :=
  unionCellRel walkingEquivComputad (StrictAxiomRel walkingEquivComputad) WalkingEquivCancellationRow

/-! ## The four generating 3-cells -/

/-- ★ **THE UNIT-CANCEL-FORWARD GENERATING 3-CELL** (E1a). -/
def walkingEquivUnitCancelForwardThreeCell :
    SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      walkingEquivEtaEtaInv walkingEquivIdIdA :=
  SaturatedConvOverWithId.ofRelation (Or.inr WalkingEquivCancellationRow.unitCancelForward)

/-- ★ **THE UNIT-CANCEL-BACKWARD GENERATING 3-CELL** (E1b). -/
def walkingEquivUnitCancelBackwardThreeCell :
    SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      walkingEquivEtaInvEta walkingEquivIdUnitA :=
  SaturatedConvOverWithId.ofRelation (Or.inr WalkingEquivCancellationRow.unitCancelBackward)

/-- ★ **THE COUNIT-CANCEL-FORWARD GENERATING 3-CELL** (E2a). -/
def walkingEquivCounitCancelForwardThreeCell :
    SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      walkingEquivEpsEpsInv walkingEquivIdUnitB :=
  SaturatedConvOverWithId.ofRelation (Or.inr WalkingEquivCancellationRow.counitCancelForward)

/-- ★ **THE COUNIT-CANCEL-BACKWARD GENERATING 3-CELL** (E2b). -/
def walkingEquivCounitCancelBackwardThreeCell :
    SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      walkingEquivEpsInvEps walkingEquivIdIdB :=
  SaturatedConvOverWithId.ofRelation (Or.inr WalkingEquivCancellationRow.counitCancelBackward)

/-! ## The assembled per-pair resolution (peak refl, valley refl — literally globular on both boundaries) -/

/-- ★ A **coherent resolution** of one cancellation row — the shipped family shape (peak / legs / valley), but
BOTH the peak and the valley close on the nose (`refl`) because both sides of every cancellation row are
identity-typed and share literally-identical boundaries.  Parameterised by the two legs. -/
structure WalkingEquivCancellationResolved {d : Nat}
    (leftLeg rightLeg : CellExpr walkingEquivComputad (d + 1)) : Prop where
  /-- The two leg SOURCES are convertible (here literally equal — `refl`). -/
  peakJoined : SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
    (boundarySource leftLeg) (boundarySource rightLeg)
  /-- The two legs are convertible (the generating 3-cell). -/
  legsConvertible : SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel leftLeg rightLeg
  /-- The two leg TARGETS are convertible (here literally equal — `refl`). -/
  valleyJoined : SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
    (boundaryTarget leftLeg) (boundaryTarget rightLeg)

/-- (E1a) is coherently resolved (peak refl, valley refl — literally globular on both boundaries). -/
theorem walkingEquivUnitCancelForwardResolved :
    WalkingEquivCancellationResolved walkingEquivEtaEtaInv walkingEquivIdIdA :=
  ⟨SaturatedConvOverWithId.refl _, walkingEquivUnitCancelForwardThreeCell,
    SaturatedConvOverWithId.refl _⟩

/-- (E1b) is coherently resolved (peak refl, valley refl). -/
theorem walkingEquivUnitCancelBackwardResolved :
    WalkingEquivCancellationResolved walkingEquivEtaInvEta walkingEquivIdUnitA :=
  ⟨SaturatedConvOverWithId.refl _, walkingEquivUnitCancelBackwardThreeCell,
    SaturatedConvOverWithId.refl _⟩

/-- (E2a) is coherently resolved (peak refl, valley refl). -/
theorem walkingEquivCounitCancelForwardResolved :
    WalkingEquivCancellationResolved walkingEquivEpsEpsInv walkingEquivIdUnitB :=
  ⟨SaturatedConvOverWithId.refl _, walkingEquivCounitCancelForwardThreeCell,
    SaturatedConvOverWithId.refl _⟩

/-- (E2b) is coherently resolved (peak refl, valley refl). -/
theorem walkingEquivCounitCancelBackwardResolved :
    WalkingEquivCancellationResolved walkingEquivEpsInvEps walkingEquivIdIdB :=
  ⟨SaturatedConvOverWithId.refl _, walkingEquivCounitCancelBackwardThreeCell,
    SaturatedConvOverWithId.refl _⟩

/-! ## The coherent-presentation statement (the honest-scope bundle) -/

/-- ★ **The walking-equivalence coherent-presentation statement.**  All FOUR iso-cancellation rows are
coherently resolved — a `Prop` conjunction of the four per-pair resolutions. -/
def WalkingEquivalenceCoherentPresentationStatement : Prop :=
  WalkingEquivCancellationResolved walkingEquivEtaEtaInv walkingEquivIdIdA ∧
  WalkingEquivCancellationResolved walkingEquivEtaInvEta walkingEquivIdUnitA ∧
  WalkingEquivCancellationResolved walkingEquivEpsEpsInv walkingEquivIdUnitB ∧
  WalkingEquivCancellationResolved walkingEquivEpsInvEps walkingEquivIdIdB

/-- ★★ **THE WALKING-EQUIVALENCE PRESENTATION (four iso-cancellations, literally globular on both
boundaries).**  The walking equivalence `<f, g | eta, etaInv, eps, epsInv | four iso-cancellations>` re-encoded
as a two-object `OmegaComputad` 2-polygraph has all FOUR cancellation rows exhibited as generating 3-cells,
each joinable on the nose at peak AND valley — the first two-object walker and the first literally globular on
both boundaries. -/
theorem walkingEquivalenceCoherentPresentation : WalkingEquivalenceCoherentPresentationStatement :=
  ⟨walkingEquivUnitCancelForwardResolved, walkingEquivUnitCancelBackwardResolved,
    walkingEquivCounitCancelForwardResolved, walkingEquivCounitCancelBackwardResolved⟩

/-! ## The least-congruence universal property (map-out) -/

/-- ★ **THE FOUR 3-CELLS GENERATE THE IDENTIFICATION (least-congruence UP).**  For any relation `targetRel`
absorbing the walking-equivalence base relation (a congruence containing the strict laws and the four
cancellation rows), the two sides of EVERY cancellation row are `targetRel`-related — so the four generating
3-cells are the datum whose fold through `SaturatedConvOverWithId.recInto` identifies each iso-cancellation in
EVERY model.  Uniform in the row (keyed on `WalkingEquivCancellationRow`). -/
theorem walkingEquivCancellationsIdentifiedInEveryModel {targetRel : CellRelOver walkingEquivComputad}
    (absorbs : IsSaturatedCongruenceWithId walkingEquivComputad walkingEquivBaseRel targetRel)
    {d : Nat} {leftLeg rightLeg : CellExpr walkingEquivComputad d}
    (row : WalkingEquivCancellationRow leftLeg rightLeg) : targetRel leftLeg rightLeg :=
  SaturatedConvOverWithId.recInto absorbs (SaturatedConvOverWithId.ofRelation (Or.inr row))

/-! ## The four-row census -/

/-- The four cancellation-row labels. -/
inductive WalkingEquivCancellationLabel
  /-- (E1a) `eta . etaInv ~ id (id A)`. -/
  | unitCancelForward
  /-- (E1b) `etaInv . eta ~ id u_A`. -/
  | unitCancelBackward
  /-- (E2a) `eps . epsInv ~ id u_B`. -/
  | counitCancelForward
  /-- (E2b) `epsInv . eps ~ id (id B)`. -/
  | counitCancelBackward

/-- The complete enumeration of the walking-equivalence cancellation rows — FOUR, listed. -/
def allWalkingEquivCancellations : List WalkingEquivCancellationLabel :=
  [.unitCancelForward, .unitCancelBackward, .counitCancelForward, .counitCancelBackward]

/-- ★ **The cancellation-row count is exactly FOUR** — kernel-checked (`rfl`). -/
theorem walkingEquivCancellationCountIsFour : allWalkingEquivCancellations.length = 4 := rfl

/-- ★ **The enumeration is EXHAUSTIVE** — every label appears (full case split). -/
theorem allWalkingEquivCancellationsExhaustive :
    ∀ label : WalkingEquivCancellationLabel, label ∈ allWalkingEquivCancellations
  | .unitCancelForward => List.Mem.head _
  | .unitCancelBackward => List.Mem.tail _ (List.Mem.head _)
  | .counitCancelForward => List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | .counitCancelBackward =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-! ## Non-vacuity — the objects, the generators, and the row legs are genuinely distinct -/

/-- ★ **The two objects are genuinely distinct 0-cells** — `A` (`ofMode false`) and `B` (`ofMode true`) are
structurally NOT equal (the real `Bool` mode comparator separates them). -/
theorem walkingEquivObjects_distinct :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq walkingEquivObjectA walkingEquivObjectB = false := rfl

/-- ★ **The two 1-generators are genuinely distinct 1-cells** — `f : A => B` and `g : B => A` are structurally
NOT equal (both the mode boundaries and the label tags separate them). -/
theorem walkingEquivFG_distinct :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq walkingEquivFGen walkingEquivGGen = false := rfl

/-- The E1a legs are structurally DISTINCT (`vcomp` vs `id`). -/
theorem walkingEquivUnitCancelForwardLegs_distinct :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq walkingEquivEtaEtaInv walkingEquivIdIdA = false := rfl

/-- The E1b legs are structurally DISTINCT. -/
theorem walkingEquivUnitCancelBackwardLegs_distinct :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq walkingEquivEtaInvEta walkingEquivIdUnitA = false := rfl

/-- The E2a legs are structurally DISTINCT. -/
theorem walkingEquivCounitCancelForwardLegs_distinct :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq walkingEquivEpsEpsInv walkingEquivIdUnitB = false := rfl

/-- The E2b legs are structurally DISTINCT. -/
theorem walkingEquivCounitCancelBackwardLegs_distinct :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq walkingEquivEpsInvEps walkingEquivIdIdB = false := rfl

/-- ★ **THE E1a ROW IS LITERALLY GLOBULAR AT THE SOURCE.**  The two leg source 1-cells are the LITERALLY
IDENTICAL `id A`, so `cellBeq` computes `true` — the peak closes on the nose (contrast the idempotent
semigroup's modulo-strict peak). -/
theorem walkingEquivUnitCancelForwardLegs_literallyParallelSource :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq
      (boundarySource walkingEquivEtaEtaInv) (boundarySource walkingEquivIdIdA) = true := rfl

/-- ★ **THE E1a ROW IS LITERALLY GLOBULAR AT THE TARGET.**  The two leg target 1-cells are the LITERALLY
IDENTICAL `id A` — so the valley closes on the nose too.  Both boundaries literal is the walking equivalence's
distinctive scope (the first walker literally globular on BOTH boundaries). -/
theorem walkingEquivUnitCancelForwardLegs_literallyParallelTarget :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq
      (boundaryTarget walkingEquivEtaEtaInv) (boundaryTarget walkingEquivIdIdA) = true := rfl

/-! ## Non-vacuity probes -/

#eval cellBeq walkingEquivModeBeq walkingEquivGenBeq walkingEquivObjectA walkingEquivObjectB
#eval cellBeq walkingEquivModeBeq walkingEquivGenBeq walkingEquivFGen walkingEquivGGen
#eval cellBeq walkingEquivModeBeq walkingEquivGenBeq walkingEquivEtaEtaInv walkingEquivIdIdA
#eval cellBeq walkingEquivModeBeq walkingEquivGenBeq
  (boundarySource walkingEquivEtaEtaInv) (boundarySource walkingEquivIdIdA)
#eval allWalkingEquivCancellations.length

/-! ## The honesty markers -/

/-- ★ **ESTABLISHED (B1).**  The walking equivalence `<f, g | eta, etaInv, eps, epsInv | four
iso-cancellations>` re-encoded as a two-object (`modeCarrier := Bool`) `OmegaComputad` 2-polygraph: six
generator labels, four invertible-unit/counit 2-cell generators, the FOUR iso-cancellation rows exhibited as
generating 3-cells (`walkingEquiv*ThreeCell`) each coherently resolved on the nose at peak AND valley
(`walkingEquivalenceCoherentPresentation`), the four-row census
(`walkingEquivCancellationCountIsFour`), and the least-congruence UP.  `= true`. -/
def fxEquiv_walkingEquivalencePresentationShipped : Bool := true

/-- ★ **THE FIRST WALKER LITERALLY GLOBULAR ON BOTH BOUNDARIES.**  `= true` records that every cancellation
row's peak AND valley close on the nose (`walkingEquivUnitCancelForwardLegs_literallyParallelSource /
Target = true`): both sides of each iso-cancellation are identity-typed with literally-identical boundaries.
The first walker whose relations are literally globular on both boundaries (contrast the idempotent semigroup's
half-globular, the monad's three modulo-strict pairs). -/
def fxEquiv_cancellationRowsLiterallyGlobularBothBoundaries : Bool := true

/-- ★ **THE FIRST TWO-OBJECT OMEGA WALKER.**  `= true` records the genuine mode-carrier upgrade to
`modeCarrier := Bool` — the first Omega walker outside the single-mode (`modeCarrier := Unit`) family pattern,
with real `Bool` mode and six-label tag comparators separating the two objects and the six generators
(`walkingEquivObjects_distinct`, `walkingEquivFG_distinct`). -/
def fxEquiv_firstTwoObjectOmegaWalker : Bool := true

/-! # =========================================================================================
    # B2 — THE WALKING ADJOINT EQUIVALENCE (the two triangle rows added) + the op-duality note
    # =========================================================================================

★ **The walking adjoint equivalence = the walking equivalence (B1) + the two triangle-identity rows.**  A bare
equivalence becomes an ADJOINT equivalence by imposing the two triangle identities (the zig-zag laws).  Over
the shipped carrier they are the standard whiskerings:

  * Left triangle (for `f`): `(eta |> f) . (f <| eps) ~ id f` — a 2-cell `f => f`.
  * Right triangle (for `g`): `(g <| eta) . (eps |> g) ~ id g` — a 2-cell `g => g`.

Each is a critical pair MODULO the strict UNIT laws: the triangle leg's boundaries are `(id A . f)` / `(f . id
B)` (left) and `(g . id A)` / `(id B . g)` (right), joined to `f` / `g` by `vcompUnitLeft` / `vcompUnitRight`.
So — unlike the B1 iso-cancellations, which are literally globular on both boundaries — the triangle rows are
modulo-strict at both boundaries, exactly the monad / idempotent situation.

## The op-duality note (recon §4)

The equivalence is SELF-OP-DUAL up to the label involution `colourF <-> colourG`, `etaUnit <-> epsCounit`,
`etaInv <-> epsInv`.  Under the COOP involution `opCellExpr` (reverse cells, flip `vcomp`, swap whisker kinds)
the presentation maps to an equivalence of the SAME SHAPE with the two objects and the two 1-generators
swapped; the four cancellation rows and the two triangle rows are closed under `op` (up to relabeling).  So the
op-dual walker is a FREE-RIDER: its resolutions are `op`-transports of the originals through the shipped
generic machine `opCriticalPairResolved` (a machine-checked truth-probe below), NOT a new walker.  This is a
POSITIVE of self-duality — contrast the adjunction, which is also self-dual but yields nothing new.  (The
duality is UP TO RELABELING: `opCellExpr` preserves generator LABELS while swapping boundaries, so `op f` is a
colourF-labeled `B => A` cell, distinct on the nose from `g`; the presentations are isomorphic under the label
involution, not literally identical.) -/

/-! ## The two triangle legs and the identity 2-cells they collapse to -/

/-- `id f : f => f` — the left triangle's target. -/
def walkingEquivIdF : CellExpr walkingEquivComputad 2 := CellExpr.id walkingEquivFGen

/-- `id g : g => g` — the right triangle's target. -/
def walkingEquivIdG : CellExpr walkingEquivComputad 2 := CellExpr.id walkingEquivGGen

/-- ★ The **left triangle leg** `(eta |> f) . (f <| eps) : (id A . f) => (f . id B)` — the left zig-zag for
`f`, whose collapse to `id f` is the left triangle identity. -/
def walkingEquivLeftTriangleLeg : CellExpr walkingEquivComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEtaGen walkingEquivFGen)
    (CellExpr.whiskerLeft walkingEquivFGen walkingEquivEpsGen)

/-- ★ The **right triangle leg** `(g <| eta) . (eps |> g) : (g . id A) => (id B . g)` — the right zig-zag for
`g`, whose collapse to `id g` is the right triangle identity. -/
def walkingEquivRightTriangleLeg : CellExpr walkingEquivComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen)
    (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)

/-- The left triangle leg's source boundary is `id A . f` (joined to `f` by the left unit). -/
theorem walkingEquivLeftTriangleLeg_boundarySource :
    boundarySource walkingEquivLeftTriangleLeg =
      CellExpr.vcomp walkingEquivIdA walkingEquivFGen := rfl

/-- The left triangle leg's target boundary is `f . id B` (joined to `f` by the right unit). -/
theorem walkingEquivLeftTriangleLeg_boundaryTarget :
    boundaryTarget walkingEquivLeftTriangleLeg =
      CellExpr.vcomp walkingEquivFGen walkingEquivIdB := rfl

/-- The right triangle leg's source boundary is `g . id A` (joined to `g` by the right unit). -/
theorem walkingEquivRightTriangleLeg_boundarySource :
    boundarySource walkingEquivRightTriangleLeg =
      CellExpr.vcomp walkingEquivGGen walkingEquivIdA := rfl

/-- The right triangle leg's target boundary is `id B . g` (joined to `g` by the left unit). -/
theorem walkingEquivRightTriangleLeg_boundaryTarget :
    boundaryTarget walkingEquivRightTriangleLeg =
      CellExpr.vcomp walkingEquivIdB walkingEquivGGen := rfl

/-! ## The two triangle rows and the adjoint base relation (= B1 rows + triangles) -/

/-- ★ The **two triangle-identity rows** — the left and right zig-zag laws.  Adding these two rows to the four
iso-cancellation rows (B1) presents the walking ADJOINT equivalence. -/
inductive WalkingEquivTriangleRow :
    {d : Nat} → CellExpr walkingEquivComputad d → CellExpr walkingEquivComputad d → Prop where
  /-- The left triangle identity `(eta |> f) . (f <| eps) ~ id f`. -/
  | leftTriangle : WalkingEquivTriangleRow walkingEquivLeftTriangleLeg walkingEquivIdF
  /-- The right triangle identity `(g <| eta) . (eps |> g) ~ id g`. -/
  | rightTriangle : WalkingEquivTriangleRow walkingEquivRightTriangleLeg walkingEquivIdG

/-- The adjoint-equivalence presentation rows: the four iso-cancellations united with the two triangles. -/
def walkingAdjEquivPresentationRow : CellRelOver walkingEquivComputad :=
  unionCellRel walkingEquivComputad WalkingEquivCancellationRow WalkingEquivTriangleRow

/-- ★ The **walking adjoint equivalence base relation** — the strict omega laws united with (the four
iso-cancellations + the two triangle rows).  This is `walkingEquivBaseRel` extended by the two triangles. -/
def walkingAdjEquivBaseRel : CellRelOver walkingEquivComputad :=
  unionCellRel walkingEquivComputad (StrictAxiomRel walkingEquivComputad) walkingAdjEquivPresentationRow

/-! ## The two triangle generating 3-cells -/

/-- ★ **THE LEFT-TRIANGLE GENERATING 3-CELL.** -/
def walkingEquivLeftTriangleThreeCell :
    SaturatedConvOverWithId walkingEquivComputad walkingAdjEquivBaseRel
      walkingEquivLeftTriangleLeg walkingEquivIdF :=
  SaturatedConvOverWithId.ofRelation (Or.inr (Or.inr WalkingEquivTriangleRow.leftTriangle))

/-- ★ **THE RIGHT-TRIANGLE GENERATING 3-CELL.** -/
def walkingEquivRightTriangleThreeCell :
    SaturatedConvOverWithId walkingEquivComputad walkingAdjEquivBaseRel
      walkingEquivRightTriangleLeg walkingEquivIdG :=
  SaturatedConvOverWithId.ofRelation (Or.inr (Or.inr WalkingEquivTriangleRow.rightTriangle))

/-! ## The six per-pair resolutions over the adjoint base relation (generic `CriticalPairResolvedOver`)

The four iso-cancellations re-fire over `walkingAdjEquivBaseRel` (peak / valley `refl`, literally globular);
the two triangles join their peak / valley MODULO the strict unit laws (`vcompUnitLeft` / `vcompUnitRight`). -/

/-- (E1a) resolved over the adjoint base relation (peak refl, valley refl). -/
theorem walkingAdjEquivUnitCancelForwardResolved :
    CriticalPairResolvedOver walkingEquivComputad walkingAdjEquivBaseRel
      walkingEquivEtaEtaInv walkingEquivIdIdA :=
  ⟨SaturatedConvOverWithId.refl _,
    SaturatedConvOverWithId.ofRelation (Or.inr (Or.inl WalkingEquivCancellationRow.unitCancelForward)),
    SaturatedConvOverWithId.refl _⟩

/-- (E1b) resolved over the adjoint base relation. -/
theorem walkingAdjEquivUnitCancelBackwardResolved :
    CriticalPairResolvedOver walkingEquivComputad walkingAdjEquivBaseRel
      walkingEquivEtaInvEta walkingEquivIdUnitA :=
  ⟨SaturatedConvOverWithId.refl _,
    SaturatedConvOverWithId.ofRelation (Or.inr (Or.inl WalkingEquivCancellationRow.unitCancelBackward)),
    SaturatedConvOverWithId.refl _⟩

/-- (E2a) resolved over the adjoint base relation. -/
theorem walkingAdjEquivCounitCancelForwardResolved :
    CriticalPairResolvedOver walkingEquivComputad walkingAdjEquivBaseRel
      walkingEquivEpsEpsInv walkingEquivIdUnitB :=
  ⟨SaturatedConvOverWithId.refl _,
    SaturatedConvOverWithId.ofRelation (Or.inr (Or.inl WalkingEquivCancellationRow.counitCancelForward)),
    SaturatedConvOverWithId.refl _⟩

/-- (E2b) resolved over the adjoint base relation. -/
theorem walkingAdjEquivCounitCancelBackwardResolved :
    CriticalPairResolvedOver walkingEquivComputad walkingAdjEquivBaseRel
      walkingEquivEpsInvEps walkingEquivIdIdB :=
  ⟨SaturatedConvOverWithId.refl _,
    SaturatedConvOverWithId.ofRelation (Or.inr (Or.inl WalkingEquivCancellationRow.counitCancelBackward)),
    SaturatedConvOverWithId.refl _⟩

/-- ★ **THE LEFT TRIANGLE IS COHERENTLY RESOLVED** — peak `id A . f ~ f` (left unit), valley `f . id B ~ f`
(right unit), legs the generating 3-cell.  Modulo-strict at both boundaries. -/
theorem walkingEquivLeftTriangleResolved :
    CriticalPairResolvedOver walkingEquivComputad walkingAdjEquivBaseRel
      walkingEquivLeftTriangleLeg walkingEquivIdF :=
  ⟨SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft walkingEquivFGen)),
    walkingEquivLeftTriangleThreeCell,
    SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight walkingEquivFGen))⟩

/-- ★ **THE RIGHT TRIANGLE IS COHERENTLY RESOLVED** — peak `g . id A ~ g` (right unit), valley `id B . g ~ g`
(left unit), legs the generating 3-cell. -/
theorem walkingEquivRightTriangleResolved :
    CriticalPairResolvedOver walkingEquivComputad walkingAdjEquivBaseRel
      walkingEquivRightTriangleLeg walkingEquivIdG :=
  ⟨SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight walkingEquivGGen)),
    walkingEquivRightTriangleThreeCell,
    SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft walkingEquivGGen))⟩

/-! ## The adjoint-equivalence coherent presentation and its least-congruence UP -/

/-- ★ **The walking adjoint-equivalence coherent-presentation statement.**  All SIX rows (four
iso-cancellations + two triangles) coherently resolved over `walkingAdjEquivBaseRel`. -/
def WalkingAdjointEquivalenceCoherentPresentationStatement : Prop :=
  CriticalPairResolvedOver walkingEquivComputad walkingAdjEquivBaseRel
    walkingEquivEtaEtaInv walkingEquivIdIdA ∧
  CriticalPairResolvedOver walkingEquivComputad walkingAdjEquivBaseRel
    walkingEquivEtaInvEta walkingEquivIdUnitA ∧
  CriticalPairResolvedOver walkingEquivComputad walkingAdjEquivBaseRel
    walkingEquivEpsEpsInv walkingEquivIdUnitB ∧
  CriticalPairResolvedOver walkingEquivComputad walkingAdjEquivBaseRel
    walkingEquivEpsInvEps walkingEquivIdIdB ∧
  CriticalPairResolvedOver walkingEquivComputad walkingAdjEquivBaseRel
    walkingEquivLeftTriangleLeg walkingEquivIdF ∧
  CriticalPairResolvedOver walkingEquivComputad walkingAdjEquivBaseRel
    walkingEquivRightTriangleLeg walkingEquivIdG

/-- ★★ **THE WALKING ADJOINT EQUIVALENCE (six rows: four iso-cancellations + two triangles).**  The walking
adjoint equivalence `<f, g | eta, etaInv, eps, epsInv | four iso-cancellations + two triangles>` re-encoded as
a two-object `OmegaComputad` 2-polygraph: all six rows exhibited as generating 3-cells, the cancellations
joined on the nose and the triangles joined modulo the strict units. -/
theorem walkingAdjointEquivalenceCoherentPresentation :
    WalkingAdjointEquivalenceCoherentPresentationStatement :=
  ⟨walkingAdjEquivUnitCancelForwardResolved, walkingAdjEquivUnitCancelBackwardResolved,
    walkingAdjEquivCounitCancelForwardResolved, walkingAdjEquivCounitCancelBackwardResolved,
    walkingEquivLeftTriangleResolved, walkingEquivRightTriangleResolved⟩

/-- ★ **THE SIX ADJOINT 3-CELLS GENERATE THE IDENTIFICATION (least-congruence UP).**  For any relation
`targetRel` absorbing the adjoint base relation, the two sides of every adjoint presentation row (the four
cancellations + the two triangles) are `targetRel`-related — the six generating 3-cells fold through
`SaturatedConvOverWithId.recInto` to identify each row in EVERY model. -/
theorem walkingAdjEquivRowsIdentifiedInEveryModel {targetRel : CellRelOver walkingEquivComputad}
    (absorbs : IsSaturatedCongruenceWithId walkingEquivComputad walkingAdjEquivBaseRel targetRel)
    {d : Nat} {leftLeg rightLeg : CellExpr walkingEquivComputad d}
    (row : walkingAdjEquivPresentationRow leftLeg rightLeg) : targetRel leftLeg rightLeg :=
  SaturatedConvOverWithId.recInto absorbs (SaturatedConvOverWithId.ofRelation (Or.inr row))

/-! ## The two-row triangle census (adjoint total = four cancellations + two triangles = six) -/

/-- The two triangle-row labels. -/
inductive WalkingEquivTriangleLabel
  /-- The left triangle (for `f`). -/
  | leftTriangle
  /-- The right triangle (for `g`). -/
  | rightTriangle

/-- The complete enumeration of the triangle rows — TWO, listed. -/
def allWalkingEquivTriangles : List WalkingEquivTriangleLabel := [.leftTriangle, .rightTriangle]

/-- ★ **The triangle-row count is exactly TWO** — kernel-checked (`rfl`). -/
theorem walkingEquivTriangleCountIsTwo : allWalkingEquivTriangles.length = 2 := rfl

/-- ★ **The adjoint-equivalence total row count is exactly SIX** — four iso-cancellations + two triangles,
kernel-checked (`rfl`). -/
theorem walkingAdjEquivRowCountIsSix :
    allWalkingEquivCancellations.length + allWalkingEquivTriangles.length = 6 := rfl

/-! ## The op-duality note — the transported resolution truth-probe (self-op-dual free-rider) -/

/-- ★ **THE OP-DUAL TRANSPORT TRUTH-PROBE (left triangle).**  The left-triangle resolution transported through
the COOP involution `opCellExpr` via the shipped generic machine `opCriticalPairResolved`: a coherent
resolution of the op'd legs over `opCellRelOver walkingAdjEquivBaseRel`, with peak and valley SWAPPED.  The
machine fires on a real shipped resolution — confirming the walking equivalence is a self-op-dual free-rider
(its op-dual presentation's resolutions ARE the op-transports of the originals, no re-derivation). -/
theorem walkingEquivLeftTriangleResolvedOpTransported :
    CriticalPairResolvedOver walkingEquivComputad (opCellRelOver walkingAdjEquivBaseRel)
      (opCellExpr walkingEquivLeftTriangleLeg) (opCellExpr walkingEquivIdF) :=
  opCriticalPairResolved walkingEquivLeftTriangleResolved

/-- ★ **THE OP-DUAL TRANSPORT TRUTH-PROBE (unit-cancel-forward).**  The literally-globular E1a resolution
transported through `op` — confirming the machine fires on the cancellation rows too. -/
theorem walkingEquivUnitCancelForwardResolvedOpTransported :
    CriticalPairResolvedOver walkingEquivComputad (opCellRelOver walkingAdjEquivBaseRel)
      (opCellExpr walkingEquivEtaEtaInv) (opCellExpr walkingEquivIdIdA) :=
  opCriticalPairResolved walkingAdjEquivUnitCancelForwardResolved

/-! ## B2 non-vacuity — the triangle legs are genuinely distinct and modulo-strict -/

/-- The left triangle legs are structurally DISTINCT (`vcomp` of whiskers vs `id f`). -/
theorem walkingEquivLeftTriangleLegs_distinct :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq walkingEquivLeftTriangleLeg walkingEquivIdF = false := rfl

/-- The right triangle legs are structurally DISTINCT. -/
theorem walkingEquivRightTriangleLegs_distinct :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq walkingEquivRightTriangleLeg walkingEquivIdG = false := rfl

/-- ★ **THE LEFT TRIANGLE IS MODULO-STRICT AT THE SOURCE** — the leg source `id A . f` and `id f`'s source `f`
are structurally DISTINCT (differ by the left unit), so the triangle peak joins only MODULO strict (contrast
the B1 cancellations, literally globular). -/
theorem walkingEquivLeftTriangleLegs_notLiterallyParallelSource :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq
      (boundarySource walkingEquivLeftTriangleLeg) (boundarySource walkingEquivIdF) = false := rfl

/-- ★ **THE LEFT TRIANGLE IS MODULO-STRICT AT THE TARGET** — `f . id B` and `f` differ by the right unit. -/
theorem walkingEquivLeftTriangleLegs_notLiterallyParallelTarget :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq
      (boundaryTarget walkingEquivLeftTriangleLeg) (boundaryTarget walkingEquivIdF) = false := rfl

/-! ## B2 non-vacuity probes -/

#eval cellBeq walkingEquivModeBeq walkingEquivGenBeq walkingEquivLeftTriangleLeg walkingEquivIdF
#eval cellBeq walkingEquivModeBeq walkingEquivGenBeq walkingEquivRightTriangleLeg walkingEquivIdG
#eval cellBeq walkingEquivModeBeq walkingEquivGenBeq
  (boundarySource walkingEquivLeftTriangleLeg) (boundarySource walkingEquivIdF)
#eval allWalkingEquivTriangles.length

/-! ## B2 honesty markers -/

/-- ★ **ESTABLISHED (B2).**  The walking ADJOINT equivalence adds the two triangle-identity rows to the B1
presentation: the two triangle legs (`walkingEquivLeftTriangleLeg` / `walkingEquivRightTriangleLeg`), the two
generating 3-cells, and the six-row coherent presentation
(`walkingAdjointEquivalenceCoherentPresentation`) with the four cancellations joined on the nose and the two
triangles joined modulo the strict units.  `= true`. -/
def fxEquiv_walkingAdjointEquivalenceTrianglesShipped : Bool := true

/-- ★ **THE EQUIVALENCE IS A SELF-OP-DUAL FREE-RIDER.**  `= true` records that the walking equivalence is
self-op-dual up to the label involution (`colourF <-> colourG`, `etaUnit <-> epsCounit`, `etaInv <-> epsInv`):
its resolutions transport through the shipped generic `opCriticalPairResolved`
(`walkingEquivLeftTriangleResolvedOpTransported`, `walkingEquivUnitCancelForwardResolvedOpTransported`), so
the op-dual walker is a free-rider on the same presentation — a POSITIVE of self-duality (contrast the
adjunction, self-dual but yielding nothing).  The duality is UP TO RELABELING (`opCellExpr` preserves labels
while swapping boundaries), not literal identity. -/
def fxEquiv_equivalenceSelfOpDualFreeRider : Bool := true

/-! # =========================================================================================
    # B3 — THE PROMOTION: the corrected counit + the derived triangle (hand-worked, mechanized)
    # =========================================================================================

★ **The promotion of the bare equivalence to an adjoint equivalence, at the recon-adjudicated scope.**  The
classical promotion (Mac Lane CWM IV.4; Johnson–Yau §6.2) keeps the unit `eta` and derives the triangle
identities once `eta`, `eps` are invertible.  The recon's clean load-bearing route: over the BARE cancellation
congruence `walkingEquivBaseRel` (strict laws + the four iso-cancellations, NO triangles), the RIGHT triangle
`ψ_g := (g <| eta) . (eps |> g) ~ id g` is FORCED once the left triangle holds — because `ψ_g` is an INVERTIBLE
2-cell (its inverse built from `eta^{-1}`, `eps^{-1}` and the whiskered cancellations), and an invertible
idempotent is the identity.

## What is MECHANIZED here (the honest, machine-checked core)

  1. **`convEndoInvertibleIdempotent_isIdentity`** — the abstract algebraic engine: over any
     `SaturatedConvOverWithId`, a 2-cell `loop` with a left inverse `loopInv` (`loopInv . loop ~ id`) that is
     idempotent (`loop . loop ~ loop`) is convertible to the identity `id (boundarySource loop)`.  A four-`trans`
     proof, generic in the base relation.

  2. **`walkingEquivRightDefect_leftInverse`** — the RIGHT DEFECT `ψ_g` IS INVERTIBLE over the bare cancellation
     congruence: `ψ_g^{-1} . ψ_g ~ id (g . 1_A)`, mechanized as a ~15-step chain of the shipped whiskered
     cancellations (`whiskerLeftFunctorial` / `whiskerRightFunctorial` symm, `whiskerLeft/RightCongr` on the
     E1b / E2b 3-cells, the whisker-unit laws, associativity and unit normalizations, `idCongr` for the
     dim-bump).  This is the recon's "row inventory (a) already ships", exercised.

  3. **`walkingEquivRightTriangle_ofIdempotency`** — the CONDITIONAL PROMOTION: FROM the idempotency
     `ψ_g . ψ_g ~ ψ_g` (the single fact the left triangle supplies), the right triangle `ψ_g ~ id g` FOLLOWS —
     via the abstract engine + the mechanized invertibility.  So the promotion is REDUCED to one idempotency
     fact.

## The honest WALL (the interchange-bracketed core — recon §2 steps 3-4)

The one residual is `ψ_g . ψ_g ~ ψ_g` FROM the left triangle `(eta |> f) . (f <| eps) ~ id f`.  This is the
recon's steps 3-4: whisker the left-triangle hypothesis by `g`, insert `eta^{-1}/eta` and `eps/eps^{-1}` pairs,
and SLIDE them past each other with two `StrictAxiomRel.interchange` (Godement) firings so the inserted inverse
pairs become vertically adjacent and annihilate.  The exact interchange bracketing is the genuine
hand-computation the recon flagged; it is NAMED here as the blocking node
(`fxEquiv_promotionIdempotencyFromLeftTriangleWalled`), NOT axiomatized and NOT fabricated.  Everything up to
it is machine-checked.  (The LEFT defect `φ_f` is symmetric under the op-duality of B2.) -/

/-! ## The abstract algebraic engine — an invertible idempotent is the identity -/

/-- ★ **AN INVERTIBLE IDEMPOTENT IS THE IDENTITY (abstract).**  Over any `SaturatedConvOverWithId baseRel`, a
`(dim+1)`-cell `loop` with a left inverse `loopInv` (`loopInv . loop ~ id (boundarySource loop)`) that is
idempotent (`loop . loop ~ loop`) is convertible to `id (boundarySource loop)`.  The unit and associativity
inputs are taken as hypotheses (supplied by the strict rows at the call site), so the lemma is generic.  Four
`trans` steps: `loop ~ id . loop ~ (loopInv . loop) . loop ~ loopInv . (loop . loop) ~ loopInv . loop ~ id`. -/
theorem convEndoInvertibleIdempotent_isIdentity {computad : OmegaComputad}
    {baseRel : CellRelOver computad} {dim : Nat}
    {loop loopInv : CellExpr computad (dim + 1)}
    (hLeftUnit : SaturatedConvOverWithId computad baseRel
      (CellExpr.vcomp (CellExpr.id (boundarySource loop)) loop) loop)
    (hAssoc : SaturatedConvOverWithId computad baseRel
      (CellExpr.vcomp (CellExpr.vcomp loopInv loop) loop)
      (CellExpr.vcomp loopInv (CellExpr.vcomp loop loop)))
    (hLeftInv : SaturatedConvOverWithId computad baseRel
      (CellExpr.vcomp loopInv loop) (CellExpr.id (boundarySource loop)))
    (hIdem : SaturatedConvOverWithId computad baseRel (CellExpr.vcomp loop loop) loop) :
    SaturatedConvOverWithId computad baseRel loop (CellExpr.id (boundarySource loop)) :=
  SaturatedConvOverWithId.trans (SaturatedConvOverWithId.symm hLeftUnit)
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.vcompCongrLeft loop (SaturatedConvOverWithId.symm hLeftInv))
      (SaturatedConvOverWithId.trans hAssoc
        (SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.vcompCongrRight loopInv hIdem)
          hLeftInv)))

/-! ## The right defect and its inverse (built from the inverse generators) -/

/-- The **inverse of the right defect** `ψ_g^{-1} := (eps^{-1} |> g) . (g <| eta^{-1})` — reverse the two
factors of `ψ_g` and invert each, using the inverse generators. -/
def walkingEquivRightDefectInverse : CellExpr walkingEquivComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsInvGen walkingEquivGGen)
    (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen)

/-! ## The right defect is invertible over the bare cancellation congruence (mechanized) -/

/-- ★ **THE RIGHT DEFECT IS INVERTIBLE.**  `ψ_g^{-1} . ψ_g ~ id (g . 1_A)` over `walkingEquivBaseRel` (the bare
cancellations + strict laws, NO triangles) — the recon's whiskered-cancellation chain, machine-checked: the two
inner factors `(g <| eta^{-1}) . (g <| eta)` collapse to `id (g . u_A)` by `whiskerLeftFunctorial` + the E1b
cancellation + `whiskerLeftUnit`, then the outer factors `(eps^{-1} |> g) . (eps |> g)` collapse to
`id (1_B . g)` by `whiskerRightFunctorial` + the E2b cancellation + `whiskerRightUnit`, with associativity and
unit normalizations bridging the boundaries.  So `ψ_g` is a genuine iso — the promotion's structural fact. -/
theorem walkingEquivRightDefect_leftInverse :
    SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      (CellExpr.vcomp walkingEquivRightDefectInverse walkingEquivRightTriangleLeg)
      (CellExpr.id (boundarySource walkingEquivRightTriangleLeg)) := by
  -- Abbreviations: A = eps^{-1} |> g, B = g <| eta^{-1}, C = g <| eta, D = eps |> g.
  -- ψ_g^{-1} = A . B, ψ_g = C . D, goal (A.B).(C.D) ~ id (g . 1_A).
  -- Reassociate ((A.B).(C.D)) to A . (B . (C.D)).
  have hAssocStart :
      SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
        (CellExpr.vcomp walkingEquivRightDefectInverse walkingEquivRightTriangleLeg)
        (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsInvGen walkingEquivGGen)
          (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen)
            walkingEquivRightTriangleLeg)) :=
    SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompAssoc
      (CellExpr.whiskerRight walkingEquivEpsInvGen walkingEquivGGen)
      (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen)
      walkingEquivRightTriangleLeg))
  -- Reassociate the inner B . (C . D) to (B . C) . D.
  have hReassocMid :
      SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
        (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen)
          walkingEquivRightTriangleLeg)
        (CellExpr.vcomp
          (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen)
            (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen))
          (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)) :=
    SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompAssoc
      (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen)
      (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen)
      (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen))))
  -- The inner unit pair B . C collapses to id (g . u_A).
  have hBC :
      SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
        (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen)
          (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen))
        (CellExpr.id (CellExpr.vcomp walkingEquivGGen walkingEquivUnitA)) :=
    SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
        (Or.inl (StrictAxiomRel.whiskerLeftFunctorial walkingEquivGGen
          walkingEquivEtaInvGen walkingEquivEtaGen))))
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.whiskerLeftCongr walkingEquivGGen
          walkingEquivUnitCancelBackwardThreeCell)
        (SaturatedConvOverWithId.ofRelation
          (Or.inl (StrictAxiomRel.whiskerLeftUnit walkingEquivGGen walkingEquivUnitA))))
  -- (B . C) . D collapses to D via the assoc-normalized left unit.
  have hBCD :
      SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
        (CellExpr.vcomp
          (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen)
            (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen))
          (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen))
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen) :=
    SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.vcompCongrLeft (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen) hBC)
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrLeft
          (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
          (SaturatedConvOverWithId.idCongr (SaturatedConvOverWithId.symm
            (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompAssoc
              walkingEquivGGen walkingEquivFGen walkingEquivGGen))))))
        (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft
          (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)))))
  -- Assemble the middle: A . (B . (C.D)) ~ A . D.
  have hMid :
      SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
        (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsInvGen walkingEquivGGen)
          (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen)
            walkingEquivRightTriangleLeg))
        (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsInvGen walkingEquivGGen)
          (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)) :=
    SaturatedConvOverWithId.vcompCongrRight
      (CellExpr.whiskerRight walkingEquivEpsInvGen walkingEquivGGen)
      (SaturatedConvOverWithId.trans hReassocMid hBCD)
  -- The outer counit pair A . D collapses to id (1_B . g).
  have hAD :
      SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
        (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsInvGen walkingEquivGGen)
          (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen))
        (CellExpr.id (CellExpr.vcomp walkingEquivIdB walkingEquivGGen)) :=
    SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
        (Or.inl (StrictAxiomRel.whiskerRightFunctorial
          walkingEquivEpsInvGen walkingEquivEpsGen walkingEquivGGen))))
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.whiskerRightCongr walkingEquivGGen
          walkingEquivCounitCancelBackwardThreeCell)
        (SaturatedConvOverWithId.ofRelation
          (Or.inl (StrictAxiomRel.whiskerRightUnit walkingEquivIdB walkingEquivGGen))))
  -- Normalize id (1_B . g) ~ id (g . 1_A) modulo the units.
  have hFinalNorm :
      SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
        (CellExpr.id (CellExpr.vcomp walkingEquivIdB walkingEquivGGen))
        (CellExpr.id (CellExpr.vcomp walkingEquivGGen walkingEquivIdA)) :=
    SaturatedConvOverWithId.idCongr
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft walkingEquivGGen)))
        (SaturatedConvOverWithId.symm
          (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight walkingEquivGGen)))))
  exact SaturatedConvOverWithId.trans hAssocStart
    (SaturatedConvOverWithId.trans hMid
      (SaturatedConvOverWithId.trans hAD hFinalNorm))

/-! ## The conditional promotion — the right triangle from the single idempotency fact -/

/-- ★★ **THE CONDITIONAL PROMOTION.**  FROM the idempotency `ψ_g . ψ_g ~ ψ_g` (the single fact the left
triangle supplies), the RIGHT triangle `ψ_g ~ id g` FOLLOWS — via the abstract engine
`convEndoInvertibleIdempotent_isIdentity` fed the mechanized invertibility `walkingEquivRightDefect_leftInverse`
and the strict unit / associativity rows, then normalized `id (g . 1_A) ~ id g` by the right unit.  The whole
promotion is thus REDUCED to the idempotency fact (the interchange-bracketed residual, walled below). -/
theorem walkingEquivRightTriangle_ofIdempotency
    (hIdem : SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      (CellExpr.vcomp walkingEquivRightTriangleLeg walkingEquivRightTriangleLeg)
      walkingEquivRightTriangleLeg) :
    SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      walkingEquivRightTriangleLeg walkingEquivIdG :=
  SaturatedConvOverWithId.trans
    (convEndoInvertibleIdempotent_isIdentity
      (SaturatedConvOverWithId.ofRelation
        (Or.inl (StrictAxiomRel.vcompUnitLeft walkingEquivRightTriangleLeg)))
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompAssoc
        walkingEquivRightDefectInverse walkingEquivRightTriangleLeg walkingEquivRightTriangleLeg)))
      walkingEquivRightDefect_leftInverse
      hIdem)
    (SaturatedConvOverWithId.idCongr
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight walkingEquivGGen))))

/-! ## B3 non-vacuity — the defect inverse is a genuine distinct 2-cell -/

/-- The right defect and its inverse are structurally DISTINCT 2-cells (the inverse uses the inverse
generators). -/
theorem walkingEquivRightDefectInverse_distinct :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq
      walkingEquivRightTriangleLeg walkingEquivRightDefectInverse = false := rfl

/-- The right-defect round-trip `ψ_g^{-1} . ψ_g` is structurally NOT the identity `id (g . 1_A)` on the nose
(it collapses to it only via the cancellations — the invertibility theorem is non-vacuous). -/
theorem walkingEquivRightDefectRoundTrip_notLiterallyId :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq
      (CellExpr.vcomp walkingEquivRightDefectInverse walkingEquivRightTriangleLeg)
      (CellExpr.id (boundarySource walkingEquivRightTriangleLeg)) = false := rfl

/-! ## B3 non-vacuity probe -/

#eval cellBeq walkingEquivModeBeq walkingEquivGenBeq
  (CellExpr.vcomp walkingEquivRightDefectInverse walkingEquivRightTriangleLeg)
  (CellExpr.id (boundarySource walkingEquivRightTriangleLeg))

/-! ## B3 honesty markers -/

/-- ★ **THE RIGHT DEFECT INVERTIBILITY IS MECHANIZED (B3).**  `= true` records that the right-triangle defect
`ψ_g = (g <| eta) . (eps |> g)` is a genuine INVERTIBLE 2-cell over the bare cancellation congruence
(`walkingEquivRightDefect_leftInverse` — a machine-checked ~15-step whiskered-cancellation chain), so the
promotion's structural fact (the defect is an iso) is proved zero-axiom. -/
def fxEquiv_promotionRightDefectInvertibilityMechanized : Bool := true

/-- ★ **THE PROMOTION IS REDUCED TO ONE IDEMPOTENCY FACT (B3).**  `= true` records the conditional promotion
`walkingEquivRightTriangle_ofIdempotency`: FROM `ψ_g . ψ_g ~ ψ_g`, the right triangle `ψ_g ~ id g` FOLLOWS
(abstract invertible-idempotent engine + mechanized invertibility).  The whole "one-triangle-forces-the-other"
promotion is thus reduced to a single idempotency fact. -/
def fxEquiv_promotionReducedToIdempotency : Bool := true

/-- ★ **WALL — the idempotency-from-left-triangle interchange core (B3, honest).**  `= true` records the single
residual of the promotion: the idempotency `ψ_g . ψ_g ~ ψ_g` FROM the left triangle
`(eta |> f) . (f <| eps) ~ id f`.  Blocking node: the recon §2 steps 3-4 — whisker the left-triangle
hypothesis by `g`, insert `eta^{-1}/eta` and `eps/eps^{-1}` pairs, and slide them past each other with two
`StrictAxiomRel.interchange` (Godement) firings so the inserted inverse pairs annihilate.  The exact
interchange bracketing is the genuine hand-computation; it is NAMED, NOT axiomatized, NOT fabricated.
Everything else in the promotion is machine-checked. -/
def fxEquiv_promotionIdempotencyFromLeftTriangleWalled : Bool := true

/-! # =========================================================================================
    # B4 — THE DECISION: parallel-uniqueness for the adjoint walker (contractibility exercised)
    # =========================================================================================

★ **The decision content of the walking equivalence, adjudicated adjoint-vs-bare.**  Unlike the walking
ADJUNCTION — whose 2-cell decision rides a non-crossing-matching engine because `generatorCount` is a
conv-invariant (`AdjunctionTriangleObstruction`) — the equivalence's cancellations DROP the generator count
(`eta . eta^{-1} ~ id`), so that invariant is UNAVAILABLE.  The decision splits:

  * **ADJOINT equivalence (b): parallel-uniqueness is TRUE (contractibility).**  Everything is invertible AND
    the triangles STRAIGHTEN every zig-zag to the identity, so any two parallel 2-cells are convertible over
    `walkingAdjEquivBaseRel` — the decision is `isTrue` always, its content the DERIVATION (no matching engine).
    Reachable r1: the contractibility EXERCISED on concrete parallel pairs (below); the full quantified
    "every parallel pair" needs a small 2-cell normalizer (the OMEGA-5 full-basis obligation, walled uniformly
    across the walker family).

  * **BARE equivalence (a): parallel-uniqueness is an HONEST OPEN.**  Without the triangles the zig-zags are
    NOT straightened: the left zig-zag `φ_f = (eta |> f) . (f <| eps)` and `id f` are (modulo units) parallel
    but NOT forced convertible by the four cancellation rows alone (the winding word problem — a free-groupoid
    object, NOT r1).  The concrete candidate distinguishing pair is `(φ_f, id f)` over `walkingEquivBaseRel`.
    We do NOT claim to decide it; we name it and wall it.

## What is MECHANIZED here

The contractibility EXERCISES: distinct parallel 2-cell WORDS convertible over the adjoint base relation — the
unit loop `eta . eta^{-1} ~ id (id A)` (a literally-parallel `id A => id A` pair, holds even bare), the left and
right zig-zags `φ_f ~ id f` / `ψ_g ~ id g` (the triangle 3-cells straightening the loops), and the DOUBLED
left zig-zag `φ_f . φ_f ~ id f` (a genuine contractibility witness: the doubled loop still collapses).  Each is
a `SaturatedConvOverWithId` term over `walkingAdjEquivBaseRel`. -/

/-! ## The concrete contractibility exercises (distinct parallel 2-cell words, convertible) -/

/-- ★ **THE UNIT LOOP IS CONTRACTIBLE.**  `eta . eta^{-1} ~ id (id A)` — a literally-parallel `id A => id A`
pair of distinct 2-cell words, convertible (the E1a cancellation; holds over the bare relation too). -/
theorem walkingAdjEquivUnitLoopContractible :
    SaturatedConvOverWithId walkingEquivComputad walkingAdjEquivBaseRel
      walkingEquivEtaEtaInv walkingEquivIdIdA :=
  SaturatedConvOverWithId.ofRelation (Or.inr (Or.inl WalkingEquivCancellationRow.unitCancelForward))

/-- ★ **THE LEFT ZIG-ZAG IS CONTRACTIBLE.**  `φ_f ~ id f` over the adjoint base relation — the left triangle
straightens the left zig-zag loop (unavailable over the bare relation; this is what the triangle ADDS). -/
theorem walkingAdjEquivLeftZigzagContractible :
    SaturatedConvOverWithId walkingEquivComputad walkingAdjEquivBaseRel
      walkingEquivLeftTriangleLeg walkingEquivIdF :=
  walkingEquivLeftTriangleThreeCell

/-- ★ **THE RIGHT ZIG-ZAG IS CONTRACTIBLE.**  `ψ_g ~ id g` — the right triangle straightens the right loop. -/
theorem walkingAdjEquivRightZigzagContractible :
    SaturatedConvOverWithId walkingEquivComputad walkingAdjEquivBaseRel
      walkingEquivRightTriangleLeg walkingEquivIdG :=
  walkingEquivRightTriangleThreeCell

/-- ★★ **THE DOUBLED LEFT ZIG-ZAG IS CONTRACTIBLE.**  `φ_f . φ_f ~ id f` — even the DOUBLED zig-zag loop
collapses to the identity (fire the left triangle twice, then absorb the trailing identity).  A genuine
contractibility witness: two structurally very different parallel 2-cell words (`φ_f . φ_f` versus `id f`) are
convertible, so the hom is contracted to a point by the triangle. -/
theorem walkingAdjEquivDoubledLeftZigzagContractible :
    SaturatedConvOverWithId walkingEquivComputad walkingAdjEquivBaseRel
      (CellExpr.vcomp walkingEquivLeftTriangleLeg walkingEquivLeftTriangleLeg) walkingEquivIdF :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrLeft walkingEquivLeftTriangleLeg walkingEquivLeftTriangleThreeCell)
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.vcompCongrRight walkingEquivIdF walkingEquivLeftTriangleThreeCell)
      (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft walkingEquivIdF))))

/-! ## The bundled contractibility-exercises statement -/

/-- ★ **The adjoint-walker contractibility-exercises statement.**  A `Prop` conjunction of the four concrete
parallel-uniqueness exercises — the reachable r1 content of the decision. -/
def WalkingAdjEquivContractibilityExercisesStatement : Prop :=
  SaturatedConvOverWithId walkingEquivComputad walkingAdjEquivBaseRel
    walkingEquivEtaEtaInv walkingEquivIdIdA ∧
  SaturatedConvOverWithId walkingEquivComputad walkingAdjEquivBaseRel
    walkingEquivLeftTriangleLeg walkingEquivIdF ∧
  SaturatedConvOverWithId walkingEquivComputad walkingAdjEquivBaseRel
    walkingEquivRightTriangleLeg walkingEquivIdG ∧
  SaturatedConvOverWithId walkingEquivComputad walkingAdjEquivBaseRel
    (CellExpr.vcomp walkingEquivLeftTriangleLeg walkingEquivLeftTriangleLeg) walkingEquivIdF

/-- ★★ **THE ADJOINT-WALKER CONTRACTIBILITY, EXERCISED.**  All four concrete parallel-uniqueness exercises,
machine-checked: the unit loop, the two triangle-straightened zig-zags, and the doubled zig-zag all convertible
to identities over `walkingAdjEquivBaseRel`.  The reachable decision content — the full quantified
parallel-uniqueness is the OMEGA-5 normalizer handoff (below). -/
theorem walkingAdjEquivContractibilityExercised : WalkingAdjEquivContractibilityExercisesStatement :=
  ⟨walkingAdjEquivUnitLoopContractible, walkingAdjEquivLeftZigzagContractible,
    walkingAdjEquivRightZigzagContractible, walkingAdjEquivDoubledLeftZigzagContractible⟩

/-! ## The bare-walker winding candidate (the honest OPEN) -/

/-- The **bare-walker winding candidate pair** `(φ_f, id f)` — the concrete distinguishing pair whose
convertibility over the BARE cancellation relation `walkingEquivBaseRel` (no triangle) is the OPEN winding word
problem.  Over `walkingAdjEquivBaseRel` (with the triangle) it IS convertible
(`walkingAdjEquivLeftZigzagContractible`); over the bare relation it is the free-groupoid decision we do NOT
claim.  Named as data, not decided. -/
def walkingEquivBareWindingCandidate : CellExpr walkingEquivComputad 2 × CellExpr walkingEquivComputad 2 :=
  (walkingEquivLeftTriangleLeg, walkingEquivIdF)

/-! ## B4 non-vacuity -/

/-- The doubled left zig-zag is structurally DISTINCT from `id f` (so the doubled-loop contractibility is
non-vacuous — a genuinely different word collapsing to the identity). -/
theorem walkingAdjEquivDoubledLeftZigzag_distinct :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq
      (CellExpr.vcomp walkingEquivLeftTriangleLeg walkingEquivLeftTriangleLeg) walkingEquivIdF = false := rfl

/-- The winding-candidate pair is a pair of structurally DISTINCT 2-cells (the open decision is between genuinely
different words). -/
theorem walkingEquivBareWindingCandidate_distinct :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq
      walkingEquivBareWindingCandidate.1 walkingEquivBareWindingCandidate.2 = false := rfl

/-! ## B4 non-vacuity probe -/

#eval cellBeq walkingEquivModeBeq walkingEquivGenBeq
  (CellExpr.vcomp walkingEquivLeftTriangleLeg walkingEquivLeftTriangleLeg) walkingEquivIdF

/-! ## B4 honesty markers -/

/-- ★ **THE ADJOINT PARALLEL-UNIQUENESS IS EXERCISED (B4).**  `= true` records the decision content reached:
the adjoint walker's contractibility is EXERCISED on four concrete distinct parallel 2-cell words
(`walkingAdjEquivContractibilityExercised`) — the unit loop, the two triangle-straightened zig-zags, and the
doubled zig-zag, all convertible to identities.  Unlike the walking adjunction (matching-engine decision), the
equivalence's decision is `isTrue`-flavored: the triangles straighten every zig-zag. -/
def fxEquiv_adjointParallelUniquenessExercised : Bool := true

/-- ★ **WALL — the FULL quantified adjoint parallel-uniqueness (B4, OMEGA-5 handoff).**  `= false` records that
the fully quantified "EVERY pair of parallel 2-cells is convertible" is NOT reached this round: it needs a small
2-cell normalizer (a `TwoPath` NF over the invertible generators, straightening arbitrary zig-zag words), the
same OMEGA-5 full-homotopy-basis obligation walled uniformly across the walker family
(`fxOmega4_*FullHomotopyBasisReached = false`).  The shipped content is the concrete contractibility exercises,
not the closure of every parallel hom. -/
def fxEquiv_adjointParallelUniquenessFullyQuantifiedReached : Bool := false

/-- ★ **WALL — the BARE-equivalence parallel-uniqueness is OPEN (B4, honest).**  `= false` records that the
bare walker's parallel-uniqueness is NOT decided: without the triangle, the winding loop `φ_f` and `id f` (the
named candidate `walkingEquivBareWindingCandidate`) are parallel modulo units but NOT forced convertible by the
four cancellation rows — a free-groupoid / winding word problem, a research object.  We name the candidate and
wall the decision; we do NOT claim convertibility (false over the bare relation) NOR non-convertibility (needs a
distinguishing model). -/
def fxEquiv_bareEquivalenceParallelUniquenessOpen : Bool := false

end FX1Poly.Polygraph.Omega
