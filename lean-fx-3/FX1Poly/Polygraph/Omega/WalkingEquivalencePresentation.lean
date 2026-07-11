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

end FX1Poly.Polygraph.Omega
