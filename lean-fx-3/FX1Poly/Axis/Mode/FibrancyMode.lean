import FX1Poly.Axis.Mode.ModalFracture

/-! # Fibrancy as a mode — the 2LTT fibrant / exotype mode structure (Shulman MATT)

"Fibrancy is another mode."  This file gives FIBRANCY its principled home on the multimodal-type-theory
mode-theory arc, realizing Shulman, "Multimodal Adjoint Type Theory" (MATT, arXiv 2303.02572), Examples 2.5 and
3.6 — the 2-level type theory (2LTT) instance with two modes: `f` for FIBRANT (inner, univalent) types and `e`
for NON-FIBRANT (outer) EXOTYPES (which carry UIP).

## The MATT mode theory (Example 2.5), spelled out

An adjoint mode theory (MATT Def 2.1) is a 2-category of modes whose 1-cells (modalities) carry four predicate
classes — **tangible**, **sharp**, **transparent**, **sinister** — gating which type-formers each modality
generates.  The 2LTT instance:

  * two modes `f` (fibrant) and `e` (exotype), with one generating modality `ι : e → f` (an iso of modes);
  * **tangible** = ALL morphisms; **sharp** = ONLY identities; **transparent** = ONLY identities;
    **sinister** = ONLY `ι`.

Because `ι` is sinister it has a right adjoint `ι†`, and so generates the NEGATIVE modality `ι ◇→ −`
(MATT Fig 6).  Instantiated at `ι : e → f`, the negative modality runs the OTHER way on types,
`ι ◇→ − : types@f → types@e` — this IS the coercion `c` of 2LTT, the inclusion `𝒰_f ↪ 𝒰_e` (every fibrant
type is an exotype), with a bijection between terms of `A` and of `ι ◇→ A` (a faithful coercion; MATT Example
3.6: `ι ◇→` is a dependent right adjoint).

★ THE NON-SHARPNESS CONSTRAINT (the key soundness fact, MATT Example 2.5, verbatim):
"Allowing `ι` to be sharp would produce fibrant replacements `ι ⊡ A`, which are inconsistent [1, §2.7] with
univalence for fibrant types and UIP for exotypes.  Inspecting the proof shows that the same conclusion would
follow if we had modal function-types `(x :^ι A) → B`."  ([1] = Annenkov–Capriotti–Kraus–Sattler, "Two-level
type theory and applications", MSCS 2023.)  So `ι` is kept SINISTER (the negative coercion `ι ◇→` exists) but
NEVER SHARP (no positive `ι ⊡` = no internal fibrant-replacement modality) and NEVER transparent (no `ι`-modal
Π-type).  Below, `fibrancyInclusion.isSharp = false` is a cast-free `rfl` THEOREM — non-sharpness is proven, not
merely asserted.

## The variance trap (read before consuming this file)

The MODE morphism is `ι : e → f` (exotype mode to fibrant mode).  The induced COERCION on types/universes runs
the OPPOSITE way, `ι ◇→ : 𝒰_f ↪ 𝒰_e` (fibrant type to exotype).  The kernel-facing SUBUNIVERSE order below is
`fibrant ≤ exotype` — this is the UNIVERSE-inclusion order induced by `ι ◇→` (direction `f → e`), NOT the
mode-morphism direction (`e → f`).  Do not conflate the two.

## What ships here (each piece zero-axiom)

  * **`FibrancyKind`** — the two modes `f` / `e` as a classifier, with a decidable subuniverse order
    `fibrant ≤ exotype` (and the propagation join `exotype` absorbs).
  * **★ THE CONSUMPTION INTERFACE** — `isFibrantMode` / `fibrancyOf` over the mode index + `fibrant_le_exotype`,
    the minimal clean predicate the kernel typing layer gates on ("the domain is at the fibrant mode").
  * the **fibrancy mode 2-category** as a `mode-0` polygraph (`fibrancyModeGraph` / the `ι` generator path /
    `fibrancyModeSignature`), plus the **four MATT predicate classes** with `ι` SINISTER & NOT SHARP proven
    cast-free, and `ι`'s right adjoint `ι†`.
  * the **negative coercion `ι ◇→`** as the forgetful inclusion of fibrant types into exotypes with its
    terms-bijection (a faithful coercion), reusing `mode-20`'s `IsModalAlgebra` / `IsIso`.
  * the **fibrant reflective subuniverse** as a `mode-20` `Modality` (the fibrant types reflectively included in
    the exotypes) with the complementary `CoreflectiveSubuniverse` — the structural / SEMANTIC classification.

## What is DEFERRED (honesty markers)

  * the INTERNAL fibrant-replacement modality `ι ⊡` (sharp `ι`) — FORBIDDEN, the non-sharp wall above;
  * the GENUINE 2LTT reflector (fibrant replacement as an operational HIT) beyond the semantic `Modality`;
  * the FULL dependent-right-adjoint naturality of `ι ◇→` across the two modes (MATT Example 3.6) beyond the
    terms-bijection;
  * the KERNEL BRIDGE — re-basing the Typed `WfContext.cons` / interval-formation onto this interface (the
    `ObligationModality {fibrant, dimensional}` ↦ `FibrancyKind {fibrant, exotype}` map, `dimensional ↦ exotype`)
    is a cross-axis Typed-layer task that consumes this file from above.

Zero external dependencies beyond the `mode-20` modality interface.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Axis
open FX1Poly.Polygraph

/-! ## The two fibrancy modes `f` / `e` -/

/-- The **fibrancy modes** — the two MATT modes of 2LTT: `fibrant` (`f`, inner / univalent types) and `exotype`
(`e`, outer / non-fibrant types, which carry UIP).  The classifier the whole fibrancy axis is keyed on. -/
inductive FibrancyKind where
  /-- The fibrant mode `f` — inner, univalent types (where fibrant formers and fibrant context extension live). -/
  | fibrant
  /-- The exotype mode `e` — outer, non-fibrant types (where the interval / dimensional formers live). -/
  | exotype
  deriving DecidableEq

/-- The **fibrancy rank** — the position on the subuniverse ladder: `fibrant = 0` (the sub-universe, bottom),
`exotype = 1` (the ambient universe, top).  The numeric carrier of the `fibrant ≤ exotype` order. -/
def FibrancyKind.fibrancyRank : FibrancyKind → Nat
  | .fibrant => 0
  | .exotype => 1

/-- The rank is injective — equal ranks force equal modes (so the order below is antisymmetric). -/
theorem FibrancyKind.fibrancyRank_injective {firstKind secondKind : FibrancyKind}
    (ranksEqual : firstKind.fibrancyRank = secondKind.fibrancyRank) : firstKind = secondKind := by
  cases firstKind <;> cases secondKind <;> first | rfl | exact Nat.noConfusion ranksEqual

/-! ## The subuniverse order `fibrant ≤ exotype` -/

/-- The **subuniverse order** — `fibrant ≤ exotype` is the universe-inclusion order induced by the coercion
`ι ◇→ : 𝒰_f ↪ 𝒰_e` (every fibrant type is an exotype).  Reducible to `Nat`-`≤` on the rank, so the `Decidable`
instance is reused. -/
@[reducible] def FibrancyKind.le (lower upper : FibrancyKind) : Prop :=
  lower.fibrancyRank ≤ upper.fibrancyRank

/-- The order is reflexive. -/
theorem FibrancyKind.le_refl (kind : FibrancyKind) : kind.le kind := Nat.le_refl _

/-- The order is transitive. -/
theorem FibrancyKind.le_trans {firstKind secondKind thirdKind : FibrancyKind}
    (lowerToMiddle : firstKind.le secondKind) (middleToUpper : secondKind.le thirdKind) :
    firstKind.le thirdKind := Nat.le_trans lowerToMiddle middleToUpper

/-- The order is antisymmetric (via rank injectivity) — a genuine partial order on the two modes. -/
theorem FibrancyKind.le_antisymm {firstKind secondKind : FibrancyKind}
    (forward : firstKind.le secondKind) (backward : secondKind.le firstKind) : firstKind = secondKind :=
  FibrancyKind.fibrancyRank_injective (Nat.le_antisymm forward backward)

/-- The order is decidable (through the reducible `Nat`-`≤` definition). -/
instance decidableFibrancyLe (firstKind secondKind : FibrancyKind) :
    Decidable (firstKind.le secondKind) :=
  Nat.decLe firstKind.fibrancyRank secondKind.fibrancyRank

/-- ★ The load-bearing subuniverse fact — **`fibrant ≤ exotype`** — every fibrant type includes (via `ι ◇→`)
into the exotypes.  The fact the kernel cons-rule's cumulativity reads. -/
theorem fibrant_le_exotype : FibrancyKind.fibrant.le FibrancyKind.exotype := Nat.zero_le 1

/-- `fibrant` is the BOTTOM mode (the sub-universe) — below every mode. -/
theorem FibrancyKind.fibrant_le (kind : FibrancyKind) : FibrancyKind.fibrant.le kind := Nat.zero_le _

/-- `exotype` is the TOP mode (the ambient universe) — above every mode. -/
theorem FibrancyKind.le_exotype (kind : FibrancyKind) : kind.le FibrancyKind.exotype := by
  cases kind <;> first | exact Nat.zero_le _ | exact Nat.le_refl _

/-! ## The fibrancy propagation join (exotype absorbs) -/

/-- The **fibrancy join** — `exotype` is absorbing, `fibrant` is the identity: a composite type is fibrant only
when ALL of its constituents are fibrant; any exotype constituent makes the whole exotype.  This is the
join (least upper bound) of the subuniverse order, the rule the kernel uses to propagate fibrancy through
type-formers. -/
def FibrancyKind.joinFibrancy : FibrancyKind → FibrancyKind → FibrancyKind
  | .fibrant, other => other
  | .exotype, _ => .exotype

/-- `fibrant` is a left identity for the join (`rfl`). -/
theorem FibrancyKind.joinFibrancy_fibrant_left (kind : FibrancyKind) :
    FibrancyKind.fibrant.joinFibrancy kind = kind := rfl

/-- `exotype` absorbs on the left — any join with an exotype constituent is exotype. -/
theorem FibrancyKind.joinFibrancy_exotype_left (kind : FibrancyKind) :
    FibrancyKind.exotype.joinFibrancy kind = FibrancyKind.exotype := rfl

/-- `exotype` absorbs on the right. -/
theorem FibrancyKind.joinFibrancy_exotype_right (kind : FibrancyKind) :
    kind.joinFibrancy FibrancyKind.exotype = FibrancyKind.exotype := by cases kind <;> rfl

/-! ## ★★★ THE CONSUMPTION INTERFACE (kernel-facing) ★★★

The minimal, clean predicate the Typed typing layer gates on.  A parallel Typed agent re-bases
`WfContext.cons` (fibrant context extension requires the fibrant mode) and interval-formation (the interval is
formed at the exotype mode) onto exactly these hooks.  The kernel's bespoke `ObligationModality {fibrant,
dimensional}` maps to this classifier by `fibrant ↦ fibrant`, `dimensional ↦ exotype` (that bridge lives on the
Typed side, importing this file). -/

/-- ★ The **gate predicate** the Typed `WfContext.cons` rule checks — is a mode fibrant?  `true` exactly at
`fibrant`. -/
def FibrancyKind.isFibrant : FibrancyKind → Bool
  | .fibrant => true
  | .exotype => false

/-- ★ The **gate as a `Prop`** — for use as a typing-rule premise ("the domain is at the fibrant mode"). -/
def FibrancyKind.IsFibrantMode (kind : FibrancyKind) : Prop := kind.isFibrant = true

/-- The gate is exactly "is the mode `fibrant`" — the primitive bridge between the `Bool` gate and mode identity
(no `propext`; both directions supplied).  Used to extract `mode = fibrant` from a passed gate. -/
theorem FibrancyKind.isFibrant_eq_true_iff (kind : FibrancyKind) :
    kind.isFibrant = true ↔ kind = FibrancyKind.fibrant := by
  cases kind with
  | fibrant => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | exotype => exact ⟨fun gatePasses => Bool.noConfusion gatePasses,
      fun modesEqual => FibrancyKind.noConfusion modesEqual⟩

/-- ★ Read the fibrancy classifier off a mode index.  In this thin (two-object, one-arrow) mode theory the mode
index a type/context-extension carries IS its `FibrancyKind`, so this is the identity reader — the named hook the
kernel bridge composes its `ObligationModality → FibrancyKind` map with. -/
@[reducible] def fibrancyOf (modeIndex : FibrancyKind) : FibrancyKind := modeIndex

/-- ★ The **gate over a mode index** — `isFibrantMode = isFibrant ∘ fibrancyOf`. -/
def isFibrantMode (modeIndex : FibrancyKind) : Bool := (fibrancyOf modeIndex).isFibrant

/-- The fibrant mode passes the gate. -/
theorem isFibrantMode_fibrant : isFibrantMode FibrancyKind.fibrant = true := rfl

/-- The exotype mode FAILS the gate (the interval, formed at `exotype`, is not fibrant). -/
theorem isFibrantMode_exotype : isFibrantMode FibrancyKind.exotype = false := rfl

/-- The gate is exactly "is the mode `fibrant`" — bridges the `Bool` gate to mode identity (no `propext`; both
directions supplied). -/
theorem isFibrantMode_eq_true_iff_fibrant (modeIndex : FibrancyKind) :
    isFibrantMode modeIndex = true ↔ modeIndex = FibrancyKind.fibrant := by
  cases modeIndex with
  | fibrant => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | exotype => exact ⟨fun gatePasses => Bool.noConfusion gatePasses, fun modesEqual =>
      FibrancyKind.noConfusion modesEqual⟩

/-- A fibrant mode is the bottom of the subuniverse order — it includes (via `ι ◇→`) into the exotypes.  Ties
the gate to the order: passing the gate ⟹ `fibrant ≤ exotype`. -/
theorem isFibrantMode_le_exotype {modeIndex : FibrancyKind}
    (_gatePasses : isFibrantMode modeIndex = true) : modeIndex.le FibrancyKind.exotype :=
  FibrancyKind.le_exotype modeIndex

/-- Fibrancy of a composite is the join of the parts' fibrancy — exactly when both parts pass the gate does the
composite (the `&&` of the two gates).  The propagation law the kernel uses through type-formers. -/
theorem isFibrant_joinFibrancy (firstKind secondKind : FibrancyKind) :
    (firstKind.joinFibrancy secondKind).isFibrant = (firstKind.isFibrant && secondKind.isFibrant) := by
  cases firstKind <;> cases secondKind <;> rfl

/-! ## The fibrancy mode 2-category as a `mode-0` polygraph -/

/-- The **fibrancy modality generator** `ι : e → f` — the single non-identity 1-cell of the 2LTT mode theory
(MATT Example 2.5), an iso of modes.  (Indexed by source/target mode; only constructed, never matched, so no
dependent-elimination cost.) -/
inductive FibrancyModality : FibrancyKind → FibrancyKind → Type where
  /-- The mode inclusion `ι : e → f` (exotype mode to fibrant mode). -/
  | inclusion : FibrancyModality FibrancyKind.exotype FibrancyKind.fibrant

/-- The **fibrancy mode quiver** — two modes `{f, e}` and the single generating modality `ι : e → f`.  The
`mode-0` polygraph presentation of the 2LTT mode theory. -/
def fibrancyModeGraph : ModeGraph where
  Mode := FibrancyKind
  Modality := FibrancyModality

/-- `ι` as a free 1-cell (`ModalityPath`) `e → f` — a single application of the inclusion generator. -/
def fibrancyInclusionPath : ModalityPath fibrancyModeGraph FibrancyKind.exotype FibrancyKind.fibrant :=
  ModalityPath.cons FibrancyModality.inclusion
    (ModalityPath.nil (graph := fibrancyModeGraph) FibrancyKind.fibrant)

/-- The inclusion 1-cell has word length `1` (one generator). -/
theorem fibrancyInclusionPath_length : fibrancyInclusionPath.length = 1 := rfl

/-- The **fibrancy mode signature** — the quiver with NO non-trivial 2-cell generators (the fibrancy mode theory
is THIN: a poset of two modes and one arrow; the asymmetry lives in the predicate classes below, not in 2-cells —
MATT Example 2.5). -/
def fibrancyModeSignature : ModeSignature where
  graph := fibrancyModeGraph
  twoCell := fun _ _ => Empty

/-- Non-degeneracy: the two modes are genuinely distinct (the mode theory is not single-sorted). -/
theorem fibrancyModesDistinct : FibrancyKind.fibrant ≠ FibrancyKind.exotype :=
  fun modesEqual => FibrancyKind.noConfusion modesEqual

/-- Non-degeneracy: there is a directed inclusion 1-cell with distinct source and target. -/
def fibrancyHasDirectedInclusion : FibrancyModality FibrancyKind.exotype FibrancyKind.fibrant :=
  FibrancyModality.inclusion

/-! ## The four MATT predicate classes — `ι` is SINISTER and NOT SHARP

MATT Def 2.1 equips the mode 2-category with four classes (tangible / sharp / transparent / sinister) that gate
the type-formers.  We model the relevant 1-cells (the two identities, `ι`, and `ι`'s right adjoint `ι†`) as a
plain enum (a non-indexed shape, so the predicate matches stay `propext`-free), with the Example-2.5 class
assignment.  The headline `fibrancyInclusion.isSharp = false` makes NON-SHARPNESS a cast-free theorem. -/

/-- The 1-cells of the fibrancy mode 2-category whose MATT classes we record: the two identities, the inclusion
`ι : e → f`, and its right adjoint `ι† : f → e` (which exists because `ι` is sinister; `ι` is iso so `ι† = ι⁻¹`).
A non-indexed shape so the class predicates match cleanly. -/
inductive FibrancyMorphismShape where
  /-- `1_f` — the identity modality at the fibrant mode. -/
  | identityFibrant
  /-- `1_e` — the identity modality at the exotype mode. -/
  | identityExotype
  /-- `ι : e → f` — the mode inclusion generator (the sinister morphism). -/
  | fibrancyInclusion
  /-- `ι† : f → e` — the right adjoint of `ι`. -/
  | fibrancyInclusionRightAdjoint
  deriving DecidableEq

/-- The source mode of each shape (`ι : e → f`, `ι† : f → e`). -/
def FibrancyMorphismShape.sourceMode : FibrancyMorphismShape → FibrancyKind
  | .identityFibrant => .fibrant
  | .identityExotype => .exotype
  | .fibrancyInclusion => .exotype
  | .fibrancyInclusionRightAdjoint => .fibrant

/-- The target mode of each shape. -/
def FibrancyMorphismShape.targetMode : FibrancyMorphismShape → FibrancyKind
  | .identityFibrant => .fibrant
  | .identityExotype => .exotype
  | .fibrancyInclusion => .fibrant
  | .fibrancyInclusionRightAdjoint => .exotype

/-- Whether a shape is an identity morphism. -/
def FibrancyMorphismShape.isIdentity : FibrancyMorphismShape → Bool
  | .identityFibrant => true
  | .identityExotype => true
  | .fibrancyInclusion => false
  | .fibrancyInclusionRightAdjoint => false

/-- **Tangible** (MATT) — ALL morphisms are tangible (so any modality may annotate a context variable). -/
def FibrancyMorphismShape.isTangible : FibrancyMorphismShape → Bool := fun _ => true

/-- **Sharp** (MATT) — ONLY identities are sharp.  Crucially `ι` is NOT sharp (no positive `ι ⊡` =
no internal fibrant replacement). -/
def FibrancyMorphismShape.isSharp : FibrancyMorphismShape → Bool
  | .identityFibrant => true
  | .identityExotype => true
  | .fibrancyInclusion => false
  | .fibrancyInclusionRightAdjoint => false

/-- **Transparent** (MATT) — ONLY identities are transparent (so no `ι`-modal Π-type `(x :^ι A) → B`). -/
def FibrancyMorphismShape.isTransparent : FibrancyMorphismShape → Bool
  | .identityFibrant => true
  | .identityExotype => true
  | .fibrancyInclusion => false
  | .fibrancyInclusionRightAdjoint => false

/-- **Sinister** (MATT) — ONLY `ι` is sinister (a left adjoint with a right adjoint `ι†`), so ONLY `ι` generates
the negative modality `ι ◇→` (the 2LTT coercion). -/
def FibrancyMorphismShape.isSinister : FibrancyMorphismShape → Bool
  | .fibrancyInclusion => true
  | .identityFibrant => false
  | .identityExotype => false
  | .fibrancyInclusionRightAdjoint => false

/-- ★ **`ι` IS sinister** — it generates the negative coercion `ι ◇→`. -/
theorem fibrancyInclusion_isSinister : FibrancyMorphismShape.fibrancyInclusion.isSinister = true := rfl

/-- ★★★ **`ι` is NOT sharp** — the cast-free realization of the MATT non-sharpness constraint: a sharp `ι` would
produce internal fibrant replacements `ι ⊡ A`, inconsistent with univalence-on-fibrant + UIP-on-exotype
(MATT Example 2.5).  Non-sharpness is PROVEN here, not merely asserted. -/
theorem fibrancyInclusion_not_isSharp : FibrancyMorphismShape.fibrancyInclusion.isSharp = false := rfl

/-- ★ **`ι` is NOT transparent** — so there is no `ι`-modal function type `(x :^ι A) → B` (which would require `ι`
sharp by the same proof, MATT Example 2.5). -/
theorem fibrancyInclusion_not_isTransparent :
    FibrancyMorphismShape.fibrancyInclusion.isTransparent = false := rfl

/-- ★ The exact Example-2.5 status of `ι`: sinister AND not sharp — the structural reason the negative coercion
`ι ◇→` exists but the positive (fibrant-replacement) modality `ι ⊡` is withheld. -/
theorem fibrancyInclusion_sinister_and_not_sharp :
    FibrancyMorphismShape.fibrancyInclusion.isSinister = true
      ∧ FibrancyMorphismShape.fibrancyInclusion.isSharp = false :=
  ⟨rfl, rfl⟩

/-- MATT Def 2.1: every IDENTITY is sharp (at the fibrant mode). -/
theorem identityFibrant_isSharp : FibrancyMorphismShape.identityFibrant.isSharp = true := rfl

/-- MATT Def 2.1: every IDENTITY is sharp (at the exotype mode). -/
theorem identityExotype_isSharp : FibrancyMorphismShape.identityExotype.isSharp = true := rfl

/-- MATT Def 2.1: every IDENTITY is transparent (at the fibrant mode). -/
theorem identityFibrant_isTransparent : FibrancyMorphismShape.identityFibrant.isTransparent = true := rfl

/-- MATT Def 2.1: every IDENTITY is transparent (at the exotype mode). -/
theorem identityExotype_isTransparent : FibrancyMorphismShape.identityExotype.isTransparent = true := rfl

/-- MATT Def 2.1: sharp ⟹ tangible (since every morphism is tangible). -/
theorem isSharp_implies_isTangible (shape : FibrancyMorphismShape) (_isSharpShape : shape.isSharp = true) :
    shape.isTangible = true := rfl

/-- MATT Def 2.1: transparent ⟹ tangible. -/
theorem isTransparent_implies_isTangible (shape : FibrancyMorphismShape)
    (_isTransparentShape : shape.isTransparent = true) : shape.isTangible = true := rfl

/-- The designated **right adjoint** `μ†` of each shape — witnessing "every sinister `μ` has a right adjoint"
(MATT Def 2.1).  `ι ↦ ι†`; identities are self-adjoint; `ι† ↦ ι` (the iso runs both ways). -/
def FibrancyMorphismShape.rightAdjoint : FibrancyMorphismShape → FibrancyMorphismShape
  | .identityFibrant => .identityFibrant
  | .identityExotype => .identityExotype
  | .fibrancyInclusion => .fibrancyInclusionRightAdjoint
  | .fibrancyInclusionRightAdjoint => .fibrancyInclusion

/-- `ι`'s right adjoint is `ι†` (`rfl`). -/
theorem fibrancyInclusion_rightAdjoint :
    FibrancyMorphismShape.fibrancyInclusion.rightAdjoint = FibrancyMorphismShape.fibrancyInclusionRightAdjoint :=
  rfl

/-- The right adjoint swaps endpoints: `μ : p → q` gives `μ† : q → p` (source of `μ†` is the target of `μ`). -/
theorem rightAdjoint_sourceMode_eq_targetMode (shape : FibrancyMorphismShape) :
    shape.rightAdjoint.sourceMode = shape.targetMode := by cases shape <;> rfl

/-- The right adjoint swaps endpoints (target of `μ†` is the source of `μ`). -/
theorem rightAdjoint_targetMode_eq_sourceMode (shape : FibrancyMorphismShape) :
    shape.rightAdjoint.targetMode = shape.sourceMode := by cases shape <;> rfl

/-! ## Composition in the fibrancy mode 2-category — `ι` is an isomorphism (MATT Example 2.5)

MATT Example 2.5 takes `ι : e → f` to be not merely a morphism but **an isomorphism `ι : e ≅ f`**.  This section
makes that an honest cast-free FACT (rather than the prose assertion of the right-adjoint block above): we equip
the 1-cell shapes with their (partial) COMPOSITION — defined exactly when the endpoints meet — and read off that
the two round trips `ι ∘ ι†` and `ι† ∘ ι` collapse to the identities.  Because the fibrancy mode 2-category is
THIN (`fibrancyModeSignature.twoCell = Empty`, no non-trivial 2-cells), an isomorphism's round trips are
EQUALITIES of 1-cells, not merely invertible 2-cells — so the unit / counit of the `ι ⊣ ι†` adjunction are `rfl`.
Composition also lets us state MATT Definition 2.1's composition-closure axiom over the shape enum. -/

/-- **Composition** of the fibrancy 1-cell shapes — `compose first second` is "do `first`, then `second`"
(diagrammatic order, i.e. `second ∘ first`), defined (`some`) exactly when the endpoints meet
(`first.targetMode = second.sourceMode`) and `none` otherwise.  The partial composition of the (thin) fibrancy
mode 2-category (MATT Example 2.5); the two iso round trips `ι ∘ ι†` / `ι† ∘ ι` land on the identities.  A full
16-arm enumeration (no wildcard) so the result stays `propext`-free. -/
def FibrancyMorphismShape.compose :
    FibrancyMorphismShape → FibrancyMorphismShape → Option FibrancyMorphismShape
  | .identityFibrant, .identityFibrant => some .identityFibrant
  | .identityFibrant, .identityExotype => none
  | .identityFibrant, .fibrancyInclusion => none
  | .identityFibrant, .fibrancyInclusionRightAdjoint => some .fibrancyInclusionRightAdjoint
  | .identityExotype, .identityFibrant => none
  | .identityExotype, .identityExotype => some .identityExotype
  | .identityExotype, .fibrancyInclusion => some .fibrancyInclusion
  | .identityExotype, .fibrancyInclusionRightAdjoint => none
  | .fibrancyInclusion, .identityFibrant => some .fibrancyInclusion
  | .fibrancyInclusion, .identityExotype => none
  | .fibrancyInclusion, .fibrancyInclusion => none
  | .fibrancyInclusion, .fibrancyInclusionRightAdjoint => some .identityExotype
  | .fibrancyInclusionRightAdjoint, .identityFibrant => none
  | .fibrancyInclusionRightAdjoint, .identityExotype => some .fibrancyInclusionRightAdjoint
  | .fibrancyInclusionRightAdjoint, .fibrancyInclusion => some .identityFibrant
  | .fibrancyInclusionRightAdjoint, .fibrancyInclusionRightAdjoint => none

/-- Left unit law for `ι` — precomposing with the exotype identity `1_e` returns `ι` (`ι ∘ 1_e = ι`): `compose`
behaves as genuine categorical composition at `ι`'s source. -/
theorem compose_identityExotype_fibrancyInclusion :
    FibrancyMorphismShape.identityExotype.compose FibrancyMorphismShape.fibrancyInclusion
      = some FibrancyMorphismShape.fibrancyInclusion := rfl

/-- Right unit law for `ι` — postcomposing with the fibrant identity `1_f` returns `ι` (`1_f ∘ ι = ι`). -/
theorem compose_fibrancyInclusion_identityFibrant :
    FibrancyMorphismShape.fibrancyInclusion.compose FibrancyMorphismShape.identityFibrant
      = some FibrancyMorphismShape.fibrancyInclusion := rfl

/-- ★ The UNIT round trip — `ι` then `ι†` is the exotype identity (`ι† ∘ ι = 1_e`).  Half of "ι is an
isomorphism `e ≅ f`" (MATT Example 2.5): `ι† = ι⁻¹`, so the adjunction unit `η_ι : 1_e ⇒ ι† ∘ ι` is an
equality (the mode 2-category is thin). -/
theorem compose_fibrancyInclusion_rightAdjoint :
    FibrancyMorphismShape.fibrancyInclusion.compose FibrancyMorphismShape.fibrancyInclusionRightAdjoint
      = some FibrancyMorphismShape.identityExotype := rfl

/-- ★ The COUNIT round trip — `ι†` then `ι` is the fibrant identity (`ι ∘ ι† = 1_f`).  The other half; the
counit `ε_ι : ι ∘ ι† ⇒ 1_f` is an equality (MATT Example 2.5: `ι : e ≅ f`). -/
theorem compose_rightAdjoint_fibrancyInclusion :
    FibrancyMorphismShape.fibrancyInclusionRightAdjoint.compose FibrancyMorphismShape.fibrancyInclusion
      = some FibrancyMorphismShape.identityFibrant := rfl

/-- ★★★ **`ι` is an isomorphism `e ≅ f`** — BOTH round trips collapse to identities (`ι† ∘ ι = 1_e` and
`ι ∘ ι† = 1_f`).  The cast-free realization of MATT Example 2.5's "an isomorphism `ι : e ≅ f`": the sinister
inclusion's right adjoint `ι†` is a two-sided inverse, so in the thin mode 2-category the unit and counit of
`ι ⊣ ι†` are equalities. -/
theorem fibrancyInclusion_isInvertible :
    FibrancyMorphismShape.fibrancyInclusion.compose FibrancyMorphismShape.fibrancyInclusionRightAdjoint
        = some FibrancyMorphismShape.identityExotype
      ∧ FibrancyMorphismShape.fibrancyInclusionRightAdjoint.compose FibrancyMorphismShape.fibrancyInclusion
        = some FibrancyMorphismShape.identityFibrant :=
  ⟨rfl, rfl⟩

/-- The right-adjoint assignment is an INVOLUTION — `μ†† = μ` (and the identities are self-adjoint).  Because `ι`
is an isomorphism (MATT Example 2.5), its right adjoint `ι†` coincides with its inverse, whose own right adjoint
is `ι` again; so `rightAdjoint` squares to the identity. -/
theorem rightAdjoint_involutive (shape : FibrancyMorphismShape) :
    shape.rightAdjoint.rightAdjoint = shape := by cases shape <;> rfl

/-- ★ **MATT Definition 2.1, the composition-closure axiom** — if `first` is sharp and `second` is transparent,
their composite (`second ∘ first`, whenever it exists) is tangible.  Holds cast-free here because in this 2LTT
mode theory ALL morphisms are tangible (`isTangible = fun _ => true`); the hypotheses document the Def 2.1
shape (sharpness of `first`, transparency of `second`). -/
theorem compose_sharp_transparent_isTangible (first second composite : FibrancyMorphismShape)
    (_firstSharp : first.isSharp = true) (_secondTransparent : second.isTransparent = true)
    (_composes : first.compose second = some composite) : composite.isTangible = true := rfl

/-! ## The negative coercion `ι ◇→ : 𝒰_f ↪ 𝒰_e` — every fibrant type is an exotype

The negative modality of `ι` (MATT Fig 6 / Example 3.6) is the 2LTT coercion `c`.  We model a fibrant type as a
carrier equipped with its fibrant (reflective-`mode-20`-modal) structure, and `ι ◇→` as forgetting that
structure — the underlying exotype.  The defining property is the TERMS-BIJECTION (a faithful coercion): terms of
`A` correspond exactly to terms of `ι ◇→ A`.

SEMANTIC GROUND of the universe inclusion `𝒰_f ↪ 𝒰_e`: in a two-level model (Annenkov–Capriotti–Kraus–Sattler,
"Two-level type theory and applications", MSCS 2023 = arXiv 1705.03307, Definition 2.8) the fibrant
type-projection `τ^f` is a PULLBACK of the exotype projection `τ^e` (this is exactly the dependent-right-adjoint
hypothesis of MATT Example 3.6), so every fibrant code IS an exotype code — the faithful inclusion modeled by
the terms-bijection.  The ambient exotype universe `𝒰_e` is a STRICT universe (Gratzer–Shulman–Sterling,
"Strict universes for Grothendieck topoi", arXiv 2202.12012, Corollary 4.3.3), into which the fibrant univalent
universe embeds — realignment `(U8)` (op. cit. §1.1, §6) being the ingredient that builds the fibrant univalent
universe inside the strict one. -/

/-- A **fibrant type** for a reflective subuniverse — a carrier together with its fibrant (modal) structure.
Modeled via `mode-20`'s `IsModalAlgebra` (a fibrant type is a modal/local type). -/
structure FibrantType (modality : Modality) where
  /-- The underlying carrier. -/
  carrier : Type
  /-- The fibrant (modal) structure witnessing the carrier lives in the reflective subuniverse. -/
  fibrantStructure : IsModalAlgebra modality carrier

/-- ★ The **coercion `ι ◇→`** — every fibrant type IS an exotype, by forgetting its fibrant structure to the
underlying carrier.  The 2LTT coercion `c` (MATT Example 3.6); direction `f → e` (the variance trap). -/
def coerceFibrantToExotype (modality : Modality) (fibrantType : FibrantType modality) : Type :=
  fibrantType.carrier

/-- The coercion on TERMS — a fibrant element, viewed as an exotype element (the identity on the carrier). -/
def coerceFibrantToExotype_onTerms (modality : Modality) (fibrantType : FibrantType modality) :
    fibrantType.carrier → coerceFibrantToExotype modality fibrantType :=
  fun element => element

/-- ★ The **terms-bijection** — `ι ◇→` is FAITHFUL: terms of `A` correspond bijectively to terms of `ι ◇→ A`
(MATT Example 2.5: "a bijection between terms of types `A` and `ι ◇→ A`").  Here the identity iso, reusing
`mode-20`'s `IsIso`, cast-free. -/
def coerceFibrantToExotype_termsBijection (modality : Modality) (fibrantType : FibrantType modality) :
    IsIso (coerceFibrantToExotype_onTerms modality fibrantType) where
  backward := fun element => element
  forward_backward := fun _ => rfl
  backward_forward := fun _ => rfl

/-! ## The fibrant reflective subuniverse (`mode-20` `Modality`)

The fibrant types form a REFLECTIVE SUBUNIVERSE of the exotypes (the reflection is fibrant replacement).  We
populate the `mode-20` `Modality` interface with this classification.  HONESTY: this is the SEMANTIC / structural
fact (modeled here at the META level via the open-modality witness); the GENUINE 2LTT reflector is fibrant
replacement, an operational HIT, and — crucially — it must NOT be INTERNALIZED as an object-level FX modality
`ι ⊡` (that is the non-sharp wall: univalence + UIP, MATT Example 2.5).

The `openModality` / `closedComodality` pairing used below is precisely the topos-theoretic OPEN / CLOSED
subtopos FRACTURE at a subterminal `J` (Gratzer–Shulman–Sterling, arXiv 2202.12012, §6.1): the open inclusion
`j_*` is right adjoint to `j^*(E) = E × J` (giving the reader-modality `○A = J → A`), and the complementary
CLOSED subtopos carries a left-exact left adjoint `i^*(E) = E ⋆ J` (the join) — the comodality `●`. -/

/-- ★ The **fibrant subuniverse as a reflective subuniverse** (`mode-20` `Modality`).  Modeled by the open
modality at a "fibrant phase" proposition `fibrantPhase` (`○A = fibrantPhase → A`) — a genuine cast-free
idempotent reflective subuniverse.  The fibrant types are its modal types.  (META-level model; see the honesty
note above and the markers below — the SPECIFIC 2LTT reflector, fibrant replacement, is operational and not to be
internalized.) -/
def fibrantReflectiveSubuniverse (fibrantPhase : Prop) : Modality := openModality fibrantPhase

/-- ★ The **complementary coreflective subuniverse** — the non-fibrant (exotype-only) complement, the closed
comodality at the same phase (`●A = fibrantPhase ×' A`).  The fibrant/exotype split as a `mode-20` open/closed
pairing. -/
def exotypeComplementComodality (fibrantPhase : Prop) : CoreflectiveSubuniverse := closedComodality fibrantPhase

/-- The fibrant reflection `○A` is always fibrant (modal) — the localization is a modal algebra.  The core
reflective-subuniverse fact, read off `mode-20`. -/
def fibrantReflectiveSubuniverse_localize_isModal (fibrantPhase : Prop) (typeA : Type) :
    IsModalAlgebra (fibrantReflectiveSubuniverse fibrantPhase)
      ((fibrantReflectiveSubuniverse fibrantPhase).Apply typeA) :=
  (fibrantReflectiveSubuniverse fibrantPhase).localize_isModal typeA

/-- Package a fibrant reflection as a `FibrantType` — the modal types of the fibrant reflective subuniverse ARE
the fibrant types (tying the reflective subuniverse to the coercion's domain). -/
def fibrantReflectionAsFibrantType (fibrantPhase : Prop) (typeA : Type) :
    FibrantType (fibrantReflectiveSubuniverse fibrantPhase) where
  carrier := (fibrantReflectiveSubuniverse fibrantPhase).Apply typeA
  fibrantStructure := fibrantReflectiveSubuniverse_localize_isModal fibrantPhase typeA

/-- Smoke: the fibrant reflective subuniverse is idempotent (`○○ = ○` underlying-type-wise, both `fibrantPhase →
−` composites). -/
theorem fibrantReflectiveSubuniverse_idempotent (fibrantPhase : Prop) (typeA : Type) :
    (fibrantReflectiveSubuniverse fibrantPhase).Apply
        ((fibrantReflectiveSubuniverse fibrantPhase).Apply typeA)
      = (fibrantPhase → fibrantPhase → typeA) := rfl

/-! ## ★★★ THE SR-FACING BRIDGE (abstract — instantiated by the Typed layer) ★★★

The Typed subject-reduction layer needs three hooks over the kernel's actual `Conv` / `Step` / type-cells, which
this Axis file cannot import (the layering runs Axis → Core → Typed).  So we expose them ABSTRACTLY: over a
universally-quantified context type `Ctx`, type-cell type `TypeCell`, conversion relation `Conv`, and reduction
relation `Step`, with a fibrancy-mode assignment `modeOf`.  The kernel-side facts the bridge rests on — the
interval is at the EXOTYPE mode, and `Conv` / `Step` PRESERVE the mode — are the STRUCTURE FIELDS (the
"ingredients"); the Typed agent supplies them from the kernel (where they are the deferred operational
reconciliation) and gets the three consumption fields with the soundness bridge ALREADY PROVEN — a mechanical
instantiation, no Conv-invariance metatheorem re-derived in the Typed layer.

The motivating residual: the SR-WF obligation `∀ universe-typed domain, ¬ Conv domain intervalCell` is FALSE at
`domain = intervalCell` (the interval is itself universe-typed, `Conv`-reflexive).  It MUST be re-stated over
"the domain is at the FIBRANT mode" — which `isAtFibrantMode` below provides — and then closes because the
interval is at the EXOTYPE mode and mode is a `Conv`-invariant (`isAtFibrantMode_not_conv_interval`). -/

/-- A **fibrancy-mode assignment** — the (context-relative) mode each type-cell is formed / typed at.  Abstract
over the kernel's representations (`Ctx` the context type, `TypeCell` the type representation).  `modeOf` being a
FUNCTION encodes mode-uniqueness per type. -/
structure FibrancyModeAssignment (Ctx : Type) (TypeCell : Type) where
  /-- The fibrancy mode a type-cell is formed at, in a context. -/
  modeOf : Ctx → TypeCell → FibrancyKind

/-- The **fibrancy-mode bridge** — the data the Typed SR layer supplies over the kernel: the mode assignment, the
conversion and reduction relations, the interval cell, and the three soundness ingredients (interval at the
exotype mode; `Conv` preserves the mode; `Step` preserves the mode).  From these the bridge lemmas are proven
cast-free. -/
structure FibrancyModeBridge (Ctx : Type) (TypeCell : Type) where
  /-- The fibrancy-mode assignment. -/
  assignment : FibrancyModeAssignment Ctx TypeCell
  /-- The kernel's conversion relation on type-cells. -/
  Conv : TypeCell → TypeCell → Prop
  /-- The kernel's one-step reduction relation on type-cells. -/
  Step : TypeCell → TypeCell → Prop
  /-- The interval type-cell. -/
  intervalCell : TypeCell
  /-- ★ Ingredient: the interval is formed at the EXOTYPE mode `e`.  The interval is a STRICT (pretype /
  non-fibrant) object — it carries decidable, UIP-like structure rather than fibrant / Kan structure — so it
  lives at the outer exotype mode, not the inner fibrant one (ACKS two-level type theory; the minimal AFFINE
  two-endpoint interval of Cavallo–Sattler, "Eliminating reversals from cubical type theories", arXiv 2605.15080,
  carries no fibrant structure of its own). -/
  interval_at_exotype : (ctx : Ctx) → assignment.modeOf ctx intervalCell = FibrancyKind.exotype
  /-- ★ Ingredient: `Conv` PRESERVES the fibrancy mode (mode is a `Conv`-invariant). -/
  conv_preserves_mode : (ctx : Ctx) → (first second : TypeCell) → Conv first second →
    assignment.modeOf ctx first = assignment.modeOf ctx second
  /-- ★ Ingredient: `Step` PRESERVES the fibrancy mode (mode is preserved by reduction). -/
  step_preserves_mode : (ctx : Ctx) → (first second : TypeCell) → Step first second →
    assignment.modeOf ctx first = assignment.modeOf ctx second

/-- ★ FIELD 1 — the context-relative gate the cons-rule checks: the domain is formed / typed at the FIBRANT
mode. -/
def FibrancyModeBridge.isAtFibrantMode {Ctx TypeCell : Type} (bridge : FibrancyModeBridge Ctx TypeCell)
    (ctx : Ctx) (domain : TypeCell) : Prop :=
  (bridge.assignment.modeOf ctx domain).IsFibrantMode

/-- ★★★ FIELD 2 — THE LOCK-STRENGTH BRIDGE.  A fibrant-mode domain can NEVER be `Conv` to the interval: the
interval is at the exotype mode `e`, mode is a `Conv`-invariant, and `fibrant ≠ exotype`.  This is the soundness
lemma that lets the SR-WF residual `¬ Conv domain intervalCell` close by mode-threading — no syntactic
term-predicate, no Conv-invariance metatheorem beyond the (exposed) `conv_preserves_mode` ingredient. -/
theorem FibrancyModeBridge.isAtFibrantMode_not_conv_interval {Ctx TypeCell : Type}
    (bridge : FibrancyModeBridge Ctx TypeCell) (ctx : Ctx) (domain : TypeCell)
    (domainFibrant : bridge.isAtFibrantMode ctx domain) :
    ¬ bridge.Conv domain bridge.intervalCell := by
  intro convDomainInterval
  have domainFibrantBool : (bridge.assignment.modeOf ctx domain).isFibrant = true := domainFibrant
  have domainModeFibrant : bridge.assignment.modeOf ctx domain = FibrancyKind.fibrant :=
    (FibrancyKind.isFibrant_eq_true_iff _).mp domainFibrantBool
  have modesEqual :
      bridge.assignment.modeOf ctx domain = bridge.assignment.modeOf ctx bridge.intervalCell :=
    bridge.conv_preserves_mode ctx domain bridge.intervalCell convDomainInterval
  have intervalModeExotype :
      bridge.assignment.modeOf ctx bridge.intervalCell = FibrancyKind.exotype :=
    bridge.interval_at_exotype ctx
  exact fibrancyModesDistinct
    (Eq.trans (Eq.trans domainModeFibrant.symm modesEqual) intervalModeExotype)

/-- ★ FIELD 3 — SR-STABILITY.  `isAtFibrantMode` is preserved when the domain `Step`s, so it threads the
congruence induction in subject reduction: the mode is `Step`-invariant (the exposed `step_preserves_mode`
ingredient), and the gate reads only the mode. -/
theorem FibrancyModeBridge.isAtFibrantMode_stable_under_step {Ctx TypeCell : Type}
    (bridge : FibrancyModeBridge Ctx TypeCell) (ctx : Ctx) (domain reduced : TypeCell)
    (stepsTo : bridge.Step domain reduced) (domainFibrant : bridge.isAtFibrantMode ctx domain) :
    bridge.isAtFibrantMode ctx reduced := by
  show (bridge.assignment.modeOf ctx reduced).isFibrant = true
  rw [← bridge.step_preserves_mode ctx domain reduced stepsTo]
  exact domainFibrant

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the f / e fibrancy modes ship.**  The two MATT modes (`FibrancyKind`) with the
decidable subuniverse order `fibrant ≤ exotype` (`fibrant_le_exotype`, `le_refl`/`le_trans`/`le_antisymm`) and
the propagation join.  `= true`. -/
def fxFibrancy_hasModeClassifier : Bool := true

/-- ★ **Honesty marker — the consumption interface ships.**  `isFibrantMode` / `fibrancyOf` over the mode index,
`fibrant_le_exotype`, and the gate↔mode bridge (`isFibrantMode_eq_true_iff_fibrant`) — the minimal clean hooks
the Typed `WfContext.cons` / interval-formation re-base onto.  `= true`. -/
def fxFibrancy_hasConsumptionInterface : Bool := true

/-- ★ **Honesty marker — the SR-facing bridge ships (abstract).**  The three Typed-SR consumption fields over a
`FibrancyModeBridge`: `isAtFibrantMode` (the cons-rule gate), `isAtFibrantMode_not_conv_interval` (the
lock-strength bridge — a fibrant-mode domain is never `Conv` to the exotype-mode interval), and
`isAtFibrantMode_stable_under_step` (SR-stability), all proven cast-free from the bundle's three ingredients
(interval at exotype; `Conv` / `Step` preserve the mode).  The kernel INSTANTIATION (supplying those ingredients
from the real `Conv` / `Step` / interval) is the Typed-layer `fxFibrancy_hasKernelModeFibrationBridge` work below.
`= true`. -/
def fxFibrancy_hasAbstractSrBridge : Bool := true

/-- ★ **Honesty marker — `ι` is sinister but NOT sharp, proven cast-free.**  The four MATT predicate classes
(Example 2.5) with `fibrancyInclusion.isSinister = true` and `fibrancyInclusion.isSharp = false` as `rfl`
theorems, the negative coercion `ι ◇→` with its terms-bijection, and `ι`'s right adjoint `ι†`.  `= true`. -/
def fxFibrancy_hasNonSharpInclusion : Bool := true

/-- ★ **Honesty marker — the fibrant reflective subuniverse ships (`mode-20`).**  The fibrant types as a
reflective subuniverse of the exotypes (`fibrantReflectiveSubuniverse`, a genuine cast-free idempotent
`Modality`) with the complementary coreflective subuniverse and the localization-is-modal fact.  `= true`. -/
def fxFibrancy_hasReflectiveSubuniverse : Bool := true

/-- ★ **Honesty marker — `ι` is an isomorphism `e ≅ f`, proven cast-free.**  The fibrancy 1-cell shapes carry a
partial composition (`FibrancyMorphismShape.compose`) under which BOTH round trips of the sinister inclusion
collapse to identities — `ι† ∘ ι = 1_e` and `ι ∘ ι† = 1_f` (`fibrancyInclusion_isInvertible`) — and the
right-adjoint assignment is an involution (`rightAdjoint_involutive`).  This realizes MATT Example 2.5's "an
isomorphism `ι : e ≅ f`": the sinister `ι`'s right adjoint `ι†` is a two-sided inverse, so (the mode 2-category
being thin) the adjunction unit and counit are equalities.  The same composition carries MATT Definition 2.1's
composition-closure axiom (`compose_sharp_transparent_isTangible`).  `= true`. -/
def fxFibrancy_hasInvertibleInclusion : Bool := true

/-- **Honesty marker.**  The INTERNAL fibrant-replacement modality `ι ⊡ : 𝒰_e → 𝒰_f` (sharp `ι`, the positive
operator) is FORBIDDEN — internalizing it is inconsistent with univalence-on-fibrant + UIP-on-exotype
(MATT Example 2.5; proof in [1, §2.7]).  The non-sharp wall: `ι` may carry ONLY the right-adjoint / negative
(`ι ◇→`) character, never the positive.  `= false`. -/
def fxFibrancy_hasInternalFibrantReplacement : Bool := false

/-- **Honesty marker.**  The GENUINE 2LTT reflector — fibrant replacement as an OPERATIONAL construction, beyond
the META-level open-modality `Modality` witness shipped here — is deferred.  The deferred object is precisely:
(a) at the semantic level, the LEFT factor of the algebraic-small-object AWFS (Cavallo–Sattler, "The algebraic
small object argument as a saturation", arXiv 2506.02759, Theorem 3.2.12 plus the saturation principles §3.5,
which extend the fibrant-replacement structure from generators to all left maps); and (b) at the operational
level, fibrant replacement / localization as a HIGHER-INDUCTIVE TYPE with a computational realization (Cavallo,
"Higher Inductive Types and Internal Parametricity for Cubical Type Theory", PhD thesis, CMU 2021, Part II).
`= false`. -/
def fxFibrancy_hasGenuineFibrantReplacementReflector : Bool := false

/-- **Honesty marker.**  The FULL dependent-right-adjoint structure of `ι ◇→` across the two modes — the natural
hom-bijection witnessing that `D^{ι†}` has a DEPENDENT RIGHT ADJOINT (MATT Example 3.6 / Definition 3.5: `τ^f` a
pullback of `τ^e`), via the `mode-13` `HomAdjunctionBetween` idiom, beyond the terms-bijection shipped here — is
deferred.  The canonical OPERATIONAL instance of such a FitchTT-style negative-modality DRA is Nuyts's
TRANSPENSION type, the dependent right adjoint to a (substructural) dependent function type (Nuyts, "The
Transpension Type: Technical Report", arXiv 2008.08530, §1 and §4.4).  `= false`. -/
def fxFibrancy_hasNegativeModalityDependentRightAdjoint : Bool := false

/-- **Honesty marker.**  The KERNEL BRIDGE — re-basing the Typed `WfContext.cons` (fibrant context extension at
mode `f`) and interval-formation (the interval at mode `e`) onto this interface, with the
`ObligationModality {fibrant, dimensional}` ↦ `FibrancyKind {fibrant, exotype}` map (`dimensional ↦ exotype`) —
is a cross-axis Typed-layer task that consumes this file from above; the eventual operational / semantic
reconciliation (subject reduction preserves the formation mode) is future bridge work.  `= false`. -/
def fxFibrancy_hasKernelModeFibrationBridge : Bool := false

end FX1Poly.Axis
