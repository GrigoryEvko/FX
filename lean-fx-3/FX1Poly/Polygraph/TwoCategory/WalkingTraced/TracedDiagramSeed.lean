/-! # WalkingTraced/TracedDiagramSeed — the walking traced (single-object) PROP: signature + trace-axiom convertibility

The presentation of a WALKING traced monoidal category (Joyal–Street–Verity) as a single-object traced PROP: one
object generator `W`, so objects are wire-counts `Nat` (`I = 0`, `⊗ = +`), and one genuine morphism generator
`box : W ⟶ W` living beside the structural pieces (identities, the symmetry `swap`, sequential `∘`, parallel `⊗`,
and the trace operation `Tr`).  The relations imposed on the free traced PROP are a DECIDABLE-SAFE subset of the
Joyal–Street–Verity trace axioms, phrased as diagram convertibilities:

* **vanishing-I** `Tr^I(f) = f` — tracing zero wires is the identity (`traceN 0 f ≈ f`);
* **yanking** `Tr^W(σ) = id_W` — the yanking / snake move (`traceN 1 swap ≈ idWire`);
* **left naturality / tightening** `Tr^W((g ⊗ id_W) ∘ f) = g ∘ Tr^W(f)` — a bystander on the non-traced input
  wire slides out of the trace (`traceN 1 (seq (tensor g idWire) f) ≈ seq g (traceN 1 f)`).

## ★ Why a NEW carrier — a traced category is not a category and not an operad

The generic 2-computad substrate (`FX1Poly/Polygraph/Computad/Signature.lean`) has `ModalityPath`, the free
CATEGORY: linear composable words, single-input composition by concatenation.  A traced monoidal category's
morphisms compose TWO ways — sequential `∘` AND parallel `⊗` — and additionally carry the trace feedback `Tr`.
Neither `⊗` nor `Tr` has a `ModalityPath` representation (exactly the operad's argument, sharpened by the extra
trace operation), so — like `OperadTree` — brick 1 introduces a fresh inductive `TracedDiagram` and does NOT
instantiate `ModeSignature`.

## ★ Why the carrier is UN-INDEXED (not `Hom : Nat → Nat → Type`)

The trace axioms are naturally stated over `Hom(A ⊗ X, B ⊗ X)`, object-indexed.  Indexing the carrier by objects
would make the convertibility HETEROGENEOUS — LHS and RHS at different object indices — forcing transport along
object equalities (the propext-leak hazard the operad file is built to avoid).  Resolution (the operad's exact
recipe): keep the carrier UN-INDEXED over objects and recover the boundary as a `Nat` structural fold.  With ONE
object generator `W`, objects are `Nat` wire-counts, so the whole signature is a single-object traced PROP and
`TracedDiagramConv` stays homogeneous.  The trace payload `traceN : Nat → …` is a plain `Nat` (the number of
wires fed back), NOT an object index — the carrier stays un-indexed, no transport.

## Scope — BRICK 1

This file ships the SIGNATURE (the un-indexed `TracedDiagram` carrier + the `box` generator + the orientation-only
boundary-signature view + sample diagrams) and the three trace-axiom diagram convertibilities.  The soundness
invariant `boxCount : TracedDiagram → Nat` (genuine-generator count) and the SOUNDNESS theorem (convertible
diagrams ⟹ equal `boxCount`) live in `TracedDiagramBoxCount`.  The FULL traced word-problem DECISION — the
Int-construction `Int(C)` embedding into a compact-closed category and its completeness — is the later brick, NOT
attempted here.

Deliberately EXCLUDED from brick 1's relation (deferred, and one is a soundness trap): vanishing-⊗,
right-tightening, sliding / dinaturality, superposing — and critically the tempting-but-FALSE rule
`traceN 1 (tensor f idWire) ≈ f`: in a general traced category `Tr^W(f ⊗ id_W) = f ⊗ Tr^W(id_W) = f ⊗ loop`,
where `loop = Tr^W(id_W)` is the dimension-of-`W` scalar, NOT the identity — including it would be UNSOUND.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1Poly.Polygraph

/-! ## The traced-diagram carrier -/

/-- ★ The **traced-diagram carrier** of the walking traced PROP: an UN-INDEXED diagram over the single object
generator `W` (objects are wire-counts, `I = 0`, `⊗ = +`).  `empty` is `id_I` (the empty diagram, `0 → 0`);
`idWire` is `id_W` (an identity wire, `1 → 1`); `box` is the ONE genuine morphism generator `b : W ⟶ W`
(`1 → 1`); `swap` is the symmetry `σ` (`2 → 2`, the yanking ingredient); `seq` composes sequentially (`∘`);
`tensor` composes in parallel (`⊗`); and `traceN k` is the trace operation `Tr^{W^k}` feeding the last `k` wires
back.  Un-indexed over objects, so `TracedDiagramConv` is homogeneous — the boundary is recovered by folds, never
carried as an index. -/
inductive TracedDiagram where
  /-- The empty diagram `id_I` (`0 → 0`). -/
  | empty
  /-- An identity wire `id_W` (`1 → 1`). -/
  | idWire
  /-- The one genuine morphism generator `box : W ⟶ W` (`1 → 1`). -/
  | box
  /-- The symmetry `swap = σ : W ⊗ W ⟶ W ⊗ W` (`2 → 2`) — the yanking ingredient. -/
  | swap
  /-- Sequential composition `∘` (the outputs of the first feed the inputs of the second). -/
  | seq : TracedDiagram → TracedDiagram → TracedDiagram
  /-- Parallel composition `⊗` (side-by-side; boundaries add). -/
  | tensor : TracedDiagram → TracedDiagram → TracedDiagram
  /-- The trace operation `Tr^{W^k}` feeding the last `k` output wires back to the last `k` input wires.  The
  `Nat` payload is the fed-back wire-count, NOT an object index — the carrier stays un-indexed. -/
  | traceN : Nat → TracedDiagram → TracedDiagram

/-! ## The genuine morphism generator -/

/-- The generating morphisms of the walking traced PROP — a SINGLETON: the one genuine generator `box`.  The
identities / symmetry / composites / trace are the PROP+trace STRUCTURE, not generators. -/
inductive TracedGenerator where
  /-- The genuine morphism generator `box : W ⟶ W`. -/
  | box

/-! ## The orientation-only boundary signature view

The signature of a single-object traced PROP is, per boundary `(inWires, outWires)`, the SET of genuine
generators of that boundary.  For the walking traced PROP that set is a singleton at boundary `(1, 1)` (the
generator `box : W ⟶ W`) and empty at every other boundary; below it is the boundary-indexed family
`TracedSignature := Nat → Nat → Type` with `(1, 1) ↦ Unit` and everything else `↦ Empty`.  This is the
ORIENTATION-only signature; brick 1 does NOT build a generic boundary-`(m, n)` node from an arbitrary such
signature — that (the free traced PROP on an arbitrary signature) is a later, boundary-generic brick. -/

/-- A single-object traced-PROP **signature**: a boundary-indexed family of generator sets. -/
def TracedSignature := Nat → Nat → Type

/-- ★ The **walking-traced-PROP signature**: one genuine generator (`box : W ⟶ W`, boundary `(1, 1) ↦ Unit`),
and NO generators at any other boundary (`↦ Empty`).  Boundary `(2, 2)` is `Empty` — `swap` is STRUCTURE (the
symmetry of the PROP), not a generator. -/
def tracedBoxSignature : TracedSignature := fun inWires outWires =>
  match inWires, outWires with
  | 1, 1 => Unit
  | _, _ => Empty

/-- Smoke: there is a genuine generator at boundary `(1, 1)` — the morphism `box : W ⟶ W`. -/
theorem tracedBoxSignature_oneOne : tracedBoxSignature 1 1 = Unit := rfl

/-- Smoke: there is NO genuine generator at boundary `(2, 2)` — `swap` is the PROP's symmetry (structure), not a
generator. -/
theorem tracedBoxSignature_twoTwo : tracedBoxSignature 2 2 = Empty := rfl

/-- Smoke: there is NO genuine generator at boundary `(0, 0)` — the empty diagram is `id_I` (structure). -/
theorem tracedBoxSignature_zeroZero : tracedBoxSignature 0 0 = Empty := rfl

/-! ## Concrete sample diagrams -/

/-- The symmetry `σ` on two wires (`swap`). -/
def tracedSwapDiagram : TracedDiagram := TracedDiagram.swap

/-- The genuine generator `box`. -/
def tracedBoxDiagram : TracedDiagram := TracedDiagram.box

/-- The yanking law's left-hand diagram `Tr^W(σ)` — trace one wire of the symmetry. -/
def tracedYankingLeft : TracedDiagram := TracedDiagram.traceN 1 TracedDiagram.swap

/-- The vanishing-I law's left-hand diagram `Tr^I(box)` — trace zero wires of the generator. -/
def tracedVanishingBoxLeft : TracedDiagram := TracedDiagram.traceN 0 TracedDiagram.box

/-- The left-tightening law's left-hand diagram `Tr^W((box ⊗ id_W) ∘ box)` — a bystander `box` on the
non-traced wire, still inside the trace. -/
def tracedTighteningLeft : TracedDiagram :=
  TracedDiagram.traceN 1
    (TracedDiagram.seq (TracedDiagram.tensor TracedDiagram.box TracedDiagram.idWire) TracedDiagram.box)

/-- The left-tightening law's right-hand diagram `box ∘ Tr^W(box)` — the bystander `box` pulled OUT of the
trace, sequenced before the traced remainder. -/
def tracedTighteningRight : TracedDiagram :=
  TracedDiagram.seq TracedDiagram.box (TracedDiagram.traceN 1 TracedDiagram.box)

/-! ## The trace-axiom diagram convertibility -/

/-- ★ The **trace-axiom diagram convertibility** of the walking traced PROP — the free-traced-PROP convertibility
closed under a DECIDABLE-SAFE subset of the Joyal–Street–Verity trace axioms (vanishing-I, yanking, left
naturality / tightening), the FULL diagram-congruence (reaching into the children of `seq` / `tensor` and under a
`traceN`), and `refl` / `symm` / `trans`.  Two diagrams denote the same morphism of the walking traced PROP
exactly when they are `TracedDiagramConv`-related.  The three congruence generators are the diagram analogs of the
operad walker's `mulCongr` / the braid walker's `consCongr`: they whisker a convertibility under each structural
former and (with the axiom firings + `symm` / `trans`) generate the full traced-PROP congruence.  Homogeneous
(both sides `TracedDiagram`) because the carrier is un-indexed over objects — no transport. -/
inductive TracedDiagramConv : TracedDiagram → TracedDiagram → Prop where
  /-- **Vanishing-I** `Tr^I(f) ≈ f` — tracing zero wires is the identity.  The honest firing form (the reason to
  count wires in `traceN` rather than trace a single fixed wire). -/
  | vanishingUnit (innerDiagram : TracedDiagram) :
      TracedDiagramConv (TracedDiagram.traceN 0 innerDiagram) innerDiagram
  /-- **Yanking** `Tr^W(σ) ≈ id_W` — the snake / yanking move.  The signature axiom that puts `swap` in the
  signature. -/
  | yanking :
      TracedDiagramConv (TracedDiagram.traceN 1 TracedDiagram.swap) TracedDiagram.idWire
  /-- **Left naturality / tightening** `Tr^W((g ⊗ id_W) ∘ f) ≈ g ∘ Tr^W(f)` — a bystander `g` on the non-traced
  INPUT wire slides out of the trace.  Realized with the traced wire entering as a LITERAL `idWire`, so the
  soundness arm closes by `rfl`. -/
  | leftTightening (bystander innerDiagram : TracedDiagram) :
      TracedDiagramConv
        (TracedDiagram.traceN 1
          (TracedDiagram.seq (TracedDiagram.tensor bystander TracedDiagram.idWire) innerDiagram))
        (TracedDiagram.seq bystander (TracedDiagram.traceN 1 innerDiagram))
  /-- **Congruence under sequential composition** — reaching into BOTH children:
  `leftOld ≈ leftNew` and `rightOld ≈ rightNew` give `seq leftOld rightOld ≈ seq leftNew rightNew`. -/
  | seqCongr {leftOld leftNew rightOld rightNew : TracedDiagram} :
      TracedDiagramConv leftOld leftNew → TracedDiagramConv rightOld rightNew →
      TracedDiagramConv (TracedDiagram.seq leftOld rightOld) (TracedDiagram.seq leftNew rightNew)
  /-- **Congruence under parallel composition** — reaching into BOTH children:
  `leftOld ≈ leftNew` and `rightOld ≈ rightNew` give `tensor leftOld rightOld ≈ tensor leftNew rightNew`. -/
  | tensorCongr {leftOld leftNew rightOld rightNew : TracedDiagram} :
      TracedDiagramConv leftOld leftNew → TracedDiagramConv rightOld rightNew →
      TracedDiagramConv (TracedDiagram.tensor leftOld rightOld) (TracedDiagram.tensor leftNew rightNew)
  /-- **Congruence under a trace** — for a fixed fed-back wire-count `traceCount`,
  `innerOld ≈ innerNew` gives `traceN traceCount innerOld ≈ traceN traceCount innerNew`. -/
  | traceCongr (traceCount : Nat) {innerOld innerNew : TracedDiagram} :
      TracedDiagramConv innerOld innerNew →
      TracedDiagramConv (TracedDiagram.traceN traceCount innerOld)
        (TracedDiagram.traceN traceCount innerNew)
  /-- Reflexivity. -/
  | refl (diagram : TracedDiagram) : TracedDiagramConv diagram diagram
  /-- Symmetry. -/
  | symm {diagram1 diagram2 : TracedDiagram} :
      TracedDiagramConv diagram1 diagram2 → TracedDiagramConv diagram2 diagram1
  /-- Transitivity. -/
  | trans {diagram1 diagram2 diagram3 : TracedDiagram} :
      TracedDiagramConv diagram1 diagram2 → TracedDiagramConv diagram2 diagram3 →
      TracedDiagramConv diagram1 diagram3

/-- ★ **Vanishing-I holds** — `Tr^I(box) ≈ box`: tracing zero wires of the generator is the identity. -/
theorem tracedVanishingUnitHolds :
    TracedDiagramConv tracedVanishingBoxLeft TracedDiagram.box :=
  TracedDiagramConv.vanishingUnit TracedDiagram.box

/-- ★ **Yanking holds** — `Tr^W(σ) ≈ id_W`: the snake / yanking move. -/
theorem tracedYankingHolds :
    TracedDiagramConv tracedYankingLeft TracedDiagram.idWire :=
  TracedDiagramConv.yanking

/-- ★ **Left tightening holds** — `Tr^W((box ⊗ id_W) ∘ box) ≈ box ∘ Tr^W(box)`: the bystander `box` slides out
of the trace on the input side. -/
theorem tracedLeftTighteningHolds :
    TracedDiagramConv tracedTighteningLeft tracedTighteningRight :=
  TracedDiagramConv.leftTightening TracedDiagram.box TracedDiagram.box

/-- Smoke: the yanking law fires WHISKERED under a parallel composition — `(Tr^W(σ)) ⊗ box ≈ id_W ⊗ box` —
exercising the full diagram-congruence `tensorCongr` (left child rewritten by yanking, right child by `refl`). -/
theorem tracedYankingWhiskeredHolds :
    TracedDiagramConv
      (TracedDiagram.tensor tracedYankingLeft TracedDiagram.box)
      (TracedDiagram.tensor TracedDiagram.idWire TracedDiagram.box) :=
  TracedDiagramConv.tensorCongr tracedYankingHolds (TracedDiagramConv.refl TracedDiagram.box)

end FX1Poly.Polygraph
