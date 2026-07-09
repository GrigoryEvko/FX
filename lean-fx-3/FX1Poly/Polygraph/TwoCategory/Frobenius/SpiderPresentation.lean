import FX1Poly.Polygraph.TwoCategory.Frobenius.PartitionModel

/-! # WP-FROB r1 (FROB-1) — the special / extraspecial commutative Frobenius PRESENTATION

The presentation of the special-commutative-Frobenius spider walker, as DATA: the thirteen relation rows over the
four generators `μ` / `δ` / `η` / `ε` (+ the reused symmetry `σ`), each a `BrauerRelation` (a parallel pair of
generator words over a common boundary), together with the extraspecial (corelation) second seed sharing all
thirteen rows and adding the **bone law** `ε ∘ η = id`.  Each row carries a per-row PARALLELISM witness (both sides
have the same boundary arity, machine-checked) and a per-row SOUNDNESS witness (both sides induce the same spider
diagram at the seed — the special rows under the full `Cospan(FinSet)` invariant, the bone row under the
partition-only extraspecial invariant).

## The symbolic boundary (documented; r1 stays value-level)

Symbolically each row is a 2-cell equation between parallel free 2-cells over the walking-spider `ModeSignature`:
one self-dual object `1`, one self-dual 1-cell `t : 1 ⟶ 1`, and the four generator 2-cells with boundaries that are
`t`-power paths — `μ : t·t ⇒ t`, `δ : t ⇒ t·t`, `η : id ⇒ t`, `ε : t ⇒ id`.  Every row's LHS / RHS share source and
target `t`-power, so the pair is parallel.  The symbolic `SaturatedConvOver` congruence (the `ModeSignature` + a
`FrobeniusLawRel : CellRel` + a `SaturatedConvOver` instance, mirroring `Amalgam/SaturatedOver.lean`'s monad
exemplar) is the r2 deliverable (`fxFrob_hasSymbolicSaturatedConvOver = false`); r1 ships the value-level engine +
presentation + per-row seed soundness, exactly as Brauer's own `WiringDesc.lean` r1 did (its symbolic conv came
later).

## The literature-anchored relation list (Lack; Carboni–Walters; Coya–Fong)

Generators μ (2⇒1), η (0⇒1), δ (1⇒2), ε (1⇒0) + the symmetry σ (2⇒2, reused from Brauer).  Rows:

  1. `frobAssoc`      μ(μ⊗1) = μ(1⊗μ)          (commutative-monoid associativity)
  2. `frobUnitLeft`   μ(η⊗1) = 1               (left unit)
  3. `frobUnitRight`  μ(1⊗η) = 1               (right unit)
  4. `frobCoassoc`    (δ⊗1)δ = (1⊗δ)δ          (cocommutative-comonoid coassociativity)
  5. `frobCounitLeft` (ε⊗1)δ = 1               (left counit)
  6. `frobCounitRight`(1⊗ε)δ = 1               (right counit)
  7. `frobLeft`       (μ⊗1)(1⊗δ) = δμ          (Frobenius / "S=X" law, Carboni–Walters)
  8. `frobRight`      (1⊗μ)(δ⊗1) = δμ          (Frobenius, other orientation)
  9. `frobCommMult`   μσ = μ                    (commutativity of μ)
  10. `frobCommComult` σδ = δ                   (cocommutativity of δ)
  11. `frobCrossingInvolution` σσ = 1⊗1         (symmetry involutivity, R2)
  12. `frobYangBaxter`  YB on three strands     (symmetry naturality, R3 — reused from Brauer, staged)
  13. `frobSpecial`   μδ = 1                    (special / "diamond=1" law, Carboni–Walters)
  B.  `frobBone`      εη = 1₀                   (extra / bone / irredundancy law, Coya–Fong — EXTRASPECIAL ONLY)

Remaining σ-naturality slides of μ / δ / η / ε past a crossing are DERIVABLE from these + Frobenius (Lack,
*Composing PROPs*) — ledgered, not added as r1 generators.

## The two load-bearing checks, discharged in the model

  * Row 13 (special) `μδ = 1` is sound ONLY because the same-class merge (the μ-after-δ bubble) leaves a component
    still touching boundary and is therefore uncounted (`specialBubble_uncounted`): both sides read `{1,1,[0,0],0}`.
    Keeping Brauer's `loops` would break it (loops would read 1 ≠ 0).
  * Row B (bone) `εη = 1₀` is the DISCRIMINATOR between the two seeds: under the special (`Cospan`) invariant the
    unit-then-counit circle has `closedComponents = 1 ≠ 0` (SEPARATED — special does NOT have the bone law), while
    under the extraspecial (corelation) partition-only invariant both sides read `{0,0,[]}` (IDENTIFIED).

Raw Lean 4 + Init; reuses the shipped `BrauerRelation` datum, the spider partition engine (`PartitionModel`), and
Brauer's staged Yang–Baxter process lemmas verbatim.  Structural recursion, no `omega` / `simp`-AC / `native_decide`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The special commutative Frobenius relation rows (as data) -/

/-- **Associativity** μ(μ⊗1) = μ(1⊗μ) over three strands. -/
def frobAssoc : BrauerRelation := { boundaryCount := 3, lhs := [multAt 0, multAt 0], rhs := [multAt 1, multAt 0] }

/-- **Left unit** μ(η⊗1) = 1: a unit on the left leg of a multiplication straightens to the identity strand. -/
def frobUnitLeft : BrauerRelation := { boundaryCount := 1, lhs := [unitAt 0, multAt 0], rhs := [] }

/-- **Right unit** μ(1⊗η) = 1: a unit on the right leg straightens to the identity strand. -/
def frobUnitRight : BrauerRelation := { boundaryCount := 1, lhs := [unitAt 1, multAt 0], rhs := [] }

/-- **Coassociativity** (δ⊗1)δ = (1⊗δ)δ. -/
def frobCoassoc : BrauerRelation :=
  { boundaryCount := 1, lhs := [comultAt 0, comultAt 0], rhs := [comultAt 0, comultAt 1] }

/-- **Left counit** (ε⊗1)δ = 1: a counit on the left leg of a comultiplication straightens to the identity. -/
def frobCounitLeft : BrauerRelation := { boundaryCount := 1, lhs := [comultAt 0, counitAt 0], rhs := [] }

/-- **Right counit** (1⊗ε)δ = 1: a counit on the right leg straightens to the identity. -/
def frobCounitRight : BrauerRelation := { boundaryCount := 1, lhs := [comultAt 0, counitAt 1], rhs := [] }

/-- **Frobenius law** (μ⊗1)(1⊗δ) = δμ (Carboni–Walters "S=X"): comultiply the right strand, then multiply the left
pair, equals multiply then comultiply. -/
def frobLeft : BrauerRelation := { boundaryCount := 2, lhs := [comultAt 1, multAt 0], rhs := [multAt 0, comultAt 0] }

/-- **Frobenius law, other orientation** (1⊗μ)(δ⊗1) = δμ. -/
def frobRight : BrauerRelation := { boundaryCount := 2, lhs := [comultAt 0, multAt 1], rhs := [multAt 0, comultAt 0] }

/-- **Commutativity of μ** μσ = μ: a crossing before a multiplication is absorbed. -/
def frobCommMult : BrauerRelation := { boundaryCount := 2, lhs := [crossingAt 0, multAt 0], rhs := [multAt 0] }

/-- **Cocommutativity of δ** σδ = δ: a crossing after a comultiplication is absorbed. -/
def frobCommComult : BrauerRelation := { boundaryCount := 1, lhs := [comultAt 0, crossingAt 0], rhs := [comultAt 0] }

/-- **Symmetry involutivity** σσ = 1⊗1 (R2) — reused from the Brauer relation set. -/
def frobCrossingInvolution : BrauerRelation :=
  { boundaryCount := 2, lhs := [crossingAt 0, crossingAt 0], rhs := [] }

/-- **Yang–Baxter** (R3) on three strands — reuses Brauer's `yangBaxterLhsWord` / `yangBaxterRhsWord`. -/
def frobYangBaxter : BrauerRelation :=
  { boundaryCount := 3, lhs := yangBaxterLhsWord, rhs := yangBaxterRhsWord }

/-- ★ **The special law** μδ = 1 (Carboni–Walters "diamond=1"): comultiply then multiply straightens to the
identity strand.  The r1 sentinel — sound ONLY because the same-class merge is uncounted. -/
def frobSpecial : BrauerRelation := { boundaryCount := 1, lhs := [comultAt 0, multAt 0], rhs := [] }

/-- ★ **The bone / extra law** εη = 1₀ (Coya–Fong "bone" / "irredundancy") — EXTRASPECIAL ONLY: a unit then a counit
(an isolated circle) is the empty diagram.  Under the special invariant this is SEPARATED (the circle counts);
under the extraspecial partition-only invariant it is IDENTIFIED. -/
def frobBone : BrauerRelation := { boundaryCount := 0, lhs := [unitAt 0, counitAt 0], rhs := [] }

/-- ★ The **special commutative Frobenius presentation**, as a value: the thirteen rows (commutative monoid,
cocommutative comonoid, Frobenius, symmetry, special) presenting the `Cospan(FinSet)` PROP. -/
def specialFrobeniusPresentation : List BrauerRelation :=
  [frobAssoc, frobUnitLeft, frobUnitRight, frobCoassoc, frobCounitLeft, frobCounitRight,
    frobLeft, frobRight, frobCommMult, frobCommComult, frobCrossingInvolution, frobYangBaxter, frobSpecial]

/-- ★ The **extraspecial (corelation) presentation** — the thirteen special rows EXTENDED with the bone law.  The
special presentation is untouched; only the seed adds `frobBone`. -/
def extraSpecialPresentation : List BrauerRelation := specialFrobeniusPresentation ++ [frobBone]

/-! ## Per-row PARALLELISM — both sides have the same boundary arity (machine-checked)

The number of open wires after processing a word over its bottom boundary is the word's top-boundary arity.  Each
row's two sides must produce the SAME top count (the pair is parallel) — checked here independently of the partition
semantics, so the relation is well-formed as a 2-cell equation before any soundness claim. -/

/-- The top-boundary arity of a generator word over `boundaryCount` bottom wires — the open-wire count after
processing.  Reads only `openWires.length`, not the partition extract. -/
def frobWordOutputCount (boundaryCount : Nat) (word : List BrauerAtom) : Nat :=
  (processBrauer (brauerSeed boundaryCount) word).openWires.length

/-- Associativity is parallel (both sides `3 ⇒ 1`). -/
theorem frobAssoc_parallel :
    frobWordOutputCount frobAssoc.boundaryCount frobAssoc.lhs
      = frobWordOutputCount frobAssoc.boundaryCount frobAssoc.rhs := rfl

/-- Left unit is parallel (`1 ⇒ 1`). -/
theorem frobUnitLeft_parallel :
    frobWordOutputCount frobUnitLeft.boundaryCount frobUnitLeft.lhs
      = frobWordOutputCount frobUnitLeft.boundaryCount frobUnitLeft.rhs := rfl

/-- Right unit is parallel (`1 ⇒ 1`). -/
theorem frobUnitRight_parallel :
    frobWordOutputCount frobUnitRight.boundaryCount frobUnitRight.lhs
      = frobWordOutputCount frobUnitRight.boundaryCount frobUnitRight.rhs := rfl

/-- Coassociativity is parallel (`1 ⇒ 3`). -/
theorem frobCoassoc_parallel :
    frobWordOutputCount frobCoassoc.boundaryCount frobCoassoc.lhs
      = frobWordOutputCount frobCoassoc.boundaryCount frobCoassoc.rhs := rfl

/-- Left counit is parallel (`1 ⇒ 1`). -/
theorem frobCounitLeft_parallel :
    frobWordOutputCount frobCounitLeft.boundaryCount frobCounitLeft.lhs
      = frobWordOutputCount frobCounitLeft.boundaryCount frobCounitLeft.rhs := rfl

/-- Right counit is parallel (`1 ⇒ 1`). -/
theorem frobCounitRight_parallel :
    frobWordOutputCount frobCounitRight.boundaryCount frobCounitRight.lhs
      = frobWordOutputCount frobCounitRight.boundaryCount frobCounitRight.rhs := rfl

/-- The Frobenius law is parallel (`2 ⇒ 2`). -/
theorem frobLeft_parallel :
    frobWordOutputCount frobLeft.boundaryCount frobLeft.lhs
      = frobWordOutputCount frobLeft.boundaryCount frobLeft.rhs := rfl

/-- The other Frobenius orientation is parallel (`2 ⇒ 2`). -/
theorem frobRight_parallel :
    frobWordOutputCount frobRight.boundaryCount frobRight.lhs
      = frobWordOutputCount frobRight.boundaryCount frobRight.rhs := rfl

/-- Commutativity of μ is parallel (`2 ⇒ 1`). -/
theorem frobCommMult_parallel :
    frobWordOutputCount frobCommMult.boundaryCount frobCommMult.lhs
      = frobWordOutputCount frobCommMult.boundaryCount frobCommMult.rhs := rfl

/-- Cocommutativity of δ is parallel (`1 ⇒ 2`). -/
theorem frobCommComult_parallel :
    frobWordOutputCount frobCommComult.boundaryCount frobCommComult.lhs
      = frobWordOutputCount frobCommComult.boundaryCount frobCommComult.rhs := rfl

/-- Symmetry involutivity is parallel (`2 ⇒ 2`). -/
theorem frobCrossingInvolution_parallel :
    frobWordOutputCount frobCrossingInvolution.boundaryCount frobCrossingInvolution.lhs
      = frobWordOutputCount frobCrossingInvolution.boundaryCount frobCrossingInvolution.rhs := rfl

/-- Yang–Baxter is parallel (`3 ⇒ 3`) — via Brauer's staged process lemmas (a direct depth-3 fold blows up). -/
theorem frobYangBaxter_parallel :
    frobWordOutputCount frobYangBaxter.boundaryCount frobYangBaxter.lhs
      = frobWordOutputCount frobYangBaxter.boundaryCount frobYangBaxter.rhs := by
  show (processBrauer (brauerSeed 3) yangBaxterLhsWord).openWires.length
      = (processBrauer (brauerSeed 3) yangBaxterRhsWord).openWires.length
  rw [yangBaxterProcessLeft, yangBaxterProcessRight]
  rfl

/-- The special law is parallel (`1 ⇒ 1`). -/
theorem frobSpecial_parallel :
    frobWordOutputCount frobSpecial.boundaryCount frobSpecial.lhs
      = frobWordOutputCount frobSpecial.boundaryCount frobSpecial.rhs := rfl

/-- The bone law is parallel (`0 ⇒ 0`). -/
theorem frobBone_parallel :
    frobWordOutputCount frobBone.boundaryCount frobBone.lhs
      = frobWordOutputCount frobBone.boundaryCount frobBone.rhs := rfl

/-- ★ **Every row of the special presentation is parallel** — the boundaries are machine-checked well-formed. -/
theorem specialFrobeniusPresentation_allParallel :
    (frobWordOutputCount frobAssoc.boundaryCount frobAssoc.lhs
        = frobWordOutputCount frobAssoc.boundaryCount frobAssoc.rhs)
    ∧ (frobWordOutputCount frobUnitLeft.boundaryCount frobUnitLeft.lhs
        = frobWordOutputCount frobUnitLeft.boundaryCount frobUnitLeft.rhs)
    ∧ (frobWordOutputCount frobUnitRight.boundaryCount frobUnitRight.lhs
        = frobWordOutputCount frobUnitRight.boundaryCount frobUnitRight.rhs)
    ∧ (frobWordOutputCount frobCoassoc.boundaryCount frobCoassoc.lhs
        = frobWordOutputCount frobCoassoc.boundaryCount frobCoassoc.rhs)
    ∧ (frobWordOutputCount frobCounitLeft.boundaryCount frobCounitLeft.lhs
        = frobWordOutputCount frobCounitLeft.boundaryCount frobCounitLeft.rhs)
    ∧ (frobWordOutputCount frobCounitRight.boundaryCount frobCounitRight.lhs
        = frobWordOutputCount frobCounitRight.boundaryCount frobCounitRight.rhs)
    ∧ (frobWordOutputCount frobLeft.boundaryCount frobLeft.lhs
        = frobWordOutputCount frobLeft.boundaryCount frobLeft.rhs)
    ∧ (frobWordOutputCount frobRight.boundaryCount frobRight.lhs
        = frobWordOutputCount frobRight.boundaryCount frobRight.rhs)
    ∧ (frobWordOutputCount frobCommMult.boundaryCount frobCommMult.lhs
        = frobWordOutputCount frobCommMult.boundaryCount frobCommMult.rhs)
    ∧ (frobWordOutputCount frobCommComult.boundaryCount frobCommComult.lhs
        = frobWordOutputCount frobCommComult.boundaryCount frobCommComult.rhs)
    ∧ (frobWordOutputCount frobCrossingInvolution.boundaryCount frobCrossingInvolution.lhs
        = frobWordOutputCount frobCrossingInvolution.boundaryCount frobCrossingInvolution.rhs)
    ∧ (frobWordOutputCount frobYangBaxter.boundaryCount frobYangBaxter.lhs
        = frobWordOutputCount frobYangBaxter.boundaryCount frobYangBaxter.rhs)
    ∧ (frobWordOutputCount frobSpecial.boundaryCount frobSpecial.lhs
        = frobWordOutputCount frobSpecial.boundaryCount frobSpecial.rhs) :=
  ⟨frobAssoc_parallel, frobUnitLeft_parallel, frobUnitRight_parallel, frobCoassoc_parallel,
    frobCounitLeft_parallel, frobCounitRight_parallel, frobLeft_parallel, frobRight_parallel,
    frobCommMult_parallel, frobCommComult_parallel, frobCrossingInvolution_parallel, frobYangBaxter_parallel,
    frobSpecial_parallel⟩

/-! ## Per-row SOUNDNESS under the special (`Cospan(FinSet)`) invariant

Both sides of each of the thirteen rows induce the SAME full spider diagram at the seed — the shallow one-atom-deep
rows (units, counits, `μσ`, `σδ`, `σσ`, special) by `rfl`, the four depth-2 four-port rows (associativity,
coassociativity, both Frobenius orientations) via per-row STAGED process reductions, and the Yang–Baxter row by
Brauer's staged single-step chain.

Why the staging: `extractSpiderDiagram` queries `unionFindRootOf state.links` many times, and a monolithic `rfl`
leaves `state.links` as the unreduced `processBrauer` fold — so the kernel re-reduces the whole fold on every
union-find query (no WHNF sharing) and the depth-2 rows explode.  Rewriting `processBrauer` to its concrete
`WireState` literal FIRST (a cheap, bounded, one-shot fold) lets the extractor run on a shared small literal; the
residual `extractSpiderDiagram lit = extractSpiderDiagram lit'` closes by a default-transparency `rfl`. -/

/-- `frobAssoc` LHS `μ(μ⊗1)` processes to its concrete four-node wire state — the staged reduction feeding
`frobAssoc_sound`. -/
theorem frobAssocLhsProcess :
    processBrauer (brauerSeed 3) [multAt 0, multAt 0]
      = { openWires := [4], links := [(2, 4), (3, 4), (1, 3), (0, 3)], nextFresh := 5, loops := 0 } := rfl

/-- `frobAssoc` RHS `μ(1⊗μ)` processes to its concrete wire state. -/
theorem frobAssocRhsProcess :
    processBrauer (brauerSeed 3) [multAt 1, multAt 0]
      = { openWires := [4], links := [(3, 4), (0, 4), (2, 3), (1, 3)], nextFresh := 5, loops := 0 } := rfl

/-- `frobCoassoc` LHS `(δ⊗1)δ` processes to its concrete wire state. -/
theorem frobCoassocLhsProcess :
    processBrauer (brauerSeed 1) [comultAt 0, comultAt 0]
      = { openWires := [3, 4, 2], links := [(3, 4), (2, 3), (1, 2), (0, 1)], nextFresh := 5, loops := 0 } := rfl

/-- `frobCoassoc` RHS `(1⊗δ)δ` processes to its concrete wire state. -/
theorem frobCoassocRhsProcess :
    processBrauer (brauerSeed 1) [comultAt 0, comultAt 1]
      = { openWires := [1, 3, 4], links := [(3, 4), (2, 3), (1, 2), (0, 1)], nextFresh := 5, loops := 0 } := rfl

/-- `frobLeft` LHS `(μ⊗1)(1⊗δ)` processes to its concrete wire state. -/
theorem frobLeftLhsProcess :
    processBrauer (brauerSeed 2) [comultAt 1, multAt 0]
      = { openWires := [4, 3], links := [(3, 4), (0, 4), (2, 3), (1, 2)], nextFresh := 5, loops := 0 } := rfl

/-- The **Frobenius H element** `δμ` (`[multAt 0, comultAt 0]`) processes to its concrete wire state — the SHARED
RHS of both Frobenius orientations (`frobLeft` and `frobRight`). -/
theorem frobHElementProcess :
    processBrauer (brauerSeed 2) [multAt 0, comultAt 0]
      = { openWires := [3, 4], links := [(3, 4), (2, 3), (1, 2), (0, 2)], nextFresh := 5, loops := 0 } := rfl

/-- `frobRight` LHS `(1⊗μ)(δ⊗1)` processes to its concrete wire state. -/
theorem frobRightLhsProcess :
    processBrauer (brauerSeed 2) [comultAt 0, multAt 1]
      = { openWires := [2, 4], links := [(1, 4), (3, 4), (2, 3), (0, 2)], nextFresh := 5, loops := 0 } := rfl

/-- Associativity is diagram-sound — both sides `{3,1,[0,0,0,0],0}` (all four ports one block), via the staged
process reductions (a direct `rfl` re-reduces the fold per union-find query and blows up). -/
theorem frobAssoc_sound :
    spiderDiagramOf frobAssoc.boundaryCount frobAssoc.lhs
      = spiderDiagramOf frobAssoc.boundaryCount frobAssoc.rhs := by
  show extractSpiderDiagram 3 (processBrauer (brauerSeed 3) [multAt 0, multAt 0])
      = extractSpiderDiagram 3 (processBrauer (brauerSeed 3) [multAt 1, multAt 0])
  rw [frobAssocLhsProcess, frobAssocRhsProcess]
  rfl

/-- Left unit is diagram-sound — both sides the identity strand `{1,1,[0,0],0}`. -/
theorem frobUnitLeft_sound :
    spiderDiagramOf frobUnitLeft.boundaryCount frobUnitLeft.lhs
      = spiderDiagramOf frobUnitLeft.boundaryCount frobUnitLeft.rhs := rfl

/-- Right unit is diagram-sound — both sides the identity strand. -/
theorem frobUnitRight_sound :
    spiderDiagramOf frobUnitRight.boundaryCount frobUnitRight.lhs
      = spiderDiagramOf frobUnitRight.boundaryCount frobUnitRight.rhs := rfl

/-- Coassociativity is diagram-sound — both sides `{1,3,[0,0,0,0],0}`, via the staged process reductions. -/
theorem frobCoassoc_sound :
    spiderDiagramOf frobCoassoc.boundaryCount frobCoassoc.lhs
      = spiderDiagramOf frobCoassoc.boundaryCount frobCoassoc.rhs := by
  show extractSpiderDiagram 1 (processBrauer (brauerSeed 1) [comultAt 0, comultAt 0])
      = extractSpiderDiagram 1 (processBrauer (brauerSeed 1) [comultAt 0, comultAt 1])
  rw [frobCoassocLhsProcess, frobCoassocRhsProcess]
  rfl

/-- Left counit is diagram-sound — the counit's wire stays boundary-connected, `{1,1,[0,0],0}`. -/
theorem frobCounitLeft_sound :
    spiderDiagramOf frobCounitLeft.boundaryCount frobCounitLeft.lhs
      = spiderDiagramOf frobCounitLeft.boundaryCount frobCounitLeft.rhs := rfl

/-- Right counit is diagram-sound. -/
theorem frobCounitRight_sound :
    spiderDiagramOf frobCounitRight.boundaryCount frobCounitRight.lhs
      = spiderDiagramOf frobCounitRight.boundaryCount frobCounitRight.rhs := rfl

/-- The Frobenius law is diagram-sound — both sides the `2 ⇒ 2` block `{2,2,[0,0,0,0],0}` (all four ports one
class, no closed component), via the staged process reductions. -/
theorem frobLeft_sound :
    spiderDiagramOf frobLeft.boundaryCount frobLeft.lhs
      = spiderDiagramOf frobLeft.boundaryCount frobLeft.rhs := by
  show extractSpiderDiagram 2 (processBrauer (brauerSeed 2) [comultAt 1, multAt 0])
      = extractSpiderDiagram 2 (processBrauer (brauerSeed 2) [multAt 0, comultAt 0])
  rw [frobLeftLhsProcess, frobHElementProcess]
  rfl

/-- The other Frobenius orientation is diagram-sound, via the staged process reductions (its RHS is the same
`frobHElementProcess` δμ literal). -/
theorem frobRight_sound :
    spiderDiagramOf frobRight.boundaryCount frobRight.lhs
      = spiderDiagramOf frobRight.boundaryCount frobRight.rhs := by
  show extractSpiderDiagram 2 (processBrauer (brauerSeed 2) [comultAt 0, multAt 1])
      = extractSpiderDiagram 2 (processBrauer (brauerSeed 2) [multAt 0, comultAt 0])
  rw [frobRightLhsProcess, frobHElementProcess]
  rfl

/-- Commutativity of μ is diagram-sound — the crossing before μ does not change the merged class. -/
theorem frobCommMult_sound :
    spiderDiagramOf frobCommMult.boundaryCount frobCommMult.lhs
      = spiderDiagramOf frobCommMult.boundaryCount frobCommMult.rhs := rfl

/-- Cocommutativity of δ is diagram-sound — the crossing after δ permutes labels within one block. -/
theorem frobCommComult_sound :
    spiderDiagramOf frobCommComult.boundaryCount frobCommComult.lhs
      = spiderDiagramOf frobCommComult.boundaryCount frobCommComult.rhs := rfl

/-- Symmetry involutivity is diagram-sound — two crossings restore the straight pair. -/
theorem frobCrossingInvolution_sound :
    spiderDiagramOf frobCrossingInvolution.boundaryCount frobCrossingInvolution.lhs
      = spiderDiagramOf frobCrossingInvolution.boundaryCount frobCrossingInvolution.rhs := rfl

/-- ★ Yang–Baxter is diagram-sound — both sides the full reversal `{3,3,[0,1,2,2,1,0],0}`, via Brauer's staged
process lemmas. -/
theorem frobYangBaxter_sound :
    spiderDiagramOf frobYangBaxter.boundaryCount frobYangBaxter.lhs
      = spiderDiagramOf frobYangBaxter.boundaryCount frobYangBaxter.rhs := by
  show extractSpiderDiagram 3 (processBrauer (brauerSeed 3) yangBaxterLhsWord)
      = extractSpiderDiagram 3 (processBrauer (brauerSeed 3) yangBaxterRhsWord)
  rw [yangBaxterProcessLeft, yangBaxterProcessRight]
  rfl

/-- ★ The **special law is genuinely sound** — both sides the identity strand `{1,1,[0,0],0}`, the closed-component
count `0` on both because the μ-after-δ bubble stays boundary-connected (the r1 sentinel). -/
theorem frobSpecial_sound :
    spiderDiagramOf frobSpecial.boundaryCount frobSpecial.lhs
      = spiderDiagramOf frobSpecial.boundaryCount frobSpecial.rhs := rfl

/-- ★ **Every row of the special presentation is diagram-sound** — the conjunction of the thirteen per-row witnesses
under the full `Cospan(FinSet)` invariant. -/
theorem specialFrobeniusPresentation_allSound :
    (spiderDiagramOf frobAssoc.boundaryCount frobAssoc.lhs
        = spiderDiagramOf frobAssoc.boundaryCount frobAssoc.rhs)
    ∧ (spiderDiagramOf frobUnitLeft.boundaryCount frobUnitLeft.lhs
        = spiderDiagramOf frobUnitLeft.boundaryCount frobUnitLeft.rhs)
    ∧ (spiderDiagramOf frobUnitRight.boundaryCount frobUnitRight.lhs
        = spiderDiagramOf frobUnitRight.boundaryCount frobUnitRight.rhs)
    ∧ (spiderDiagramOf frobCoassoc.boundaryCount frobCoassoc.lhs
        = spiderDiagramOf frobCoassoc.boundaryCount frobCoassoc.rhs)
    ∧ (spiderDiagramOf frobCounitLeft.boundaryCount frobCounitLeft.lhs
        = spiderDiagramOf frobCounitLeft.boundaryCount frobCounitLeft.rhs)
    ∧ (spiderDiagramOf frobCounitRight.boundaryCount frobCounitRight.lhs
        = spiderDiagramOf frobCounitRight.boundaryCount frobCounitRight.rhs)
    ∧ (spiderDiagramOf frobLeft.boundaryCount frobLeft.lhs
        = spiderDiagramOf frobLeft.boundaryCount frobLeft.rhs)
    ∧ (spiderDiagramOf frobRight.boundaryCount frobRight.lhs
        = spiderDiagramOf frobRight.boundaryCount frobRight.rhs)
    ∧ (spiderDiagramOf frobCommMult.boundaryCount frobCommMult.lhs
        = spiderDiagramOf frobCommMult.boundaryCount frobCommMult.rhs)
    ∧ (spiderDiagramOf frobCommComult.boundaryCount frobCommComult.lhs
        = spiderDiagramOf frobCommComult.boundaryCount frobCommComult.rhs)
    ∧ (spiderDiagramOf frobCrossingInvolution.boundaryCount frobCrossingInvolution.lhs
        = spiderDiagramOf frobCrossingInvolution.boundaryCount frobCrossingInvolution.rhs)
    ∧ (spiderDiagramOf frobYangBaxter.boundaryCount frobYangBaxter.lhs
        = spiderDiagramOf frobYangBaxter.boundaryCount frobYangBaxter.rhs)
    ∧ (spiderDiagramOf frobSpecial.boundaryCount frobSpecial.lhs
        = spiderDiagramOf frobSpecial.boundaryCount frobSpecial.rhs) :=
  ⟨frobAssoc_sound, frobUnitLeft_sound, frobUnitRight_sound, frobCoassoc_sound, frobCounitLeft_sound,
    frobCounitRight_sound, frobLeft_sound, frobRight_sound, frobCommMult_sound, frobCommComult_sound,
    frobCrossingInvolution_sound, frobYangBaxter_sound, frobSpecial_sound⟩

/-! ## The extraspecial (corelation) soundness — the bone row under the partition-only invariant

Under the extraspecial invariant the closed-component count is discarded (`forgetSpiderClosed`).  The thirteen
special rows stay sound (they carry no closed component to forget), and the bone row `εη = 1₀` becomes sound: both
sides read the empty partition `{0,0,[]}`. -/

/-- The bone law is sound under the extraspecial (partition-only) invariant — both sides `{0,0,[]}` (the isolated
circle is forgotten). -/
theorem frobBone_extraSound :
    extraSpiderDiagramOf frobBone.boundaryCount frobBone.lhs
      = extraSpiderDiagramOf frobBone.boundaryCount frobBone.rhs := rfl

/-- ★ **Every row of the extraspecial presentation is diagram-sound under the partition-only invariant** — the
thirteen special rows (their soundness projected through `forgetSpiderClosed`) together with the bone row. -/
theorem extraSpecialPresentation_allSound :
    (extraSpiderDiagramOf frobAssoc.boundaryCount frobAssoc.lhs
        = extraSpiderDiagramOf frobAssoc.boundaryCount frobAssoc.rhs)
    ∧ (extraSpiderDiagramOf frobUnitLeft.boundaryCount frobUnitLeft.lhs
        = extraSpiderDiagramOf frobUnitLeft.boundaryCount frobUnitLeft.rhs)
    ∧ (extraSpiderDiagramOf frobUnitRight.boundaryCount frobUnitRight.lhs
        = extraSpiderDiagramOf frobUnitRight.boundaryCount frobUnitRight.rhs)
    ∧ (extraSpiderDiagramOf frobCoassoc.boundaryCount frobCoassoc.lhs
        = extraSpiderDiagramOf frobCoassoc.boundaryCount frobCoassoc.rhs)
    ∧ (extraSpiderDiagramOf frobCounitLeft.boundaryCount frobCounitLeft.lhs
        = extraSpiderDiagramOf frobCounitLeft.boundaryCount frobCounitLeft.rhs)
    ∧ (extraSpiderDiagramOf frobCounitRight.boundaryCount frobCounitRight.lhs
        = extraSpiderDiagramOf frobCounitRight.boundaryCount frobCounitRight.rhs)
    ∧ (extraSpiderDiagramOf frobLeft.boundaryCount frobLeft.lhs
        = extraSpiderDiagramOf frobLeft.boundaryCount frobLeft.rhs)
    ∧ (extraSpiderDiagramOf frobRight.boundaryCount frobRight.lhs
        = extraSpiderDiagramOf frobRight.boundaryCount frobRight.rhs)
    ∧ (extraSpiderDiagramOf frobCommMult.boundaryCount frobCommMult.lhs
        = extraSpiderDiagramOf frobCommMult.boundaryCount frobCommMult.rhs)
    ∧ (extraSpiderDiagramOf frobCommComult.boundaryCount frobCommComult.lhs
        = extraSpiderDiagramOf frobCommComult.boundaryCount frobCommComult.rhs)
    ∧ (extraSpiderDiagramOf frobCrossingInvolution.boundaryCount frobCrossingInvolution.lhs
        = extraSpiderDiagramOf frobCrossingInvolution.boundaryCount frobCrossingInvolution.rhs)
    ∧ (extraSpiderDiagramOf frobYangBaxter.boundaryCount frobYangBaxter.lhs
        = extraSpiderDiagramOf frobYangBaxter.boundaryCount frobYangBaxter.rhs)
    ∧ (extraSpiderDiagramOf frobSpecial.boundaryCount frobSpecial.lhs
        = extraSpiderDiagramOf frobSpecial.boundaryCount frobSpecial.rhs)
    ∧ (extraSpiderDiagramOf frobBone.boundaryCount frobBone.lhs
        = extraSpiderDiagramOf frobBone.boundaryCount frobBone.rhs) :=
  ⟨congrArg forgetSpiderClosed frobAssoc_sound, congrArg forgetSpiderClosed frobUnitLeft_sound,
    congrArg forgetSpiderClosed frobUnitRight_sound, congrArg forgetSpiderClosed frobCoassoc_sound,
    congrArg forgetSpiderClosed frobCounitLeft_sound, congrArg forgetSpiderClosed frobCounitRight_sound,
    congrArg forgetSpiderClosed frobLeft_sound, congrArg forgetSpiderClosed frobRight_sound,
    congrArg forgetSpiderClosed frobCommMult_sound, congrArg forgetSpiderClosed frobCommComult_sound,
    congrArg forgetSpiderClosed frobCrossingInvolution_sound, congrArg forgetSpiderClosed frobYangBaxter_sound,
    congrArg forgetSpiderClosed frobSpecial_sound, frobBone_extraSound⟩

/-! ## Non-vacuity — both directions -/

/-- ★ **Identification (non-vacuity).**  The Frobenius law `frobLeft` identifies two GENUINELY DIFFERENT generator
words — `[comultAt 1, multAt 0]` and `[multAt 0, comultAt 0]` are distinct as words — as the SAME spider diagram.
So the invariant makes real identifications, not only reflexive ones. -/
theorem frobLeft_identifies_distinct_words :
    frobLeft.lhs ≠ frobLeft.rhs
      ∧ spiderDiagramOf frobLeft.boundaryCount frobLeft.lhs
          = spiderDiagramOf frobLeft.boundaryCount frobLeft.rhs :=
  ⟨by decide, frobLeft_sound⟩

/-- ★ **Separation (non-vacuity).**  The Frobenius "H" element δμ (`[multAt 0, comultAt 0]`, merging all four ports
into one block) and the identity on two strands (two separate blocks) share the SAME `2 ⇒ 2` boundary yet induce
DIFFERENT spider diagrams — so the invariant refutes a genuine parallel pair.  (The full "different invariant ⟹ not
convertible" against a symbolic congruence is the r2 layer; at r1 this is the value-level separation.) -/
theorem frobeniusH_ne_identity :
    spiderDiagramOf 2 [multAt 0, comultAt 0]
      ≠ spiderDiagramOf 2 [identityStrandAt 0, identityStrandAt 1] := by decide

/-- ★ **The two seeds are a real choice (non-vacuity).**  The bone pair `η` then `ε` vs the empty word is SEPARATED
by the special (`Cospan`) invariant (the isolated circle counts, `closedComponents` `1 ≠ 0`) but IDENTIFIED by the
extraspecial (corelation) partition-only invariant — witnessing that adding the bone law is a genuine, non-trivial
quotient (Coya–Fong: corelations discard the isolated-component count). -/
theorem special_separates_bone_extraspecial_identifies :
    spiderDiagramOf frobBone.boundaryCount frobBone.lhs
        ≠ spiderDiagramOf frobBone.boundaryCount frobBone.rhs
      ∧ extraSpiderDiagramOf frobBone.boundaryCount frobBone.lhs
          = extraSpiderDiagramOf frobBone.boundaryCount frobBone.rhs :=
  ⟨by decide, frobBone_extraSound⟩

/-! ## Honesty markers -/

/-- **Honesty marker — the special-Frobenius spider PRESENTATION is SHIPPED green with per-row parallelism.**  The
thirteen rows (`specialFrobeniusPresentation`) ship as `BrauerRelation` data; every row's boundary is machine-checked
parallel (`specialFrobeniusPresentation_allParallel`) and diagram-sound at the seed
(`specialFrobeniusPresentation_allSound`), the Yang–Baxter row via Brauer's staged process lemmas.  `= true`. -/
def fxFrob_hasSpiderPresentation : Bool := true

/-- **Honesty marker — the special commutative Frobenius seed presents `Cospan(FinSet)`.**  The commutative-monoid +
cocommutative-comonoid + Frobenius + symmetry + special rows are the Lack / Carboni–Walters presentation of the
special-CFA PROP; each is diagram-sound under the full partition + closed-component invariant.  `= true`. -/
def fxFrob_hasSpecialFrobeniusPresentation : Bool := true

/-- **Honesty marker — the extraspecial bone law is SHIPPED as the second seed.**  `extraSpecialPresentation` extends
the thirteen rows with `frobBone` (`εη = 1₀`, Coya–Fong); it is sound under the partition-only (corelation)
invariant (`frobBone_extraSound`, `extraSpecialPresentation_allSound`), and the special-vs-extraspecial split is a
genuine choice (`special_separates_bone_extraspecial_identifies`).  `= true`. -/
def fxFrob_hasExtraSpecialBone : Bool := true

/-- **Honesty marker — per-relation soundness is shipped AT THE SEED.**  Every row induces equal spider diagrams at
the ground boundary; this is the r1 soundness content (mirroring Brauer's per-relation seed witnesses).  `= true`. -/
def fxFrob_hasPerRelationSoundnessAtSeed : Bool := true

/-- **Honesty marker — the FULL contextual partition soundness is NOT closed (FROB-3).**  Lifting per-row seed
soundness to "every convertible pair has equal spider diagram" requires the contextual interchange (Godement) +
whisker congruence closure — the SAME open state-parametric union-find independence residual as the Brauer route
(`fxBrauer` shares it), now over the spider generators.  No new obstruction and no discount; the full induction is
NOT shipped in r1.  `= false`. -/
def fxFrob_hasPartitionSoundness : Bool := false

/-- **Honesty marker — contextual spider soundness rides the shared open Godement residual.**  Per-row soundness is
at the seed only; the contextual closure (relation whiskered after any prefix at any offset in any wider boundary)
is the Brauer `relationAgrees` / pad-congruence machinery re-run over `μ` / `δ` / `η` / `ε`, not yet built for the
spider.  `= false`. -/
def fxFrob_hasContextualSpiderSoundness : Bool := false

/-- **Honesty marker — the symbolic `SaturatedConvOver` congruence is the r2 deliverable.**  The value-level engine +
presentation are shipped; the `ModeSignature` (one self-dual object + self-dual 1-cell `t`) + `FrobeniusLawRel :
CellRel` + `SaturatedConvOver` instance (mirroring `Amalgam/SaturatedOver.lean`'s monad exemplar) are deferred to
r2, exactly as Brauer shipped value-level first.  `= false`. -/
def fxFrob_hasSymbolicSaturatedConvOver : Bool := false

/-- **Honesty marker — COMPLETENESS (equal spider diagram ⇒ convertible) is the classical straightening NF, not yet
built.**  The Coya–Fong spider theorem (two morphisms are equal iff they induce the same corelation) is the
reconstruction target; the Brauer/TL-style straightening algorithm for the spider is settled mathematics, real work,
not shipped.  `= false`. -/
def fxFrob_hasSpiderCompleteness : Bool := false

end FX1Poly.Polygraph
