import FX1Poly.Polygraph.TwoCategory.Table.FrobeniusSeed
import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderCompleteness
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescPadCongruence

/-! # Polygraph/TwoCategory/Table/FrobeniusReadback — the A->B readback wiring + the deep diagram invariant
transported onto the free-2-cell carrier (POLY-TAB r1 FROB-RESUME, B1)

`Table/InvariantFoldInstances.lean` shipped the boundary-determined `rowConvInvariant_foldEq` instances
(word-length, boundary record) and BANKED the DEEP diagram invariant `extraSpiderDiagramOf` (the union-find
partition over the WORD carrier B = `List BrauerAtom`) as the POLY-TAB-1 obstruction, whose FIRST cause was:
"the word interpreter is not wired — composing `extraSpiderDiagramOf` with the fold needs a bridge turning a
free-2-cell expression (carrier A) into a word (carrier B)".

## Direction: A -> B READBACK (`cell -> word`), NOT B -> A interpretation

The InvariantFoldInstances header mislabelled the bridge "B->A `interpretWordFrom`".  A `rowConvInvariant_foldEq`
invariant must be a TOTAL function `A -> Carrier`; to land `Carrier = SpiderPartitionType` we need
`A -> word -> partition`, i.e. a total `readbackToWord : RawTwoCellExpr frobeniusModeSignature .. -> List
BrauerAtom` (A -> B).  A B -> A map produces cells from words — the wrong shape.  A -> B is total and structural
(the free 2-cell tree has five constructors); the `ModeComputad.interpretWordFrom` word->1-cell-skeleton fold is
`Option`-valued and reconstructs the 1-cell skeleton, a different bridge entirely — not this map.

## The readback, generator by generator (positional convention matched to `processBrauer`)

  * `gen mult / comult / unit / counit` ↦ `[multAt 0] / [comultAt 0] / [unitAt 0] / [counitAt 0]`,
  * `id _` ↦ `[]`,
  * `vcomp a b` ↦ `readbackToWord a ++ readbackToWord b` (word concatenation — `a` fires first, bottom-to-top),
  * `whiskerLeft prefix1Cell body` ↦ `shiftBrauerWord prefix1Cell.length (readbackToWord body)` (LEFT pad:
    every atom position shifts up by the prefix's 1-cell length — the body acts on the trailing strands),
  * `whiskerRight suffix1Cell body` ↦ `readbackToWord body` (RIGHT pad: positions unchanged, the boundary width
    extends — the body acts on the leading strands, which `extraSpiderDiagramOf` reads off its own bottomCount).

The one design fact that makes this land: the readback of each of the four `FrobeniusLawRel` law cells computes
DEFINITIONALLY to the shipped Brauer law word (`frobUnitLeft.lhs`, `frobLeft.lhs`, ...), so the deep invariant's
row-preservation is exactly the shipped per-row soundness witnesses (`frob*_sound`), NOT new proof work.  This is
the transport of the union-find partition invariant onto carrier A — obstruction (1) RESOLVED.

Raw Lean 4 + Init; `readbackToWord` is a full five-case structural recursion (constant-shape `List BrauerAtom`
motive, propext-free like `RawTwoCellExpr.size`); the invariant and its row identities are `def`/`rfl`.  Additive:
nothing outside `Table/` is touched.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

open FX1Poly.Polygraph.Amalgam

/-! ## The generator readback -/

/-- Read a Frobenius generating 2-cell into its single-atom Brauer word at position `0` — the atomic wirings
`μ / δ / η / ε` fired at the leftmost boundary port.  A full four-case match with a non-dependent
`List BrauerAtom` motive, so its recursor is propext-free. -/
def frobeniusReadbackGen {sourceMode targetMode : FrobeniusMode}
    {sourcePath targetPath : ModalityPath frobeniusGraph sourceMode targetMode} :
    FrobeniusTwoCell sourcePath targetPath → List BrauerAtom
  | .mult => [multAt 0]
  | .comult => [comultAt 0]
  | .unit => [unitAt 0]
  | .counit => [counitAt 0]

/-! ## The A -> B readback -/

/-- ★ **The A -> B readback** — a free Frobenius 2-cell expression (carrier A) read into its Brauer generator word
(carrier B = `List BrauerAtom`).  Structural on the five `RawTwoCellExpr` constructors: generators to their atomic
wiring, identity to the empty word, vertical composite to word concatenation, left whisker to the position-shifted
body (LEFT pad by the prefix 1-cell length), right whisker to the unchanged body (RIGHT pad — the boundary width is
read off `extraSpiderDiagramOf`'s bottomCount).  This is the bridge `Table/InvariantFoldInstances.lean` banked as
POLY-TAB-1 obstruction (1). -/
def readbackToWord {sourceMode targetMode : FrobeniusMode} :
    {sourcePath targetPath : ModalityPath frobeniusGraph sourceMode targetMode} →
    RawTwoCellExpr frobeniusModeSignature sourcePath targetPath → List BrauerAtom
  | _, _, .gen generator => frobeniusReadbackGen generator
  | _, _, .id _ => []
  | _, _, .vcomp cellAlpha cellBeta => readbackToWord cellAlpha ++ readbackToWord cellBeta
  | _, _, .whiskerLeft prefix1Cell body => shiftBrauerWord prefix1Cell.length (readbackToWord body)
  | _, _, .whiskerRight _ body => readbackToWord body

/-! ## Homomorphism smokes — the readback is definitional on each constructor -/

/-- Readback commutes with vertical composition (word concatenation) — definitional. -/
theorem readbackToWord_vcomp {sourceMode targetMode : FrobeniusMode}
    {oneCellF oneCellG oneCellH : ModalityPath frobeniusGraph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr frobeniusModeSignature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr frobeniusModeSignature oneCellG oneCellH) :
    readbackToWord (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = readbackToWord cellAlpha ++ readbackToWord cellBeta := rfl

/-- Readback commutes with a left whisker (the LEFT pad shift) — definitional. -/
theorem readbackToWord_whiskerLeft {sourceMode middleMode targetMode : FrobeniusMode}
    (prefix1Cell : ModalityPath frobeniusGraph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath frobeniusGraph middleMode targetMode}
    (body : RawTwoCellExpr frobeniusModeSignature oneCellG oneCellH) :
    readbackToWord (RawTwoCellExpr.whiskerLeft prefix1Cell body)
      = shiftBrauerWord prefix1Cell.length (readbackToWord body) := rfl

/-- Readback commutes with a right whisker (positions unchanged) — definitional. -/
theorem readbackToWord_whiskerRight {sourceMode middleMode targetMode : FrobeniusMode}
    {oneCellF oneCellG : ModalityPath frobeniusGraph sourceMode middleMode}
    (suffix1Cell : ModalityPath frobeniusGraph middleMode targetMode)
    (body : RawTwoCellExpr frobeniusModeSignature oneCellF oneCellG) :
    readbackToWord (RawTwoCellExpr.whiskerRight suffix1Cell body) = readbackToWord body := rfl

/-- Readback of a boundary cast strips it — the cast is `Eq.rec`, collapsing to the identity once its two boundary
equalities are substituted; the word content is boundary-path-invisible. -/
theorem readbackToWord_castBoundary {sourceMode targetMode : FrobeniusMode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath frobeniusGraph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr frobeniusModeSignature sourcePath targetPath) :
    readbackToWord (RawTwoCellExpr.castBoundary hsource htarget cell) = readbackToWord cell := by
  cases hsource; cases htarget; rfl

/-! ## The four law cells read back to the shipped Brauer law words (definitional) -/

/-- The left-unit law cell reads back to `frobUnitLeft.lhs = [unitAt 0, multAt 0]`. -/
theorem readbackToWord_unitLeftCell : readbackToWord frobeniusUnitLeftCell = frobUnitLeft.lhs := rfl

/-- The identity-on-`t` cell reads back to the empty word `frobUnitLeft.rhs`. -/
theorem readbackToWord_idTCell : readbackToWord frobeniusIdTCell = frobUnitLeft.rhs := rfl

/-- The Frobenius "S=X" left composite reads back to `frobLeft.lhs = [comultAt 1, multAt 0]` — the LEFT-pad shift
`shiftBrauerWord 1 [comultAt 0] = [comultAt 1]` fired past the whiskering `t` strand. -/
theorem readbackToWord_leftLhsCell : readbackToWord frobeniusLeftLhsCell = frobLeft.lhs := rfl

/-- The Frobenius "H" element reads back to `frobLeft.rhs = frobRight.rhs = [multAt 0, comultAt 0]`. -/
theorem readbackToWord_HCell : readbackToWord frobeniusHCell = frobLeft.rhs := rfl

/-- The other Frobenius orientation reads back to `frobRight.lhs = [comultAt 0, multAt 1]`. -/
theorem readbackToWord_rightLhsCell : readbackToWord frobeniusRightLhsCell = frobRight.lhs := rfl

/-- The special composite reads back to `frobSpecial.lhs = [comultAt 0, multAt 0]`. -/
theorem readbackToWord_specialCell : readbackToWord frobeniusSpecialCell = frobSpecial.lhs := rfl

/-! ## The deep diagram invariant, transported onto carrier A -/

/-- ★ **The deep Frobenius spider (corelation) invariant on carrier A** — read the free 2-cell into its Brauer
word, then take the extraspecial partition `extraSpiderDiagramOf` over the source 1-cell's word length as
bottomCount.  This is the DEEP invariant `Table/InvariantFoldInstances.lean` banked (not boundary-determined — it
reads the internal generator structure), now a TOTAL function `A -> SpiderPartitionType` via the wired readback. -/
def frobeniusSpiderInvariant {sourceMode targetMode : FrobeniusMode}
    {sourcePath targetPath : ModalityPath frobeniusGraph sourceMode targetMode}
    (cell : RawTwoCellExpr frobeniusModeSignature sourcePath targetPath) : SpiderPartitionType :=
  extraSpiderDiagramOf sourcePath.length (readbackToWord cell)

/-! ## Row preservation — the deep invariant on the four `FrobeniusLawRel` rows

Each row's two law cells read back (definitionally) to the shipped Brauer law words at the row's bottomCount, so
the deep-invariant equality is exactly the shipped per-row seed soundness (`frob*_sound`), projected through
`forgetSpiderClosed`.  This is `rowsPreserve` for the deep `foldEq`/`foldRel` — NOT new proof work. -/

/-- ★ The deep invariant preserves the **left-unit** row `μ(η⊗1) = 1`. -/
theorem frobeniusSpiderInvariant_unitLeft :
    frobeniusSpiderInvariant frobeniusUnitLeftCell = frobeniusSpiderInvariant frobeniusIdTCell :=
  congrArg forgetSpiderClosed frobUnitLeft_sound

/-- ★ The deep invariant preserves the **Frobenius "S=X"** row `(μ⊗1)(1⊗δ) = δμ` — a REAL FUSION row: the two
sides are genuinely different generator words identified as the same spider partition. -/
theorem frobeniusSpiderInvariant_frobLeft :
    frobeniusSpiderInvariant frobeniusLeftLhsCell = frobeniusSpiderInvariant frobeniusHCell :=
  congrArg forgetSpiderClosed frobLeft_sound

/-- ★ The deep invariant preserves the **other Frobenius orientation** row `(1⊗μ)(δ⊗1) = δμ`. -/
theorem frobeniusSpiderInvariant_frobRight :
    frobeniusSpiderInvariant frobeniusRightLhsCell = frobeniusSpiderInvariant frobeniusHCell :=
  congrArg forgetSpiderClosed frobRight_sound

/-- ★ The deep invariant preserves the **special** row `μδ = 1`. -/
theorem frobeniusSpiderInvariant_special :
    frobeniusSpiderInvariant frobeniusSpecialCell = frobeniusSpiderInvariant frobeniusIdTCell :=
  congrArg forgetSpiderClosed frobSpecial_sound

/-! ## Non-vacuity — the deep invariant fires on a real fusion row, taking distinct values across cells -/

-- The Frobenius "S=X" left composite reads back to the connected `{2, 2, [0,0,0,0]}` partition.
#eval frobeniusSpiderInvariant frobeniusLeftLhsCell        -- {2, 2, [0,0,0,0]}
-- The left-unit LHS reads back to the identity-strand `{1, 1, [0,0]}` partition.
#eval frobeniusSpiderInvariant frobeniusUnitLeftCell       -- {1, 1, [0,0]}

/-- ★ **The deep invariant on the Frobenius "S=X" row realizes the connected `2 ⇒ 2` block** — machine-checked, so
the row-preservation `frobeniusSpiderInvariant_frobLeft` is populated by a genuine `{2,2,[0,0,0,0]}` value. -/
theorem frobeniusSpiderInvariant_frobLeft_realizes :
    frobeniusSpiderInvariant frobeniusLeftLhsCell
      = { bottomCount := 2, topCount := 2, blockLabels := [0, 0, 0, 0] } := by decide

/-- ★ **The deep invariant takes MORE than one value across fired rows** — the `frobLeft` row lands the connected
`2 ⇒ 2` block `{2,2,[0,0,0,0]}` while the `unitLeft` row lands the identity strand `{1,1,[0,0]}`, so the invariant
is non-trivial (not a constant). -/
theorem frobeniusSpiderInvariant_twoValues :
    frobeniusSpiderInvariant frobeniusLeftLhsCell
        = { bottomCount := 2, topCount := 2, blockLabels := [0, 0, 0, 0] }
      ∧ frobeniusSpiderInvariant frobeniusUnitLeftCell
        = { bottomCount := 1, topCount := 1, blockLabels := [0, 0] } :=
  ⟨by decide, by decide⟩

/-- ★ **Separation** — the "H" element `δμ` and the identity pair induce DIFFERENT deep invariants on carrier A
(distinct partitions), so the invariant genuinely refutes a parallel pair, exactly as at carrier B
(`extraSpiderDiagram_H_ne_identity`). -/
theorem frobeniusSpiderInvariant_H_ne_identityPair :
    frobeniusSpiderInvariant frobeniusHCell
      ≠ extraSpiderDiagramOf 2 [identityStrandAt 0, identityStrandAt 1] := by decide

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the A -> B readback + the deep diagram invariant on carrier A SHIP (FROB-RESUME B1).**
`readbackToWord` reads a free Frobenius 2-cell (carrier A) into its Brauer generator word (carrier B), structural
over the five `RawTwoCellExpr` constructors (vcomp → `++`, whiskerLeft → `shiftBrauerWord`, whiskerRight →
positions unchanged, castBoundary stripped); the four `FrobeniusLawRel` law cells read back DEFINITIONALLY to the
shipped Brauer law words (`readbackToWord_unitLeftCell` / `_leftLhsCell` / `_rightLhsCell` / `_specialCell`).
`frobeniusSpiderInvariant` transports the DEEP union-find partition invariant `extraSpiderDiagramOf` onto carrier A
— resolving POLY-TAB-1 obstruction (1) (the word interpreter was "not wired") — and PRESERVES each of the four
rows via the shipped seed soundness (`frobeniusSpiderInvariant_unitLeft` / `_frobLeft` / `_frobRight` / `_special`).
NON-VACUOUS: the `frobLeft` fusion row realizes the connected `{2,2,[0,0,0,0]}` block, the invariant takes more
than one value across rows (`frobeniusSpiderInvariant_twoValues`), and separates the "H"/identity pair
(`frobeniusSpiderInvariant_H_ne_identityPair`).  The deep invariant as a full `rowConvInvariant_foldRel` instance
(the four context congruences + the 13-arm `fullPreserves`) is the FROB-RESUME B2 residual.  `= true`. -/
def fxTab_hasFrobeniusReadbackInvariant : Bool := true

end FX1Poly.Polygraph
