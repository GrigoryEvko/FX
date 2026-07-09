import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderWhiskerDerivability
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStaircaseCanonical

/-! # WP-FROB r10 (FROB-10) — the row-suffix brick (WALL) + the comb rerun ASSEMBLY (WIRE)

r9 (`Frobenius/SpiderWhiskerDerivability.lean`) isolated the crossing-straightening residual to ONE named brick — the
row-level SUFFIX congruence — and diagnosed BOTH lift routes (transport recursor, comb-fold rerun) dead at it.  r10
takes the honest next step under the "wire-or-wall, commit per piece" discipline: it EXECUTES the wall at the exact
constructor level and BANKS the carrier-independent crossing-canonicity substrate into the row program.

## The two obstruction levels, sharpened

  * **WALL (P1) — the row-level suffix congruence is structurally unavailable.**  The wanted brick is
    `RowSuffixCongruence`: a `SpiderConvRows` convertibility whiskered by an in-range SUFFIX stays a `SpiderConvRows`
    convertibility (landing in the ROWS, not in `SpiderConv`).  It walls at the CONSTRUCTOR level: every non-equivalence
    generator of `SpiderConvRows` fires its content at the word's TAIL —
      - `ofTable` fires `prefixAtoms ++ frobX.lhs` / `prefixAtoms ++ frobX.rhs` (the r5 gate-free `SpiderConvTable`),
      - `rowBone` fires `frobBone.lhs` / `frobBone.rhs` at the empty boundary,
      - `interchange` fires `prefixAtoms ++ [swapped pair]` at the tail —
    so appending a common suffix `+ + suffix` moves the fired content OFF the tail, where NO generator can re-absorb it.
    Machine-confirmed: on `induction conv`, the `symm` / `trans` arms close, but the three tail-firing arms have no
    closer (the only in-repo suffix closer, `spiderConvTable_suffixCongruence` / `spiderConv_suffixCongruence`, lands in
    `SpiderConv` via the `whisker` PRIMITIVE — the r8 wall).  This SHARPENS r9's "one named row-level suffix congruence"
    from a residual NAME to a CONSTRUCTOR-LEVEL structural impossibility: the `SpiderConvTable` content-at-tail firing
    shape forbids a row-level suffix re-fire; only a table REDESIGN (a suffix-parametric firing, `prefix ++ row ++
    suffix`) would open it.  Flag `fxFrob_hasRowLevelSuffixCongruence = false`.

  * **WIRE (P2) — the crossing canonical section is imported and the comb rerun's ASSEMBLY is shipped conditional on
    the isolated brick.**  The BREACH-2 crossing canonicity (`Brauer/WiringDescStaircaseCanonical.lean`) is
    CARRIER-INDEPENDENT — `recComb` / `combCanonicity` are pure `Nat` / `List` facts with NO `BrauerConvFree7` — so they
    import verbatim into the row program (`frobCrossingStaircase_respectsPermutation` = `combCanonicity` re-exposed, plus
    concrete Frobenius-layer crossing-canonicity witnesses).  The comb rerun's ASSEMBLY
    (`crossingWords_equalPerm_convRows_ofStaircase`) is then SHIPPED: given the whole-staircase convertibility brick
    `RowStaircaseConv` (the `SpiderConvRows` analogue of `recCombConv`), two crossing words with equal through-strand
    permutation are `SpiderConvRows`-convertible — via the imported `combCanonicity` + `trans`/`symm`.  This is SOUND
    (every intermediate is the crossing staircase `crossingWord (recComb …)`, so the detour of obstruction A never
    arises), small, and non-vacuous (`RowStaircaseConv` is inhabited at `generatorCount = 0`).  Per the r9 analysis the
    `RowStaircaseConv` brick's OWN construction rides the walled `RowSuffixCongruence` (the `recCombConv` carry is
    `whiskerRight`), so it stays a hypothesis; flag `fxFrob_hasCrossingRerunAssembly = true`,
    `fxFrob_hasCrossingCanonicityImport = true`.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## P1 — the row-level SUFFIX congruence brick (the isolated WALLED antecedent) -/

/-- ★ **`RowSuffixCongruence`** — the isolated brick r9 named, stated in the ROWS (not in `SpiderConv`): a
row-generated convertibility whiskered by any in-range SUFFIX stays row-generated.  This is the `SpiderConvRows`
analogue of the shipped `spiderConvRows_suffixCongruence` — whose codomain is `SpiderConv` (via the `whisker`
primitive), NOT `SpiderConvRows`.  It is WALLED at the constructor level (see the module docstring): the three
tail-firing generators of `SpiderConvRows` (`ofTable` / `rowBone` / `interchange`) fire content at the word's TAIL, so
a common suffix moves that content off the tail where no generator can re-absorb it.  Kept as an EXPLICIT antecedent —
the honest hypothesis the comb rerun would consume. -/
def RowSuffixCongruence : Prop :=
  ∀ {bottomCount : Nat} {leftWord rightWord suffix : List BrauerAtom},
    0 < bottomCount →
    SpiderConvRows bottomCount leftWord rightWord →
    BrauerWordInRange (processBrauer (brauerSeed bottomCount) leftWord).openWires.length suffix →
    SpiderConvRows bottomCount (leftWord ++ suffix) (rightWord ++ suffix)

/-- ★ **The row-level suffix ESCAPE that DOES close — into `SpiderConv`, not `SpiderConvRows`.**  The r8/r6 shipped
`spiderConvRows_suffixCongruence` gives exactly the brick's conclusion ONE relation up: `SpiderConv` (through the
`whisker` primitive).  So the brick is not false — it is the SAME move, blocked only by the codomain being the rows.
This names precisely what a table redesign would need to internalise. -/
theorem rowSuffixCongruence_escapesToSpiderConv
    {bottomCount : Nat} {leftWord rightWord suffix : List BrauerAtom}
    (bottomPos : 0 < bottomCount) (conv : SpiderConvRows bottomCount leftWord rightWord)
    (suffixInRange :
      BrauerWordInRange (processBrauer (brauerSeed bottomCount) leftWord).openWires.length suffix) :
    SpiderConv bottomCount (leftWord ++ suffix) (rightWord ++ suffix) :=
  spiderConvRows_suffixCongruence bottomPos conv suffixInRange

/-- ★ **The brick's CONCLUSION SHAPE is inhabited at a concrete empty-suffix instance** (non-vacuity of the walled
antecedent).  The two distinct connected words `(μ⊗1)(1⊗δ)` and `(1⊗μ)(δ⊗1)`, each with a trivial `[]` suffix
appended (which reduces definitionally on the concrete literal words), are `SpiderConvRows`-convertible by the rows
alone — so the brick's target relation is genuinely populated, and the wall is a MISSING GENERATOR, not an empty type. -/
theorem rowSuffixCongruence_shape_atEmptySuffix :
    SpiderConvRows 2 (frobLeft.lhs ++ []) (frobRight.lhs ++ []) :=
  spiderConvRows_frobLeft_frobRight_lhs

/-! ## P2 — the crossing canonical section IMPORTED for the row program (carrier-independent WIRE) -/

/-- ★ **The crossing canonical section, exposed for the row program.**  `recComb generatorCount word` is the
recursive-comb STAIRCASE of a crossing word (`Brauer/WiringDescStaircaseCanonical.lean`) — a pure `List Nat → List Nat`
data function with NO `BrauerConvFree7` dependence, so it re-homes verbatim.  It is the crossing-fragment readback the
row program's `CrossingCompletenessHook.readback` restricts to (single symmetric-group block). -/
def frobCrossingStaircase (generatorCount : Nat) (word : List Nat) : List Nat :=
  recComb generatorCount word

/-- ★ **The crossing staircase respects the through-strand permutation (canonicity, banked into the row program).**
This IS `combCanonicity` re-exposed at the Frobenius layer: two crossing words over generators `< generatorCount` with
the SAME permutation on `generatorCount + 1` strands reach the SAME staircase.  Carrier-independent — the Regev–Roichman
section property, importable with zero rewrite. -/
theorem frobCrossingStaircase_respectsPermutation (generatorCount : Nat) (word1 word2 : List Nat)
    (hRange1 : mentionsOnlyBelow generatorCount word1 = true)
    (hRange2 : mentionsOnlyBelow generatorCount word2 = true)
    (permEq : permuteOfCrossingWord (generatorCount + 1) word1
      = permuteOfCrossingWord (generatorCount + 1) word2) :
    frobCrossingStaircase generatorCount word1 = frobCrossingStaircase generatorCount word2 :=
  combCanonicity generatorCount word1 word2 hRange1 hRange2 permEq

/-- Concrete Frobenius-layer canonicity witness — the r9 jam pair `[2,0,1,2]` / `[0,1,2,1]` (same permutation on four
strands) reaches the SAME crossing staircase.  The BREACH-2 canonicity is LIVE for the row program. -/
theorem frobCrossingStaircase_r9jam :
    frobCrossingStaircase 3 [2, 0, 1, 2] = frobCrossingStaircase 3 [0, 1, 2, 1] :=
  frobCrossingStaircase_respectsPermutation 3 [2, 0, 1, 2] [0, 1, 2, 1] (by decide) (by decide) rfl

/-- Concrete Frobenius-layer STRAIGHTENING witness — the same r9 jam pair is `BrauerConvFree7`-convertible (the crossing
straightening, re-exposed).  This is the substrate the row rerun rides; it is imported and firing. -/
theorem frobCrossingStraightening_r9jam :
    BrauerConvFree7 (crossingWord [2, 0, 1, 2]) (crossingWord [0, 1, 2, 1]) :=
  crossingWords_equalPerm_conv 3 [2, 0, 1, 2] [0, 1, 2, 1] (by decide) (by decide) rfl

/-! ## P2 — the whole-staircase convertibility brick + the comb rerun ASSEMBLY -/

/-- ★ **`RowStaircaseConv bottomCount generatorCount`** — the `SpiderConvRows` analogue of `recCombConv`: every
crossing word over generators `< generatorCount` is row-generatively convertible to its crossing staircase.  This is
the whole-staircase convertibility the comb rerun would prove; per the r9 machine-anchored analysis its OWN proof rides
the walled `RowSuffixCongruence` (the `recCombConv` recursive carry is `BrauerConvFree7.whiskerRight (crossingWord
(descendingPositions …))`, the append-common-suffix step), so it is kept as the honest antecedent the assembly
consumes.  Inhabited at `generatorCount = 0` (`rowStaircaseConv_atGeneratorCountZero`). -/
def RowStaircaseConv (bottomCount generatorCount : Nat) : Prop :=
  ∀ word : List Nat, mentionsOnlyBelow generatorCount word = true →
    SpiderConvRows bottomCount (crossingWord word) (crossingWord (recComb generatorCount word))

/-- ★★ **The comb rerun ASSEMBLY (WIRE) — equal-permutation crossing words are `SpiderConvRows`-convertible, given the
staircase brick.**  Mirrors `crossingWords_equalPerm_conv` exactly, but inside the ROW-generated congruence: each word
straightens to its staircase (the brick), the imported `combCanonicity` proves equal permutations reach the SAME
staircase, and `trans`/`symm` chain them.  SOUND without the transport detour (obstruction A): every intermediate is
the crossing staircase `crossingWord (recComb …)`, never a non-crossing word.  So the crossing STRAIGHTENING transports
into `SpiderConvRows` modulo exactly the one walled brick — the comb rerun done, minus the row-level suffix congruence. -/
theorem crossingWords_equalPerm_convRows_ofStaircase {bottomCount generatorCount : Nat}
    (staircase : RowStaircaseConv bottomCount generatorCount)
    (word1 word2 : List Nat)
    (hRange1 : mentionsOnlyBelow generatorCount word1 = true)
    (hRange2 : mentionsOnlyBelow generatorCount word2 = true)
    (permEq : permuteOfCrossingWord (generatorCount + 1) word1
      = permuteOfCrossingWord (generatorCount + 1) word2) :
    SpiderConvRows bottomCount (crossingWord word1) (crossingWord word2) := by
  have canon : recComb generatorCount word1 = recComb generatorCount word2 :=
    combCanonicity generatorCount word1 word2 hRange1 hRange2 permEq
  have conv2 : SpiderConvRows bottomCount
      (crossingWord (recComb generatorCount word1)) (crossingWord word2) := by
    rw [canon]
    exact (staircase word2 hRange2).symm
  exact SpiderConvRows.trans (staircase word1 hRange1) conv2

/-- ★ **The staircase brick is inhabited at `generatorCount = 0`** (non-vacuity of the antecedent).  At level `0` the
only in-range word is empty (`mentionsOnlyBelow 0 (head :: tail)` reduces to `false`), `recComb 0 word = []`, and both
crossing words are `[]`, so the obligation is `SpiderConvRows bottomCount [] []` — closed by the reflexive table row.
So the conditional assembly is genuinely conditional on a NON-EMPTY antecedent type. -/
theorem rowStaircaseConv_atGeneratorCountZero (bottomCount : Nat) :
    RowStaircaseConv bottomCount 0 := by
  intro word hRange
  cases word with
  | nil => exact SpiderConvRows.ofTable (SpiderConvTable.refl bottomCount [])
  | cons head tail => exact Bool.noConfusion hRange

/-- ★ **The assembly FIRES end-to-end at `generatorCount = 0`** — feeding the proven gc=0 brick into
`crossingWords_equalPerm_convRows_ofStaircase` yields a genuine `SpiderConvRows` conclusion (non-vacuity of the whole
conditional, no hypothesis left dangling). -/
theorem crossingWords_equalPerm_convRows_atGeneratorCountZero (bottomCount : Nat)
    (word1 word2 : List Nat)
    (hRange1 : mentionsOnlyBelow 0 word1 = true) (hRange2 : mentionsOnlyBelow 0 word2 = true)
    (permEq : permuteOfCrossingWord 1 word1 = permuteOfCrossingWord 1 word2) :
    SpiderConvRows bottomCount (crossingWord word1) (crossingWord word2) :=
  crossingWords_equalPerm_convRows_ofStaircase (rowStaircaseConv_atGeneratorCountZero bottomCount)
    word1 word2 hRange1 hRange2 permEq

/-- ★ **The assembly's CONCLUSION shape is populated by the rows** — the distant-commute crossing identification
`crossingWord [0,2] ~ crossingWord [2,0]` is a genuine `SpiderConvRows` (via the Godement `interchange`), matching the
assembly's `SpiderConvRows bottomCount (crossingWord _) (crossingWord _)` target on DISTINCT words.  (`crossingWord
[0,2]` reduces definitionally to `[crossingAt 0, crossingAt 2]`.) -/
theorem crossingWords_convRows_distantCommute :
    SpiderConvRows 4 (crossingWord [0, 2]) (crossingWord [2, 0]) :=
  spiderConvRows_distantCommute

end FX1Poly.Polygraph
