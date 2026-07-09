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

end FX1Poly.Polygraph
