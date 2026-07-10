import FX1Poly.Polygraph.TwoCategory.Table.FrobeniusReadback

/-! # Polygraph/TwoCategory/Table/FrobeniusFusionNF — spider fusion to the connected canonical spider, on the
carrier-A deep invariant + the general-arity realization scaffolding (POLY-TAB r1 FROB-RESUME, B3)

`Frobenius/SpiderCompleteness.lean` already ships the extraspecial (corelation) word-problem DECISION UNCONDITIONALLY:

  * `spiderConv_complete` — equal `extraSpiderDiagramOf` ⟹ `SpiderConv`, hypothesis-free (no `S_n` crossing comb);
  * `instDecidableSpiderConv` + `fxFrob_hasSpiderConvDecision = true` — the decidable extraspecial word problem;
  * `spiderConvDecision_bothVerdicts` — the decider returns `isTrue` on `frobLeft` and `isFalse` on `H`-vs-identity;
  * `canonicalSpiderOf` (the μ-comb `mergeToOne` then δ-comb `fanToN`, Fauser Thm 3.8) + the CONNECTED realization
    on a demonstrated `(m, n)` family + the carrier-B fusion witnesses (`spiderFusion_frobLeftLhs_toCanonical`).

So B3's headline — "if completeness closes: the #2017 decision + the FROB masters hypothesis-free + both verdicts"
— is SHIPPED.  This file adds the carrier-A face of the spider-fusion normal form (transporting the fusion story onto
the free-2-cell carrier the POLY-TAB lane rides, resolving `Table/FrobeniusReadback.lean`'s B1 invariant into a fusion
statement) and the STRUCTURAL RECURSION SCAFFOLDING the general-arity realization induction (the `fxFrob_hasSpiderFusionNF`
residual) rests on.

## What ships here

  * **The canonical-spider structural recursion** (`canonicalSpiderOf_mergeStep`, `canonicalSpiderOf_fanStep`, the
    base cases) — the μ-comb / δ-comb unfold ONE generator at a time, `rfl`.  These are the cons-recursions a general
    realization induction `extraSpiderDiagramOf m (canonicalSpiderOf m n) = ⟨m, n, replicate (m+n) 0⟩` folds over.
  * **Carrier-A spider fusion** — the free Frobenius law cells' DEEP invariant (`frobeniusSpiderInvariant`, B1) lands
    ON the connected canonical spider: the "H" element IS the canonical `2 ⇒ 2` spider readback (`rfl`), and both
    Frobenius "S=X" orientations FUSE to it (distinct generator words, one canonical spider partition), machine-checked.
  * **One-spider-per-component NF on carrier A** — all three connected `2 ⇒ 2` Frobenius cells share ONE deep invariant,
    which IS the canonical connected `2 ⇒ 2` spider; the left-unit cell fuses to the `1 ⇒ 1` identity strand.

## The residual, banked precisely

The GENERAL-arity realization `extraSpiderDiagramOf m (canonicalSpiderOf m n) = ⟨m, n, replicate (m+n) 0⟩` for ALL `m`,
`n` (the `fxFrob_hasSpiderFusionNF` flip) is a comb-FREE `foldl` induction over the union-find engine
(`processBrauer`): the crux missing step is the seed-merge lemma "prepending `multAt 0` to the word merges the first
two seed wires into the fresh output, dropping the bottom count by one" — union-find surgery on `stepWiring` /
`unionFindJoin` / the fresh-node allocation, the class of proof the shipped `Frobenius/SpiderSuffixCongruence.lean`
soundness stack occupies.  The carrier-A fusion facts here are the CONCRETE instances; the general theorem stays honestly
open (`fxFrob_hasSpiderFusionNF = false`), decoupled from the DECISION (which is already unconditional).

Raw Lean 4 + Init; the recursion lemmas are `rfl`, the fusion facts `rfl` / `decide` on the shipped realizations.
Additive: nothing outside `Table/` is touched.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The canonical-spider structural recursion — the general-realization induction scaffolding -/

/-- The μ-comb `mergeToOne` prepends ONE multiplication per extra input above the singleton: the connected `(m+2) ⇒ n`
canonical spider is `multAt 0` then the `(m+1) ⇒ n` canonical spider.  `rfl` (`mergeToOne` cons + `List.cons_append`) —
the recursion an `extraSpiderDiagramOf`-realization induction folds over on the input side. -/
theorem canonicalSpiderOf_mergeStep (inputs outputCount : Nat) :
    canonicalSpiderOf (inputs + 2) outputCount = multAt 0 :: canonicalSpiderOf (inputs + 1) outputCount := rfl

/-- The δ-comb `fanToN` prepends ONE comultiplication per extra output above the singleton: the connected `1 ⇒ (n+2)`
canonical spider is `comultAt 0` then the `1 ⇒ (n+1)` canonical spider.  `rfl` — the recursion on the output side. -/
theorem canonicalSpiderOf_fanStep (outputs : Nat) :
    canonicalSpiderOf 1 (outputs + 2) = comultAt 0 :: canonicalSpiderOf 1 (outputs + 1) := rfl

/-- The `1 ⇒ 1` canonical spider is the empty word (the bare identity strand). -/
theorem canonicalSpiderOf_oneOne : canonicalSpiderOf 1 1 = [] := rfl

/-- The `2 ⇒ 1` canonical spider is a single multiplication `[μ]`. -/
theorem canonicalSpiderOf_twoOne : canonicalSpiderOf 2 1 = [multAt 0] := rfl

/-- The `2 ⇒ 2` canonical spider is `[μ, δ]` — the Frobenius "H" element (multiply, then comultiply). -/
theorem canonicalSpiderOf_twoTwo : canonicalSpiderOf 2 2 = [multAt 0, comultAt 0] := rfl

/-! ## Carrier-A spider fusion — the free Frobenius cells land on the connected canonical spider

The B1 deep invariant `frobeniusSpiderInvariant` (`extraSpiderDiagramOf` of the readback) sends each connected
`2 ⇒ 2` Frobenius cell onto the canonical connected `2 ⇒ 2` spider partition.  For the "H" cell this is `rfl` (its
readback IS `canonicalSpiderOf 2 2`); for the two "S=X" orientations it is a genuine FUSION (a distinct generator word
identified with the canonical one by a shared partition), machine-checked. -/

/-- The Frobenius "H" element's deep invariant IS the canonical connected `2 ⇒ 2` spider — DEFINITIONALLY: its readback
`[μ, δ]` is exactly `canonicalSpiderOf 2 2`.  The canonical spider is a live free Frobenius cell. -/
theorem frobeniusSpiderInvariant_HCell_isCanonical :
    frobeniusSpiderInvariant frobeniusHCell = extraSpiderDiagramOf 2 (canonicalSpiderOf 2 2) := rfl

/-- ★ **Spider fusion, carrier A: the "S=X" left composite FUSES to the canonical `2 ⇒ 2` spider.**  The distinct
generator word `(mult |> t) . (t <| comult)` (readback `[comultAt 1, multAt 0]`) carries the SAME deep invariant as the
canonical `[μ, δ]` — one connected spider, both orientations collapse to it.  Chains the shipped B1 row soundness
(`frobLeft` collapses to the "H" element) with `_HCell_isCanonical`, no numeric re-evaluation. -/
theorem frobeniusSpiderInvariant_frobLeft_fusesToCanonical :
    frobeniusSpiderInvariant frobeniusLeftLhsCell = extraSpiderDiagramOf 2 (canonicalSpiderOf 2 2) :=
  frobeniusSpiderInvariant_frobLeft.trans frobeniusSpiderInvariant_HCell_isCanonical

/-- ★ **Spider fusion, carrier A: the "S=X" right composite FUSES to the same canonical `2 ⇒ 2` spider.** -/
theorem frobeniusSpiderInvariant_frobRight_fusesToCanonical :
    frobeniusSpiderInvariant frobeniusRightLhsCell = extraSpiderDiagramOf 2 (canonicalSpiderOf 2 2) :=
  frobeniusSpiderInvariant_frobRight.trans frobeniusSpiderInvariant_HCell_isCanonical

/-- ★ **One spider per connected component (carrier A, `2 ⇒ 2`).**  All three connected `2 ⇒ 2` Frobenius cells — the
two "S=X" orientations and the "H" element — carry ONE deep invariant, and that common value is the canonical connected
`2 ⇒ 2` spider `canonicalSpiderOf 2 2`.  The spider-fusion normal form realized on the free-2-cell carrier: distinct
words, one canonical spider. -/
theorem frobeniusCells_fuseToOneSpider :
    frobeniusSpiderInvariant frobeniusLeftLhsCell = extraSpiderDiagramOf 2 (canonicalSpiderOf 2 2)
      ∧ frobeniusSpiderInvariant frobeniusRightLhsCell = extraSpiderDiagramOf 2 (canonicalSpiderOf 2 2)
      ∧ frobeniusSpiderInvariant frobeniusHCell = extraSpiderDiagramOf 2 (canonicalSpiderOf 2 2) :=
  ⟨frobeniusSpiderInvariant_frobLeft_fusesToCanonical,
   frobeniusSpiderInvariant_frobRight_fusesToCanonical,
   frobeniusSpiderInvariant_HCell_isCanonical⟩

/-- The identity-on-`t` cell's deep invariant IS the canonical `1 ⇒ 1` spider — DEFINITIONALLY: its readback is the
empty word, exactly `canonicalSpiderOf 1 1`. -/
theorem frobeniusSpiderInvariant_idTCell_isStrand :
    frobeniusSpiderInvariant frobeniusIdTCell = extraSpiderDiagramOf 1 (canonicalSpiderOf 1 1) := rfl

/-- ★ **The left-unit cell fuses to the `1 ⇒ 1` identity strand.**  `mult . (unit |> t)`'s deep invariant is the
canonical `1 ⇒ 1` spider (the empty word / bare strand) — the unit law collapses a birth-then-merge to the identity, on
the carrier-A invariant.  Chains the shipped B1 row soundness (`unitLeft` collapses to `id_t`) with `_idTCell_isStrand`. -/
theorem frobeniusSpiderInvariant_unitLeft_fusesToStrand :
    frobeniusSpiderInvariant frobeniusUnitLeftCell = extraSpiderDiagramOf 1 (canonicalSpiderOf 1 1) :=
  frobeniusSpiderInvariant_unitLeft.trans frobeniusSpiderInvariant_idTCell_isStrand

/-! ## Honesty markers -/

/-- ★ **Honesty marker — spider fusion to the connected canonical spider SHIPS on carrier A (FROB-RESUME B3).**  The
canonical-spider structural recursion (`canonicalSpiderOf_mergeStep` / `_fanStep` + the base cases, the μ-comb / δ-comb
one-generator unfolds an `extraSpiderDiagramOf`-realization induction folds over) and the carrier-A fusion facts: the B1
deep invariant `frobeniusSpiderInvariant` sends the "H" element onto the canonical `2 ⇒ 2` spider DEFINITIONALLY
(`frobeniusSpiderInvariant_HCell_isCanonical`), FUSES both "S=X" orientations to it
(`frobeniusSpiderInvariant_frobLeft_fusesToCanonical` / `_frobRight_`), collapses all three connected `2 ⇒ 2` cells to
ONE spider (`frobeniusCells_fuseToOneSpider`), and fuses the left-unit cell to the `1 ⇒ 1` identity strand
(`frobeniusSpiderInvariant_unitLeft_fusesToStrand`).  This is the "one spider per connected component" normal form on the
free-2-cell carrier, resting on the shipped `canonicalSpiderOf` (Fauser) NF + the B1 readback invariant.  `= true`. -/
def fxTab_hasCarrierASpiderFusion : Bool := true

/-- **Honesty marker — the GENERAL-arity connected realization stays open (FROB-RESUME B3 residual).**  The DECISION is
unconditional (`fxFrob_hasSpiderConvDecision = true`) and the fusion facts above are the CONCRETE `2 ⇒ 2` / `1 ⇒ 1`
instances; the general theorem `extraSpiderDiagramOf m (canonicalSpiderOf m n) = ⟨m, n, replicate (m+n) 0⟩` for ALL `m`,
`n` (which would flip `fxFrob_hasSpiderFusionNF`) is a comb-FREE `foldl` induction over `processBrauer` whose crux is the
seed-merge step lemma "prepending `multAt 0` merges the first two seed wires into the fresh output, dropping the bottom
count" — union-find surgery on `stepWiring` / `unionFindJoin` / fresh-node allocation, the class of proof the shipped
soundness stack (`Frobenius/SpiderSuffixCongruence.lean`) occupies.  Decoupled from the decision; honestly unbuilt.
`= false`. -/
def fxTab_hasGeneralAritySpiderRealization : Bool := false

end FX1Poly.Polygraph
