import FX1Poly.Polygraph.TwoCategory.Table.WordProblemDecisionLedger

/-! # Polygraph/TwoCategory/Table/WordProblemCostLedger — the per-rung decision COST ledger

★ **Complexity tags on every decided rung (WP-CEIL-COST #2046)** — the cost-lane companion to
`WordProblemDecisionLedger` (WP-LEDGER #2048 owed item (2)).

Every rung of the decided-16 gets a COST CLASS (what the decider costs, read off its algorithmic structure) and
a COST EVIDENCE tag (HOW that class is known).  The evidence discipline is the honest part: a class is
`proved` only when an in-repo machine-checked cost theorem bounds the decider; it is `cited` when the class is
read off the decider's structure and recorded here by decl-name citation.  Today the repo holds ZERO cost
theorems about any decider (the `PolyBound` cost-declaration language itself is still `.openProblem` in
`Typed/Dimensions/Cost/CostArcLedger`, COST-7), so all sixteen tags are `cited` and
`fxWpCost_allTagsProved = false`.

## The per-rung cost table (decl NAMES cited, per the anchor-rot discipline — never file:line)

  | Walker               | Decider                                        | Class        | Structural reason |
  |----------------------|------------------------------------------------|--------------|-------------------|
  | walking involution   | `decideInvolutionOneCellConv`                  | linear       | `involutionParityOf = natParity ∘ ModalityPath.length` — one length fold per word, O(1) parity compare |
  | walking monad        | `monadSaturatedTwoCellDecision`                | polynomial   | `monadMonotoneMapOf` spine foldl; each `monadMonoStepAtom` composes maps by per-entry `monotoneMapGet` list indexing — O(atoms·width²); then `DecidableEq (List Nat)` |
  | walking cyclic-3     | `decideCyclicThreeOneCellConv`                 | linear       | `cyclicThreeResidueOf = natMod3 ∘ ModalityPath.length` — one length fold + structural mod-3, O(1) residue compare |
  | idempotent semigroup | `decideSaturatedConvOverIdempotentNative`      | constantTime | `fun a b => isTrue (idempotentLocalPosetalityGeneric a b)` — the VERDICT never inspects the cells (locally posetal; the normalizer lives only in the erased `Prop` proof) |
  | walking comonad      | `decideSaturatedConvOverComonadNative`         | polynomial   | `decideSaturatedConvUnderOp`: computes `opCell` of both inputs (linear structural reversal) then runs the polynomial monad base |
  | idempotent comonad   | `decideSaturatedConvOverIdempotentComonadNative` | linear     | op-transport over the constant-time idempotent decider — strict evaluation forces the two `opCell` reversals (linear); the always-`isTrue` base never inspects them |
  | walking KZ           | `decideKZEq` + `decideKZLETotal`               | polynomial   | both compute the monad monotone-map fold per cell, then compare by `DecidableEq (List Nat)` / pointwise `decMapLE` |
  | walking co-KZ        | `decideCoKZLETotal`                            | polynomial   | pure argument swap `decideKZLETotal b a` — identical cost to the KZ order decider |
  | walking adjunction   | `decideSaturatedTwoCellConv_ofSeed`            | polynomial   | `matchingOf = extractDiagram ∘ processSpine` — foldl of O(width) list surgery per atom + `partnerIndexOf` link scans over all boundary indices (O(boundary²·links)); then `DiagramType` `DecidableEq` |
  | walking monoid operad | `decideOperadTreeConv`                        | linear       | `arityOf` structural tree fold per tree + `Nat.decEq` on the two arities — one fold each, O(1) compare |
  | walking traced (frag) | `decideTracedDiagramConv`                     | quadratic    | `tracedNF` bottom-up fold, but each `traceN 1` node's `contractTraceOne` walks the seq-spine of its normalized child — nested traces stack the walks, O(n²) worst case; then the structural `tracedDiagramDecEq` |
  | walking double (grid) | `decideDoubleTileConv`                        | linear       | two `(tileWidth, tileHeight)` structural folds + `Nat.decEq` on the pair — one fold each, O(1) compare |
  | `B_3^+` (Garside)     | `decideBraidThreeConv`                        | quadratic    | `braidNormalizeWord` folds `braidPrependAtom`; each prepend's Δ-power carry (`braidPrependAtomWithPower`) walks up to the accumulated `deltaPower` ≤ word length — O(n²) worst case, the classical fixed-strand Garside bound; then `braidGarsideCanonDecEq` |
  | walking comm. monoid  | `decideCommMonoidTreeConv`                    | linear       | `leafCount` structural tree fold per tree + `Nat.decEq` on the two counts — one fold each, O(1) compare |
  | walking bdd. semilatt. | `decideSemilatticeTreeConv`                  | linear       | `slotPresenceOf` structural tree fold per tree + `slotPresenceDecEq` on the two `SlotPresence` values — one fold each, O(1) compare |
  | walking abelian group  | `decideAbelianGroupTreeConv`                 | linear       | `windingOf` structural tree fold per tree (a difference pair `ℕ²`) + `Nat.decEq` on the two winding-difference sums — one fold each, O(1) compare |

Class census: constantTime 1, linear 8, quadratic 2, polynomial 5, exponentialBounded 0.
Evidence census: proved 0, measured 0, cited 16, unassessed 0.

## The KZ/co-KZ row subtlety

A row tags the RUNG's decider(s), not one decl: the witness bundle's SEVENTEEN grounding aliases map onto these
SIXTEEN rows with KZ carrying two (`wpLedgerKZEqDecider` and `wpLedgerKZOrderDecider` — both are the same
monotone-map fold, so one class covers both; `fxWpCost_kzRowCoversBothDeciders`).

## One honest correction (vs the folk expectation "normalizer ⟹ cost")

The idempotent family's normalizer folds do NOT run at decision time.  The idempotent decider is
always-`isTrue` (locally posetal), so its verdict is CONSTANT; its comonad dual pays only the two `opCell`
reversals (LINEAR).  The cost class tags the DECIDER's computation, not the soundness proof's.

Raw Lean 4 + Init; a machine-checked census (two enums, two total maps over the LIVE
`WordProblemDecidedWalker`, `rfl` counts and rows, `List.Mem` exhaustiveness, `Bool` markers), every
declaration axiom-free.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Table

/-! ## The cost-evidence taxonomy -/

/-- **HOW a rung's cost class is known** — the epistemic tag that keeps the ledger honest. -/
inductive WordProblemCostEvidence
  /-- An in-repo MACHINE-CHECKED cost theorem bounds the decider (none exist today — the `PolyBound`
  cost-declaration language is itself still open, COST-7 in `CostArcLedger`). -/
  | proved
  /-- An in-repo executable measurement (e.g. a step-counting instrumentation) exhibits the bound on a
  benchmark family (none exist today). -/
  | measured
  /-- The class is READ OFF the decider's algorithmic structure and recorded by decl-name citation in this
  ledger's row docstring — a documented claim, not a machine-checked theorem. -/
  | cited
  /-- No cost assessment at all (used by future rungs landing ahead of their cost read; empty today). -/
  | unassessed

/-! ## The cost-class taxonomy -/

/-- **The decider's asymptotic cost class** in the total input size (both cells' syntactic size). -/
inductive WordProblemCostClass
  /-- O(1) — the verdict never inspects the inputs (a locally-posetal always-`isTrue` decider). -/
  | constantTime
  /-- O(n) — a single structural fold over the inputs (length folds, `opCell` reversals). -/
  | linear
  /-- O(n²) — a structural fold whose per-node step can itself walk a linear-size sub-structure (the traced
  smart-constructor spine walks; the braid Δ-power carry). -/
  | quadratic
  /-- O(n^k) for a fixed small k > 2 — nested folds with per-step list indexing / link scans. -/
  | polynomial
  /-- Exponential with a PROVED bound (better than unbounded search) — reserved for future rungs; empty
  today. -/
  | exponentialBounded

/-! ## The per-rung cost maps (total over the LIVE decided-15 enum, full enumeration, no wildcard arm) -/

/-- The **cost class of each rung's decider** — the module-docstring table's class column, machine-held.
Full enumeration (no wildcard arm) so the match stays propext-free.  Per-rung citations: involution
`decideInvolutionOneCellConv` (length fold — linear); monad `monadSaturatedTwoCellDecision`
(`monadMonotoneMapOf` fold with per-atom map composition — polynomial); cyclic-3
`decideCyclicThreeOneCellConv` (length fold + mod-3 — linear); idempotent semigroup
`decideSaturatedConvOverIdempotentNative` (always-`isTrue`, verdict inspects nothing — constantTime); comonad
`decideSaturatedConvOverComonadNative` (`opCell` + the polynomial monad base — polynomial); idempotent comonad
`decideSaturatedConvOverIdempotentComonadNative` (`opCell` over the constant base — linear); KZ `decideKZEq` /
`decideKZLETotal` (the monad monotone-map fold + compare — polynomial); co-KZ `decideCoKZLETotal` (argument
swap of the KZ order decider — polynomial); adjunction `decideSaturatedTwoCellConv_ofSeed` (link-scan
matching extraction — polynomial); operad `decideOperadTreeConv` (`arityOf` tree fold per input + `Nat.decEq`
— linear); traced `decideTracedDiagramConv` (`tracedNF` fold with per-trace-node `contractTraceOne` spine
walks — quadratic); double `decideDoubleTileConv` (two `(width, height)` folds + `Nat.decEq` — linear);
`B_3^+` `decideBraidThreeConv` (`braidNormalizeWord` fold with per-letter Δ-power carry — quadratic); abelian
group `decideAbelianGroupTreeConv` (`windingOf` difference-pair tree fold per input + `Nat.decEq` on the two
winding sums — linear). -/
def wordProblemCostClass : WordProblemDecidedWalker → WordProblemCostClass
  | .walkingInvolution => .linear
  | .walkingMonad => .polynomial
  | .walkingCyclicThree => .linear
  | .idempotentSemigroup => .constantTime
  | .walkingComonad => .polynomial
  | .idempotentComonad => .linear
  | .walkingKZ => .polynomial
  | .walkingCoKZ => .polynomial
  | .walkingAdjunction => .polynomial
  | .walkingOperad => .linear
  | .walkingTraced => .quadratic
  | .walkingDouble => .linear
  | .walkingBraidPositive => .quadratic
  | .walkingCommutativeMonoid => .linear
  | .walkingBoundedSemilattice => .linear
  | .walkingAbelianGroup => .linear

/-- The **cost evidence of each rung's tag** — `.cited` at ALL SIXTEEN (honest): every class above is read
off the decider's structure; NO in-repo cost theorem or measurement exists for any decider today.  Full
enumeration (no wildcard arm). -/
def wordProblemCostEvidence : WordProblemDecidedWalker → WordProblemCostEvidence
  | .walkingInvolution => .cited
  | .walkingMonad => .cited
  | .walkingCyclicThree => .cited
  | .idempotentSemigroup => .cited
  | .walkingComonad => .cited
  | .idempotentComonad => .cited
  | .walkingKZ => .cited
  | .walkingCoKZ => .cited
  | .walkingAdjunction => .cited
  | .walkingOperad => .cited
  | .walkingTraced => .cited
  | .walkingDouble => .cited
  | .walkingBraidPositive => .cited
  | .walkingCommutativeMonoid => .cited
  | .walkingBoundedSemilattice => .cited
  | .walkingAbelianGroup => .cited

/-! ## The kernel-checked rows (keyed off the LIVE decision-ledger enumeration) -/

/-- ★ **The class row over the LIVE decided-15 enumeration** — mapping `wordProblemCostClass` over
`allWordProblemDecidedWalkers` (the decision ledger's list, ledger order) yields exactly the module table's
class column.  Kernel-checked (`rfl`). -/
theorem allWordProblemDecidedWalkersCostClassRow :
    allWordProblemDecidedWalkers.map wordProblemCostClass =
      [.linear, .polynomial, .linear, .constantTime, .polynomial, .linear,
        .polynomial, .polynomial, .polynomial, .linear, .quadratic, .linear, .quadratic,
        .linear, .linear, .linear] := rfl

/-- ★ **The evidence row over the LIVE decided-15 enumeration** — every entry `.cited`.
Kernel-checked (`rfl`). -/
theorem allWordProblemDecidedWalkersCostEvidenceRow :
    allWordProblemDecidedWalkers.map wordProblemCostEvidence =
      [.cited, .cited, .cited, .cited, .cited, .cited, .cited, .cited, .cited, .cited,
        .cited, .cited, .cited, .cited, .cited, .cited] := rfl

/-- ★ **Every decided walker's cost tag is CITED** — full case split, `rfl` per arm.  The machine-checked
"nothing is proved" statement: the dual of `wordProblemCostProvedWalkerCountIsZero`. -/
theorem allWordProblemDecidedWalkersCostEvidenceCited :
    ∀ walker : WordProblemDecidedWalker, wordProblemCostEvidence walker = .cited
  | .walkingInvolution => rfl
  | .walkingMonad => rfl
  | .walkingCyclicThree => rfl
  | .idempotentSemigroup => rfl
  | .walkingComonad => rfl
  | .idempotentComonad => rfl
  | .walkingKZ => rfl
  | .walkingCoKZ => rfl
  | .walkingAdjunction => rfl
  | .walkingOperad => rfl
  | .walkingTraced => rfl
  | .walkingDouble => rfl
  | .walkingBraidPositive => rfl
  | .walkingCommutativeMonoid => rfl
  | .walkingBoundedSemilattice => rfl
  | .walkingAbelianGroup => rfl

/-! ## The per-evidence enumerations and counts -/

/-- The walkers whose cost tag is `.cited` — ALL SIXTEEN (ledger order). -/
def allWordProblemCostCitedWalkers : List WordProblemDecidedWalker :=
  [.walkingInvolution, .walkingMonad, .walkingCyclicThree, .idempotentSemigroup,
    .walkingComonad, .idempotentComonad, .walkingKZ, .walkingCoKZ, .walkingAdjunction,
    .walkingOperad, .walkingTraced, .walkingDouble, .walkingBraidPositive,
    .walkingCommutativeMonoid, .walkingBoundedSemilattice, .walkingAbelianGroup]

/-- ★ **The cited-tag count is exactly SIXTEEN** — kernel-checked (`rfl`). -/
theorem wordProblemCostCitedWalkerCountIsSixteen :
    allWordProblemCostCitedWalkers.length = 16 := rfl

/-- The walkers whose cost tag is `.proved` — NONE (the honest zero: no in-repo cost theorem exists about any
decider; the `PolyBound` cost language is itself `.openProblem` per `CostArcLedger`). -/
def allWordProblemCostProvedWalkers : List WordProblemDecidedWalker := []

/-- ★ **The proved-tag count is exactly ZERO** — kernel-checked (`rfl`).  The honest zero. -/
theorem wordProblemCostProvedWalkerCountIsZero : allWordProblemCostProvedWalkers.length = 0 := rfl

/-- The walkers whose cost tag is `.measured` — NONE (no step-counting instrumentation exists). -/
def allWordProblemCostMeasuredWalkers : List WordProblemDecidedWalker := []

/-- ★ **The measured-tag count is exactly ZERO** — kernel-checked (`rfl`). -/
theorem wordProblemCostMeasuredWalkerCountIsZero : allWordProblemCostMeasuredWalkers.length = 0 := rfl

/-! ## The per-class enumerations and counts -/

/-- The `.constantTime` walkers — ONE (the locally-posetal idempotent semigroup). -/
def allWordProblemConstantTimeCostWalkers : List WordProblemDecidedWalker :=
  [.idempotentSemigroup]

/-- ★ **The constant-time count is exactly ONE** — kernel-checked (`rfl`). -/
theorem wordProblemConstantTimeCostWalkerCountIsOne :
    allWordProblemConstantTimeCostWalkers.length = 1 := rfl

/-- The `.linear` walkers — EIGHT (the two length-fold residue deciders, the op-transported constant base,
the operad's arity-fold tree decider, the double-cat `(width, height)` grid decider, and the three
single-generator algebra-operad folds — commutative-monoid leaf count, semilattice slot-presence, and
abelian-group winding count). -/
def allWordProblemLinearCostWalkers : List WordProblemDecidedWalker :=
  [.walkingInvolution, .walkingCyclicThree, .idempotentComonad, .walkingOperad, .walkingDouble,
    .walkingCommutativeMonoid, .walkingBoundedSemilattice, .walkingAbelianGroup]

/-- ★ **The linear count is exactly EIGHT** — kernel-checked (`rfl`). -/
theorem wordProblemLinearCostWalkerCountIsEight :
    allWordProblemLinearCostWalkers.length = 8 := rfl

/-- The `.quadratic` walkers — TWO (the traced smart-constructor fold with per-trace-node spine walks; the
`B_3^+` Garside normalizer with per-letter Δ-power carries).  The class is no longer reserved. -/
def allWordProblemQuadraticCostWalkers : List WordProblemDecidedWalker :=
  [.walkingTraced, .walkingBraidPositive]

/-- ★ **The quadratic count is exactly TWO** — kernel-checked (`rfl`). -/
theorem wordProblemQuadraticCostWalkerCountIsTwo :
    allWordProblemQuadraticCostWalkers.length = 2 := rfl

/-- The `.polynomial` walkers — FIVE (the monotone-map family: monad, its op, KZ, co-KZ; plus the
link-scanning adjunction matcher). -/
def allWordProblemPolynomialCostWalkers : List WordProblemDecidedWalker :=
  [.walkingMonad, .walkingComonad, .walkingKZ, .walkingCoKZ, .walkingAdjunction]

/-- ★ **The polynomial count is exactly FIVE** — kernel-checked (`rfl`). -/
theorem wordProblemPolynomialCostWalkerCountIsFive :
    allWordProblemPolynomialCostWalkers.length = 5 := rfl

/-- The `.exponentialBounded` walkers — NONE today (every shipped decider is polynomial or better; the class
is reserved for future rungs). -/
def allWordProblemExponentialBoundedCostWalkers : List WordProblemDecidedWalker := []

/-- ★ **The exponential-bounded count is exactly ZERO** — kernel-checked (`rfl`). -/
theorem wordProblemExponentialBoundedCostWalkerCountIsZero :
    allWordProblemExponentialBoundedCostWalkers.length = 0 := rfl

/-! ## Exhaustiveness glue: the class union covers the decided-16 -/

/-- The decided-16 grouped by cost class (constantTime, then linear, then quadratic, then polynomial) — the
union list the per-class enumerations concatenate to. -/
def allWordProblemCostClassifiedWalkers : List WordProblemDecidedWalker :=
  [.idempotentSemigroup, .walkingInvolution, .walkingCyclicThree, .idempotentComonad,
    .walkingOperad, .walkingDouble, .walkingCommutativeMonoid, .walkingBoundedSemilattice,
    .walkingAbelianGroup,
    .walkingTraced, .walkingBraidPositive,
    .walkingMonad, .walkingComonad, .walkingKZ, .walkingCoKZ, .walkingAdjunction]

/-- ★ **The class-grouped count is exactly SIXTEEN** — kernel-checked (`rfl`). -/
theorem wordProblemCostClassifiedWalkerCountIsSixteen :
    allWordProblemCostClassifiedWalkers.length = 16 := rfl

/-- ★ **The class-grouped list IS the union of the per-class enumerations** — the five per-class lists
(one empty) concatenate to it, kernel-checked (`rfl`). -/
theorem allWordProblemCostClassifiedWalkersIsClassUnion :
    allWordProblemCostClassifiedWalkers =
      allWordProblemConstantTimeCostWalkers ++ allWordProblemLinearCostWalkers ++
        allWordProblemQuadraticCostWalkers ++ allWordProblemPolynomialCostWalkers ++
          allWordProblemExponentialBoundedCostWalkers := rfl

/-- ★ **The class-grouped classes line up with the grouping** — mapping `wordProblemCostClass` over the
grouped list yields the constant/linear/quadratic/polynomial blocks in order, kernel-checked (`rfl`). -/
theorem allWordProblemCostClassifiedWalkersClassRow :
    allWordProblemCostClassifiedWalkers.map wordProblemCostClass =
      [.constantTime, .linear, .linear, .linear, .linear, .linear, .linear, .linear, .linear,
        .quadratic, .quadratic,
        .polynomial, .polynomial, .polynomial, .polynomial, .polynomial] := rfl

/-- ★ **The class union is EXHAUSTIVE** — every decided walker appears in the class-grouped list (full case
split, `List.Mem` ctors, propext-free). -/
theorem allWordProblemCostClassifiedWalkersExhaustive :
    ∀ walker : WordProblemDecidedWalker, walker ∈ allWordProblemCostClassifiedWalkers
  | .idempotentSemigroup => List.Mem.head _
  | .walkingInvolution => List.Mem.tail _ (List.Mem.head _)
  | .walkingCyclicThree => List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | .idempotentComonad => List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  | .walkingOperad =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  | .walkingDouble =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _)))))
  | .walkingCommutativeMonoid =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))))
  | .walkingBoundedSemilattice =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  | .walkingAbelianGroup =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  | .walkingTraced =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
  | .walkingBraidPositive =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.head _))))))))))
  | .walkingMonad =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))))))))))
  | .walkingComonad =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))
  | .walkingKZ =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))
  | .walkingCoKZ =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))
  | .walkingAdjunction =>
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))

/-! ## The cost markers -/

/-- ★ **ALL SIXTEEN decided rungs carry a cost tag (recorded).**  `= true` records that
`wordProblemCostClass` and `wordProblemCostEvidence` are TOTAL over the live decided-16 enum
(full-enumeration matches, no wildcard), the cited census is sixteen-of-sixteen
(`wordProblemCostCitedWalkerCountIsSixteen`, `allWordProblemDecidedWalkersCostEvidenceCited`), and the class
union covers all sixteen (`allWordProblemCostClassifiedWalkersExhaustive`,
`allWordProblemCostClassifiedWalkersIsClassUnion`). -/
def fxWpCost_allRungsTagged : Bool := true

/-- ★ **NO COST TAG IS PROVED (honest).**  `= false` records that every one of the sixteen class tags is
`.cited` — read off the decider's structure, documented by decl-name citation — and ZERO are backed by an
in-repo machine-checked cost theorem or measurement (`wordProblemCostProvedWalkerCountIsZero`,
`wordProblemCostMeasuredWalkerCountIsZero`).  The `PolyBound` cost-declaration language that proved tags would
be stated in is itself still `.openProblem` (COST-7, `Typed/Dimensions/Cost/CostArcLedger`).  Set `true` only
when a genuine in-repo cost theorem bounds a decider and its rung's evidence flips to `.proved`. -/
def fxWpCost_allTagsProved : Bool := false

/-- ★ **The single KZ row covers BOTH KZ deciders (recorded).**  `= true` records that the walkingKZ row's
`.polynomial` tag covers both `decideKZEq` and `decideKZLETotal` (the witness bundle's `wpLedgerKZEqDecider`
and `wpLedgerKZOrderDecider`) — both compute the SAME monad monotone-map fold per cell and differ only in the
final comparison (`DecidableEq (List Nat)` vs pointwise `decMapLE`), so one class tags both.  The seventeen
grounding aliases map onto these sixteen rows with KZ carrying two. -/
def fxWpCost_kzRowCoversBothDeciders : Bool := true

end FX1Poly.Polygraph.Table
