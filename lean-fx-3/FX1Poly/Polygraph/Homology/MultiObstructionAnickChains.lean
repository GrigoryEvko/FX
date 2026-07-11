import FX1Poly.Polygraph.Homology.CyclicThreeAnickChains

/-! # FX1Poly/Polygraph/Homology/MultiObstructionAnickChains — the MULTI-OBSTRUCTION Anick carrier: a
    branching two-generator monomial system whose minimal-overlap chains GROW without bound, the
    generalized word-carrying marked chain + decidable multi-obstruction guard, the fueled binary-word
    enumerator, the Fibonacci growth census, and the crown ledger re-firing the rank oracle at the
    branching carrier (TOWER-ANICK r3, #2144)

The r1/r2 file `CyclicThreeAnickChains` ships the SINGLE-obstruction / unary Anick carrier
(`MarkedAnickChain`, one word `sᵏ`), whose per-degree chain count is the constant `1` — maximally
FINITE.  Its r2 crown NAMES the residual node `multiObstructionAnickCarrierIsNamedNode`: a
MULTI-obstruction carrier whose minimal overlaps BRANCH so the Anick n-chain count grows with `n`.
This module REALIZES that named node.

## The chosen branching system (Ufnarovski chain graph, compute first)

Over the two-letter alphabet `{x, y}` (encoded `{0, 1}`) take the three length-2 leading-term
obstructions `{xx, xy, yx}` — equivalently "forbid `yy`".  For a UNIFORM length-2 monomial ideal a
proper overlap forces the next occurrence at `p + 1` exactly, so minimality is AUTOMATIC and a
degree-`d` Anick chain is exactly a binary word of length `d + 1` with no `yy` factor (every adjacent
letter-pair is an obstruction).  The Ufnarovski chain graph on letters is `x → x` (xx), `x → y` (xy),
`y → x` (yx) — adjacency `[[1, 1], [1, 0]]`, the FIBONACCI matrix.  Vertex `x` has out-degree two, both
live, so the overlaps genuinely BRANCH (unlike the unary `sᵏ`, whose leftmost-canonicity collapses
self-overlap multiplicity to one).

Hand-worked census (degree `d` = number of obstruction marks = word length `d + 1`):

  | d | words (length d+1, no `yy`)                         | count `c(d)` |
  |---|-----------------------------------------------------|--------------|
  | 0 | x, y                                                | 2            |
  | 1 | xx, xy, yx                                           | 3            |
  | 2 | xxx, xxy, xyx, yxx, yxy                              | 5            |
  | 3 | (8 words)                                            | 8            |
  | 4 |                                                     | 13           |
  | 5 |                                                     | 21           |
  | 6 |                                                     | 34           |

`c(d) = F(d + 3)` (Fibonacci, `F(1) = F(2) = 1`): `2, 3, 5, 8, 13, 21, 34, …` — GROWS without bound,
the FIRST carrier in the lane with unbounded per-degree rank.  Transfer recursion (split by last
letter, `a` = ending in `x`, `b` = ending in `y`): `a(d+1) = a(d) + b(d)` (→x from xx, yx),
`b(d+1) = a(d)` (→y from xy only), seeds `a(0) = b(0) = 1`; then `c(d) = a(d) + b(d)` satisfies
`c(d+2) = c(d+1) + c(d)` — proved here (`fibChainCountSatisfiesFibonacciRecursion`, `rfl`) and used to
SHIP the asymptotic unboundedness `∀ bound, ∃ degree, bound < c(degree)`.

## Convergence honesty

Only the leading-term set `{xx, xy, yx}` drives the chain combinatorics (Ufnarovski).  A concrete
CONVERGENT monoid string-rewriting system witnessing that set is `xx → x, xy → x, yx → x`:
length-reducing (`2 → 1`, terminating) and confluent (the five overlap critical pairs `xxx, xxy, xyx,
yxx, yxy` all join to `x`).  Cited for honesty as `fibObstructionSystemHasConvergentWitness`; the
chains are presented over the leading-term set as data.

## Honest scope (NO overclaim — the load-bearing flags)

  * The growing thing is the Anick CHAIN / resolution RANK `C_d` (the free-module ranks), NOT the
    homology `H_d`.  This particular monoid's actual homology may be small; chain-rank growth is NOT
    homology growth.  This file exhibits CHAIN-rank growth only — the Anick differential and `H_d` are
    a NAMED node (`multiObstructionAnickBoundaryAndHomologyIsNamedNode`).
  * The `S_1` obligation-3 wall (`SquierNoGoInterface.carrierDegreeThreeChainIsAlwaysFinite`) consumes
    INFINITE rank at a SINGLE degree (`basisCount 3 → ∞`).  This carrier's per-degree rank is FINITE at
    every degree (`C_3 = 8`), so the wall stays verbatim UNMOVED
    (`multiObstructionSingleDegreeInfinityStaysWalled`).  Unbounded-ACROSS-degrees (`sup_d C_d = ∞`) is
    a genuinely new rung — the monomial analog of unbounded Betti numbers — but it is NOT single-degree
    infinity, and it does NOT witness `S_1`.
  * The concrete carrier is length-2 uniform, so the `marks` (position, ruleIndex) are recoverable from
    the word and the guard reads the word alone.  The general variable-length multi-obstruction guard
    (the leftmost-minimality scan + overlap arithmetic) is a NAMED node
    (`variableLengthMultiObstructionGuardIsNamedNode`).

## Zero-axiom design decisions

  * The alphabet is `List Nat` over `{0, 1}`; the letter equality reuses the shipped propext-clean
    `natEqBool` (`CyclicThreeAnickChains`).  The guard is full-enum structural Bool (`&&` / `||`, no
    wildcard `_ =>`), every concrete probe closing by `rfl` on the Bool it computes to.
  * The enumerator `allWordsOfLength` is hand-rolled structural `flatMap` (NO `List.range`); the census
    closes by `rfl` on `Nat` literals (the oracle computes filter + length once, cheaper than list
    equality).
  * The transfer count is a SINGLE `Nat → Nat × Nat` structural recursion (no mutual recursion, no
    `unfold`), so the Fibonacci recursion is `rfl` and the growth induction is single-step structural
    over `Nat.add_le_add` / `Nat.le_trans` / `Nat.succ_le_succ` / `Nat.zero_le` (all propext-clean).

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/MultiObstructionAnickChains.lean`. -/

namespace FX1Poly.Polygraph.Homology

/-! ## A — the obstruction systems as data (the branching instance + the degenerate single-obstruction) -/

/-- ★ **The branching "forbid `yy`" obstruction system** — the three length-2 leading terms
`{xx, xy, yx}` as ordered letter-pairs over `{0 = x, 1 = y}`.  Its Ufnarovski chain graph is the
Fibonacci matrix, so the minimal overlaps BRANCH and the Anick chain count grows as `F(d + 3)`. -/
def fibObstructionSystem : List (Nat × Nat) := [(0, 0), (0, 1), (1, 0)]

/-- The degenerate SINGLE-obstruction system `{xx}` — one length-2 obstruction.  The guard "every
adjacent pair is `xx`" accepts only the all-`x` word at each degree `≥ 1`, so the chain count collapses
to the constant `1` (r1's single-letter shape), witnessing that the multi-obstruction carrier strictly
GENERALIZES the single-obstruction one. -/
def singleObstructionUnarySystem : List (Nat × Nat) := [(0, 0)]

/-! ## B — the multi-obstruction guard, the word-carrying marked chain, and the B1 truth probes FIRST -/

/-- Structural membership: is `(firstLetter, secondLetter)` one of the obstruction pairs?  Full-enum on
the obstruction list, letter equality via the shipped `natEqBool`; `||` short-circuits over the list. -/
def isObstructionPair : List (Nat × Nat) → Nat → Nat → Bool
  | [], _, _ => false
  | pair :: remaining, firstLetter, secondLetter =>
      (natEqBool firstLetter pair.1 && natEqBool secondLetter pair.2)
        || isObstructionPair remaining firstLetter secondLetter

/-- ★ **The decidable multi-obstruction minimal-overlap guard** (concrete, length-2 uniform): every
adjacent letter-pair of the chain word must be an obstruction.  The exact analog of r1's
`isMinimalAnickChain` — r1 pins positions to the forced max-two recursion; here a length-2 uniform ideal
forces every overlap width to `1`, so minimality reduces to "no non-obstruction adjacent pair" (for the
Fibonacci system: no `yy` factor).  Full-enum three-arm structural fold. -/
def allAdjacentPairsAreObstructions (obstructions : List (Nat × Nat)) : List Nat → Bool
  | [] => true
  | [_] => true
  | firstLetter :: secondLetter :: rest =>
      isObstructionPair obstructions firstLetter secondLetter
        && allAdjacentPairsAreObstructions obstructions (secondLetter :: rest)

/-- **A word-carrying marked multi-obstruction chain**: the chain word over the alphabet together with
the `(position, ruleIndex)` marks in ascending position order.  For the length-2 uniform carrier the
`ruleIndex` is recoverable from the word content, so the guard reads `word` alone; `marks` is kept in
the general-layer signature (variable-length obstructions genuinely need it — the named guard node). -/
structure MarkedMultiChain where
  /-- The chain word over the alphabet `{0, 1}`. -/
  word : List Nat
  /-- The obstruction marks `(position, ruleIndex)` in ascending position order. -/
  marks : List (Nat × Nat)

/-- The marked-chain wrapper of the guard: is this marked occurrence a minimal multi-obstruction chain
under the given obstruction system?  Reads the word (the concrete length-2 carrier). -/
def MarkedMultiChain.isMinimal (chain : MarkedMultiChain) (obstructions : List (Nat × Nat)) : Bool :=
  allAdjacentPairsAreObstructions obstructions chain.word

/-- ★ **Truth probe (recognised / rejected pair membership): `xx, xy, yx` are obstructions, `yy` is
NOT.**  The branching structure at the letter level — `x` extends to both `x` and `y`, `y` only to `x`.
`rfl` on the computed `Bool`. -/
theorem xyIsObstructionYyIsNot :
    isObstructionPair fibObstructionSystem 0 0 = true ∧
    isObstructionPair fibObstructionSystem 0 1 = true ∧
    isObstructionPair fibObstructionSystem 1 0 = true ∧
    isObstructionPair fibObstructionSystem 1 1 = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- ★ **Truth probe (recognised): the recon's five hand-worked degree-2 chains are all minimal.**  The
length-3 `yy`-free words `xxx, xxy, xyx, yxx, yxy` — exactly the census `c(2) = 5`.  `rfl` per word. -/
theorem degreeTwoChainCensusRecognized :
    allAdjacentPairsAreObstructions fibObstructionSystem [0, 0, 0] = true ∧
    allAdjacentPairsAreObstructions fibObstructionSystem [0, 0, 1] = true ∧
    allAdjacentPairsAreObstructions fibObstructionSystem [0, 1, 0] = true ∧
    allAdjacentPairsAreObstructions fibObstructionSystem [1, 0, 0] = true ∧
    allAdjacentPairsAreObstructions fibObstructionSystem [1, 0, 1] = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ★ **Truth probe (rejected non-minimal overlap): any word carrying a `yy` factor is NOT a minimal
chain** — `yyx`, `xyy`, and the bare `yy` all fail the guard (the `y → y` edge is absent, so the
overlap is non-minimal / forbidden).  The multi-obstruction analog of r1's non-minimal `{0, 2}`
rejection.  `rfl` per word. -/
theorem yyFactorChainIsRejected :
    allAdjacentPairsAreObstructions fibObstructionSystem [1, 1, 0] = false ∧
    allAdjacentPairsAreObstructions fibObstructionSystem [0, 1, 1] = false ∧
    allAdjacentPairsAreObstructions fibObstructionSystem [1, 1] = false :=
  ⟨rfl, rfl, rfl⟩

/-- The marked degree-2 chain `xyx` (word `[0, 1, 0]`, marks `xy` at 0, `yx` at 1). -/
def markedXyxChain : MarkedMultiChain := { word := [0, 1, 0], marks := [(0, 1), (1, 0)] }

/-- ★ **Truth probe (marked-chain wrapper): the marked `xyx` chain is minimal under the Fibonacci
system.**  `rfl`. -/
theorem markedChainXyxIsMinimal : markedXyxChain.isMinimal fibObstructionSystem = true := rfl

/-! ## C — the fueled binary-word enumerator, the Fibonacci growth census, and the degeneracy to r1 -/

/-- All binary words of a given length over `{0, 1}`, hand-rolled structural `flatMap` (NO `List.range`)
— `2^length` words, each reducing by `rfl`.  The candidate space at degree `d` is the length-`d + 1`
words (marks recoverable for the length-2 uniform carrier, so no separate marks bound). -/
def allWordsOfLength : Nat → List (List Nat)
  | 0 => [[]]
  | length + 1 => (allWordsOfLength length).flatMap (fun word => [0 :: word, 1 :: word])

/-- ★ **THE MULTI-OBSTRUCTION ENUMERATOR.**  The minimal multi-obstruction chains at a degree = all
binary words of length `degree + 1` filtered by the decidable guard.  Ports the r2 enumerator SHAPE
verbatim (fueled candidate generation + decidable minimal-overlap guard + `.filter`); only the guard
(multi-obstruction) and the alphabet are new. -/
def multiObstructionChainsAtDegree (obstructions : List (Nat × Nat)) (degree : Nat) : List (List Nat) :=
  (allWordsOfLength (degree + 1)).filter (allAdjacentPairsAreObstructions obstructions)

/-- ★ **THE COMPUTABLE RANK ORACLE, re-fired at the branching carrier.**  The per-degree
multi-obstruction chain count — the same `Nat → Nat` rank-data interface r2's
`anickMinimalChainRankOracle` exposes, now pointed at a BRANCHING system so the sequence GROWS instead
of returning the constant `1`. -/
def multiObstructionChainRankOracle (obstructions : List (Nat × Nat)) (degree : Nat) : Nat :=
  (multiObstructionChainsAtDegree obstructions degree).length

/-- ★★ **THE GROWING CENSUS (machine-checked, `rfl` on `Nat` literals): `c(0..5) = 2, 3, 5, 8, 13, 21`
= `F(3..8)`.**  The enumerator reproduces the recon hand census EXACTLY through degree 5 (candidate
spaces `2^1 … 2^6`) — the Fibonacci growth exhibited directly on the branching enumerator. -/
theorem multiObstructionCensusThroughDegreeFive :
    multiObstructionChainRankOracle fibObstructionSystem 0 = 2 ∧
    multiObstructionChainRankOracle fibObstructionSystem 1 = 3 ∧
    multiObstructionChainRankOracle fibObstructionSystem 2 = 5 ∧
    multiObstructionChainRankOracle fibObstructionSystem 3 = 8 ∧
    multiObstructionChainRankOracle fibObstructionSystem 4 = 13 ∧
    multiObstructionChainRankOracle fibObstructionSystem 5 = 21 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★ **Census probe past the Squier degree-3 truncation: `c(6) = 34 = F(9)`** (candidate space `2^7`).
`rfl`. -/
theorem multiObstructionChainCountAtDegreeSix :
    multiObstructionChainRankOracle fibObstructionSystem 6 = 34 := rfl

/-- ★ **Degeneracy to r1: the single-obstruction system's chain count is the constant `1`** at degrees
1–4 — with only `xx` allowed, the sole surviving word at each degree `≥ 1` is all-`x`, so the branching
count collapses to the single-letter shape.  (At degree 0 both length-1 words survive vacuously — the
two binary generators, an artifact of the fixed `{0, 1}` alphabet; the honest content is the constant
`1` from degree 1 on.)  `rfl` per degree. -/
theorem singleObstructionMultiChainCountIsConstantOne :
    multiObstructionChainRankOracle singleObstructionUnarySystem 1 = 1 ∧
    multiObstructionChainRankOracle singleObstructionUnarySystem 2 = 1 ∧
    multiObstructionChainRankOracle singleObstructionUnarySystem 3 = 1 ∧
    multiObstructionChainRankOracle singleObstructionUnarySystem 4 = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- ★ **The single-obstruction count IS r1's constant `anickChainCountAtDegree`** — both `1` at degree 3
(the branching enumerator, degenerated to one obstruction, reproduces the shipped single-letter Anick
chain count).  `rfl`. -/
theorem singleObstructionDegeneratesToAnickConstant :
    multiObstructionChainRankOracle singleObstructionUnarySystem 3 = anickChainCountAtDegree 3 := rfl

/-! ## D — the two-state transfer recursion, the Fibonacci law, enumerator agreement, and the SHIPPED
    asymptotic unboundedness -/

/-- The two-state transfer count as a SINGLE structural recursion (no mutual recursion): `.1` = chains
ending in `x`, `.2` = chains ending in `y`.  `(a(n+1), b(n+1)) = (a(n) + b(n), a(n))` — `→ x` from
`{xx, yx}`, `→ y` from `{xy}` only; seed `(1, 1)`.  Reduces by `rfl` on variable successors. -/
def fibChainCountPair : Nat → Nat × Nat
  | 0 => (1, 1)
  | n + 1 => ((fibChainCountPair n).1 + (fibChainCountPair n).2, (fibChainCountPair n).1)

/-- Chains of degree `n` ending in `x` (letter `0`) — the first transfer component. -/
def fibChainCountEndingInX (n : Nat) : Nat := (fibChainCountPair n).1

/-- Chains of degree `n` ending in `y` (letter `1`) — the second transfer component. -/
def fibChainCountEndingInY (n : Nat) : Nat := (fibChainCountPair n).2

/-- The total transfer count `c(n) = a(n) + b(n)` — the closed transfer form of the chain census. -/
def fibChainCountTotal (n : Nat) : Nat := (fibChainCountPair n).1 + (fibChainCountPair n).2

/-- ★★ **THE FIBONACCI RECURSION `c(d+2) = c(d+1) + c(d)`** — the branching carrier's chain count obeys
the exact Fibonacci law, forced by the single-recursion transfer def, holds for EVERY degree.  The
provable (not merely computed) growth engine.  `rfl`. -/
theorem fibChainCountSatisfiesFibonacciRecursion (n : Nat) :
    fibChainCountTotal (n + 2) = fibChainCountTotal (n + 1) + fibChainCountTotal n := rfl

/-- ★ **The transfer census reproduces the Fibonacci sequence `2, 3, 5, 8, 13, 21, 34`** at degrees
0–6 — the `O(n)` closed form of the growing chain count.  `rfl` per degree. -/
theorem fibChainCountCensusThroughDegreeSix :
    fibChainCountTotal 0 = 2 ∧
    fibChainCountTotal 1 = 3 ∧
    fibChainCountTotal 2 = 5 ∧
    fibChainCountTotal 3 = 8 ∧
    fibChainCountTotal 4 = 13 ∧
    fibChainCountTotal 5 = 21 ∧
    fibChainCountTotal 6 = 34 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★ **The transfer count AGREES with the branching enumerator** — `c(d) = ` the guard-filtered
binary-word count at degrees 0–5, so the `O(n)` transfer recursion is a faithful closed form for the
`2^{d+1}`-candidate enumeration (the growth engine really counts the chains).  `rfl` per degree. -/
theorem fibChainCountAgreesWithEnumeratorThroughDegreeFive :
    fibChainCountTotal 0 = multiObstructionChainRankOracle fibObstructionSystem 0 ∧
    fibChainCountTotal 1 = multiObstructionChainRankOracle fibObstructionSystem 1 ∧
    fibChainCountTotal 2 = multiObstructionChainRankOracle fibObstructionSystem 2 ∧
    fibChainCountTotal 3 = multiObstructionChainRankOracle fibObstructionSystem 3 ∧
    fibChainCountTotal 4 = multiObstructionChainRankOracle fibObstructionSystem 4 ∧
    fibChainCountTotal 5 = multiObstructionChainRankOracle fibObstructionSystem 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★★ **THE GROWTH EXHIBITED: the chain count STRICTLY increases across computed degrees.**
`c(0) < c(1) < … < c(6)` (`2 < 3 < 5 < 8 < 13 < 21 < 34`), machine-checked on the transfer count (which
agrees with the enumerator, `fibChainCountAgreesWithEnumeratorThroughDegreeFive`).  `by decide` on the
`O(n)` census literals. -/
theorem multiObstructionChainCountStrictlyGrows :
    fibChainCountTotal 0 < fibChainCountTotal 1 ∧
    fibChainCountTotal 1 < fibChainCountTotal 2 ∧
    fibChainCountTotal 2 < fibChainCountTotal 3 ∧
    fibChainCountTotal 3 < fibChainCountTotal 4 ∧
    fibChainCountTotal 4 < fibChainCountTotal 5 ∧
    fibChainCountTotal 5 < fibChainCountTotal 6 := by
  decide

/-- The paired growth invariant (single-step structural induction): the chain count strictly exceeds the
degree at `n` AND at `n + 1`.  The paired form threads the two-back Fibonacci step through ONE `Nat`
recursion — the base `⟨0 < 2, 1 < 3⟩` by `decide`; the step uses the Fibonacci recursion (`rfl`),
`c(n) ≥ 1` (from the first component `n < c(n)`), and `Nat.add_le_add`.  All arithmetic propext-clean. -/
theorem fibChainCountExceedsBoth :
    ∀ n, n < fibChainCountTotal n ∧ (n + 1) < fibChainCountTotal (n + 1)
  | 0 => ⟨by decide, by decide⟩
  | n + 1 => by
      have inductionHypothesis := fibChainCountExceedsBoth n
      have countAtLowerIsPositive : 1 ≤ fibChainCountTotal n :=
        Nat.le_trans (Nat.succ_le_succ (Nat.zero_le n)) inductionHypothesis.1
      have fibonacciStep : fibChainCountTotal (n + 1 + 1)
          = fibChainCountTotal (n + 1) + fibChainCountTotal n := rfl
      refine ⟨inductionHypothesis.2, ?_⟩
      rw [fibonacciStep]
      exact Nat.add_le_add inductionHypothesis.2 countAtLowerIsPositive

/-- ★ **The chain count strictly exceeds its degree at EVERY degree** — `n < c(n)` for all `n`, the
first projection of the paired invariant.  The monotone-dominance certificate behind unboundedness. -/
theorem fibChainCountTotalExceedsDegree (n : Nat) : n < fibChainCountTotal n :=
  (fibChainCountExceedsBoth n).1

/-- ★★ **THE ASYMPTOTIC UNBOUNDEDNESS (SHIPPED, not merely named): `∀ bound, ∃ degree, bound < c(degree)`.**
The branching carrier's Anick chain rank exceeds every bound — witnessed at `degree = bound` by
`fibChainCountTotalExceedsDegree`.  This is the honest content of "unbounded per-degree rank ACROSS
degrees" (`sup_d C_d = ∞`), discharged zero-axiom off the clean Fibonacci recursion.  It is UNBOUNDED
across degrees, NOT infinite at a single degree (each `c(degree)` is a finite `Nat`), so it does not
witness Squier's `S_1` — see the crown ledger. -/
theorem multiObstructionRankIsUnbounded :
    ∀ bound, ∃ degree, bound < fibChainCountTotal degree :=
  fun bound => ⟨bound, fibChainCountTotalExceedsDegree bound⟩

/-- ★ **The general enumerator = transfer equality (`∀ d`) is a NAMED node.**  The concrete agreement
(degrees 0–5, `fibChainCountAgreesWithEnumeratorThroughDegreeFive`) is shipped; the general
`multiObstructionChainRankOracle fibObstructionSystem d = fibChainCountTotal d` for EVERY `d` needs a
filter-collapse / transfer-matrix count over the binary-word tree (the same shape as r2's
`anickGeneralDerivedCountCollapseIsNamedNode`).  Composed with the SHIPPED transfer unboundedness, this
would upgrade unboundedness from the transfer count to the enumerator directly.  Read the meaning from
THIS docstring.  `= true`. -/
def multiObstructionGeneralEnumeratorCollapseIsNamedNode : Bool := true

/-! ## E — the crown ledger: the rank oracle re-fired at the branching carrier, the `S_1` obligations
    audit (what moved, what stays), and the #2144 r3 ledger -/

/-- ★ **The convergent-witness marker.**  The leading-term set `{xx, xy, yx}` is witnessed by the
convergent monoid rewriting system `xx → x, xy → x, yx → x` (length-reducing + confluent, five joinable
critical pairs) — cited for honesty so the branching chains are anchored to an actual convergent
presentation, not a free-floating obstruction list.  The content is in the module docstring.  `= true`. -/
def fibObstructionSystemHasConvergentWitness : Bool := true

/-- ★ **The Fibonacci carrier's degree-3 rank is FINITE (`= 8`)** — the wall-consistency point: the
branching carrier grows ACROSS degrees but is a finite `Nat` at each individual degree, exactly what the
`S_1` obligation-3 wall (`carrierDegreeThreeChainIsAlwaysFinite`, finite rank per degree) requires.
`rfl`. -/
theorem fibCarrierDegreeThreeRankIsFinite :
    multiObstructionChainRankOracle fibObstructionSystem 3 = 8 := rfl

/-- ★★ **The branching rank STRICTLY EXCEEDS the single-letter constant** — `anickChainCountAtDegree 3 =
1 < 8 = ` the Fibonacci carrier's degree-3 rank.  The first carrier in the lane whose per-degree rank is
above the constant `1` of both the single-letter Anick carrier (r1/r2) and the periodic tower.  `by
decide`. -/
theorem multiObstructionRankExceedsSingleLetterConstant :
    anickChainCountAtDegree 3 < multiObstructionChainRankOracle fibObstructionSystem 3 := by
  decide

/-- ★ **THE r3 REALIZATION marker.**  This module REALIZES r2's named node
`multiObstructionAnickCarrierIsNamedNode`: the two-generator branching monomial carrier `{xx, xy, yx}`
whose minimal-overlap Anick chain count is UNBOUNDED (`multiObstructionRankIsUnbounded`), the
single-obstruction degeneration recovering r1's constant `1`
(`singleObstructionDegeneratesToAnickConstant`).  The enumerator SHAPE ported verbatim from r2 (fueled
candidate generation + decidable guard + `.length`); only the guard (multi-obstruction) and the example
are new.  Read the meaning from THIS docstring.  `= true`. -/
def multiObstructionAnickCarrierIsRealized : Bool := true

/-- ★ **THE `S_1` WALL STAYS WALLED (honest).**  Squier's `S_1` obligation-3 needs INFINITE rank at a
SINGLE degree (`basisCount 3 → ∞`), unexpressible by any finite `Nat`.  This carrier delivers unbounded
rank ACROSS degrees (`sup_d C_d = ∞`, `multiObstructionRankIsUnbounded`) with each degree still FINITE
(`C_3 = 8`, `fibCarrierDegreeThreeRankIsFinite`) — a genuinely new rung (the monomial analog of
unbounded Betti numbers), but NOT single-degree infinity.  So
`SquierNoGoInterface.carrierDegreeThreeChainIsAlwaysFinite` and
`squierWitnessLedger.homologicalNonFinitenessStatus = walledByCarrierFiniteness` stay verbatim UNMOVED;
witnessing `S_1` still needs the infinite-basis substrate (the standing R2 wall).  NO close claim beyond
delivery.  `= true`. -/
def multiObstructionSingleDegreeInfinityStaysWalled : Bool := true

/-- ★ **The Anick differential and homology `H_d` from these chains is a NAMED node.**  This file
exhibits CHAIN-rank growth (the free-module ranks `C_d`), NOT homology growth: the Anick boundary maps,
their `d ∘ d = 0`, and the resulting `H_d` are not derived here (the r1 boundary rode the shipped tower;
the multi-obstruction boundary is genuinely new).  Chain-rank growth is NOT `H_d` growth — deriving the
differential and the homology of the branching carrier is deferred.  Read the meaning from THIS
docstring.  `= true`. -/
def multiObstructionAnickBoundaryAndHomologyIsNamedNode : Bool := true

/-- ★ **The general variable-length multi-obstruction guard is a NAMED node.**  The concrete guard is
length-2 uniform (every overlap width `1`, minimality automatic, `marks` recoverable).  The general
variable-length carrier needs the guard to VERIFY word content at each mark (`word[p..p+len] =
obstruction[r]`), the proper-overlap arithmetic `p_i < p_{i+1} ≤ p_i + len − 1` with strict extension,
AND the leftmost-minimality scan (no obstruction occurs strictly between consecutive marks), plus the
candidate-bound arithmetic `L_max(n) = n·(k−1)+1`.  Deferred (mirrors r1 shipping the concrete guard and
naming the general).  Read the meaning from THIS docstring.  `= true`. -/
def variableLengthMultiObstructionGuardIsNamedNode : Bool := true

/-! ### The TOWER-ANICK (#2144) r3 ledger (bricks shipped, residuals named)

  * **B1 — THE UPGRADED CARRIER**: SHIPPED.  `isObstructionPair` / `allAdjacentPairsAreObstructions`
    (the decidable multi-obstruction guard, reusing `natEqBool`), `MarkedMultiChain` (the word-carrying
    marked chain) + `MarkedMultiChain.isMinimal`.  Truth probes FIRST: the recon's five degree-2 chains
    recognised (`degreeTwoChainCensusRecognized`), the branching pair membership (`xyIsObstructionYyIsNot`),
    the non-minimal `yy`-factor overlaps rejected (`yyFactorChainIsRejected`), the marked `xyx`
    (`markedChainXyxIsMinimal`).
  * **B2 — THE BRANCHING INSTANCE + ENUMERATOR**: SHIPPED.  `fibObstructionSystem` as data; the fueled
    `allWordsOfLength` + `multiObstructionChainsAtDegree` + `multiObstructionChainRankOracle`; the census
    `c(0..5) = 2, 3, 5, 8, 13, 21` (`multiObstructionCensusThroughDegreeFive`) + `c(6) = 34`
    (`multiObstructionChainCountAtDegreeSix`) — matching the recon hand census EXACTLY; the degeneracy to
    r1's constant `1` (`singleObstructionMultiChainCountIsConstantOne`,
    `singleObstructionDegeneratesToAnickConstant`).
  * **B3 — THE GROWTH EXHIBITED**: SHIPPED.  ★★ the Fibonacci recursion `c(d+2) = c(d+1) + c(d)`
    (`fibChainCountSatisfiesFibonacciRecursion`, `rfl`); the strict growth `c(0) < … < c(6)`
    (`multiObstructionChainCountStrictlyGrows`); the transfer = enumerator agreement
    (`fibChainCountAgreesWithEnumeratorThroughDegreeFive`); and — beyond the recon's minimum — the
    SHIPPED asymptotic unboundedness `∀ bound, ∃ degree, bound < c(degree)`
    (`multiObstructionRankIsUnbounded`, off the clean Fibonacci recursion).  Honest scope: computed
    instances by `rfl`/`decide`; the ASYMPTOTIC lemma is SHIPPED on the transfer count (the general
    enumerator = transfer bridge is the named `multiObstructionGeneralEnumeratorCollapseIsNamedNode`).
  * **B4 — THE CROWN LEDGER**: SHIPPED.  The rank oracle re-fired at the branching carrier (returns the
    growing sequence); the `S_1` obligations audit — what MOVED: the lane now has a carrier with
    unbounded per-degree rank ACROSS degrees (`multiObstructionRankIsUnbounded`), the monomial analog of
    unbounded Betti numbers, strictly above the constant `1` of the single-letter carrier and the tower
    (`multiObstructionRankExceedsSingleLetterConstant`); what STAYS: the `S_1` obligation-3 wall
    (INFINITE rank at ONE degree) is verbatim UNMOVED — each degree is finite
    (`fibCarrierDegreeThreeRankIsFinite`), unbounded-across ≠ single-degree-∞
    (`multiObstructionSingleDegreeInfinityStaysWalled`).  NO close claim beyond delivery.
  * **B5 — this ledger**: SHIPPED.

### Named residual nodes (deferred, decided elsewhere)

  * `multiObstructionGeneralEnumeratorCollapseIsNamedNode` — the general enumerator = transfer equality
    (`∀ d`), upgrading unboundedness from the transfer count to the enumerator directly.
  * `multiObstructionAnickBoundaryAndHomologyIsNamedNode` — the Anick differential + `H_d` of the
    branching carrier (this file shows CHAIN-rank growth, not homology).
  * `variableLengthMultiObstructionGuardIsNamedNode` — the general variable-length guard (content check
    + overlap arithmetic + leftmost-minimality scan + candidate bounds).
  * The true `S_1` single-degree infinite rank stays the standing R2 wall
    (`SquierNoGoInterface.squierWitnessLedger`); the r1 named nodes (full Anick-resolution exactness, the
    polygraphic-Anick monad census) still stand.

### Honest scoping (no overclaim)

r3 realizes r2's named multi-obstruction node: a genuine BRANCHING carrier whose Anick chain rank GROWS
(`F(d+3)`, unbounded).  It exhibits CHAIN-rank growth ONLY (not homology), delivers unbounded rank
ACROSS degrees (not single-degree infinity), and leaves the `S_1` wall verbatim UNMOVED.  Every
deferral is a NAMED node, not a jam; nothing is papered. -/

/-- ★ **The TOWER-ANICK (#2144) r3 ledger marker (the branching / growth round).**  What stands,
zero-axiom, realizing r2's named node: THE UPGRADED CARRIER (the word-carrying `MarkedMultiChain` + the
decidable multi-obstruction guard, truth-probed — the five degree-2 chains recognised, the `yy`-factor
overlaps rejected); THE BRANCHING INSTANCE (`fibObstructionSystem`) + the fueled binary-word enumerator
with the census `2, 3, 5, 8, 13, 21, 34` matching the recon EXACTLY and degenerating to r1's constant
`1`; ★★ THE GROWTH EXHIBITED (the Fibonacci recursion `c(d+2) = c(d+1) + c(d)`, strict growth
`c(0) < … < c(6)`, and the SHIPPED asymptotic unboundedness `∀ bound, ∃ degree, bound < c(degree)`); and
THE CROWN LEDGER (the rank oracle re-fired at the branching carrier, the `S_1` obligations audit — the
unbounded-across-degrees rung MOVED in, the single-degree-∞ wall STAYS UNMOVED, no close claim beyond
delivery).  Residuals NAMED (the general enumerator = transfer collapse, the Anick differential + `H_d`,
the variable-length guard), never papered.  Read the meaning from THIS docstring (the honest-record
convention). -/
def towerAnickRoundThreeLedgerIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
