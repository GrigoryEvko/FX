import FX1Poly.Polygraph.Homology.AcyclicSoundnessLoopExtractionAndSaturation

/-! # FX1Poly/Polygraph/Homology/AcyclicSystemTruncationCertificate — the general-graph census-zero
    closed form (c) and the eventual-exactness assembly (d) for any acyclic Ufnarovski graph, at the
    loose pigeonhole bound `alphabet.length` (TOWER-ANICK r14, #2145 TOWER-TRUNC — the monomial model)

The r13 file `AcyclicSoundnessLoopExtractionAndSaturation` shipped the checker-soundness core, residuals
(ii) + (iii): `closedEdgeWalkImpliesCheckerFalse` drives `isAcyclicUfnarovskiGraph edges alphabet.length`
to `false` from ANY edge-respecting word with a repeated vertex whose letters lie in `alphabet` — at the
single fixed fuel `alphabet.length` (the loose pigeonhole bound baked in, subsuming saturation via the
`loopIsShort` length bound).  r12 `NaryAlphabetObstructionChainEnumerator` shipped residual (0), the
n-ary enumerator + the re-based census oracle + the census -> exactness bridge `censusZeroImpliesExactOver`.
r11 `FiniteCarrierWalkPigeonhole` shipped ingredient (i), `listOverCarrierRepeats`.  This module ASSEMBLES
(0)+(i)+(ii)+(iii) into the two r14 residuals the r11/r12/r6/r10 ledgers named:

## (c) THE GENERAL-GRAPH CENSUS-ZERO CLOSED FORM

`acyclicCensusZeroAboveAlphabetLength`: for ANY acyclic Ufnarovski graph (`isAcyclicUfnarovskiGraph edges
alphabet.length = true`), every degree `>= alphabet.length` has census `0`.  The contrapositive chain,
leg-by-leg: a degree-`degree` chain word is a `(degree + 1)`-vertex edge-walk under the SAME guard
`allAdjacentPairsAreObstructions`; if it passed the guard it would have letters in `alphabet` (the NEW
`memWordsOverAlphabetLettersInAlphabet` leg) and length `degree + 1 > alphabet.length` (r12
`memWordsOverAlphabetHasLength`), so by the pigeonhole (`listOverCarrierRepeats`) it repeats a vertex, so
by r13 (`closedEdgeWalkImpliesCheckerFalse`) it drives the checker at `fuel = alphabet.length` to `false`
— contradicting acyclicity.  Hence NO word passes the guard (`filterAllFalseIsNil`), so the census is `0`.
The fuel line-up is exact: the checker refutation is at `alphabet.length`, the same fuel as the acyclicity
hypothesis, closing by `Bool.noConfusion`.

## (d) THE EVENTUAL-EXACTNESS ASSEMBLY

`acyclicSystemExactAboveAlphabetLength`: composes (c) with r12 `censusZeroImpliesExactOver` — every degree
`>= alphabet.length` is exact (`isExactAtDegree`) in the zero-boundary (monomial) homology model.

## The NEW leg (the only genuinely-new proof burden here — the rest is composition)

`memWordsOverAlphabetLettersInAlphabet`: `word ∈ allWordsOverAlphabet alphabet targetLength ==> every
vertex of word is in alphabet`.  A near-verbatim clone of r12's length-bridge trio (`memMapConsHasLength`
/ `memFlatMapWordsOverAlphabetHasLength` / `memWordsOverAlphabetHasLength`), re-payloaded from
"length = targetLength" to "letters in alphabet", plus two trivial helpers `natEqBoolRefl` /
`natListContainsOfMem` (the `List.Mem` -> `natListContains`-Bool bridge over the `natEqBool` comparison).
The only real proof-engineering is the two-level `List.Mem` destructure in the map arm, isolated by
`memMapConsSplit` (which decouples "which letter" extraction from the conclusion).

## Honest scope (NO overclaim — the #2145 monomial-instance scope stated)

r14 delivers the truncation certificate for the MONOMIAL (zero-boundary) homology model over ANY acyclic
obstruction graph, at the loose bound `degree >= alphabet.length`.  The exactness in (d) uses the zero
boundary `⟨[[0]]⟩` of `multiObstructionHomologyDataAtDegreeOver` (r12/r6's tensored model).  For a general
CONVERGENT (non-monomial) presentation the Anick differential need not vanish, so `censusZeroImpliesExactOver`
captures only the monomial/tensored model — the TELESCOPE WALL.  The general-convergent `finiteConvergent
==> H_d` (`generalTelescopeHomologyIsNamedNode`) stays EXPLICITLY OPEN.  Two further caveats: the bound is
the LOOSE `alphabet.length` (the graph-specific tight longest-path bound is residual (iii)'s tight form, not
delivered), and the delivery is in the n-ary oracle `multiObstructionChainRankOracleOver` (FINDING A's
healed form) — the binary `vertexCount` phrasing of the r6/r10 ledgers is superseded, not literally proved.
No Smith import, no Homology<->Omega edge.

## Zero-axiom design decisions (the lane's propext minefield)

  * Membership is BUILT and DESTRUCTURED by `List.Mem.head` / `List.Mem.tail` constructors — never `decide`
    on `List.Mem` (leaks `propext`), never `List.mem_map` / `List.mem_append` / `List.mem_flatMap` (all
    leak).  The variable-arity `map`-cons is split by `memMapConsSplit` and `memAppendCases` (r12).
  * `natListContainsOfMem`'s head arm closes the `true || _` residual by an EXPLICIT default-transparency
    `rfl` (the `rw` trailing reducible `rfl` does not reduce `Bool.or true _` — the lane's `sorryAx` trap);
    the tail arm uses `Bool.or_true` (the computation, NOT the leaking `Bool.or_eq_true` iff).
  * The `< ` bound is `Nat.succ_le_succ` (additive, never `Nat.sub`); the checker contradiction is
    `Bool.noConfusion` on `true = false` (never `Option.noConfusion`, which mis-elaborates in-lane).
  * No enumeration: (c)/(d) are structural, no `set_option maxRecDepth` needed (the r12 4-letter fixtures
    are reused only for the cheap end-to-end witness).

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  STRUCTURAL
recursion (alphabet / word / targetLength lists).  Per-declaration gated (and independently `#print
axioms`-checked for the load-bearing decls) in
`FX1PolyAudit/Polygraph/Homology/AcyclicSystemTruncationCertificate.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

/-! ## A — the two trivial `List.Mem` -> `natListContains`-Bool bridges -/

/-- **Reflexivity of the guard's `Nat` equality**: `natEqBool value value = true`.  STRUCTURAL on `value`
(the `value + 1` case reduces DEFINITIONALLY to `natEqBool value value`). -/
theorem natEqBoolRefl : ∀ (value : Nat), natEqBool value value = true
  | 0 => rfl
  | value + 1 => natEqBoolRefl value

/-- **The `List.Mem` -> Bool-membership bridge**: `target ∈ listVal ==> natListContains listVal target =
true`.  STRUCTURAL on `listVal`; the `List.Mem` witness is destructured by its constructors (never `decide`
on `List.Mem`).  The head arm rewrites `natEqBool target target` to `true` via `natEqBoolRefl` and closes
the `true || _` residual by an EXPLICIT `rfl`; the tail arm delegates the disjunct's right side to the
recursion and closes with `Bool.or_true`. -/
theorem natListContainsOfMem (target : Nat) :
    ∀ (listVal : List Nat), target ∈ listVal → natListContains listVal target = true
  | [], hMem => by cases hMem
  | headVal :: remainingList, hMem => by
      cases hMem with
      | head =>
          show (natEqBool target target || natListContains remainingList target) = true
          rw [natEqBoolRefl target]
          rfl
      | tail _ hTail =>
          show (natEqBool headVal target || natListContains remainingList target) = true
          rw [natListContainsOfMem target remainingList hTail]
          exact Bool.or_true _

/-! ## B — the letters-in-alphabet bridge (the n-ary analog of r12's length bridge) -/

/-- **The map-cons splitter**: a member of `alphabetPart.map (fun letter => letter :: base)` is `chosenLetter
:: base` for some `chosenLetter ∈ alphabetPart`.  STRUCTURAL on `alphabetPart`; the `List.Mem` witness is
destructured by its constructors (never `List.mem_map`, which leaks `propext`).  Isolates the "which letter"
extraction — at the top call `alphabetPart` is the full fixed alphabet, so the returned membership is over
the full alphabet, exactly what `natListContainsOfMem` consumes. -/
theorem memMapConsSplit (base : List Nat) :
    ∀ (alphabetPart resultWord : List Nat),
      resultWord ∈ alphabetPart.map (fun letter => letter :: base) →
      ∃ chosenLetter, chosenLetter ∈ alphabetPart ∧ resultWord = chosenLetter :: base
  | [], resultWord, hMem => by
      have hMemNil : resultWord ∈ ([] : List (List Nat)) := hMem
      cases hMemNil
  | alphabetHead :: remainingAlphabet, resultWord, hMem => by
      have hMemCons : resultWord ∈
          (alphabetHead :: base) :: remainingAlphabet.map (fun letter => letter :: base) := hMem
      cases hMemCons with
      | head => exact ⟨alphabetHead, List.Mem.head remainingAlphabet, rfl⟩
      | tail _ hTail =>
          obtain ⟨chosenLetter, hChosenMem, hEq⟩ :=
            memMapConsSplit base remainingAlphabet resultWord hTail
          exact ⟨chosenLetter, List.Mem.tail alphabetHead hChosenMem, hEq⟩

/-- **The inner list-induction of the letters bridge**: if every base word of `wordsList` has all letters in
`alphabet`, then every word of the `flatMap` (one alphabet letter prepended per base) has all letters in
`alphabet`.  STRUCTURAL on `wordsList`; the `flatMap`-cons reduces DEFINITIONALLY to `gen base ++
remainingBases.flatMap gen`, split by r12's `memAppendCases`; the map arm splits the result word by
`memMapConsSplit` and closes the prepended letter via `natListContainsOfMem`, the tail via the base
hypothesis.  Never `List.mem_flatMap` / `List.mem_append` (both leak `propext`). -/
theorem memFlatMapWordsOverAlphabetLettersInAlphabet (alphabet : List Nat) :
    ∀ (wordsList : List (List Nat)),
      (∀ base, base ∈ wordsList → ∀ vertex, vertex ∈ base → natListContains alphabet vertex = true) →
      ∀ resultWord,
        resultWord ∈ wordsList.flatMap (fun word => alphabet.map (fun letter => letter :: word)) →
        ∀ vertex, vertex ∈ resultWord → natListContains alphabet vertex = true
  | [], _, resultWord, hMem => by
      have hMemNil : resultWord ∈ ([] : List (List Nat)) := hMem
      cases hMemNil
  | base :: remainingBases, hAllBaseLetters, resultWord, hMem => by
      have hBaseLetters : ∀ vertex, vertex ∈ base → natListContains alphabet vertex = true :=
        hAllBaseLetters base (List.Mem.head remainingBases)
      have hMemAppend : resultWord ∈
          alphabet.map (fun letter => letter :: base)
            ++ remainingBases.flatMap (fun word => alphabet.map (fun letter => letter :: word)) := hMem
      cases memAppendCases _ resultWord _ hMemAppend with
      | inl hInMap =>
          obtain ⟨chosenLetter, hChosenMem, hEq⟩ := memMapConsSplit base alphabet resultWord hInMap
          intro vertex hVertexMem
          rw [hEq] at hVertexMem
          cases hVertexMem with
          | head => exact natListContainsOfMem _ alphabet hChosenMem
          | tail _ hTail => exact hBaseLetters _ hTail
      | inr hInRest =>
          exact memFlatMapWordsOverAlphabetLettersInAlphabet alphabet remainingBases
            (fun candidate hCandidate => hAllBaseLetters candidate (List.Mem.tail base hCandidate))
            resultWord hInRest

/-- ★★ **THE LETTERS-IN-ALPHABET WALL**: `word ∈ allWordsOverAlphabet alphabet targetLength ==> every vertex
of word is in alphabet`.  Outer STRUCTURAL induction on `targetLength` (`0 => [[]]`, the empty word, vacuous;
`n + 1 => flatMap`, delegated to `memFlatMapWordsOverAlphabetLettersInAlphabet`).  The n-ary analog of r12's
`memWordsOverAlphabetHasLength`, re-payloaded to letter membership — the load-bearing fact (c) feeds to the
pigeonhole `listOverCarrierRepeats` (whose carrier is exactly `alphabet`). -/
theorem memWordsOverAlphabetLettersInAlphabet (alphabet : List Nat) :
    ∀ (targetLength : Nat) (word : List Nat),
      word ∈ allWordsOverAlphabet alphabet targetLength →
      ∀ vertex, vertex ∈ word → natListContains alphabet vertex = true
  | 0, word, hMem => by
      have hMemSingleton : word ∈ ([[]] : List (List Nat)) := hMem
      cases hMemSingleton with
      | head =>
          intro vertex hVertexMem
          cases hVertexMem
      | tail _ hMemTail => cases hMemTail
  | targetLength + 1, word, hMem =>
      memFlatMapWordsOverAlphabetLettersInAlphabet alphabet
        (allWordsOverAlphabet alphabet targetLength)
        (fun base hBase => memWordsOverAlphabetLettersInAlphabet alphabet targetLength base hBase)
        word hMem

/-! ## C — (c) the general-graph census-zero closed form -/

/-- ★★ **THE GENERAL-GRAPH CENSUS-ZERO CLOSED FORM** (c): ANY acyclic Ufnarovski graph
(`isAcyclicUfnarovskiGraph edges alphabet.length = true`) has census `0` at every degree `>= alphabet.length`,
in the n-ary oracle over `alphabet`.  The contrapositive chain: every candidate word of length `degree + 1`
that PASSED the guard would (letters-in-alphabet + length `> alphabet.length`) repeat a vertex by the
pigeonhole, driving the checker at `fuel = alphabet.length` to `false` (r13) — contradicting acyclicity; so
every candidate fails the guard and `filterAllFalseIsNil` empties the chain list.  This is the FINDING-A-healed
n-ary form of the r6/r10 `acyclic ==> census 0` named node, at the loose bound `alphabet.length`. -/
theorem acyclicCensusZeroAboveAlphabetLength (edges : List (Nat × Nat)) (alphabet : List Nat)
    (hAcyclic : isAcyclicUfnarovskiGraph edges alphabet.length = true) :
    ∀ degree, alphabet.length ≤ degree →
      multiObstructionChainRankOracleOver alphabet edges degree = 0 := by
  intro degree hAlphaLeDegree
  have hChainsEmpty : multiObstructionChainsAtDegreeOver alphabet edges degree = [] := by
    show (allWordsOverAlphabet alphabet (degree + 1)).filter
        (allAdjacentPairsAreObstructions edges) = []
    apply filterAllFalseIsNil
    intro word hWordMem
    cases hGuard : allAdjacentPairsAreObstructions edges word with
    | false => rfl
    | true =>
        have hLetters : ∀ vertex, vertex ∈ word → natListContains alphabet vertex = true :=
          memWordsOverAlphabetLettersInAlphabet alphabet (degree + 1) word hWordMem
        have hWordLen : word.length = degree + 1 :=
          memWordsOverAlphabetHasLength alphabet (degree + 1) word hWordMem
        have hLenLt : alphabet.length < word.length := by
          rw [hWordLen]; exact Nat.succ_le_succ hAlphaLeDegree
        have hRepeat : hasRepeatedVertex word = true :=
          listOverCarrierRepeats alphabet word hLetters hLenLt
        have hCheckerFalse : isAcyclicUfnarovskiGraph edges alphabet.length = false :=
          closedEdgeWalkImpliesCheckerFalse edges alphabet word hGuard hRepeat hLetters
        rw [hAcyclic] at hCheckerFalse
        exact Bool.noConfusion hCheckerFalse
  show (multiObstructionChainsAtDegreeOver alphabet edges degree).length = 0
  rw [hChainsEmpty]
  rfl

/-! ## D — (d) the eventual-exactness assembly + the end-to-end witness -/

/-- ★★ **THE GENERAL-GRAPH EVENTUAL-EXACTNESS CERTIFICATE** (d, #2145 TOWER-TRUNC, monomial model): any
acyclic Ufnarovski graph's ZERO-BOUNDARY homology is exact at every degree `>= alphabet.length`.  Composes
(c) `acyclicCensusZeroAboveAlphabetLength` with r12 `censusZeroImpliesExactOver`.  SCOPE (no overclaim): the
boundary is `⟨[[0]]⟩` (the monomial/tensored model); the GENERAL-CONVERGENT `finiteConvergent ==> H_d` with
non-vanishing Anick differential stays OPEN (`generalTelescopeHomologyIsNamedNode`, the telescope wall), and
the bound is the LOOSE `alphabet.length`. -/
theorem acyclicSystemExactAboveAlphabetLength (edges : List (Nat × Nat)) (alphabet : List Nat)
    (hAcyclic : isAcyclicUfnarovskiGraph edges alphabet.length = true) :
    ∀ degree, alphabet.length ≤ degree →
      isExactAtDegree (multiObstructionHomologyDataAtDegreeOver alphabet edges degree) :=
  fun degree hLe =>
    censusZeroImpliesExactOver alphabet edges degree
      (acyclicCensusZeroAboveAlphabetLength edges alphabet hAcyclic degree hLe)

/-- ★ **THE END-TO-END WITNESS** (cross-check, no enumeration): the r11/r12 DAG chain `[(0,1),(1,2),(2,3)]`
over `[0,1,2,3]` (alphabet length `4`) is acyclic at `fuel = 4` (`rfl` on 3 edges), so (d) delivers
`isExactAtDegree` at degree `4` — the SAME fact r12's `dagChainExactAtDegreeFour` gets from the `rfl` census,
now via the census-ZERO CLOSED FORM (c) instead of the computed count.  Two routes, one value. -/
theorem dagChainExactAtDegreeFourViaAcyclicity :
    isExactAtDegree (multiObstructionHomologyDataAtDegreeOver graphReconnectAlphabet dagChainSystem 4) :=
  acyclicSystemExactAboveAlphabetLength dagChainSystem graphReconnectAlphabet rfl 4
    (Nat.le_refl graphReconnectAlphabet.length)

/-! ## E — the TOWER-ANICK (#2145) r14 ledger marker -/

/-- ★ **The TOWER-ANICK (#2145 TOWER-TRUNC) r14 ledger marker.**  What stands, zero-axiom, additively over
r13: the two residuals the r6/r10/r11/r12 ledgers named as r14 — (c) `acyclicCensusZeroAboveAlphabetLength`
(the general-graph `acyclic ==> census 0` closed form in the n-ary oracle, at the loose bound
`alphabet.length`, assembling (0)+(i)+(ii)+(iii) via `memWordsOverAlphabetLettersInAlphabet` +
`memWordsOverAlphabetHasLength` + `listOverCarrierRepeats` + `closedEdgeWalkImpliesCheckerFalse` +
`filterAllFalseIsNil`) and (d) `acyclicSystemExactAboveAlphabetLength` (the eventual-exactness assembly, (c)
composed with `censusZeroImpliesExactOver`), witnessed end-to-end on the DAG chain
(`dagChainExactAtDegreeFourViaAcyclicity`, two routes one value).  The genuinely-new proof burden is the
letters-in-alphabet leg (the n-ary analog of r12's length bridge).  HONEST SCOPE: the delivery is the
MONOMIAL (zero-boundary) truncation certificate over ANY acyclic obstruction graph; the general-CONVERGENT
tower (`generalTelescopeHomologyIsNamedNode`, the telescope wall — non-vanishing Anick differential) and the
general k-block additivity (`naryDisjointAdditivityGeneralIsNamedNode`) stay EXPLICITLY OPEN, and the bound is
the loose `alphabet.length` (the tight longest-path bound is not delivered).  Read the meaning from THIS
docstring (the honest-record convention). -/
def acyclicSystemTruncationCertificateIsComplete : Bool := true

end FX1Poly.Polygraph.Homology
