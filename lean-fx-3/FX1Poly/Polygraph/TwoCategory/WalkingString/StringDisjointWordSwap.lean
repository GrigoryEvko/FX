import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDisjointWordFactorization
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap

/-! # WalkingString/StringDisjointWordSwap — the realized WORD-indexed swap + its WORD-chain preservation (FC-3 r4, B1/B2)

Brick B1's factorization (`spineAtom_contextsFactor_of_disjointWordWindows`) exhibits the whisker shape the
`SpineAtomSwap` constructor demands; this file APPLIES it (B1 swap) and THREADS the boundary-WORD chain across
the transposition (B2), the word analogues of `WalkingAdjunction/DisjointWindowSwap`'s two theorems:

  * `spineAtomSwap_of_disjointWordWindows` — ★ (B1) two adjacent atoms whose boundary words chain
    (`sharedWord`) with a right-of gap genuinely TRANSPOSE by a `SpineAtomSwap`, with the moved atoms given as
    explicit record updates and the inert gap-length pin returned; signature-generic, so it fires at the
    walking adjoint triple;
  * `spineBoundaryWordChained_swappedPair` — ★ (B2) the transposed pair stays boundary-WORD-chained at the
    SAME running boundary word.  Unlike the length version (`adjunctionSwappedPair_isBoundaryChained`, pure
    `Nat` bookkeeping), this threads WORDS: the moved-second atom fires at the original running boundary word
    (via `rightFactor` + `composePath_assoc`), the moved-first at the moved-second's target word, and the tail
    is transported to the moved-first's target word (via `leftFactor` + `composePath_assoc`).  All
    `composePath` re-association — no split-pack needed here.

Non-vacuity (`stringDisjointWordSwap_equalLengthDistinctWord`) fires BOTH bricks on the
equal-length-DISTINCT-word `(η : F·G, ε' : H·G)` config on a genuinely word-chained spine — the class the
length-rigid engine could not touch.

Raw Lean 4 + Init; the swap is one factorization + one `composePath_assoc` bridge, the preservation is pure
`composePath` re-association.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The realized WORD-indexed swap (B1) -/

/-- ★ **The realized WORD-indexed disjoint-window swap.**  Adjacent atoms whose boundary words chain
(`sharedWord`) with the second window a `windowGap` to the RIGHT of the first's produced window transpose by a
genuine `SpineAtomSwap`: the word-indexed factorization (B1) exhibits the constructor's whisker shape (up to
one `composePath_assoc`), and the swap fires with the moved atoms as record updates — the second atom's left
context re-threads through the first's SOURCE 1-cell, the first atom's right context re-threads through the
second's TARGET 1-cell.  The inert gap-length pin rides along.  Signature-GENERIC (the factorization is), so
it runs at the walking adjoint triple where length-rigidity fails. -/
theorem spineAtomSwap_of_disjointWordWindows {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (atomFirst atomSecond : SpineAtom signature overallSource overallTarget)
    (rest : List (SpineAtom signature overallSource overallTarget))
    (sharedWord :
      composePath atomFirst.leftContext (composePath atomFirst.generatorCod atomFirst.rightContext)
        = composePath atomSecond.leftContext
            (composePath atomSecond.generatorDom atomSecond.rightContext))
    (windowGap : Nat)
    (windowsDisjoint :
      atomFirst.leftContext.length + atomFirst.generatorCod.length + windowGap
        = atomSecond.leftContext.length) :
    ∃ inertPath : ModalityPath signature.graph atomFirst.rightMidMode atomSecond.leftMidMode,
      inertPath.length = windowGap
        ∧ SpineAtomSwap signature
            (atomFirst :: atomSecond :: rest)
            ({ atomSecond with
                leftContext :=
                  composePath (composePath atomFirst.leftContext atomFirst.generatorDom) inertPath }
              :: { atomFirst with
                    rightContext :=
                      composePath (composePath inertPath atomSecond.generatorCod)
                        atomSecond.rightContext }
              :: rest) := by
  obtain ⟨inertPath, leftFactor, rightFactor, inertLength⟩ :=
    spineAtom_contextsFactor_of_disjointWordWindows atomFirst atomSecond sharedWord windowGap
      windowsDisjoint
  refine ⟨inertPath, inertLength, ?_⟩
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := atomFirst
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := atomSecond
  dsimp only at leftFactor rightFactor ⊢
  rw [leftFactor, rightFactor, ← composePath_assoc inertPath generatorDomB rightContextB]
  exact SpineAtomSwap.swap generatorA generatorB leftContextA inertPath rightContextB rest

/-! ## The WORD-chain preservation (B2) -/

/-- ★ **The swapped pair stays boundary-WORD-chained.**  If `atomFirst :: atomSecond :: rest` is
boundary-word-chained at the running boundary word and the two atoms' contexts factor through the inert path
(the B1 factorization output `leftFactor` / `rightFactor`), then the transposed list produced by
`spineAtomSwap_of_disjointWordWindows` is boundary-word-chained at the SAME running boundary word.  Threads
WORDS (not just lengths): the moved-second atom fires at the original running boundary word (via `rightFactor`
+ `composePath_assoc`), the moved-first fires at the moved-second's target boundary word, and the tail's chain
is transported to the moved-first's target boundary word (via `leftFactor` + `composePath_assoc`).  This is the
peel's iteration invariant at the word granularity — after each bubble step the next swap's word-chainedness
premise is available. -/
theorem spineBoundaryWordChained_swappedPair {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (atomFirst atomSecond : SpineAtom signature overallSource overallTarget)
    {rest : List (SpineAtom signature overallSource overallTarget)}
    {boundaryWord : ModalityPath signature.graph overallSource overallTarget}
    (pairWordChained : SpineBoundaryWordChained boundaryWord (atomFirst :: atomSecond :: rest))
    (inertPath : ModalityPath signature.graph atomFirst.rightMidMode atomSecond.leftMidMode)
    (leftFactor :
      atomSecond.leftContext
        = composePath (composePath atomFirst.leftContext atomFirst.generatorCod) inertPath)
    (rightFactor :
      atomFirst.rightContext
        = composePath inertPath (composePath atomSecond.generatorDom atomSecond.rightContext)) :
    SpineBoundaryWordChained boundaryWord
      ({ atomSecond with
          leftContext :=
            composePath (composePath atomFirst.leftContext atomFirst.generatorDom) inertPath }
        :: { atomFirst with
              rightContext :=
                composePath (composePath inertPath atomSecond.generatorCod)
                  atomSecond.rightContext }
        :: rest) := by
  obtain ⟨firstFires, tailWordChained⟩ := spineBoundaryWordChained_tail pairWordChained
  obtain ⟨_secondFires, restWordChained⟩ := spineBoundaryWordChained_tail tailWordChained
  obtain ⟨leftMidA, rightMidA, leftContextA, generatorDomA, generatorCodA, generatorA,
    rightContextA⟩ := atomFirst
  obtain ⟨leftMidB, rightMidB, leftContextB, generatorDomB, generatorCodB, generatorB,
    rightContextB⟩ := atomSecond
  dsimp only at firstFires restWordChained leftFactor rightFactor ⊢
  refine SpineBoundaryWordChained.cons _ ?_ (SpineBoundaryWordChained.cons _ ?_ ?_)
  · rw [firstFires, rightFactor,
        composePath_assoc (composePath leftContextA generatorDomA) inertPath
          (composePath generatorDomB rightContextB),
        composePath_assoc leftContextA generatorDomA
          (composePath inertPath (composePath generatorDomB rightContextB))]
  · rw [composePath_assoc (composePath leftContextA generatorDomA) inertPath
          (composePath generatorCodB rightContextB),
        composePath_assoc leftContextA generatorDomA
          (composePath inertPath (composePath generatorCodB rightContextB)),
        composePath_assoc inertPath generatorCodB rightContextB]
  · rw [composePath_assoc inertPath generatorCodB rightContextB,
        ← composePath_assoc leftContextA generatorCodA
          (composePath inertPath (composePath generatorCodB rightContextB)),
        ← composePath_assoc (composePath leftContextA generatorCodA) inertPath
          (composePath generatorCodB rightContextB),
        ← leftFactor]
    exact restWordChained

/-! ## Non-vacuity — both bricks fire on the equal-length-DISTINCT-word class -/

/-- ★ **Both bricks fire on the equal-length-DISTINCT-word config.**  The lower cup `η : id_base ⇒ F·G`
directly followed by the upper counit `ε' : H·G ⇒ id_base` (both windows length `2`, `F·G ≠ H·G`) on a
genuinely word-chained spine: the realized word swap (B1) transposes them, and the swapped pair stays
boundary-word-chained (B2) at the same boundary word `F·G·H·G` — the class the length-rigid engine could not
run. -/
theorem stringDisjointWordSwap_equalLengthDistinctWord :
    (∃ firstOrder secondOrder :
        List (SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base),
      SpineAtomSwap adjointTripleModeSignature firstOrder secondOrder)
    ∧ (∃ swappedPair :
        List (SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base),
      SpineBoundaryWordChained (signature := adjointTripleModeSignature) stringHG swappedPair) := by
  let cupAtom : SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
    ⟨AdjointTripleMode.base, AdjointTripleMode.base,
      ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
      ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base, stringFG,
      StringTwoCell.unitLower, stringHG⟩
  let capAtom : SpineAtom adjointTripleModeSignature AdjointTripleMode.base AdjointTripleMode.base :=
    ⟨AdjointTripleMode.base, AdjointTripleMode.base, stringFG, stringHG,
      ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base,
      StringTwoCell.counitUpper,
      ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base⟩
  have chained : SpineBoundaryWordChained (signature := adjointTripleModeSignature) stringHG
      [cupAtom, capAtom] :=
    SpineBoundaryWordChained.cons cupAtom rfl
      (SpineBoundaryWordChained.cons capAtom rfl (SpineBoundaryWordChained.nil _))
  have sharedWord := spineBoundaryWordChained_pairSharedWord chained
  refine ⟨?_, ?_⟩
  · -- B1 swap: the pair genuinely transposes.
    obtain ⟨_inertPath, _inertLength, windowSwap⟩ :=
      spineAtomSwap_of_disjointWordWindows cupAtom capAtom [] sharedWord 0 rfl
    exact ⟨_, _, windowSwap⟩
  · -- B2 preservation: the factorization's swapped pair stays word-chained.
    obtain ⟨inertPath, leftFactor, rightFactor, _⟩ :=
      spineAtom_contextsFactor_of_disjointWordWindows cupAtom capAtom sharedWord 0 rfl
    exact ⟨_, spineBoundaryWordChained_swappedPair cupAtom capAtom chained inertPath leftFactor
      rightFactor⟩

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the realized WORD-indexed disjoint-window swap is machine-checked (FC-3 r4, B1).**
`spineAtomSwap_of_disjointWordWindows` fires a genuine `SpineAtomSwap` on any adjacent word-chained pair with a
right-of gap, delegating to the B1 word factorization (one `composePath_assoc` bridge), moved atoms explicit.
Signature-GENERIC — it runs at the walking adjoint triple where length-rigidity fails.  `= true`. -/
def fxString_hasDisjointWordSwap : Bool := true

/-- **★ ESTABLISHED — the WORD-chain preservation is machine-checked (FC-3 r4, B2).**
`spineBoundaryWordChained_swappedPair` threads the transposed pair back into `SpineBoundaryWordChained` at the
same running boundary WORD — the word analogue of the length-only `adjunctionSwappedPair_isBoundaryChained`,
threading WORDS by `composePath_assoc` re-association (not `Nat` bookkeeping).  Non-vacuity
`stringDisjointWordSwap_equalLengthDistinctWord` fires both bricks on the equal-length-DISTINCT-word
`(η : F·G, ε' : H·G)` config on a word-chained spine — the class the length-rigid engine could not run.
`= true`. -/
def fxString_hasWordSwapChainPreservation : Bool := true

end FX1Poly.Polygraph
