import FX1Poly.Polygraph.Omega.ZXPhaseFree.SpiderRelationSeed
import FX1Poly.Polygraph.Omega.ZXPhaseFree.CompletenessGate
import FX1Poly.Polygraph.Omega.ZXPhaseFree.FusionRepair

/-! # Polygraph/Omega/ZXPhaseFree/NormalFormCensus — the Z-X normal form + the census gate

THE CENSUS GATE STAGE recorded in `zxrCompletenessStatement`'s docstring: before any
completeness push over `ZxrConv`, (A) a normal-form FAMILY with a STRUCTURAL denotation
theorem, and (B) a kernel census at small boundaries — surjectivity (every subspace is
hit) and injectivity (distinct subspaces stay distinct) pins.

## (A) The normal form: construction choices (binding documentation)

`zxnNormalForm domWidth codWidth generatorRows` mirrors Kissinger arXiv:2204.14038
eq. (5)/(6) — the Z-X normal form of the subspace `S = span(generatorRows)` of
`F2^(domWidth + codWidth)` — transported to the strict-layer syntax in FISSIONED form:

* eq. (6) puts ONE Z-spider PER GENERATOR (the basis-vector spider, holding the free
  coefficient of that generator) and ONE X-spider PER WIRE (adding up the incident
  generator legs).  Here each generator's Z-spider appears as a fissioned binary comb:
  a `zSpider 0 1` head creating the coefficient carrier, one `zSpider 1 2` fork per
  incident wire, and a final `zSpider 1 0` discard closing the through-strand — an
  unfissioned arity of `weight + 1` (the (sp)-decomposition of the eq. (6) spider,
  with the one extra leg absorbed by the Z-counit).
* each wire's X-spider appears as the chain: an `xSpider 0 1` zero-state base on the
  codomain side (the `zxnInitLayer`), one `xSpider 2 1` xor-merge per incident
  generator (inside the combs), and an `xSpider 1 0` zero-effect collector on the
  domain side (the `zxnKillLayer`) — unfissioned arity `columnWeight + 1` on the
  codomain side and `columnWeight + 2` on the domain side (boundary leg included).
* the wiring/crossing block of the published picture appears as the adjacent-crossing
  carrier walk inside each comb (`ZxpCell.crossing` steps), so no global permutation
  block is ever needed: the layered diagram is
  `init ; comb(g_1) ; ... ; comb(g_k) ; kill`.

PIVOT / ECHELON STRUCTURE -> SPIDER ARITIES: when the input is an RREF matrix (as in
the census below), generator `j`'s comb SKIPS (crossing steps) exactly up to its pivot
column and places its FIRST `zSpider 1 2` fork AT the pivot; the fissioned Z-tree of
generator `j` has exactly `weight(g_j)` forks, i.e. unfissioned arity
`weight(g_j) + 1`, and the number of xor-merges on wire `i` is the column weight
(number of pivots-or-free-entries hitting `i`).  The RREF pivot count = the number of
combs = `dim S`.

Denotation (`zxnNormalFormDenotes`, STRUCTURAL, no kernel evaluation): the init layer
relates `u ~ cat u 0^cod`; each comb block relates `v ~ xor v (t * g)` for a free
coefficient bit `t` (theorem `zxnCombPairIff` by induction on the row, through the
seed's `zxpComposeSpec`/`zxpTensorSpec`/`zxpIdSpec` and the FusionRepair span
characterizations); the kill layer relates `cat 0^dom w ~ w`.  Chaining:
`(u, w)` is related iff `xor (cat u 0) (cat 0 w) = cat u w` lies in `span S` — i.e.
the diagram's relation IS the input subspace, `ZxpRelEquiv`-equal to `generatorRows`.

## (B) The census (kernel pins)

`zxnAllRrefMatrices width` enumerates ALL reduced-row-echelon generator matrices over
F2 (one per subspace: pivot-column recursion; a candidate top row must be reduced
against the tail's pivots).  Enumeration sizes (kernel-pinned below):
width 2 -> 5, width 3 -> 16, width 4 -> 67 (the Galois numbers).  Census boundaries:
(dom, cod) in {(1,1), (1,2), (2,1), (2,2)} — widths 1 and 2 covered on each side;
census sizes 5 + 16 + 16 + 67 = 104 subspaces.  SURJECTIVITY pins: for every
enumerated RREF the normal form is executably well-formed, has the right target
arity, and its denotation is span-equal to the RREF (one fold per boundary, kernel
`rfl`).  INJECTIVITY: pairwise span-distinctness of the enumeration is kernel-pinned
per width, and `zxnNormalFormInjective` PROVES (via the denotation theorem, not by
kernel) that span-distinct generator lists always produce span-distinct normal forms.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`, no
`Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive
scrutinees; width-only matches; kernel evaluation confined to the census/fire pins. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — shape, arithmetic, scale-row, and span-cons kit -/

/-- A row of length 1 is a singleton. -/
theorem zxnLengthOneShape : (row : List Bool) -> row.length = 1 ->
    Exists fun onlyBit => row = [onlyBit]
  | [], hLen => nomatch hLen
  | headBit :: restBits, hLen => by
      cases restBits with
      | nil => exact Exists.intro headBit rfl
      | cons secondBit tailBits => exact nomatch Nat.succ.inj hLen

/-- A row of length 2 is an explicit pair. -/
theorem zxnLengthTwoShape : (row : List Bool) -> row.length = 2 ->
    Exists fun firstBit => Exists fun secondBit => row = [firstBit, secondBit]
  | [], hLen => nomatch hLen
  | headBit :: restBits, hLen => by
      cases restBits with
      | nil => exact nomatch Nat.succ.inj hLen
      | cons secondBit tailBits =>
          cases tailBits with
          | nil => exact Exists.intro headBit (Exists.intro secondBit rfl)
          | cons thirdBit deepBits =>
              exact nomatch Nat.succ.inj (Nat.succ.inj hLen)

/-- A row of positive length is a cons. -/
theorem zxnLengthSuccShape : (row : List Bool) -> (lengthPredValue : Nat) ->
    row.length = lengthPredValue + 1 ->
    Exists fun headBit => Exists fun restBits =>
      row = headBit :: restBits /\ restBits.length = lengthPredValue
  | [], _lengthPredValue, hLen => nomatch hLen
  | headBit :: restBits, _lengthPredValue, hLen =>
      Exists.intro headBit (Exists.intro restBits (And.intro rfl (Nat.succ.inj hLen)))

/-- `2 + t = 1 + (t + 1)` (the crossing-layer head arity shuffle). -/
theorem zxnTwoPlusEqOnePlusSucc (tailLength : Nat) : 2 + tailLength = 1 + (tailLength + 1) := by
  show (1 + 1) + tailLength = 1 + (tailLength + 1)
  rw [Nat.add_assoc 1 1 tailLength, Nat.add_comm 1 tailLength]

/-- `p + (2 + t) = (p + 1) + (1 + t)` (the carrier-step arity shuffle). -/
theorem zxnStepArityShuffle (prefixWires tailLength : Nat) :
    prefixWires + (2 + tailLength) = (prefixWires + 1) + (1 + tailLength) := by
  show prefixWires + ((1 + 1) + tailLength) = (prefixWires + 1) + (1 + tailLength)
  rw [Nat.add_assoc 1 1 tailLength, <- Nat.add_assoc prefixWires 1 (1 + tailLength)]

/-- `(p + 1) + t = p + (t + 1)` (the comb output arity shuffle). -/
theorem zxnCombCodShuffle (prefixWires tailLength : Nat) :
    (prefixWires + 1) + tailLength = prefixWires + (tailLength + 1) := by
  rw [Nat.add_assoc prefixWires 1 tailLength, Nat.add_comm 1 tailLength]

/-- `p + (2 + (t + 1)) = (p + 1) + (2 + t)` (the fork-to-merge arity shuffle). -/
theorem zxnForkArityShuffle (prefixWires tailLength : Nat) :
    prefixWires + (2 + (tailLength + 1)) = (prefixWires + 1) + (2 + tailLength) := by
  refine ((congrArg (fun innerValue => prefixWires + innerValue) ?_).trans
    (Nat.add_assoc prefixWires 1 (2 + tailLength)).symm)
  exact (Nat.add_succ 2 tailLength).trans (Nat.add_comm (2 + tailLength) 1)

/-- Scale a row by a bit: the row itself, or the zero row of the same length. -/
def zxnScaleRow : Bool -> List Bool -> List Bool
  | true, row => row
  | false, row => zxpZeroRow row.length

theorem zxnScaleRowLength : (scaleBit : Bool) -> (row : List Bool) ->
    (zxnScaleRow scaleBit row).length = row.length
  | true, _row => rfl
  | false, row => zxpZeroRowLength row.length

/-- Scaling distributes over a false head bit. -/
theorem zxnScaleRowConsFalse : (scaleBit : Bool) -> (restBits : List Bool) ->
    zxnScaleRow scaleBit (false :: restBits) = false :: zxnScaleRow scaleBit restBits
  | true, _restBits => rfl
  | false, _restBits => rfl

/-- Scaling turns a true head bit into the scale bit itself. -/
theorem zxnScaleRowConsTrue : (scaleBit : Bool) -> (restBits : List Bool) ->
    zxnScaleRow scaleBit (true :: restBits) = scaleBit :: zxnScaleRow scaleBit restBits
  | true, _restBits => rfl
  | false, _restBits => rfl

/-- Left commutation for row xor at a common width. -/
theorem zxnRowXorLeftComm (firstRow secondRow thirdRow : List Bool) :
    zxpRowXor firstRow (zxpRowXor secondRow thirdRow)
      = zxpRowXor secondRow (zxpRowXor firstRow thirdRow) := by
  rw [<- zxpRowXorAssoc firstRow secondRow thirdRow,
    zxpRowXorComm firstRow secondRow,
    zxpRowXorAssoc secondRow firstRow thirdRow]

/-- Members of a singleton-generator span: the zero row or the generator. -/
theorem zxnMemSpanSingleInv {width : Nat} {onlyRow : List Bool}
    (hLen : onlyRow.length = width) {vector : List Bool}
    (hMem : ZxpMemSpan width [onlyRow] vector) :
    vector = zxpZeroRow width \/ vector = onlyRow := by
  have hSplit := zxpMemSpanConsInv (ZxpAllWidth.cons hLen ZxpAllWidth.nil) hMem
  cases hSplit with
  | inl hInRest => exact Or.inl (zxpMemSpanNilInv hInRest)
  | inr hPacked =>
      obtain ⟨partnerVec, hPartnerMem, hSplitEq⟩ := hPacked
      have hPartnerZero := zxpMemSpanNilInv hPartnerMem
      rw [hPartnerZero, zxpRowXorZeroRight onlyRow width hLen] at hSplitEq
      exact Or.inr hSplitEq

/-- Span membership at a cons, packaged as a scale-bit existential. -/
theorem zxnMemSpanConsIff {width : Nat} {headRow : List Bool} {restRows : List (List Bool)}
    (hAll : ZxpAllWidth width (headRow :: restRows)) (vector : List Bool) :
    ZxpMemSpan width (headRow :: restRows) vector
      <-> Exists fun scaleBit => Exists fun partnerVec =>
          ZxpMemSpan width restRows partnerVec
            /\ vector = zxpRowXor (zxnScaleRow scaleBit headRow) partnerVec := by
  have hHeadLen : headRow.length = width := by
    cases hAll with
    | cons hHead _hRest => exact hHead
  have hRestAll : ZxpAllWidth width restRows := by
    cases hAll with
    | cons _hHead hRest => exact hRest
  refine Iff.intro ?_ ?_
  · intro hMem
    have hSplit := zxpMemSpanConsInv hAll hMem
    cases hSplit with
    | inl hInRest =>
        refine Exists.intro false (Exists.intro vector (And.intro hInRest ?_))
        show vector = zxpRowXor (zxpZeroRow headRow.length) vector
        rw [hHeadLen,
          zxpRowXorZeroLeft vector width (zxpMemSpanWidth hRestAll hInRest)]
    | inr hPacked =>
        obtain ⟨partnerVec, hPartnerMem, hSplitEq⟩ := hPacked
        exact Exists.intro true (Exists.intro partnerVec (And.intro hPartnerMem hSplitEq))
  · intro hPacked
    obtain ⟨scaleBit, partnerVec, hPartnerMem, hSplitEq⟩ := hPacked
    have hWeakened := zxpMemSpanWeaken headRow hPartnerMem
    cases scaleBit with
    | false =>
        rw [hSplitEq]
        show ZxpMemSpan width (headRow :: restRows)
          (zxpRowXor (zxpZeroRow headRow.length) partnerVec)
        rw [hHeadLen,
          zxpRowXorZeroLeft partnerVec width (zxpMemSpanWidth hRestAll hPartnerMem)]
        exact hWeakened
    | true =>
        rw [hSplitEq]
        exact ZxpMemSpan.pick headRow (ZxpRowMem.head headRow restRows) hWeakened

/-! ## Stage 1 — the cell relation characterizations

Each cell used by the normal form gets its pair-membership characterized once:
the Z source/sink/fork through the FusionRepair copy-span kit, the X merge and the
zero state/effect through the parity-span kit, and the crossing through the concrete
width-4 two-generator span. -/

/-- The Z source `zSpider 0 1` relates `()` to any single bit (the free coefficient). -/
theorem zxnZSourcePairIff (domVec codVec : List Bool) :
    ZxpPairMem 0 1 (zxpSpiderCopyRows 1) domVec codVec
      <-> (domVec = [] /\ Exists fun freeBit => codVec = [freeBit]) := by
  refine Iff.intro ?_ ?_
  · intro hPair
    obtain ⟨onlyBit, hShape⟩ := zxnLengthOneShape codVec hPair.right.left
    exact And.intro (zxpLengthZeroNil domVec hPair.left) (Exists.intro onlyBit hShape)
  · intro hBoth
    obtain ⟨freeBit, hShape⟩ := hBoth.right
    refine And.intro (by rw [hBoth.left]; rfl) (And.intro (by rw [hShape]; rfl) ?_)
    rw [hBoth.left, hShape]
    show ZxpMemSpan 1 (zxpSpiderCopyRows 1) [freeBit]
    cases freeBit with
    | false => exact ZxpMemSpan.zero
    | true =>
        exact ZxpMemSpan.pick (zxpAllOnesRow 1) (ZxpRowMem.head (zxpAllOnesRow 1) [])
          (ZxpMemSpan.zero (width := 1) (rows := zxpSpiderCopyRows 1))

/-- The Z sink `zSpider 1 0` relates any single bit to `()` (the carrier discard). -/
theorem zxnZSinkPairIff (domVec codVec : List Bool) :
    ZxpPairMem 1 0 (zxpSpiderCopyRows 1) domVec codVec
      <-> ((Exists fun anyBit => domVec = [anyBit]) /\ codVec = []) := by
  refine Iff.intro ?_ ?_
  · intro hPair
    obtain ⟨onlyBit, hShape⟩ := zxnLengthOneShape domVec hPair.left
    exact And.intro (Exists.intro onlyBit hShape) (zxpLengthZeroNil codVec hPair.right.left)
  · intro hBoth
    obtain ⟨anyBit, hShape⟩ := hBoth.left
    refine And.intro (by rw [hShape]; rfl) (And.intro (by rw [hBoth.right]; rfl) ?_)
    rw [hBoth.right, hShape]
    show ZxpMemSpan 1 (zxpSpiderCopyRows 1) (zxpCat [anyBit] [])
    cases anyBit with
    | false => exact ZxpMemSpan.zero
    | true =>
        exact ZxpMemSpan.pick (zxpAllOnesRow 1) (ZxpRowMem.head (zxpAllOnesRow 1) [])
          (ZxpMemSpan.zero (width := 1) (rows := zxpSpiderCopyRows 1))

/-- The Z fork `zSpider 1 2` copies its input bit onto both outputs. -/
theorem zxnZForkPairIff (domVec codVec : List Bool) :
    ZxpPairMem 1 2 (zxpSpiderCopyRows 3) domVec codVec
      <-> Exists fun copiedBit => domVec = [copiedBit] /\ codVec = [copiedBit, copiedBit] := by
  refine Iff.trans (zxrCopyPairMemIff 1 2 domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hCopy
    obtain ⟨onlyBit, hDomShape⟩ := zxnLengthOneShape domVec hCopy.left
    obtain ⟨firstBit, secondBit, hCodShape⟩ := zxnLengthTwoShape codVec hCopy.right.left
    have hConst := hCopy.right.right
    rw [hDomShape, hCodShape] at hConst
    refine Exists.intro onlyBit (And.intro hDomShape ?_)
    rw [hCodShape]
    cases hConst with
    | inl hAllFalse =>
        cases onlyBit with
        | false =>
            cases firstBit with
            | false =>
                cases secondBit with
                | false => rfl
                | true => exact Bool.noConfusion hAllFalse
            | true => exact Bool.noConfusion hAllFalse
        | true => exact Bool.noConfusion hAllFalse
    | inr hAllTrue =>
        cases onlyBit with
        | false => exact Bool.noConfusion hAllTrue
        | true =>
            cases firstBit with
            | false => exact Bool.noConfusion hAllTrue
            | true =>
                cases secondBit with
                | false => exact Bool.noConfusion hAllTrue
                | true => rfl
  · intro hPacked
    obtain ⟨copiedBit, hDomShape, hCodShape⟩ := hPacked
    refine And.intro (by rw [hDomShape]; rfl) (And.intro (by rw [hCodShape]; rfl) ?_)
    rw [hDomShape, hCodShape]
    cases copiedBit with
    | false => exact Or.inl rfl
    | true => exact Or.inr rfl

/-- The X merge `xSpider 2 1` outputs the xor of its two inputs. -/
theorem zxnXMergePairIff (domVec codVec : List Bool) :
    ZxpPairMem 2 1 (zxpParityRows 3) domVec codVec
      <-> Exists fun firstBit => Exists fun secondBit =>
          domVec = [firstBit, secondBit] /\ codVec = [zxpXorB firstBit secondBit] := by
  refine Iff.trans (zxrAddPairMemIff 2 1 domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hAdd
    obtain ⟨firstBit, secondBit, hDomShape⟩ := zxnLengthTwoShape domVec hAdd.left
    obtain ⟨outBit, hCodShape⟩ := zxnLengthOneShape codVec hAdd.right.left
    have hParity := hAdd.right.right
    rw [hDomShape, hCodShape] at hParity
    refine Exists.intro firstBit (Exists.intro secondBit (And.intro hDomShape ?_))
    rw [hCodShape]
    have hOutEq : outBit = zxpXorB firstBit secondBit := by
      cases firstBit with
      | false =>
          cases secondBit with
          | false =>
              cases outBit with
              | false => rfl
              | true => exact Bool.noConfusion hParity
          | true =>
              cases outBit with
              | false => exact Bool.noConfusion hParity
              | true => rfl
      | true =>
          cases secondBit with
          | false =>
              cases outBit with
              | false => exact Bool.noConfusion hParity
              | true => rfl
          | true =>
              cases outBit with
              | false => rfl
              | true => exact Bool.noConfusion hParity
    rw [hOutEq]
  · intro hPacked
    obtain ⟨firstBit, secondBit, hDomShape, hCodShape⟩ := hPacked
    refine And.intro (by rw [hDomShape]; rfl) (And.intro (by rw [hCodShape]; rfl) ?_)
    rw [hDomShape, hCodShape]
    cases firstBit with
    | false =>
        cases secondBit with
        | false => rfl
        | true => rfl
    | true =>
        cases secondBit with
        | false => rfl
        | true => rfl

/-- The X zero state `xSpider 0 1` relates `()` to exactly `[false]`. -/
theorem zxnXZeroStatePairIff (domVec codVec : List Bool) :
    ZxpPairMem 0 1 (zxpParityRows 1) domVec codVec
      <-> (domVec = [] /\ codVec = [false]) := by
  refine Iff.intro ?_ ?_
  · intro hPair
    have hDomNil := zxpLengthZeroNil domVec hPair.left
    have hMem := hPair.right.right
    have hZero := zxpMemSpanNilInv hMem
    rw [hDomNil] at hZero
    exact And.intro hDomNil hZero
  · intro hBoth
    refine And.intro (by rw [hBoth.left]; rfl) (And.intro (by rw [hBoth.right]; rfl) ?_)
    rw [hBoth.left, hBoth.right]
    exact ZxpMemSpan.zero

/-- The X zero effect `xSpider 1 0` relates exactly `[false]` to `()`. -/
theorem zxnXZeroEffectPairIff (domVec codVec : List Bool) :
    ZxpPairMem 1 0 (zxpParityRows 1) domVec codVec
      <-> (domVec = [false] /\ codVec = []) := by
  refine Iff.intro ?_ ?_
  · intro hPair
    have hCodNil := zxpLengthZeroNil codVec hPair.right.left
    have hMem := hPair.right.right
    have hZero := zxpMemSpanNilInv hMem
    rw [hCodNil, zxpCatNilRight domVec] at hZero
    exact And.intro hZero hCodNil
  · intro hBoth
    refine And.intro (by rw [hBoth.left]; rfl) (And.intro (by rw [hBoth.right]; rfl) ?_)
    rw [hBoth.left, hBoth.right]
    exact ZxpMemSpan.zero

/-- The concrete generator matrix of the adjacent crossing. -/
theorem zxnSwapRowsLiteral :
    zxpSwapRows 1 1 = [[true, false, false, true], [false, true, true, false]] := rfl

/-- The crossing swaps its two strands. -/
theorem zxnCrossingPairIff (domVec codVec : List Bool) :
    ZxpPairMem 2 2 (zxpSwapRows 1 1) domVec codVec
      <-> Exists fun firstBit => Exists fun secondBit =>
          domVec = [firstBit, secondBit] /\ codVec = [secondBit, firstBit] := by
  refine Iff.intro ?_ ?_
  · intro hPair
    obtain ⟨firstBit, secondBit, hDomShape⟩ := zxnLengthTwoShape domVec hPair.left
    obtain ⟨thirdBit, fourthBit, hCodShape⟩ := zxnLengthTwoShape codVec hPair.right.left
    have hMem := hPair.right.right
    rw [hDomShape, hCodShape, zxnSwapRowsLiteral] at hMem
    have hAllSwap : ZxpAllWidth 4 [[true, false, false, true], [false, true, true, false]] :=
      ZxpAllWidth.cons rfl (ZxpAllWidth.cons rfl ZxpAllWidth.nil)
    have hSplit := zxpMemSpanConsInv hAllSwap hMem
    refine Exists.intro firstBit (Exists.intro secondBit (And.intro hDomShape ?_))
    rw [hCodShape]
    cases hSplit with
    | inl hInRest =>
        have hInner := zxnMemSpanSingleInv
          (show ([false, true, true, false] : List Bool).length = 4 from rfl) hInRest
        cases hInner with
        | inl hZero =>
            injection hZero with hFirst hTail1
            injection hTail1 with hSecond hTail2
            injection hTail2 with hThird hTail3
            injection hTail3 with hFourth hTail4
            rw [hFirst, hSecond, hThird, hFourth]
        | inr hGen =>
            injection hGen with hFirst hTail1
            injection hTail1 with hSecond hTail2
            injection hTail2 with hThird hTail3
            injection hTail3 with hFourth hTail4
            rw [hFirst, hSecond, hThird, hFourth]
    | inr hPacked =>
        obtain ⟨partnerVec, hPartnerMem, hSplitEq⟩ := hPacked
        have hInner := zxnMemSpanSingleInv
          (show ([false, true, true, false] : List Bool).length = 4 from rfl) hPartnerMem
        cases hInner with
        | inl hZero =>
            rw [hZero] at hSplitEq
            injection hSplitEq with hFirst hTail1
            injection hTail1 with hSecond hTail2
            injection hTail2 with hThird hTail3
            injection hTail3 with hFourth hTail4
            rw [hFirst, hSecond, hThird, hFourth]
        | inr hGen =>
            rw [hGen] at hSplitEq
            injection hSplitEq with hFirst hTail1
            injection hTail1 with hSecond hTail2
            injection hTail2 with hThird hTail3
            injection hTail3 with hFourth hTail4
            rw [hFirst, hSecond, hThird, hFourth]
  · intro hPacked
    obtain ⟨firstBit, secondBit, hDomShape, hCodShape⟩ := hPacked
    refine And.intro (by rw [hDomShape]; rfl) (And.intro (by rw [hCodShape]; rfl) ?_)
    rw [hDomShape, hCodShape]
    show ZxpMemSpan 4 (zxpSwapRows 1 1) [firstBit, secondBit, secondBit, firstBit]
    cases firstBit with
    | false =>
        cases secondBit with
        | false => exact ZxpMemSpan.zero
        | true =>
            exact ZxpMemSpan.pick [false, true, true, false]
              (ZxpRowMem.tail (ZxpRowMem.head [false, true, true, false] []))
              (ZxpMemSpan.zero (width := 4) (rows := zxpSwapRows 1 1))
    | true =>
        cases secondBit with
        | false =>
            exact ZxpMemSpan.pick [true, false, false, true]
              (ZxpRowMem.head [true, false, false, true] [[false, true, true, false]])
              (ZxpMemSpan.zero (width := 4) (rows := zxpSwapRows 1 1))
        | true =>
            exact ZxpMemSpan.pick [true, false, false, true]
              (ZxpRowMem.head [true, false, false, true] [[false, true, true, false]])
              (ZxpMemSpan.pick [false, true, true, false]
                (ZxpRowMem.tail (ZxpRowMem.head [false, true, true, false] []))
                (ZxpMemSpan.zero (width := 4) (rows := zxpSwapRows 1 1)))

/-! ## Stage 2 — the layer-chaining and padded-cell workhorses -/

/-- Peeling one layer off a layer list splits pair membership through a middle vector. -/
theorem zxnConsLayerPairIff (headLayer : List ZxpCell) (restLayers : List (List ZxpCell))
    (hRestWF : ZxpLayersWF (zxpLayerCodArity headLayer) restLayers)
    (domVec codVec : List Bool) :
    ZxpPairMem (zxpLayerDomArity headLayer)
        (zxpLayersCodArity (zxpLayerCodArity headLayer) restLayers)
        (zxpLayersDenote (zxpLayerDomArity headLayer) (headLayer :: restLayers))
        domVec codVec
      <-> Exists fun midVec =>
          ZxpPairMem (zxpLayerDomArity headLayer) (zxpLayerCodArity headLayer)
              (zxpLayerDenote headLayer) domVec midVec
            /\ ZxpPairMem (zxpLayerCodArity headLayer)
                (zxpLayersCodArity (zxpLayerCodArity headLayer) restLayers)
                (zxpLayersDenote (zxpLayerCodArity headLayer) restLayers) midVec codVec :=
  zxpComposeSpec (zxpLayerDomArity headLayer) (zxpLayerCodArity headLayer)
    (zxpLayersCodArity (zxpLayerCodArity headLayer) restLayers)
    (zxpLayerDenote headLayer)
    (zxpLayersDenote (zxpLayerCodArity headLayer) restLayers)
    (zxpLayerDenoteWidth headLayer)
    (zxpLayersDenoteWidth restLayers hRestWF) domVec codVec

/-- `zxnConsLayerPairIff` with the three arities supplied by equations. -/
theorem zxnConsLayerPairIffAt (currentArity midArity finalArity : Nat)
    (headLayer : List ZxpCell) (restLayers : List (List ZxpCell))
    (hHeadDom : zxpLayerDomArity headLayer = currentArity)
    (hHeadCod : zxpLayerCodArity headLayer = midArity)
    (hRestWF : ZxpLayersWF midArity restLayers)
    (hFinal : zxpLayersCodArity midArity restLayers = finalArity)
    (domVec codVec : List Bool) :
    ZxpPairMem currentArity finalArity
        (zxpLayersDenote currentArity (headLayer :: restLayers)) domVec codVec
      <-> Exists fun midVec =>
          ZxpPairMem currentArity midArity (zxpLayerDenote headLayer) domVec midVec
            /\ ZxpPairMem midArity finalArity
                (zxpLayersDenote midArity restLayers) midVec codVec := by
  subst hHeadDom
  subst hHeadCod
  subst hFinal
  exact zxnConsLayerPairIff headLayer restLayers hRestWF domVec codVec

/-- A one-layer list denotes its layer (compose-with-identity collapse). -/
theorem zxnSingleLayerPairIffAt (currentArity finalArity : Nat) (theLayer : List ZxpCell)
    (hLayerDom : zxpLayerDomArity theLayer = currentArity)
    (hLayerCod : zxpLayerCodArity theLayer = finalArity)
    (domVec codVec : List Bool) :
    ZxpPairMem currentArity finalArity
        (zxpLayersDenote currentArity [theLayer]) domVec codVec
      <-> ZxpPairMem currentArity finalArity (zxpLayerDenote theLayer) domVec codVec := by
  subst hLayerDom
  subst hLayerCod
  exact zxpComposeIdRight (zxpLayerDomArity theLayer) (zxpLayerCodArity theLayer)
    (zxpLayerDenote theLayer) (zxpLayerDenoteWidth theLayer) domVec codVec

/-- Concatenated layer blocks split pair membership through a middle vector. -/
theorem zxnCatLayersPairIffAt (currentArity midArity finalArity : Nat)
    (firstLayers secondLayers : List (List ZxpCell))
    (hFirstWF : ZxpLayersWF currentArity firstLayers)
    (hFirstCod : zxpLayersCodArity currentArity firstLayers = midArity)
    (hSecondWF : ZxpLayersWF midArity secondLayers)
    (hSecondCod : zxpLayersCodArity midArity secondLayers = finalArity)
    (domVec codVec : List Bool) :
    ZxpPairMem currentArity finalArity
        (zxpLayersDenote currentArity (zxpCatLayers firstLayers secondLayers))
        domVec codVec
      <-> Exists fun midVec =>
          ZxpPairMem currentArity midArity
              (zxpLayersDenote currentArity firstLayers) domVec midVec
            /\ ZxpPairMem midArity finalArity
                (zxpLayersDenote midArity secondLayers) midVec codVec := by
  subst hFirstCod
  subst hSecondCod
  refine Iff.trans
    (zxpLayersDenoteCat firstLayers secondLayers hFirstWF hSecondWF domVec codVec) ?_
  exact zxpComposeSpec currentArity (zxpLayersCodArity currentArity firstLayers)
    (zxpLayersCodArity (zxpLayersCodArity currentArity firstLayers) secondLayers)
    (zxpLayersDenote currentArity firstLayers)
    (zxpLayersDenote (zxpLayersCodArity currentArity firstLayers) secondLayers)
    (zxpLayersDenoteWidth firstLayers hFirstWF)
    (zxpLayersDenoteWidth secondLayers hSecondWF) domVec codVec

/-- THE PADDED-CELL WORKHORSE: a single cell whiskered by wires relates exactly the
vectors that agree outside the cell block and relate through the cell inside it. -/
theorem zxnPadCellPairIff (leftWires rightWires : Nat) (cell : ZxpCell)
    (domVec codVec : List Bool) :
    ZxpPairMem (leftWires + (zxpCellDomArity cell + rightWires))
        (leftWires + (zxpCellCodArity cell + rightWires))
        (zxpLayerDenote (zxpWhiskerLayer leftWires rightWires [cell])) domVec codVec
      <-> Exists fun passVec => Exists fun cellDomVec => Exists fun sideVec =>
          Exists fun cellCodVec =>
          domVec = zxpCat passVec (zxpCat cellDomVec sideVec)
            /\ codVec = zxpCat passVec (zxpCat cellCodVec sideVec)
            /\ passVec.length = leftWires
            /\ sideVec.length = rightWires
            /\ ZxpPairMem (zxpCellDomArity cell) (zxpCellCodArity cell)
                (zxpCellRows cell) cellDomVec cellCodVec := by
  have hCellDenAll : ZxpAllWidth (zxpCellDomArity cell + zxpCellCodArity cell)
      (zxpLayerDenote [cell]) := zxpLayerDenoteWidth [cell]
  have hInnerAll : ZxpAllWidth
      ((zxpCellDomArity cell + rightWires) + (zxpCellCodArity cell + rightWires))
      (zxpTensorRows (zxpCellDomArity cell) (zxpCellCodArity cell) rightWires rightWires
        (zxpLayerDenote [cell]) (zxpIdRows rightWires)) :=
    zxpTensorRowsWidth (zxpCellDomArity cell) (zxpCellCodArity cell) rightWires rightWires
      (zxpLayerDenote [cell]) (zxpIdRows rightWires) hCellDenAll (zxpIdRowsWidth rightWires)
  refine Iff.trans (zxpWhiskerLayerDenote leftWires rightWires [cell] domVec codVec) ?_
  refine Iff.trans (zxpTensorSpec leftWires leftWires
    (zxpCellDomArity cell + rightWires) (zxpCellCodArity cell + rightWires)
    (zxpIdRows leftWires)
    (zxpTensorRows (zxpCellDomArity cell) (zxpCellCodArity cell) rightWires rightWires
      (zxpLayerDenote [cell]) (zxpIdRows rightWires))
    (zxpIdRowsWidth leftWires) hInnerAll domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hPacked
    obtain ⟨passDomVec, restDomVec, passCodVec, restCodVec,
      hDomCat, hCodCat, hPassPair, hRestPair⟩ := hPacked
    have hPassSame := (zxpIdSpec leftWires passDomVec passCodVec).mp hPassPair
    have hRest := (zxpTensorSpec (zxpCellDomArity cell) (zxpCellCodArity cell)
      rightWires rightWires (zxpLayerDenote [cell]) (zxpIdRows rightWires)
      hCellDenAll (zxpIdRowsWidth rightWires) restDomVec restCodVec).mp hRestPair
    obtain ⟨cellDomVec, sideDomVec, cellCodVec, sideCodVec,
      hRestDomCat, hRestCodCat, hCellPair, hSidePair⟩ := hRest
    have hSideSame := (zxpIdSpec rightWires sideDomVec sideCodVec).mp hSidePair
    have hCellPair2 : ZxpPairMem (zxpCellDomArity cell) (zxpCellCodArity cell)
        (zxpCellRows cell) cellDomVec cellCodVec :=
      (zxpTensorUnitRight (zxpCellDomArity cell) (zxpCellCodArity cell)
        (zxpCellRows cell) (zxpCellRowsWidth cell) cellDomVec cellCodVec).mp hCellPair
    refine Exists.intro passDomVec (Exists.intro cellDomVec (Exists.intro sideDomVec
      (Exists.intro cellCodVec (And.intro ?_ (And.intro ?_ (And.intro hPassSame.right
        (And.intro ?_ hCellPair2)))))))
    · rw [hDomCat, hRestDomCat]
    · rw [hCodCat, hRestCodCat, <- hPassSame.left, <- hSideSame.left]
    · exact hSideSame.right
  · intro hPacked
    obtain ⟨passVec, cellDomVec, sideVec, cellCodVec,
      hDomEq, hCodEq, hPassLen, hSideLen, hCellPair⟩ := hPacked
    refine Exists.intro passVec (Exists.intro (zxpCat cellDomVec sideVec)
      (Exists.intro passVec (Exists.intro (zxpCat cellCodVec sideVec)
        (And.intro hDomEq (And.intro hCodEq (And.intro ?_ ?_))))))
    · exact (zxpIdSpec leftWires passVec passVec).mpr (And.intro rfl hPassLen)
    · refine (zxpTensorSpec (zxpCellDomArity cell) (zxpCellCodArity cell)
        rightWires rightWires (zxpLayerDenote [cell]) (zxpIdRows rightWires)
        hCellDenAll (zxpIdRowsWidth rightWires)
        (zxpCat cellDomVec sideVec) (zxpCat cellCodVec sideVec)).mpr ?_
      refine Exists.intro cellDomVec (Exists.intro sideVec (Exists.intro cellCodVec
        (Exists.intro sideVec (And.intro rfl (And.intro rfl (And.intro ?_ ?_))))))
      · exact (zxpTensorUnitRight (zxpCellDomArity cell) (zxpCellCodArity cell)
          (zxpCellRows cell) (zxpCellRowsWidth cell) cellDomVec cellCodVec).mpr hCellPair
      · exact (zxpIdSpec rightWires sideVec sideVec).mpr (And.intro rfl hSideLen)

/-- The padded-cell workhorse with boundary arities supplied by equations. -/
theorem zxnPadCellPairIffAt (leftWires rightWires : Nat) (cell : ZxpCell)
    (currentArity nextArity : Nat)
    (hDomEq : leftWires + (zxpCellDomArity cell + rightWires) = currentArity)
    (hCodEq : leftWires + (zxpCellCodArity cell + rightWires) = nextArity)
    (domVec codVec : List Bool) :
    ZxpPairMem currentArity nextArity
        (zxpLayerDenote (zxpWhiskerLayer leftWires rightWires [cell])) domVec codVec
      <-> Exists fun passVec => Exists fun cellDomVec => Exists fun sideVec =>
          Exists fun cellCodVec =>
          domVec = zxpCat passVec (zxpCat cellDomVec sideVec)
            /\ codVec = zxpCat passVec (zxpCat cellCodVec sideVec)
            /\ passVec.length = leftWires
            /\ sideVec.length = rightWires
            /\ ZxpPairMem (zxpCellDomArity cell) (zxpCellCodArity cell)
                (zxpCellRows cell) cellDomVec cellCodVec := by
  subst hDomEq
  subst hCodEq
  exact zxnPadCellPairIff leftWires rightWires cell domVec codVec

/-! ## Stage 3 — the init and kill layers (boundary X-chains: zero states and collectors) -/

/-- A block of `xSpider 0 1` zero states (the codomain-side X-chain bases). -/
def zxnZeroStateCells : Nat -> List ZxpCell
  | 0 => []
  | freshCount + 1 => ZxpCell.xSpider 0 1 :: zxnZeroStateCells freshCount

/-- A block of `xSpider 1 0` zero effects (the domain-side X-chain collectors). -/
def zxnKillCells : Nat -> List ZxpCell
  | 0 => []
  | killCount + 1 => ZxpCell.xSpider 1 0 :: zxnKillCells killCount

theorem zxnZeroStateCellsDomArity : (freshCount : Nat) ->
    zxpLayerDomArity (zxnZeroStateCells freshCount) = 0
  | 0 => rfl
  | freshCount + 1 => by
      show 0 + zxpLayerDomArity (zxnZeroStateCells freshCount) = 0
      rw [zxnZeroStateCellsDomArity freshCount]

theorem zxnZeroStateCellsCodArity : (freshCount : Nat) ->
    zxpLayerCodArity (zxnZeroStateCells freshCount) = freshCount
  | 0 => rfl
  | freshCount + 1 => by
      show 1 + zxpLayerCodArity (zxnZeroStateCells freshCount) = freshCount + 1
      rw [zxnZeroStateCellsCodArity freshCount, Nat.add_comm 1 freshCount]

theorem zxnKillCellsDomArity : (killCount : Nat) ->
    zxpLayerDomArity (zxnKillCells killCount) = killCount
  | 0 => rfl
  | killCount + 1 => by
      show 1 + zxpLayerDomArity (zxnKillCells killCount) = killCount + 1
      rw [zxnKillCellsDomArity killCount, Nat.add_comm 1 killCount]

theorem zxnKillCellsCodArity : (killCount : Nat) ->
    zxpLayerCodArity (zxnKillCells killCount) = 0
  | 0 => rfl
  | killCount + 1 => by
      show 0 + zxpLayerCodArity (zxnKillCells killCount) = 0
      rw [zxnKillCellsCodArity killCount]

/-- The zero-state block relates `()` to exactly the zero row. -/
theorem zxnZeroStateCellsPairIff : (freshCount : Nat) -> (domVec codVec : List Bool) ->
    (ZxpPairMem 0 freshCount (zxpLayerDenote (zxnZeroStateCells freshCount)) domVec codVec
      <-> (domVec = [] /\ codVec = zxpZeroRow freshCount))
  | 0, domVec, codVec => by
      refine Iff.intro ?_ ?_
      · intro hPair
        exact And.intro (zxpLengthZeroNil domVec hPair.left)
          (zxpLengthZeroNil codVec hPair.right.left)
      · intro hBoth
        refine And.intro (by rw [hBoth.left]; rfl)
          (And.intro (by rw [hBoth.right]; rfl) ?_)
        rw [hBoth.left, hBoth.right]
        exact ZxpMemSpan.zero
  | freshCount + 1, domVec, codVec => by
      show ZxpPairMem 0 (freshCount + 1)
          (zxpTensorRows 0 1 (zxpLayerDomArity (zxnZeroStateCells freshCount))
            (zxpLayerCodArity (zxnZeroStateCells freshCount))
            (zxpParityRows 1) (zxpLayerDenote (zxnZeroStateCells freshCount)))
          domVec codVec
        <-> (domVec = [] /\ codVec = zxpZeroRow (freshCount + 1))
      rw [zxnZeroStateCellsDomArity freshCount, zxnZeroStateCellsCodArity freshCount]
      have hRestAll : ZxpAllWidth (0 + freshCount)
          (zxpLayerDenote (zxnZeroStateCells freshCount)) :=
        zxpAllWidthCast (by rw [zxnZeroStateCellsDomArity freshCount,
          zxnZeroStateCellsCodArity freshCount])
          (zxpLayerDenoteWidth (zxnZeroStateCells freshCount))
      refine Iff.trans (zxpPairMemCast (show (0 : Nat) = 0 + 0 from rfl)
        (Nat.add_comm freshCount 1)) ?_
      refine Iff.trans (zxpTensorSpec 0 1 0 freshCount (zxpParityRows 1)
        (zxpLayerDenote (zxnZeroStateCells freshCount))
        (zxpParityRowsWidth 1) hRestAll domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hPacked
        obtain ⟨firstDomVec, secondDomVec, firstCodVec, secondCodVec,
          hDomCat, hCodCat, hHeadPair, hRestPair⟩ := hPacked
        have hHead := (zxnXZeroStatePairIff firstDomVec firstCodVec).mp hHeadPair
        have hRest :=
          (zxnZeroStateCellsPairIff freshCount secondDomVec secondCodVec).mp hRestPair
        refine And.intro ?_ ?_
        · rw [hDomCat, hHead.left, hRest.left]
          rfl
        · rw [hCodCat, hHead.right, hRest.right]
          rfl
      · intro hBoth
        refine Exists.intro [] (Exists.intro [] (Exists.intro [false]
          (Exists.intro (zxpZeroRow freshCount)
            (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))))))
        · rw [hBoth.left]
          rfl
        · rw [hBoth.right]
          rfl
        · exact (zxnXZeroStatePairIff [] [false]).mpr (And.intro rfl rfl)
        · exact (zxnZeroStateCellsPairIff freshCount [] (zxpZeroRow freshCount)).mpr
            (And.intro rfl rfl)

/-- The kill block relates exactly the zero row to `()`. -/
theorem zxnKillCellsPairIff : (killCount : Nat) -> (domVec codVec : List Bool) ->
    (ZxpPairMem killCount 0 (zxpLayerDenote (zxnKillCells killCount)) domVec codVec
      <-> (domVec = zxpZeroRow killCount /\ codVec = []))
  | 0, domVec, codVec => by
      refine Iff.intro ?_ ?_
      · intro hPair
        exact And.intro (zxpLengthZeroNil domVec hPair.left)
          (zxpLengthZeroNil codVec hPair.right.left)
      · intro hBoth
        refine And.intro (by rw [hBoth.left]; rfl)
          (And.intro (by rw [hBoth.right]; rfl) ?_)
        rw [hBoth.left, hBoth.right]
        exact ZxpMemSpan.zero
  | killCount + 1, domVec, codVec => by
      show ZxpPairMem (killCount + 1) 0
          (zxpTensorRows 1 0 (zxpLayerDomArity (zxnKillCells killCount))
            (zxpLayerCodArity (zxnKillCells killCount))
            (zxpParityRows 1) (zxpLayerDenote (zxnKillCells killCount)))
          domVec codVec
        <-> (domVec = zxpZeroRow (killCount + 1) /\ codVec = [])
      rw [zxnKillCellsDomArity killCount, zxnKillCellsCodArity killCount]
      have hRestAll : ZxpAllWidth (killCount + 0)
          (zxpLayerDenote (zxnKillCells killCount)) :=
        zxpAllWidthCast (by rw [zxnKillCellsDomArity killCount,
          zxnKillCellsCodArity killCount])
          (zxpLayerDenoteWidth (zxnKillCells killCount))
      refine Iff.trans (zxpPairMemCast (Nat.add_comm killCount 1)
        (show (0 : Nat) = 0 + 0 from rfl)) ?_
      refine Iff.trans (zxpTensorSpec 1 0 killCount 0 (zxpParityRows 1)
        (zxpLayerDenote (zxnKillCells killCount))
        (zxpParityRowsWidth 1) hRestAll domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hPacked
        obtain ⟨firstDomVec, secondDomVec, firstCodVec, secondCodVec,
          hDomCat, hCodCat, hHeadPair, hRestPair⟩ := hPacked
        have hHead := (zxnXZeroEffectPairIff firstDomVec firstCodVec).mp hHeadPair
        have hRest := (zxnKillCellsPairIff killCount secondDomVec secondCodVec).mp hRestPair
        refine And.intro ?_ ?_
        · rw [hDomCat, hHead.left, hRest.left]
          rfl
        · rw [hCodCat, hHead.right, hRest.right]
          rfl
      · intro hBoth
        refine Exists.intro [false] (Exists.intro (zxpZeroRow killCount) (Exists.intro []
          (Exists.intro [] (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))))))
        · rw [hBoth.left]
          rfl
        · rw [hBoth.right]
          rfl
        · exact (zxnXZeroEffectPairIff [false] []).mpr (And.intro rfl rfl)
        · exact (zxnKillCellsPairIff killCount (zxpZeroRow killCount) []).mpr
            (And.intro rfl rfl)

/-- The init layer: the domain wires pass, the codomain strands are born as zero states. -/
def zxnInitLayer (domWidth codWidth : Nat) : List ZxpCell :=
  zxpCatCells (zxpWireCells domWidth) (zxnZeroStateCells codWidth)

/-- The kill layer: the domain strands are collected to zero, the codomain wires pass. -/
def zxnKillLayer (domWidth codWidth : Nat) : List ZxpCell :=
  zxpCatCells (zxnKillCells domWidth) (zxpWireCells codWidth)

theorem zxnInitLayerDomArity (domWidth codWidth : Nat) :
    zxpLayerDomArity (zxnInitLayer domWidth codWidth) = domWidth := by
  show zxpLayerDomArity
      (zxpCatCells (zxpWireCells domWidth) (zxnZeroStateCells codWidth)) = domWidth
  rw [zxpCatCellsDomArity, zxpWireCellsDomArity, zxnZeroStateCellsDomArity]
  rfl

theorem zxnInitLayerCodArity (domWidth codWidth : Nat) :
    zxpLayerCodArity (zxnInitLayer domWidth codWidth) = domWidth + codWidth := by
  show zxpLayerCodArity
      (zxpCatCells (zxpWireCells domWidth) (zxnZeroStateCells codWidth))
    = domWidth + codWidth
  rw [zxpCatCellsCodArity, zxpWireCellsCodArity, zxnZeroStateCellsCodArity]

theorem zxnKillLayerDomArity (domWidth codWidth : Nat) :
    zxpLayerDomArity (zxnKillLayer domWidth codWidth) = domWidth + codWidth := by
  show zxpLayerDomArity
      (zxpCatCells (zxnKillCells domWidth) (zxpWireCells codWidth))
    = domWidth + codWidth
  rw [zxpCatCellsDomArity, zxpWireCellsDomArity, zxnKillCellsDomArity]

theorem zxnKillLayerCodArity (domWidth codWidth : Nat) :
    zxpLayerCodArity (zxnKillLayer domWidth codWidth) = codWidth := by
  show zxpLayerCodArity
      (zxpCatCells (zxnKillCells domWidth) (zxpWireCells codWidth)) = codWidth
  rw [zxpCatCellsCodArity, zxpWireCellsCodArity, zxnKillCellsCodArity]
  rw [Nat.zero_add]

/-- The init layer relates `u` to `cat u 0^cod`. -/
theorem zxnInitLayerPairIff (domWidth codWidth : Nat) (domVec codVec : List Bool) :
    ZxpPairMem domWidth (domWidth + codWidth)
        (zxpLayerDenote (zxnInitLayer domWidth codWidth)) domVec codVec
      <-> (domVec.length = domWidth /\ codVec = zxpCat domVec (zxpZeroRow codWidth)) := by
  have hSplit := zxpLayerDenoteCatSplit (zxpWireCells domWidth) (zxnZeroStateCells codWidth)
  rw [zxpWireCellsDomArity, zxpWireCellsCodArity, zxnZeroStateCellsDomArity,
    zxnZeroStateCellsCodArity] at hSplit
  have hWireAll : ZxpAllWidth (domWidth + domWidth)
      (zxpLayerDenote (zxpWireCells domWidth)) :=
    zxpAllWidthCast (by rw [zxpWireCellsDomArity, zxpWireCellsCodArity])
      (zxpLayerDenoteWidth (zxpWireCells domWidth))
  have hZeroAll : ZxpAllWidth (0 + codWidth)
      (zxpLayerDenote (zxnZeroStateCells codWidth)) :=
    zxpAllWidthCast (by rw [zxnZeroStateCellsDomArity, zxnZeroStateCellsCodArity])
      (zxpLayerDenoteWidth (zxnZeroStateCells codWidth))
  refine Iff.trans (hSplit domVec codVec) ?_
  refine Iff.trans (zxpTensorSpec domWidth domWidth 0 codWidth
    (zxpLayerDenote (zxpWireCells domWidth))
    (zxpLayerDenote (zxnZeroStateCells codWidth)) hWireAll hZeroAll domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hPacked
    obtain ⟨passDomVec, freshDomVec, passCodVec, freshCodVec,
      hDomCat, hCodCat, hPassPair, hFreshPair⟩ := hPacked
    have hPassSame := (zxpIdSpec domWidth passDomVec passCodVec).mp
      ((zxpWireCellsDenoteId domWidth passDomVec passCodVec).mp hPassPair)
    have hFresh := (zxnZeroStateCellsPairIff codWidth freshDomVec freshCodVec).mp hFreshPair
    have hDomIsPass : domVec = passDomVec := by
      rw [hDomCat, hFresh.left, zxpCatNilRight]
    refine And.intro ?_ ?_
    · rw [hDomIsPass]
      exact hPassSame.right
    · rw [hCodCat, hFresh.right, <- hPassSame.left, hDomIsPass]
  · intro hBoth
    refine Exists.intro domVec (Exists.intro [] (Exists.intro domVec
      (Exists.intro (zxpZeroRow codWidth)
        (And.intro (zxpCatNilRight domVec).symm (And.intro hBoth.right
          (And.intro ?_ ?_))))))
    · exact (zxpWireCellsDenoteId domWidth domVec domVec).mpr
        ((zxpIdSpec domWidth domVec domVec).mpr (And.intro rfl hBoth.left))
    · exact (zxnZeroStateCellsPairIff codWidth [] (zxpZeroRow codWidth)).mpr
        (And.intro rfl rfl)

/-- The kill layer relates `cat 0^dom w` to `w`. -/
theorem zxnKillLayerPairIff (domWidth codWidth : Nat) (domVec codVec : List Bool) :
    ZxpPairMem (domWidth + codWidth) codWidth
        (zxpLayerDenote (zxnKillLayer domWidth codWidth)) domVec codVec
      <-> (codVec.length = codWidth /\ domVec = zxpCat (zxpZeroRow domWidth) codVec) := by
  have hSplit := zxpLayerDenoteCatSplit (zxnKillCells domWidth) (zxpWireCells codWidth)
  rw [zxpWireCellsDomArity, zxpWireCellsCodArity, zxnKillCellsDomArity,
    zxnKillCellsCodArity] at hSplit
  have hWireAll : ZxpAllWidth (codWidth + codWidth)
      (zxpLayerDenote (zxpWireCells codWidth)) :=
    zxpAllWidthCast (by rw [zxpWireCellsDomArity, zxpWireCellsCodArity])
      (zxpLayerDenoteWidth (zxpWireCells codWidth))
  have hKillAll : ZxpAllWidth (domWidth + 0)
      (zxpLayerDenote (zxnKillCells domWidth)) :=
    zxpAllWidthCast (by rw [zxnKillCellsDomArity, zxnKillCellsCodArity])
      (zxpLayerDenoteWidth (zxnKillCells domWidth))
  refine Iff.trans (zxpPairMemCast rfl (Nat.zero_add codWidth).symm) ?_
  refine Iff.trans (hSplit domVec codVec) ?_
  refine Iff.trans (zxpTensorSpec domWidth 0 codWidth codWidth
    (zxpLayerDenote (zxnKillCells domWidth))
    (zxpLayerDenote (zxpWireCells codWidth)) hKillAll hWireAll domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hPacked
    obtain ⟨killDomVec, passDomVec, killCodVec, passCodVec,
      hDomCat, hCodCat, hKillPair, hPassPair⟩ := hPacked
    have hKill := (zxnKillCellsPairIff domWidth killDomVec killCodVec).mp hKillPair
    have hPassSame := (zxpIdSpec codWidth passDomVec passCodVec).mp
      ((zxpWireCellsDenoteId codWidth passDomVec passCodVec).mp hPassPair)
    have hCodIsPass : codVec = passDomVec := by
      rw [hCodCat, hKill.right, hPassSame.left]
      rfl
    refine And.intro ?_ ?_
    · rw [hCodIsPass]
      exact hPassSame.right
    · rw [hDomCat, hKill.left, hCodIsPass]
  · intro hBoth
    refine Exists.intro (zxpZeroRow domWidth) (Exists.intro codVec (Exists.intro []
      (Exists.intro codVec
        (And.intro hBoth.right (And.intro (rfl : codVec = zxpCat [] codVec)
          (And.intro ?_ ?_))))))
    · exact (zxnKillCellsPairIff domWidth (zxpZeroRow domWidth) []).mpr
        (And.intro rfl rfl)
    · exact (zxpWireCellsDenoteId codWidth codVec codVec).mpr
        ((zxpIdSpec codWidth codVec codVec).mpr (And.intro rfl hBoth.left))

/-! ## Stage 4 — THE GENERATOR COMB: the fissioned per-generator conditional-xor block

The carrier bit (the generator's free coefficient) is created at the far left and walks
right by adjacent crossings; at every `true` bit of the generator row it forks
(`zSpider 1 2`) and xors into the strand (`xSpider 2 1`); at the end it is discarded
(`zSpider 1 0`).  Layer invariant: `processed-strands ++ [carrier] ++ unprocessed`. -/

/-- The comb layers over the remaining row bits, with `prefixWires` processed strands. -/
def zxnCombLayers : Nat -> List Bool -> List (List ZxpCell)
  | prefixWires, [] => [zxpWhiskerLayer prefixWires 0 [ZxpCell.zSpider 1 0]]
  | prefixWires, false :: restBits =>
      zxpWhiskerLayer prefixWires restBits.length [ZxpCell.crossing]
        :: zxnCombLayers (prefixWires + 1) restBits
  | prefixWires, true :: restBits =>
      zxpWhiskerLayer prefixWires (restBits.length + 1) [ZxpCell.zSpider 1 2]
        :: zxpWhiskerLayer (prefixWires + 1) restBits.length [ZxpCell.xSpider 2 1]
        :: zxpWhiskerLayer prefixWires restBits.length [ZxpCell.crossing]
        :: zxnCombLayers (prefixWires + 1) restBits

/-- The comb's output arity: the carrier is gone, every wire survives. -/
theorem zxnCombLayersCodArity : (rowBits : List Bool) -> (prefixWires anyArity : Nat) ->
    zxpLayersCodArity anyArity (zxnCombLayers prefixWires rowBits)
      = prefixWires + rowBits.length
  | [], prefixWires, _anyArity => by
      show zxpLayerCodArity (zxpWhiskerLayer prefixWires 0 [ZxpCell.zSpider 1 0])
        = prefixWires + 0
      rw [zxpWhiskerLayerCodArity]
      rfl
  | false :: restBits, prefixWires, _anyArity => by
      show zxpLayersCodArity
          (zxpLayerCodArity (zxpWhiskerLayer prefixWires restBits.length [ZxpCell.crossing]))
          (zxnCombLayers (prefixWires + 1) restBits)
        = prefixWires + (restBits.length + 1)
      rw [zxnCombLayersCodArity restBits (prefixWires + 1) _,
        zxnCombCodShuffle prefixWires restBits.length]
  | true :: restBits, prefixWires, _anyArity => by
      show zxpLayersCodArity
          (zxpLayerCodArity (zxpWhiskerLayer prefixWires restBits.length [ZxpCell.crossing]))
          (zxnCombLayers (prefixWires + 1) restBits)
        = prefixWires + (restBits.length + 1)
      rw [zxnCombLayersCodArity restBits (prefixWires + 1) _,
        zxnCombCodShuffle prefixWires restBits.length]

/-- Well-formedness of the comb at its entry arity. -/
theorem zxnCombLayersWF : (rowBits : List Bool) -> (prefixWires : Nat) ->
    ZxpLayersWF (prefixWires + (1 + rowBits.length)) (zxnCombLayers prefixWires rowBits)
  | [], prefixWires => by
      refine ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _)
      rw [zxpWhiskerLayerDomArity]
      rfl
  | false :: restBits, prefixWires => by
      refine ZxpLayersWF.cons ?_ ?_
      · rw [zxpWhiskerLayerDomArity]
        exact congrArg (fun innerValue => prefixWires + innerValue)
          (zxnTwoPlusEqOnePlusSucc restBits.length)
      · rw [zxpWhiskerLayerCodArity]
        have hInner := zxnCombLayersWF restBits (prefixWires + 1)
        rw [<- zxnStepArityShuffle prefixWires restBits.length] at hInner
        exact hInner
  | true :: restBits, prefixWires => by
      refine ZxpLayersWF.cons ?_ (ZxpLayersWF.cons ?_ (ZxpLayersWF.cons ?_ ?_))
      · rw [zxpWhiskerLayerDomArity]
        rfl
      · rw [zxpWhiskerLayerDomArity, zxpWhiskerLayerCodArity]
        exact (zxnForkArityShuffle prefixWires restBits.length).symm
      · rw [zxpWhiskerLayerDomArity, zxpWhiskerLayerCodArity]
        exact zxnStepArityShuffle prefixWires restBits.length
      · rw [zxpWhiskerLayerCodArity]
        have hInner := zxnCombLayersWF restBits (prefixWires + 1)
        rw [<- zxnStepArityShuffle prefixWires restBits.length] at hInner
        exact hInner

/-- THE COMB CHARACTERIZATION: the block relates `(pass | carrier | live)` to
`(pass | xor live (carrier * row))` — the conditional-xor of the generator row. -/
theorem zxnCombPairIff : (rowBits : List Bool) -> (prefixWires : Nat) ->
    (domVec codVec : List Bool) ->
    (ZxpPairMem (prefixWires + (1 + rowBits.length)) (prefixWires + rowBits.length)
        (zxpLayersDenote (prefixWires + (1 + rowBits.length))
          (zxnCombLayers prefixWires rowBits)) domVec codVec
      <-> Exists fun passVec => Exists fun carrierBit => Exists fun liveVec =>
          domVec = zxpCat passVec (carrierBit :: liveVec)
            /\ passVec.length = prefixWires
            /\ liveVec.length = rowBits.length
            /\ codVec = zxpCat passVec (zxpRowXor liveVec (zxnScaleRow carrierBit rowBits)))
  | [], prefixWires, domVec, codVec => by
      refine Iff.trans (zxnSingleLayerPairIffAt (prefixWires + (1 + 0)) (prefixWires + 0)
        (zxpWhiskerLayer prefixWires 0 [ZxpCell.zSpider 1 0])
        (zxpWhiskerLayerDomArity prefixWires 0 [ZxpCell.zSpider 1 0])
        (zxpWhiskerLayerCodArity prefixWires 0 [ZxpCell.zSpider 1 0])
        domVec codVec) ?_
      refine Iff.trans (zxnPadCellPairIff prefixWires 0 (ZxpCell.zSpider 1 0)
        domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hPacked
        obtain ⟨passVec, cellDomVec, sideVec, cellCodVec,
          hDomEq, hCodEq, hPassLen, hSideLen, hCellPair⟩ := hPacked
        have hCell := (zxnZSinkPairIff cellDomVec cellCodVec).mp hCellPair
        obtain ⟨carrierBit, hCellDomShape⟩ := hCell.left
        have hSideNil := zxpLengthZeroNil sideVec hSideLen
        refine Exists.intro passVec (Exists.intro carrierBit (Exists.intro []
          (And.intro ?_ (And.intro hPassLen (And.intro rfl ?_)))))
        · rw [hDomEq, hCellDomShape, hSideNil]
          rfl
        · rw [hCodEq, hCell.right, hSideNil]
          rfl
      · intro hPacked
        obtain ⟨passVec, carrierBit, liveVec, hDomEq, hPassLen, hLiveLen, hCodEq⟩ := hPacked
        have hLiveNil : liveVec = [] := zxpLengthZeroNil liveVec hLiveLen
        refine Exists.intro passVec (Exists.intro [carrierBit] (Exists.intro []
          (Exists.intro [] (And.intro ?_ (And.intro ?_ (And.intro hPassLen
            (And.intro rfl ?_)))))))
        · rw [hDomEq, hLiveNil]
          rfl
        · rw [hCodEq, hLiveNil]
          rfl
        · exact (zxnZSinkPairIff [carrierBit] []).mpr
            (And.intro (Exists.intro carrierBit rfl) rfl)
  | false :: restBits, prefixWires, domVec, codVec => by
      have hCrossDomEq : prefixWires
            + (zxpCellDomArity ZxpCell.crossing + restBits.length)
          = prefixWires + (1 + (restBits.length + 1)) :=
        congrArg (fun innerValue => prefixWires + innerValue)
          (zxnTwoPlusEqOnePlusSucc restBits.length)
      have hCrossCodEq : prefixWires
            + (zxpCellCodArity ZxpCell.crossing + restBits.length)
          = (prefixWires + 1) + (1 + restBits.length) :=
        zxnStepArityShuffle prefixWires restBits.length
      refine Iff.trans (zxnConsLayerPairIffAt
        (prefixWires + (1 + (restBits.length + 1)))
        ((prefixWires + 1) + (1 + restBits.length))
        (prefixWires + (restBits.length + 1))
        (zxpWhiskerLayer prefixWires restBits.length [ZxpCell.crossing])
        (zxnCombLayers (prefixWires + 1) restBits)
        ((zxpWhiskerLayerDomArity prefixWires restBits.length [ZxpCell.crossing]).trans
          hCrossDomEq)
        ((zxpWhiskerLayerCodArity prefixWires restBits.length [ZxpCell.crossing]).trans
          hCrossCodEq)
        (zxnCombLayersWF restBits (prefixWires + 1))
        ((zxnCombLayersCodArity restBits (prefixWires + 1) _).trans
          (zxnCombCodShuffle prefixWires restBits.length))
        domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hPacked
        obtain ⟨midVec, hHeadPair, hRestPair⟩ := hPacked
        have hHead := (zxnPadCellPairIffAt prefixWires restBits.length ZxpCell.crossing
          (prefixWires + (1 + (restBits.length + 1)))
          ((prefixWires + 1) + (1 + restBits.length))
          hCrossDomEq hCrossCodEq domVec midVec).mp hHeadPair
        obtain ⟨passVec, cellDomVec, sideVec, cellCodVec,
          hDomEq, hMidEq, hPassLen, hSideLen, hCellPair⟩ := hHead
        obtain ⟨carrierBit, skipBit, hCellDomShape, hCellCodShape⟩ :=
          (zxnCrossingPairIff cellDomVec cellCodVec).mp hCellPair
        have hRest := (zxnCombPairIff restBits (prefixWires + 1) midVec codVec).mp
          ((zxpPairMemCast rfl
            (zxnCombCodShuffle prefixWires restBits.length).symm).mp hRestPair)
        obtain ⟨passVec2, carrierBit2, liveVec2,
          hMidEq2, hPassLen2, hLiveLen2, hCodEq2⟩ := hRest
        have hMidBridge : zxpCat (zxpCat passVec [skipBit]) (carrierBit :: sideVec)
            = zxpCat passVec2 (carrierBit2 :: liveVec2) := by
          rw [zxpCatAssoc, <- hMidEq2, hMidEq, hCellCodShape]
          rfl
        have hLenBridge : (zxpCat passVec [skipBit]).length = passVec2.length := by
          rw [zxpCatLength, hPassLen, hPassLen2]
          rfl
        have hParts := zxpCatInj (zxpCat passVec [skipBit]) (carrierBit :: sideVec)
          passVec2 (carrierBit2 :: liveVec2) hLenBridge hMidBridge
        have hCarrierEq : carrierBit = carrierBit2 := by
          injection hParts.right with hHeadEq _hTailEq
        have hSideEq : sideVec = liveVec2 := by
          injection hParts.right with _hHeadEq hTailEq
        refine Exists.intro passVec (Exists.intro carrierBit
          (Exists.intro (skipBit :: sideVec)
            (And.intro ?_ (And.intro hPassLen (And.intro ?_ ?_)))))
        · rw [hDomEq, hCellDomShape]
          rfl
        · show sideVec.length + 1 = restBits.length + 1
          rw [hSideLen]
        · rw [hCodEq2, <- hParts.left, <- hCarrierEq, <- hSideEq, zxnScaleRowConsFalse]
          show zxpCat (zxpCat passVec [skipBit])
              (zxpRowXor sideVec (zxnScaleRow carrierBit restBits))
            = zxpCat passVec
                (zxpXorB skipBit false
                  :: zxpRowXor sideVec (zxnScaleRow carrierBit restBits))
          rw [zxpXorBFalseRight skipBit, zxpCatAssoc]
          rfl
      · intro hPacked
        obtain ⟨passVec, carrierBit, liveVec, hDomEq, hPassLen, hLiveLen, hCodEq⟩ := hPacked
        obtain ⟨skipBit, liveTail, hLiveShape, hLiveTailLen⟩ :=
          zxnLengthSuccShape liveVec restBits.length hLiveLen
        refine Exists.intro (zxpCat passVec (zxpCat [skipBit] (carrierBit :: liveTail)))
          (And.intro ?_ ?_)
        · refine (zxnPadCellPairIffAt prefixWires restBits.length ZxpCell.crossing
            (prefixWires + (1 + (restBits.length + 1)))
            ((prefixWires + 1) + (1 + restBits.length))
            hCrossDomEq hCrossCodEq domVec _).mpr ?_
          refine Exists.intro passVec (Exists.intro [carrierBit, skipBit]
            (Exists.intro liveTail (Exists.intro [skipBit, carrierBit]
              (And.intro ?_ (And.intro ?_ (And.intro hPassLen
                (And.intro hLiveTailLen ?_)))))))
          · rw [hDomEq, hLiveShape]
            rfl
          · rfl
          · exact (zxnCrossingPairIff [carrierBit, skipBit] [skipBit, carrierBit]).mpr
              (Exists.intro carrierBit (Exists.intro skipBit (And.intro rfl rfl)))
        · refine (zxpPairMemCast rfl
            (zxnCombCodShuffle prefixWires restBits.length).symm).mpr ?_
          refine (zxnCombPairIff restBits (prefixWires + 1) _ codVec).mpr ?_
          refine Exists.intro (zxpCat passVec [skipBit]) (Exists.intro carrierBit
            (Exists.intro liveTail (And.intro ?_ (And.intro ?_
              (And.intro hLiveTailLen ?_)))))
          · rw [zxpCatAssoc]
          · rw [zxpCatLength, hPassLen]
            rfl
          · rw [hCodEq, hLiveShape, zxnScaleRowConsFalse]
            show zxpCat passVec
                (zxpXorB skipBit false
                  :: zxpRowXor liveTail (zxnScaleRow carrierBit restBits))
              = zxpCat (zxpCat passVec [skipBit])
                  (zxpRowXor liveTail (zxnScaleRow carrierBit restBits))
            rw [zxpXorBFalseRight skipBit, zxpCatAssoc]
            rfl
  | true :: restBits, prefixWires, domVec, codVec => by
      have hForkDomEq : prefixWires
            + (zxpCellDomArity (ZxpCell.zSpider 1 2) + (restBits.length + 1))
          = prefixWires + (1 + (restBits.length + 1)) := rfl
      have hForkCodEq : prefixWires
            + (zxpCellCodArity (ZxpCell.zSpider 1 2) + (restBits.length + 1))
          = (prefixWires + 1) + (2 + restBits.length) :=
        zxnForkArityShuffle prefixWires restBits.length
      have hMergeDomEq : (prefixWires + 1)
            + (zxpCellDomArity (ZxpCell.xSpider 2 1) + restBits.length)
          = (prefixWires + 1) + (2 + restBits.length) := rfl
      have hMergeCodEq : (prefixWires + 1)
            + (zxpCellCodArity (ZxpCell.xSpider 2 1) + restBits.length)
          = prefixWires + (2 + restBits.length) :=
        (zxnStepArityShuffle prefixWires restBits.length).symm
      have hCrossDomEq : prefixWires
            + (zxpCellDomArity ZxpCell.crossing + restBits.length)
          = prefixWires + (2 + restBits.length) := rfl
      have hCrossCodEq : prefixWires
            + (zxpCellCodArity ZxpCell.crossing + restBits.length)
          = (prefixWires + 1) + (1 + restBits.length) :=
        zxnStepArityShuffle prefixWires restBits.length
      have hCombWFShifted : ZxpLayersWF ((prefixWires + 1) + (1 + restBits.length))
          (zxnCombLayers (prefixWires + 1) restBits) := zxnCombLayersWF restBits (prefixWires + 1)
      have hCombFinal : zxpLayersCodArity ((prefixWires + 1) + (1 + restBits.length))
          (zxnCombLayers (prefixWires + 1) restBits) = prefixWires + (restBits.length + 1) :=
        (zxnCombLayersCodArity restBits (prefixWires + 1) _).trans
          (zxnCombCodShuffle prefixWires restBits.length)
      have hCrossConsWF : ZxpLayersWF (prefixWires + (2 + restBits.length))
          (zxpWhiskerLayer prefixWires restBits.length [ZxpCell.crossing]
            :: zxnCombLayers (prefixWires + 1) restBits) := by
        refine ZxpLayersWF.cons ?_ ?_
        · rw [zxpWhiskerLayerDomArity]
          exact hCrossDomEq
        · rw [zxpWhiskerLayerCodArity]
          have hInner := zxnCombLayersWF restBits (prefixWires + 1)
          rw [<- zxnStepArityShuffle prefixWires restBits.length] at hInner
          exact hInner
      have hCrossConsFinal : zxpLayersCodArity (prefixWires + (2 + restBits.length))
          (zxpWhiskerLayer prefixWires restBits.length [ZxpCell.crossing]
            :: zxnCombLayers (prefixWires + 1) restBits)
          = prefixWires + (restBits.length + 1) := by
        show zxpLayersCodArity _ (zxnCombLayers (prefixWires + 1) restBits)
          = prefixWires + (restBits.length + 1)
        exact (zxnCombLayersCodArity restBits (prefixWires + 1) _).trans
          (zxnCombCodShuffle prefixWires restBits.length)
      have hRest3Iff : (midTwoVec finalVec : List Bool) ->
          (ZxpPairMem (prefixWires + (2 + restBits.length))
              (prefixWires + (restBits.length + 1))
              (zxpLayersDenote (prefixWires + (2 + restBits.length))
                (zxpWhiskerLayer prefixWires restBits.length [ZxpCell.crossing]
                  :: zxnCombLayers (prefixWires + 1) restBits)) midTwoVec finalVec
            <-> Exists fun midThreeVec =>
                ZxpPairMem (prefixWires + (2 + restBits.length))
                    ((prefixWires + 1) + (1 + restBits.length))
                    (zxpLayerDenote
                      (zxpWhiskerLayer prefixWires restBits.length [ZxpCell.crossing]))
                    midTwoVec midThreeVec
                  /\ ZxpPairMem ((prefixWires + 1) + (1 + restBits.length))
                      (prefixWires + (restBits.length + 1))
                      (zxpLayersDenote ((prefixWires + 1) + (1 + restBits.length))
                        (zxnCombLayers (prefixWires + 1) restBits)) midThreeVec finalVec) :=
        fun midTwoVec finalVec => zxnConsLayerPairIffAt
          (prefixWires + (2 + restBits.length))
          ((prefixWires + 1) + (1 + restBits.length))
          (prefixWires + (restBits.length + 1))
          (zxpWhiskerLayer prefixWires restBits.length [ZxpCell.crossing])
          (zxnCombLayers (prefixWires + 1) restBits)
          ((zxpWhiskerLayerDomArity prefixWires restBits.length [ZxpCell.crossing]).trans
            hCrossDomEq)
          ((zxpWhiskerLayerCodArity prefixWires restBits.length [ZxpCell.crossing]).trans
            hCrossCodEq)
          hCombWFShifted hCombFinal midTwoVec finalVec
      have hRest2Iff : (midOneVec finalVec : List Bool) ->
          (ZxpPairMem ((prefixWires + 1) + (2 + restBits.length))
              (prefixWires + (restBits.length + 1))
              (zxpLayersDenote ((prefixWires + 1) + (2 + restBits.length))
                (zxpWhiskerLayer (prefixWires + 1) restBits.length [ZxpCell.xSpider 2 1]
                  :: zxpWhiskerLayer prefixWires restBits.length [ZxpCell.crossing]
                  :: zxnCombLayers (prefixWires + 1) restBits)) midOneVec finalVec
            <-> Exists fun midTwoVec =>
                ZxpPairMem ((prefixWires + 1) + (2 + restBits.length))
                    (prefixWires + (2 + restBits.length))
                    (zxpLayerDenote (zxpWhiskerLayer (prefixWires + 1) restBits.length
                      [ZxpCell.xSpider 2 1])) midOneVec midTwoVec
                  /\ ZxpPairMem (prefixWires + (2 + restBits.length))
                      (prefixWires + (restBits.length + 1))
                      (zxpLayersDenote (prefixWires + (2 + restBits.length))
                        (zxpWhiskerLayer prefixWires restBits.length [ZxpCell.crossing]
                          :: zxnCombLayers (prefixWires + 1) restBits)) midTwoVec finalVec) :=
        fun midOneVec finalVec => zxnConsLayerPairIffAt
          ((prefixWires + 1) + (2 + restBits.length))
          (prefixWires + (2 + restBits.length))
          (prefixWires + (restBits.length + 1))
          (zxpWhiskerLayer (prefixWires + 1) restBits.length [ZxpCell.xSpider 2 1])
          (zxpWhiskerLayer prefixWires restBits.length [ZxpCell.crossing]
            :: zxnCombLayers (prefixWires + 1) restBits)
          ((zxpWhiskerLayerDomArity (prefixWires + 1) restBits.length
            [ZxpCell.xSpider 2 1]).trans hMergeDomEq)
          ((zxpWhiskerLayerCodArity (prefixWires + 1) restBits.length
            [ZxpCell.xSpider 2 1]).trans hMergeCodEq)
          hCrossConsWF hCrossConsFinal midOneVec finalVec
      refine Iff.trans (zxnConsLayerPairIffAt
        (prefixWires + (1 + (restBits.length + 1)))
        ((prefixWires + 1) + (2 + restBits.length))
        (prefixWires + (restBits.length + 1))
        (zxpWhiskerLayer prefixWires (restBits.length + 1) [ZxpCell.zSpider 1 2])
        (zxpWhiskerLayer (prefixWires + 1) restBits.length [ZxpCell.xSpider 2 1]
          :: zxpWhiskerLayer prefixWires restBits.length [ZxpCell.crossing]
          :: zxnCombLayers (prefixWires + 1) restBits)
        ((zxpWhiskerLayerDomArity prefixWires (restBits.length + 1)
          [ZxpCell.zSpider 1 2]).trans hForkDomEq)
        ((zxpWhiskerLayerCodArity prefixWires (restBits.length + 1)
          [ZxpCell.zSpider 1 2]).trans hForkCodEq)
        (ZxpLayersWF.cons (by rw [zxpWhiskerLayerDomArity]; exact hMergeDomEq)
          (by
            rw [zxpWhiskerLayerCodArity]
            have hArityBridge : (prefixWires + 1)
                + (zxpLayerCodArity [ZxpCell.xSpider 2 1] + restBits.length)
                = prefixWires + (2 + restBits.length) := hMergeCodEq
            rw [hArityBridge]
            exact hCrossConsWF))
        (by
          show zxpLayersCodArity
              (zxpLayerCodArity
                (zxpWhiskerLayer prefixWires restBits.length [ZxpCell.crossing]))
              (zxnCombLayers (prefixWires + 1) restBits)
            = prefixWires + (restBits.length + 1)
          exact (zxnCombLayersCodArity restBits (prefixWires + 1) _).trans
            (zxnCombCodShuffle prefixWires restBits.length))
        domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hPacked
        obtain ⟨midOneVec, hForkPair, hRestTwoPair⟩ := hPacked
        have hFork := (zxnPadCellPairIffAt prefixWires (restBits.length + 1)
          (ZxpCell.zSpider 1 2) (prefixWires + (1 + (restBits.length + 1)))
          ((prefixWires + 1) + (2 + restBits.length))
          hForkDomEq hForkCodEq domVec midOneVec).mp hForkPair
        obtain ⟨passVec, forkDomVec, forkSideVec, forkCodVec,
          hDomEq, hMidOneEq, hPassLen, hForkSideLen, hForkCellPair⟩ := hFork
        obtain ⟨carrierBit, hForkDomShape, hForkCodShape⟩ :=
          (zxnZForkPairIff forkDomVec forkCodVec).mp hForkCellPair
        obtain ⟨hitBit, liveTail, hForkSideShape, hLiveTailLen⟩ :=
          zxnLengthSuccShape forkSideVec restBits.length hForkSideLen
        obtain ⟨midTwoVec, hMergePair, hRestThreePair⟩ :=
          (hRest2Iff midOneVec codVec).mp hRestTwoPair
        have hMerge := (zxnPadCellPairIffAt (prefixWires + 1) restBits.length
          (ZxpCell.xSpider 2 1) ((prefixWires + 1) + (2 + restBits.length))
          (prefixWires + (2 + restBits.length))
          hMergeDomEq hMergeCodEq midOneVec midTwoVec).mp hMergePair
        obtain ⟨passVec2, mergeDomVec, mergeSideVec, mergeCodVec,
          hMidOneEq2, hMidTwoEq, hPassLen2, hMergeSideLen, hMergeCellPair⟩ := hMerge
        obtain ⟨copyBit, wireBit, hMergeDomShape, hMergeCodShape⟩ :=
          (zxnXMergePairIff mergeDomVec mergeCodVec).mp hMergeCellPair
        have hMidOneLeftForm : midOneVec
            = zxpCat (zxpCat passVec [carrierBit]) (carrierBit :: hitBit :: liveTail) := by
          rw [hMidOneEq, hForkCodShape, hForkSideShape, zxpCatAssoc]
          rfl
        have hMidOneRightForm : midOneVec
            = zxpCat passVec2 (copyBit :: wireBit :: mergeSideVec) := by
          rw [hMidOneEq2, hMergeDomShape]
          rfl
        have hMidOneBridge : zxpCat (zxpCat passVec [carrierBit])
            (carrierBit :: hitBit :: liveTail)
            = zxpCat passVec2 (copyBit :: wireBit :: mergeSideVec) :=
          hMidOneLeftForm.symm.trans hMidOneRightForm
        have hParts1 := zxpCatInj (zxpCat passVec [carrierBit])
          (carrierBit :: hitBit :: liveTail) passVec2 (copyBit :: wireBit :: mergeSideVec)
          (by rw [zxpCatLength, hPassLen, hPassLen2]; rfl) hMidOneBridge
        have hCopyEq : carrierBit = copyBit := by
          injection hParts1.right with hHeadEq _hTailEq
        have hTail1 : hitBit :: liveTail = wireBit :: mergeSideVec := by
          injection hParts1.right with _hHeadEq hTailEq
        have hWireEq : hitBit = wireBit := by
          injection hTail1 with hHeadEq _hTailEq
        have hMergeSideEq : liveTail = mergeSideVec := by
          injection hTail1 with _hHeadEq hTailEq
        obtain ⟨midThreeVec, hCrossPair, hCombPair⟩ :=
          (hRest3Iff midTwoVec codVec).mp hRestThreePair
        have hCross := (zxnPadCellPairIffAt prefixWires restBits.length
          ZxpCell.crossing (prefixWires + (2 + restBits.length))
          ((prefixWires + 1) + (1 + restBits.length))
          hCrossDomEq hCrossCodEq midTwoVec midThreeVec).mp hCrossPair
        obtain ⟨passVec3, crossDomVec, crossSideVec, crossCodVec,
          hMidTwoEq2, hMidThreeEq, hPassLen3, hCrossSideLen, hCrossCellPair⟩ := hCross
        obtain ⟨leftBit, rightBit, hCrossDomShape, hCrossCodShape⟩ :=
          (zxnCrossingPairIff crossDomVec crossCodVec).mp hCrossCellPair
        have hStepOne : midTwoVec
            = zxpCat (zxpCat passVec [carrierBit])
                (zxpXorB carrierBit hitBit :: liveTail) := by
          rw [hMidTwoEq, hMergeCodShape, <- hParts1.left, <- hCopyEq, <- hWireEq,
            <- hMergeSideEq]
          rfl
        have hMidTwoValue : midTwoVec
            = zxpCat passVec (carrierBit :: zxpXorB carrierBit hitBit :: liveTail) := by
          rw [hStepOne, zxpCatAssoc]
          rfl
        have hMidTwoBridge : zxpCat passVec
            (carrierBit :: zxpXorB carrierBit hitBit :: liveTail)
            = zxpCat passVec3 (leftBit :: rightBit :: crossSideVec) := by
          rw [<- hMidTwoValue, hMidTwoEq2, hCrossDomShape]
          rfl
        have hParts2 := zxpCatInj passVec
          (carrierBit :: zxpXorB carrierBit hitBit :: liveTail)
          passVec3 (leftBit :: rightBit :: crossSideVec)
          (by rw [hPassLen, hPassLen3]) hMidTwoBridge
        have hLeftEq : carrierBit = leftBit := by
          injection hParts2.right with hHeadEq _hTailEq
        have hTailTwo : zxpXorB carrierBit hitBit :: liveTail
            = rightBit :: crossSideVec := by
          injection hParts2.right with _hHeadEq hTailEq
        have hRightEq : zxpXorB carrierBit hitBit = rightBit := by
          injection hTailTwo with hHeadEq _hTailEq
        have hCrossSideEq : liveTail = crossSideVec := by
          injection hTailTwo with _hHeadEq hTailEq
        have hComb := (zxnCombPairIff restBits (prefixWires + 1) midThreeVec codVec).mp
          ((zxpPairMemCast rfl
            (zxnCombCodShuffle prefixWires restBits.length).symm).mp hCombPair)
        obtain ⟨passVec4, carrierBit4, liveVec4,
          hMidThreeEq2, hPassLen4, hLiveLen4, hCodEq4⟩ := hComb
        have hMidThreeValue : midThreeVec
            = zxpCat (zxpCat passVec [zxpXorB carrierBit hitBit])
                (carrierBit :: liveTail) := by
          rw [hMidThreeEq, hCrossCodShape, <- hParts2.left, <- hLeftEq, <- hRightEq,
            <- hCrossSideEq, zxpCatAssoc]
          rfl
        have hMidThreeBridge : zxpCat (zxpCat passVec [zxpXorB carrierBit hitBit])
            (carrierBit :: liveTail) = zxpCat passVec4 (carrierBit4 :: liveVec4) := by
          rw [<- hMidThreeValue, hMidThreeEq2]
        have hParts3 := zxpCatInj (zxpCat passVec [zxpXorB carrierBit hitBit])
          (carrierBit :: liveTail) passVec4 (carrierBit4 :: liveVec4)
          (by rw [zxpCatLength, hPassLen, hPassLen4]; rfl) hMidThreeBridge
        have hCarrierEqFour : carrierBit = carrierBit4 := by
          injection hParts3.right with hHeadEq _hTailEq
        have hLiveEqFour : liveTail = liveVec4 := by
          injection hParts3.right with _hHeadEq hTailEq
        refine Exists.intro passVec (Exists.intro carrierBit
          (Exists.intro (hitBit :: liveTail)
            (And.intro ?_ (And.intro hPassLen (And.intro ?_ ?_)))))
        · rw [hDomEq, hForkDomShape, hForkSideShape]
          rfl
        · show liveTail.length + 1 = restBits.length + 1
          rw [hLiveTailLen]
        · rw [hCodEq4, <- hParts3.left, <- hCarrierEqFour, <- hLiveEqFour,
            zxnScaleRowConsTrue]
          show zxpCat (zxpCat passVec [zxpXorB carrierBit hitBit])
              (zxpRowXor liveTail (zxnScaleRow carrierBit restBits))
            = zxpCat passVec (zxpXorB hitBit carrierBit
                :: zxpRowXor liveTail (zxnScaleRow carrierBit restBits))
          rw [zxpXorBComm hitBit carrierBit, zxpCatAssoc]
          rfl
      · intro hPacked
        obtain ⟨passVec, carrierBit, liveVec, hDomEq, hPassLen, hLiveLen, hCodEq⟩ := hPacked
        obtain ⟨hitBit, liveTail, hLiveShape, hLiveTailLen⟩ :=
          zxnLengthSuccShape liveVec restBits.length hLiveLen
        refine Exists.intro
          (zxpCat passVec (zxpCat [carrierBit, carrierBit] (hitBit :: liveTail)))
          (And.intro ?_ ?_)
        · refine (zxnPadCellPairIffAt prefixWires (restBits.length + 1)
            (ZxpCell.zSpider 1 2) (prefixWires + (1 + (restBits.length + 1)))
            ((prefixWires + 1) + (2 + restBits.length))
            hForkDomEq hForkCodEq domVec _).mpr ?_
          refine Exists.intro passVec (Exists.intro [carrierBit]
            (Exists.intro (hitBit :: liveTail) (Exists.intro [carrierBit, carrierBit]
              (And.intro ?_ (And.intro rfl (And.intro hPassLen (And.intro ?_ ?_)))))))
          · rw [hDomEq, hLiveShape]
            rfl
          · show liveTail.length + 1 = restBits.length + 1
            rw [hLiveTailLen]
          · exact (zxnZForkPairIff [carrierBit] [carrierBit, carrierBit]).mpr
              (Exists.intro carrierBit (And.intro rfl rfl))
        · refine (hRest2Iff _ codVec).mpr ?_
          refine Exists.intro
            (zxpCat (zxpCat passVec [carrierBit])
              (zxpCat [zxpXorB carrierBit hitBit] liveTail))
            (And.intro ?_ ?_)
          · refine (zxnPadCellPairIffAt (prefixWires + 1) restBits.length
              (ZxpCell.xSpider 2 1) ((prefixWires + 1) + (2 + restBits.length))
              (prefixWires + (2 + restBits.length))
              hMergeDomEq hMergeCodEq _ _).mpr ?_
            refine Exists.intro (zxpCat passVec [carrierBit])
              (Exists.intro [carrierBit, hitBit] (Exists.intro liveTail
                (Exists.intro [zxpXorB carrierBit hitBit]
                  (And.intro ?_ (And.intro rfl (And.intro ?_
                    (And.intro hLiveTailLen ?_)))))))
            · rw [zxpCatAssoc]
              rfl
            · rw [zxpCatLength, hPassLen]
              rfl
            · exact (zxnXMergePairIff [carrierBit, hitBit]
                [zxpXorB carrierBit hitBit]).mpr
                (Exists.intro carrierBit (Exists.intro hitBit (And.intro rfl rfl)))
          · refine (hRest3Iff _ codVec).mpr ?_
            refine Exists.intro
              (zxpCat passVec
                (zxpCat [zxpXorB carrierBit hitBit, carrierBit] liveTail))
              (And.intro ?_ ?_)
            · refine (zxnPadCellPairIffAt prefixWires restBits.length
                ZxpCell.crossing (prefixWires + (2 + restBits.length))
                ((prefixWires + 1) + (1 + restBits.length))
                hCrossDomEq hCrossCodEq _ _).mpr ?_
              refine Exists.intro passVec
                (Exists.intro [carrierBit, zxpXorB carrierBit hitBit]
                  (Exists.intro liveTail
                    (Exists.intro [zxpXorB carrierBit hitBit, carrierBit]
                      (And.intro ?_ (And.intro rfl (And.intro hPassLen
                        (And.intro hLiveTailLen ?_)))))))
              · rw [zxpCatAssoc]
                rfl
              · exact (zxnCrossingPairIff [carrierBit, zxpXorB carrierBit hitBit]
                  [zxpXorB carrierBit hitBit, carrierBit]).mpr
                  (Exists.intro carrierBit
                    (Exists.intro (zxpXorB carrierBit hitBit) (And.intro rfl rfl)))
            · refine (zxpPairMemCast rfl
                (zxnCombCodShuffle prefixWires restBits.length).symm).mpr ?_
              refine (zxnCombPairIff restBits (prefixWires + 1) _ codVec).mpr ?_
              refine Exists.intro (zxpCat passVec [zxpXorB carrierBit hitBit])
                (Exists.intro carrierBit (Exists.intro liveTail
                  (And.intro ?_ (And.intro ?_ (And.intro hLiveTailLen ?_)))))
              · rw [zxpCatAssoc]
                rfl
              · rw [zxpCatLength, hPassLen]
                rfl
              · rw [hCodEq, hLiveShape, zxnScaleRowConsTrue]
                show zxpCat passVec (zxpXorB hitBit carrierBit
                    :: zxpRowXor liveTail (zxnScaleRow carrierBit restBits))
                  = zxpCat (zxpCat passVec [zxpXorB carrierBit hitBit])
                      (zxpRowXor liveTail (zxnScaleRow carrierBit restBits))
                rw [zxpXorBComm hitBit carrierBit, zxpCatAssoc]
                rfl

/-! ## Stage 5 — the per-generator block and the generator fold -/

/-- One generator's conditional-xor block: create the coefficient carrier at the far
left, comb it across the strands, discard it. -/
def zxnXorRowLayers (rowBits : List Bool) : List (List ZxpCell) :=
  zxpWhiskerLayer 0 rowBits.length [ZxpCell.zSpider 0 1] :: zxnCombLayers 0 rowBits

theorem zxnXorRowLayersWF (rowBits : List Bool) :
    ZxpLayersWF rowBits.length (zxnXorRowLayers rowBits) := by
  refine ZxpLayersWF.cons ?_ ?_
  · rw [zxpWhiskerLayerDomArity]
    show 0 + (0 + rowBits.length) = rowBits.length
    rw [Nat.zero_add, Nat.zero_add]
  · rw [zxpWhiskerLayerCodArity]
    show ZxpLayersWF (0 + (1 + rowBits.length)) (zxnCombLayers 0 rowBits)
    exact zxnCombLayersWF rowBits 0

theorem zxnXorRowLayersCodArity (rowBits : List Bool) (anyArity : Nat) :
    zxpLayersCodArity anyArity (zxnXorRowLayers rowBits) = rowBits.length := by
  show zxpLayersCodArity
      (zxpLayerCodArity (zxpWhiskerLayer 0 rowBits.length [ZxpCell.zSpider 0 1]))
      (zxnCombLayers 0 rowBits) = rowBits.length
  rw [zxnCombLayersCodArity rowBits 0 _, Nat.zero_add]

/-- The per-generator block relates `v` to `xor v (t * row)` for a free bit `t`. -/
theorem zxnXorRowPairIff (rowBits : List Bool) (domVec codVec : List Bool) :
    ZxpPairMem rowBits.length rowBits.length
        (zxpLayersDenote rowBits.length (zxnXorRowLayers rowBits)) domVec codVec
      <-> (domVec.length = rowBits.length
            /\ Exists fun carrierBit =>
                codVec = zxpRowXor domVec (zxnScaleRow carrierBit rowBits)) := by
  have hCreateDomEq : 0 + (zxpCellDomArity (ZxpCell.zSpider 0 1) + rowBits.length)
      = rowBits.length := by
    show 0 + (0 + rowBits.length) = rowBits.length
    rw [Nat.zero_add, Nat.zero_add]
  have hCreateCodEq : 0 + (zxpCellCodArity (ZxpCell.zSpider 0 1) + rowBits.length)
      = 0 + (1 + rowBits.length) := rfl
  refine Iff.trans (zxnConsLayerPairIffAt rowBits.length (0 + (1 + rowBits.length))
    rowBits.length
    (zxpWhiskerLayer 0 rowBits.length [ZxpCell.zSpider 0 1])
    (zxnCombLayers 0 rowBits)
    ((zxpWhiskerLayerDomArity 0 rowBits.length [ZxpCell.zSpider 0 1]).trans hCreateDomEq)
    ((zxpWhiskerLayerCodArity 0 rowBits.length [ZxpCell.zSpider 0 1]).trans hCreateCodEq)
    (zxnCombLayersWF rowBits 0)
    ((zxnCombLayersCodArity rowBits 0 _).trans (Nat.zero_add rowBits.length))
    domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hPacked
    obtain ⟨midVec, hCreatePair, hCombPair⟩ := hPacked
    have hCreate := (zxnPadCellPairIffAt 0 rowBits.length (ZxpCell.zSpider 0 1)
      rowBits.length (0 + (1 + rowBits.length)) hCreateDomEq hCreateCodEq
      domVec midVec).mp hCreatePair
    obtain ⟨passVec, cellDomVec, sideVec, cellCodVec,
      hDomEq, hMidEq, hPassLen, hSideLen, hCellPair⟩ := hCreate
    have hCell := (zxnZSourcePairIff cellDomVec cellCodVec).mp hCellPair
    obtain ⟨carrierBit, hCellCodShape⟩ := hCell.right
    have hPassNil := zxpLengthZeroNil passVec hPassLen
    have hComb := (zxnCombPairIff rowBits 0 midVec codVec).mp
      ((zxpPairMemCast rfl (Nat.zero_add rowBits.length).symm).mp hCombPair)
    obtain ⟨passVec2, carrierBit2, liveVec2,
      hMidEq2, hPassLen2, hLiveLen2, hCodEq2⟩ := hComb
    have hPassNil2 := zxpLengthZeroNil passVec2 hPassLen2
    have hMidValue : midVec = carrierBit :: sideVec := by
      rw [hMidEq, hPassNil, hCellCodShape]
      rfl
    have hMidValue2 : midVec = carrierBit2 :: liveVec2 := by
      rw [hMidEq2, hPassNil2]
      rfl
    have hConsEq : carrierBit :: sideVec = carrierBit2 :: liveVec2 :=
      hMidValue.symm.trans hMidValue2
    have hCarrierEq : carrierBit = carrierBit2 := by
      injection hConsEq with hHeadEq _hTailEq
    have hLiveEq : sideVec = liveVec2 := by
      injection hConsEq with _hHeadEq hTailEq
    have hDomValue : domVec = sideVec := by
      rw [hDomEq, hPassNil, hCell.left]
      rfl
    refine And.intro ?_ (Exists.intro carrierBit ?_)
    · rw [hDomValue]
      exact hSideLen
    · rw [hCodEq2, hPassNil2, <- hCarrierEq, <- hLiveEq, hDomValue]
      rfl
  · intro hBoth
    obtain ⟨carrierBit, hCodEq⟩ := hBoth.right
    refine Exists.intro (carrierBit :: domVec) (And.intro ?_ ?_)
    · refine (zxnPadCellPairIffAt 0 rowBits.length (ZxpCell.zSpider 0 1)
        rowBits.length (0 + (1 + rowBits.length)) hCreateDomEq hCreateCodEq
        domVec (carrierBit :: domVec)).mpr ?_
      refine Exists.intro [] (Exists.intro [] (Exists.intro domVec
        (Exists.intro [carrierBit] (And.intro rfl (And.intro rfl
          (And.intro rfl (And.intro hBoth.left ?_)))))))
      exact (zxnZSourcePairIff [] [carrierBit]).mpr
        (And.intro rfl (Exists.intro carrierBit rfl))
    · refine (zxpPairMemCast rfl (Nat.zero_add rowBits.length).symm).mpr ?_
      refine (zxnCombPairIff rowBits 0 (carrierBit :: domVec) codVec).mpr ?_
      refine Exists.intro [] (Exists.intro carrierBit (Exists.intro domVec
        (And.intro rfl (And.intro rfl (And.intro hBoth.left ?_)))))
      rw [hCodEq]
      rfl

/-- The per-generator block at an externally supplied strand width. -/
theorem zxnXorRowPairIffAt (rowBits : List Bool) (strandWidth : Nat)
    (hRowLen : rowBits.length = strandWidth) (domVec codVec : List Bool) :
    ZxpPairMem strandWidth strandWidth
        (zxpLayersDenote strandWidth (zxnXorRowLayers rowBits)) domVec codVec
      <-> (domVec.length = strandWidth
            /\ Exists fun carrierBit =>
                codVec = zxpRowXor domVec (zxnScaleRow carrierBit rowBits)) := by
  subst hRowLen
  exact zxnXorRowPairIff rowBits domVec codVec

/-- The full generator fold: one conditional-xor block per generator row. -/
def zxnGeneratorBlockLayers : List (List Bool) -> List (List ZxpCell)
  | [] => []
  | generatorRow :: restRows =>
      zxpCatLayers (zxnXorRowLayers generatorRow) (zxnGeneratorBlockLayers restRows)

theorem zxnGeneratorBlockLayersWF : (generatorRows : List (List Bool)) ->
    (strandWidth : Nat) -> ZxpAllWidth strandWidth generatorRows ->
    ZxpLayersWF strandWidth (zxnGeneratorBlockLayers generatorRows)
  | [], strandWidth, _hAll => ZxpLayersWF.nil strandWidth
  | generatorRow :: restRows, strandWidth, hAll => by
      have hRowLen : generatorRow.length = strandWidth := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth strandWidth restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      show ZxpLayersWF strandWidth
        (zxpCatLayers (zxnXorRowLayers generatorRow) (zxnGeneratorBlockLayers restRows))
      refine zxpLayersWFCat (zxnXorRowLayers generatorRow)
        (zxnGeneratorBlockLayers restRows) ?_ ?_
      · rw [<- hRowLen]
        exact zxnXorRowLayersWF generatorRow
      · rw [zxnXorRowLayersCodArity generatorRow strandWidth, hRowLen]
        exact zxnGeneratorBlockLayersWF restRows strandWidth hRestAll

theorem zxnGeneratorBlockLayersCodArity : (generatorRows : List (List Bool)) ->
    (strandWidth : Nat) -> ZxpAllWidth strandWidth generatorRows ->
    zxpLayersCodArity strandWidth (zxnGeneratorBlockLayers generatorRows) = strandWidth
  | [], _strandWidth, _hAll => rfl
  | generatorRow :: restRows, strandWidth, hAll => by
      have hRowLen : generatorRow.length = strandWidth := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth strandWidth restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      show zxpLayersCodArity strandWidth
          (zxpCatLayers (zxnXorRowLayers generatorRow)
            (zxnGeneratorBlockLayers restRows))
        = strandWidth
      rw [zxpLayersCodArityCat, zxnXorRowLayersCodArity, hRowLen,
        zxnGeneratorBlockLayersCodArity restRows strandWidth hRestAll]

/-- THE GENERATOR-FOLD CHARACTERIZATION: the block relates `v` to `w` exactly when
`xor v w` lies in the span of the generator rows. -/
theorem zxnGeneratorBlockLayersPairIff : (generatorRows : List (List Bool)) ->
    (strandWidth : Nat) -> ZxpAllWidth strandWidth generatorRows ->
    (domVec codVec : List Bool) ->
    (ZxpPairMem strandWidth strandWidth
        (zxpLayersDenote strandWidth (zxnGeneratorBlockLayers generatorRows))
        domVec codVec
      <-> (domVec.length = strandWidth /\ codVec.length = strandWidth
            /\ ZxpMemSpan strandWidth generatorRows (zxpRowXor domVec codVec)))
  | [], strandWidth, _hAll, domVec, codVec => by
      refine Iff.trans (zxpIdSpec strandWidth domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hSame
        refine And.intro hSame.right (And.intro ?_ ?_)
        · rw [<- hSame.left]
          exact hSame.right
        · rw [<- hSame.left, zxpRowXorSelf domVec, hSame.right]
          exact ZxpMemSpan.zero
      · intro hPacked
        refine And.intro ?_ hPacked.left
        have hZero := zxpMemSpanNilInv hPacked.right.right
        exact zxpRowXorEqZeroImpliesEq domVec codVec strandWidth hPacked.left
          hPacked.right.left hZero
  | generatorRow :: restRows, strandWidth, hAll, domVec, codVec => by
      have hRowLen : generatorRow.length = strandWidth := by
        cases hAll with
        | cons hHead _hRest => exact hHead
      have hRestAll : ZxpAllWidth strandWidth restRows := by
        cases hAll with
        | cons _hHead hRest => exact hRest
      refine Iff.trans (zxnCatLayersPairIffAt strandWidth strandWidth strandWidth
        (zxnXorRowLayers generatorRow) (zxnGeneratorBlockLayers restRows)
        (by rw [<- hRowLen]; exact zxnXorRowLayersWF generatorRow)
        ((zxnXorRowLayersCodArity generatorRow strandWidth).trans hRowLen)
        (zxnGeneratorBlockLayersWF restRows strandWidth hRestAll)
        (zxnGeneratorBlockLayersCodArity restRows strandWidth hRestAll)
        domVec codVec) ?_
      refine Iff.intro ?_ ?_
      · intro hPacked
        obtain ⟨midVec, hRowPair, hRestPair⟩ := hPacked
        have hRow := (zxnXorRowPairIffAt generatorRow strandWidth hRowLen
          domVec midVec).mp hRowPair
        obtain ⟨hDomLen, hRowPacked⟩ := hRow
        obtain ⟨carrierBit, hMidEq⟩ := hRowPacked
        have hRest := (zxnGeneratorBlockLayersPairIff restRows strandWidth hRestAll
          midVec codVec).mp hRestPair
        obtain ⟨_hMidLen, hCodLen, hSpanRest⟩ := hRest
        refine And.intro hDomLen (And.intro hCodLen ?_)
        refine (zxnMemSpanConsIff hAll (zxpRowXor domVec codVec)).mpr ?_
        refine Exists.intro carrierBit (Exists.intro (zxpRowXor midVec codVec)
          (And.intro hSpanRest ?_))
        rw [hMidEq, zxpRowXorAssoc domVec (zxnScaleRow carrierBit generatorRow) codVec,
          zxnRowXorLeftComm (zxnScaleRow carrierBit generatorRow) domVec
            (zxpRowXor (zxnScaleRow carrierBit generatorRow) codVec)]
        rw [zxpRowXorCancelLeft (zxnScaleRow carrierBit generatorRow) codVec strandWidth
          ((zxnScaleRowLength carrierBit generatorRow).trans hRowLen) hCodLen]
      · intro hPacked
        obtain ⟨hDomLen, hCodLen, hSpanCons⟩ := hPacked
        have hSplit := (zxnMemSpanConsIff hAll (zxpRowXor domVec codVec)).mp hSpanCons
        obtain ⟨scaleBit, partnerVec, hPartnerMem, hSplitEq⟩ := hSplit
        refine Exists.intro (zxpRowXor domVec (zxnScaleRow scaleBit generatorRow))
          (And.intro ?_ ?_)
        · exact (zxnXorRowPairIffAt generatorRow strandWidth hRowLen domVec _).mpr
            (And.intro hDomLen (Exists.intro scaleBit rfl))
        · refine (zxnGeneratorBlockLayersPairIff restRows strandWidth hRestAll
            _ codVec).mpr ?_
          refine And.intro ?_ (And.intro hCodLen ?_)
          · exact zxpRowXorLength domVec _ strandWidth hDomLen
              ((zxnScaleRowLength scaleBit generatorRow).trans hRowLen)
          · rw [zxpRowXorAssoc domVec (zxnScaleRow scaleBit generatorRow) codVec,
              zxnRowXorLeftComm domVec (zxnScaleRow scaleBit generatorRow) codVec,
              hSplitEq,
              zxpRowXorCancelLeft (zxnScaleRow scaleBit generatorRow) partnerVec
                strandWidth
                ((zxnScaleRowLength scaleBit generatorRow).trans hRowLen)
                (zxpMemSpanWidth hRestAll hPartnerMem)]
            exact hPartnerMem

/-! ## Stage 6 — THE NORMAL FORM: init ; comb(g_1) ; ... ; comb(g_k) ; kill -/

/-- The Z-X normal form of the subspace spanned by `generatorRows` inside
`F2^(domWidth + codWidth)`, as a strict-layer diagram `domWidth -> codWidth`
(fissioned Kissinger eq. (5)/(6); construction documented in the file header). -/
def zxnNormalForm (domWidth codWidth : Nat)
    (generatorRows : List (List Bool)) : ZxpDiagram :=
  { sourceArity := domWidth
    layers := zxnInitLayer domWidth codWidth
      :: zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
          [zxnKillLayer domWidth codWidth] }

/-- The normal form is well-formed. -/
theorem zxnNormalFormWF (domWidth codWidth : Nat) (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth (domWidth + codWidth) generatorRows) :
    ZxpDiagramWF (zxnNormalForm domWidth codWidth generatorRows) := by
  show ZxpLayersWF domWidth (zxnInitLayer domWidth codWidth
    :: zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
        [zxnKillLayer domWidth codWidth])
  refine ZxpLayersWF.cons (zxnInitLayerDomArity domWidth codWidth) ?_
  rw [zxnInitLayerCodArity]
  refine zxpLayersWFCat (zxnGeneratorBlockLayers generatorRows)
    [zxnKillLayer domWidth codWidth]
    (zxnGeneratorBlockLayersWF generatorRows (domWidth + codWidth) hAll) ?_
  rw [zxnGeneratorBlockLayersCodArity generatorRows (domWidth + codWidth) hAll]
  exact ZxpLayersWF.cons (zxnKillLayerDomArity domWidth codWidth) (ZxpLayersWF.nil _)

/-- The normal form's source arity is the domain width (on the nose). -/
theorem zxnNormalFormSourceArity (domWidth codWidth : Nat)
    (generatorRows : List (List Bool)) :
    (zxnNormalForm domWidth codWidth generatorRows).sourceArity = domWidth := rfl

/-- The normal form's target arity is the codomain width. -/
theorem zxnNormalFormCodArity (domWidth codWidth : Nat)
    (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth (domWidth + codWidth) generatorRows) :
    zxpDiagramCodArity (zxnNormalForm domWidth codWidth generatorRows) = codWidth := by
  show zxpLayersCodArity (zxpLayerCodArity (zxnInitLayer domWidth codWidth))
      (zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
        [zxnKillLayer domWidth codWidth])
    = codWidth
  rw [zxnInitLayerCodArity, zxpLayersCodArityCat,
    zxnGeneratorBlockLayersCodArity generatorRows (domWidth + codWidth) hAll]
  show zxpLayerCodArity (zxnKillLayer domWidth codWidth) = codWidth
  exact zxnKillLayerCodArity domWidth codWidth

/-- BOUNDARIES: the normal form's boundary arities match the matrix dimensions. -/
theorem zxnNormalFormBoundaries (domWidth codWidth : Nat)
    (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth (domWidth + codWidth) generatorRows) :
    (zxnNormalForm domWidth codWidth generatorRows).sourceArity = domWidth
      /\ zxpDiagramCodArity (zxnNormalForm domWidth codWidth generatorRows) = codWidth :=
  And.intro (zxnNormalFormSourceArity domWidth codWidth generatorRows)
    (zxnNormalFormCodArity domWidth codWidth generatorRows hAll)

/-- THE DENOTATION THEOREM (structural, no kernel evaluation): the normal form's
relation IS the input subspace — the diagram's denotation is `ZxpRelEquiv`-equal to
the generator matrix itself. -/
theorem zxnNormalFormDenotes (domWidth codWidth : Nat)
    (generatorRows : List (List Bool))
    (hAll : ZxpAllWidth (domWidth + codWidth) generatorRows) :
    ZxpRelEquiv domWidth codWidth
      (zxpDiagramDenote (zxnNormalForm domWidth codWidth generatorRows))
      generatorRows := by
  have hBlocksWF := zxnGeneratorBlockLayersWF generatorRows (domWidth + codWidth) hAll
  have hBlocksCod :=
    zxnGeneratorBlockLayersCodArity generatorRows (domWidth + codWidth) hAll
  have hKillWF : ZxpLayersWF (domWidth + codWidth) [zxnKillLayer domWidth codWidth] :=
    ZxpLayersWF.cons (zxnKillLayerDomArity domWidth codWidth) (ZxpLayersWF.nil _)
  have hKillFinal : zxpLayersCodArity (domWidth + codWidth)
      [zxnKillLayer domWidth codWidth] = codWidth := by
    show zxpLayerCodArity (zxnKillLayer domWidth codWidth) = codWidth
    exact zxnKillLayerCodArity domWidth codWidth
  have hRestWF : ZxpLayersWF (domWidth + codWidth)
      (zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
        [zxnKillLayer domWidth codWidth]) := by
    refine zxpLayersWFCat _ _ hBlocksWF ?_
    rw [hBlocksCod]
    exact hKillWF
  have hRestFinal : zxpLayersCodArity (domWidth + codWidth)
      (zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
        [zxnKillLayer domWidth codWidth]) = codWidth := by
    rw [zxpLayersCodArityCat, hBlocksCod]
    exact hKillFinal
  intro domVec codVec
  refine Iff.trans (zxnConsLayerPairIffAt domWidth (domWidth + codWidth) codWidth
    (zxnInitLayer domWidth codWidth)
    (zxpCatLayers (zxnGeneratorBlockLayers generatorRows)
      [zxnKillLayer domWidth codWidth])
    (zxnInitLayerDomArity domWidth codWidth)
    (zxnInitLayerCodArity domWidth codWidth)
    hRestWF hRestFinal domVec codVec) ?_
  refine Iff.intro ?_ ?_
  · intro hPacked
    obtain ⟨midOneVec, hInitPair, hRestPair⟩ := hPacked
    have hInit := (zxnInitLayerPairIff domWidth codWidth domVec midOneVec).mp hInitPair
    obtain ⟨midTwoVec, hBlocksPair, hKillPair⟩ :=
      (zxnCatLayersPairIffAt (domWidth + codWidth) (domWidth + codWidth) codWidth
        (zxnGeneratorBlockLayers generatorRows) [zxnKillLayer domWidth codWidth]
        hBlocksWF hBlocksCod hKillWF hKillFinal midOneVec codVec).mp hRestPair
    have hBlocks := (zxnGeneratorBlockLayersPairIff generatorRows (domWidth + codWidth)
      hAll midOneVec midTwoVec).mp hBlocksPair
    have hKill := (zxnKillLayerPairIff domWidth codWidth midTwoVec codVec).mp
      ((zxnSingleLayerPairIffAt (domWidth + codWidth) codWidth
        (zxnKillLayer domWidth codWidth) (zxnKillLayerDomArity domWidth codWidth)
        (zxnKillLayerCodArity domWidth codWidth) midTwoVec codVec).mp hKillPair)
    obtain ⟨_hMidOneLen, _hMidTwoLen, hSpan⟩ := hBlocks
    have hSpanValue : zxpRowXor midOneVec midTwoVec = zxpCat domVec codVec := by
      rw [hInit.right, hKill.right,
        zxpRowXorCat domVec (zxpZeroRow codWidth) (zxpZeroRow domWidth) codVec
          (by rw [hInit.left, zxpZeroRowLength]),
        zxpRowXorZeroRight domVec domWidth hInit.left,
        zxpRowXorZeroLeft codVec codWidth hKill.left]
    rw [hSpanValue] at hSpan
    exact And.intro hInit.left (And.intro hKill.left hSpan)
  · intro hPair
    refine Exists.intro (zxpCat domVec (zxpZeroRow codWidth)) (And.intro ?_ ?_)
    · exact (zxnInitLayerPairIff domWidth codWidth domVec _).mpr
        (And.intro hPair.left rfl)
    · refine (zxnCatLayersPairIffAt (domWidth + codWidth) (domWidth + codWidth) codWidth
        (zxnGeneratorBlockLayers generatorRows) [zxnKillLayer domWidth codWidth]
        hBlocksWF hBlocksCod hKillWF hKillFinal _ codVec).mpr ?_
      refine Exists.intro (zxpCat (zxpZeroRow domWidth) codVec) (And.intro ?_ ?_)
      · refine (zxnGeneratorBlockLayersPairIff generatorRows (domWidth + codWidth)
          hAll _ _).mpr ?_
        refine And.intro ?_ (And.intro ?_ ?_)
        · rw [zxpCatLength, hPair.left, zxpZeroRowLength]
        · rw [zxpCatLength, zxpZeroRowLength, hPair.right.left]
        · have hSpanValue : zxpRowXor (zxpCat domVec (zxpZeroRow codWidth))
              (zxpCat (zxpZeroRow domWidth) codVec) = zxpCat domVec codVec := by
            rw [zxpRowXorCat domVec (zxpZeroRow codWidth) (zxpZeroRow domWidth) codVec
                (by rw [hPair.left, zxpZeroRowLength]),
              zxpRowXorZeroRight domVec domWidth hPair.left,
              zxpRowXorZeroLeft codVec codWidth hPair.right.left]
          rw [hSpanValue]
          exact hPair.right.right
      · refine (zxnSingleLayerPairIffAt (domWidth + codWidth) codWidth
          (zxnKillLayer domWidth codWidth) (zxnKillLayerDomArity domWidth codWidth)
          (zxnKillLayerCodArity domWidth codWidth) _ codVec).mpr ?_
        exact (zxnKillLayerPairIff domWidth codWidth _ codVec).mpr
          (And.intro hPair.right.left rfl)

/-! ## Stage 7 — THE CENSUS: RREF enumeration + surjectivity and injectivity pins

`zxnAllRrefMatrices width` enumerates the reduced-row-echelon generator matrices of
ALL subspaces of `F2^width` by first-column recursion: either the first column is
zero (cons-false onto a width-1 RREF) or it is a pivot column (top row `true :: v`
with `v` reduced against the tail's pivot columns, tail cons-falsed).  Sizes are the
Galois numbers: width 2 -> 5, width 3 -> 16, width 4 -> 67 (kernel-pinned). -/

/-- Prepend a `false` column to a matrix. -/
def zxnMatrixConsFalseColumn (matrixRows : List (List Bool)) : List (List Bool) :=
  zxpMapRows (fun generatorRow => false :: generatorRow) matrixRows

def zxnMapConsFalseAll : List (List (List Bool)) -> List (List (List Bool))
  | [] => []
  | headMatrix :: restMatrices =>
      zxnMatrixConsFalseColumn headMatrix :: zxnMapConsFalseAll restMatrices

/-- Is the candidate row reduced against every pivot column of the matrix? -/
def zxnIsReducedAgainstB (candidateRow : List Bool) : List (List Bool) -> Bool
  | [] => true
  | pivotRow :: restRows =>
      match zxpLead pivotRow with
      | Option.none => false
      | Option.some leadPosition =>
          cond (zxpGetBit candidateRow leadPosition) false
            (zxnIsReducedAgainstB candidateRow restRows)

/-- All pivot-first RREF extensions of one tail matrix over the candidate top rows. -/
def zxnPivotExtensions (tailMatrix : List (List Bool)) :
    List (List Bool) -> List (List (List Bool))
  | [] => []
  | candidateRow :: restCandidates =>
      cond (zxnIsReducedAgainstB candidateRow tailMatrix)
        (((true :: candidateRow) :: zxnMatrixConsFalseColumn tailMatrix)
          :: zxnPivotExtensions tailMatrix restCandidates)
        (zxnPivotExtensions tailMatrix restCandidates)

/-- Cons-only concatenation of matrix lists. -/
def zxnCatMatrixLists : List (List (List Bool)) -> List (List (List Bool))
    -> List (List (List Bool))
  | [], secondList => secondList
  | headMatrix :: restMatrices, secondList =>
      headMatrix :: zxnCatMatrixLists restMatrices secondList

def zxnAllPivotExtensions (candidateVectors : List (List Bool)) :
    List (List (List Bool)) -> List (List (List Bool))
  | [] => []
  | headMatrix :: restMatrices =>
      zxnCatMatrixLists (zxnPivotExtensions headMatrix candidateVectors)
        (zxnAllPivotExtensions candidateVectors restMatrices)

/-- THE ENUMERATOR: one RREF generator matrix per subspace of `F2^width`. -/
def zxnAllRrefMatrices : Nat -> List (List (List Bool))
  | 0 => [[]]
  | widthPred + 1 =>
      zxnCatMatrixLists (zxnMapConsFalseAll (zxnAllRrefMatrices widthPred))
        (zxnAllPivotExtensions (zxgAllBoolVectors widthPred)
          (zxnAllRrefMatrices widthPred))

/-- Census size at total width 2 (boundary (1,1)): 5 subspaces. -/
theorem zxnRrefCountWidthTwo : (zxnAllRrefMatrices 2).length = 5 := rfl

/-- Census size at total width 3 (boundaries (1,2) and (2,1)): 16 subspaces. -/
theorem zxnRrefCountWidthThree : (zxnAllRrefMatrices 3).length = 16 := rfl

/-- Census size at total width 4 (boundary (2,2)): 67 subspaces. -/
theorem zxnRrefCountWidthFour : (zxnAllRrefMatrices 4).length = 67 := rfl

/-- One census check: the normal form of the matrix is executably well-formed, has
the declared target arity, and denotes a span equal to the matrix. -/
def zxnNfMatchesSubspaceB (domWidth codWidth : Nat)
    (matrixRows : List (List Bool)) : Bool :=
  (zxpDiagramWFB (zxnNormalForm domWidth codWidth matrixRows))
    && (zxpNatEqB (zxpDiagramCodArity (zxnNormalForm domWidth codWidth matrixRows))
        codWidth)
    && (zxpSpanEqB (zxpDiagramDenote (zxnNormalForm domWidth codWidth matrixRows))
        matrixRows)

/-- Fold the census check over an enumeration. -/
def zxnCensusSurjectivityB (domWidth codWidth : Nat) : List (List (List Bool)) -> Bool
  | [] => true
  | headMatrix :: restMatrices =>
      cond (zxnNfMatchesSubspaceB domWidth codWidth headMatrix)
        (zxnCensusSurjectivityB domWidth codWidth restMatrices) false

/-- SURJECTIVITY PIN, boundary (1,1): all 5 subspaces of F2^2 are hit (kernel). -/
theorem zxnCensusSurjectivityOneOne :
    zxnCensusSurjectivityB 1 1 (zxnAllRrefMatrices 2) = true := rfl

set_option maxRecDepth 8192 in
/-- SURJECTIVITY PIN, boundary (1,2): all 16 subspaces of F2^3 are hit (kernel). -/
theorem zxnCensusSurjectivityOneTwo :
    zxnCensusSurjectivityB 1 2 (zxnAllRrefMatrices 3) = true := rfl

set_option maxRecDepth 8192 in
/-- SURJECTIVITY PIN, boundary (2,1): all 16 subspaces of F2^3 are hit (kernel). -/
theorem zxnCensusSurjectivityTwoOne :
    zxnCensusSurjectivityB 2 1 (zxnAllRrefMatrices 3) = true := rfl

set_option maxRecDepth 8192 in
/-- SURJECTIVITY PIN, boundary (2,2): all 67 subspaces of F2^4 are hit (kernel). -/
theorem zxnCensusSurjectivityTwoTwo :
    zxnCensusSurjectivityB 2 2 (zxnAllRrefMatrices 4) = true := rfl

/-- Span-distinctness of one matrix from every later one. -/
def zxnDistinctFromAllB (firstMatrix : List (List Bool)) :
    List (List (List Bool)) -> Bool
  | [] => true
  | headMatrix :: restMatrices =>
      cond (zxpSpanEqB firstMatrix headMatrix) false
        (zxnDistinctFromAllB firstMatrix restMatrices)

/-- Pairwise span-distinctness of a whole enumeration. -/
def zxnAllPairsSpanDistinctB : List (List (List Bool)) -> Bool
  | [] => true
  | headMatrix :: restMatrices =>
      cond (zxnDistinctFromAllB headMatrix restMatrices)
        (zxnAllPairsSpanDistinctB restMatrices) false

/-- INJECTIVITY PIN, width 2: the 5 enumerated subspaces are pairwise span-distinct. -/
theorem zxnCensusInjectivityWidthTwo :
    zxnAllPairsSpanDistinctB (zxnAllRrefMatrices 2) = true := rfl

/-- INJECTIVITY PIN, width 3: the 16 enumerated subspaces are pairwise span-distinct. -/
theorem zxnCensusInjectivityWidthThree :
    zxnAllPairsSpanDistinctB (zxnAllRrefMatrices 3) = true := rfl

set_option maxRecDepth 8192 in
/-- INJECTIVITY PIN, width 4: the 67 enumerated subspaces are pairwise span-distinct
(2211 kernel span decisions). -/
theorem zxnCensusInjectivityWidthFour :
    zxnAllPairsSpanDistinctB (zxnAllRrefMatrices 4) = true := rfl

/-- PROVEN INJECTIVITY (through the denotation theorem, no kernel evaluation):
span-distinct generator lists always produce span-distinct normal forms — combined
with the width pins above, distinct enumerated subspaces have span-distinct normal
forms at every census boundary. -/
theorem zxnNormalFormInjective (domWidth codWidth : Nat)
    (firstRows secondRows : List (List Bool))
    (hFirstAll : ZxpAllWidth (domWidth + codWidth) firstRows)
    (hSecondAll : ZxpAllWidth (domWidth + codWidth) secondRows)
    (hSpanDistinct : zxpSpanEqB firstRows secondRows = false) :
    zxpSpanEqB (zxpDiagramDenote (zxnNormalForm domWidth codWidth firstRows))
      (zxpDiagramDenote (zxnNormalForm domWidth codWidth secondRows)) = false := by
  cases hProbe : zxpSpanEqB
      (zxpDiagramDenote (zxnNormalForm domWidth codWidth firstRows))
      (zxpDiagramDenote (zxnNormalForm domWidth codWidth secondRows)) with
  | false => rfl
  | true =>
      have hFirstDenAll : ZxpAllWidth (domWidth + codWidth)
          (zxpDiagramDenote (zxnNormalForm domWidth codWidth firstRows)) := by
        have hRaw := zxpDiagramDenoteWidth (zxnNormalForm domWidth codWidth firstRows)
          (zxnNormalFormWF domWidth codWidth firstRows hFirstAll)
        rw [zxnNormalFormCodArity domWidth codWidth firstRows hFirstAll] at hRaw
        exact hRaw
      have hSecondDenAll : ZxpAllWidth (domWidth + codWidth)
          (zxpDiagramDenote (zxnNormalForm domWidth codWidth secondRows)) := by
        have hRaw := zxpDiagramDenoteWidth (zxnNormalForm domWidth codWidth secondRows)
          (zxnNormalFormWF domWidth codWidth secondRows hSecondAll)
        rw [zxnNormalFormCodArity domWidth codWidth secondRows hSecondAll] at hRaw
        exact hRaw
      have hNfEquiv := zxpRelEquivOfSpanEqB (domWidth := domWidth)
        (codWidth := codWidth) hFirstDenAll hSecondDenAll hProbe
      have hRowsEquiv : ZxpRelEquiv domWidth codWidth firstRows secondRows :=
        zxpRelEquivTrans (zxpRelEquivSymm
          (zxnNormalFormDenotes domWidth codWidth firstRows hFirstAll))
          (zxpRelEquivTrans hNfEquiv
            (zxnNormalFormDenotes domWidth codWidth secondRows hSecondAll))
      have hTrue := zxpSpanEqBOfRelEquiv hFirstAll hSecondAll hRowsEquiv
      exact Bool.noConfusion (hSpanDistinct.symm.trans hTrue)

/-! ## Stage 8 — fires and markers -/

/-- FIRE 1 input: the copy-pair relation at boundary 2 -> 1 (span of `[1,1,1]`:
relates `(a,a) ~ a`). -/
def zxnFireCopyPairMatrix : List (List Bool) := [[true, true, true]]

/-- FIRE 1: the normal form of the copy-pair subspace builds and is executably
well-formed (kernel). -/
theorem zxnFireCopyPairWFB :
    zxpDiagramWFB (zxnNormalForm 2 1 zxnFireCopyPairMatrix) = true := rfl

/-- FIRE 1: its target arity is 1 (kernel). -/
theorem zxnFireCopyPairCodPin :
    zxpNatEqB (zxpDiagramCodArity (zxnNormalForm 2 1 zxnFireCopyPairMatrix)) 1
      = true := rfl

/-- FIRE 1: its denotation is span-equal to the input subspace (kernel). -/
theorem zxnFireCopyPairDenotes :
    zxpSpanEqB (zxpDiagramDenote (zxnNormalForm 2 1 zxnFireCopyPairMatrix))
      zxnFireCopyPairMatrix = true := rfl

/-- FIRE 2 input: the xor-graph relation at boundary 2 -> 1 (span of
`[1,0,1], [0,1,1]`: relates `(a,b) ~ a+b`). -/
def zxnFireXorGraphMatrix : List (List Bool) :=
  [[true, false, true], [false, true, true]]

/-- FIRE 2: the normal form of the xor-graph subspace is executably well-formed
(kernel). -/
theorem zxnFireXorGraphWFB :
    zxpDiagramWFB (zxnNormalForm 2 1 zxnFireXorGraphMatrix) = true := rfl

/-- FIRE 2: its target arity is 1 (kernel). -/
theorem zxnFireXorGraphCodPin :
    zxpNatEqB (zxpDiagramCodArity (zxnNormalForm 2 1 zxnFireXorGraphMatrix)) 1
      = true := rfl

set_option maxRecDepth 8192 in
/-- FIRE 2: its denotation is span-equal to the input subspace (kernel). -/
theorem zxnFireXorGraphDenotes :
    zxpSpanEqB (zxpDiagramDenote (zxnNormalForm 2 1 zxnFireXorGraphMatrix))
      zxnFireXorGraphMatrix = true := rfl

set_option maxRecDepth 8192 in
/-- NEGATIVE CONTROL: two distinct subspaces at the same boundary (span `[1,1,1]`
vs span `[1,0,1]` at 2 -> 1) produce span-DISTINCT normal forms (kernel). -/
theorem zxnFireNegativeControl :
    zxpSpanEqB (zxpDiagramDenote (zxnNormalForm 2 1 [[true, true, true]]))
      (zxpDiagramDenote (zxnNormalForm 2 1 [[true, false, true]])) = false := rfl

#eval (zxnAllRrefMatrices 2).length
#eval (zxnAllRrefMatrices 3).length
#eval (zxnAllRrefMatrices 4).length
#eval zxnCensusSurjectivityB 2 2 (zxnAllRrefMatrices 4)
#eval zxnAllPairsSpanDistinctB (zxnAllRrefMatrices 4)

/-- (A) MARKER: the Z-X normal-form family is shipped — `zxnNormalForm` with
well-formedness (`zxnNormalFormWF`), boundary arities (`zxnNormalFormBoundaries`),
and THE STRUCTURAL DENOTATION THEOREM (`zxnNormalFormDenotes`: the diagram's
relation is `ZxpRelEquiv`-equal to the input generator matrix, at every boundary
and every generator list — proven through the seed's compose/tensor/id specs,
not by kernel evaluation). -/
def zxnHasNormalFormFamily : Bool := true

/-- (B) MARKER: THE CENSUS IS COMPLETE at the commissioned boundaries
(1,1), (1,2), (2,1), (2,2) — every enumerated RREF subspace (5 + 16 + 16 + 67 = 104)
has a well-formed normal form with the right boundaries whose denotation is
span-equal to it (surjectivity pins, kernel), the enumerations are pairwise
span-distinct (injectivity pins, kernel), and `zxnNormalFormInjective` PROVES that
span-distinct inputs give span-distinct normal forms.  HONEST SCOPE: this clears
the DENOTATIONAL half of the census gate recorded in `zxrCompletenessStatement`'s
docstring (items: NF enumeration + distinct-NFs-have-distinct-spans); the gate's
REACHABILITY item — machine-checking that every census diagram reaches its normal
form by `ZxrConv` moves — remains OPEN, blocked exactly at the right-first
exchange wall (see `NormalFormLadder.lean` for the ladder pieces and the honest
bill); the completeness induction itself is NOT attempted here. -/
def zxnCensusComplete : Bool := true

end FX1Poly.Polygraph.Omega.ZXPhaseFree
