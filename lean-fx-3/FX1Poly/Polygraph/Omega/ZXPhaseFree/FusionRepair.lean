import FX1Poly.Polygraph.Omega.ZXPhaseFree.SpiderRelationSeed
import FX1Poly.Polygraph.Omega.ZXPhaseFree.CompletenessGate

/-! # Polygraph/Omega/ZXPhaseFree/FusionRepair — REPAIR ROUTE R1: the fusion row family

The repair commissioned by `CompletenessGate.lean` header option (R1): the seed's 33-row
presentation UNDERSHOOTS because `ZxpCell` carries arbitrary-arity primitive spiders while
every published row touches only <= 3-leg spiders — the big-spider count separated
span-equal diagrams (`zxgCompletenessRefuted`).  This brick extends the congruence with
THE ARITY-INDEXED FUSION ROW FAMILY and re-runs the invariant gate.

## The chosen fusion schema (per the literature brief)

**R1 (one-wire fusion), the single indexed schema, both colours:**

    [[zSpider a (b+1), wire^c]] ; [[wire^b, zSpider (1+c) d]]  ~  [[zSpider (a+c) (b+d)]]

(`a` = `topInputs`, `b` = `topSpares`, `c` = `botSpares`, `d` = `botOutputs`; the fusion
wire is the LAST output of the top spider = the FIRST input of the bottom spider; the
spare legs pass through on wires).  Read backwards it is fission.  R2 (specialness,
`[[zSpider 1 2]];[[zSpider 2 1]] ~ [[zSpider 1 1]]`) and R3 (the identity spider
`[[zSpider 1 1]] ~ [[wire]]`) are NOT R1 instances — they are already seed rows
(`specialZ`/`specialX` compose with `zIdentitySpider`/`xIdentitySpider` to give R2).

**Why this is the minimal generating schema (the brief's recursion, documented, not
formalized):** a general adjacent k-wire fusion `zxSpider a (b+k)` over `zxSpider (k+c) d`
reduces to R1 + specialness + identity rows by (i) fissioning the top spider by reverse
R1(a, b, 0, k) into `zxSpider a (b+1)` feeding a hub `zxSpider 1 k`; (ii) dually fissioning
the bottom to expose the hub `zxSpider k 1`; (iii) collapsing the hub pair
`[[zxSpider 1 k]];[[zxSpider k 1]]` by induction on k — fission off the last two parallel
wires as `[[wire^(k-1), zxSpider 1 2]];[[wire^(k-1), zxSpider 2 1]]`, kill the right block
by specialness + identity-spider, recurse to k-1; the base k=1 is an R1 instance; and
(iv) refusing the hubs into the cores by R1.  Unit absorption is R1 with a = 0 (top
spider `zxSpider 0 1`).  Kissinger gets leg-permutation invariance for free from the
graphical convention; the strict-layer syntax supplies it through the seed's crossing
rows (`zMonoidComm`/`zComonoidCocomm` and mirrors) plus the splitLayer exchange.
Sources: Kissinger arXiv:2204.14038 Fig. 1 (sp)+(id); BSZ arXiv:1403.7048 p. 13 (n-ary
nodes as notation, `mu_{n+1} = (mu_n (x) id) ; mu`, "harmless by (A6)"), (W3)/(W4)
Frobenius + D11 special — fusion is the spider THEOREM there, a row family here because
the syntax has primitive n-ary spiders.

## Deliverables

* (A) `ZxrWindowMove` (seed embed + `zFuse`/`xFuse` at all arities), `ZxrStep` (the
  seed's pad combinator verbatim), `ZxrConv` (same groupoid closure shape).
* (B) `zxrConvSound` in the exact bundle shape of the seed's `zxpConvSound`; the fusion
  bundle is a REAL all-arity proof: the F2 span of a copy (resp. parity) spider is
  characterized once and for all (`zxrCopySpanIff` / `zxrParitySpanIff`, induction on
  width), and the one-wire relational composite is computed through the seed's
  `zxpComposeSpec`/`zxpTensorSpec`/`zxpIdSpec` — copy-of-copy is copy, add-of-add is add.
  Refutation bridge `zxrConvSpanEqB`; every seed conversion embeds (`zxrOfZxpConv`).
* (C) THE SEPARATOR DIES: `zxrFusedChainedConv` converts the gate's refuted pair
  (fused triple vs chained pair), `zxrXQuadConv` the X-colour 4->1 three-layer analogue;
  `zxrProperExtensionWitness` pins that `ZxrConv` PROPERLY extends `ZxpConv`.  Extra
  fires: `zxrZUnitAbsorptionConv` (the brief's unit absorption = R1 at a = 0),
  `zxrTwoWireFusionDemo` (the k = 2 adjacent-wire fusion derived by the brief's
  recursion: fission + specialness + identity-layer strip), and the FALSE case
  `zxrBigColourNotConv` (the refutation instrument still bites at big arity:
  `[[zSpider 4 1]]` vs `[[xSpider 4 1]]` are span-distinct, hence not convertible).
* (D) THE GATE RE-RUN (refutation pass before any completeness push): the fold engine
  generalized (`zxrConvFoldEq`), the old separator kernel-pinned UNBALANCED on the fusion
  family, the base-count delta table extended by the fusion family with a PROVED
  saturation lemma (`zxrZFuseDeltaGeneral`/`zxrXFuseDeltaGeneral`), the 128-functional
  preserved lattice re-classified (still exactly {0, legs-parity}, boundary-determined),
  and THE COLLAPSE THEOREM `zxrBalancedWeightCollapse`: every wire-vanishing cell weight
  balanced on the extended move set is IDENTICALLY ZERO — the whole per-cell count
  family (where the old separator lived) holds no separator.  Verdict: GATE CLEAN
  (outcome (b)); `zxrCompletenessStatement` minted owner-false with the census
  requirement recorded.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`, no
`Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive scrutinees. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — the all-true / parity / chunk kit (fresh, cons-only)

The seed ships `zxpAllFalse` with take/xor algebra; the fusion characterizations need the
mirror `zxrAllTrue`, the row parity fold, and the prefix-aware take/drop/cat algebra that
connects the two boundary decompositions of the shared middle layer. -/

/-- Is every bit true?  (Mirror of the seed's `zxpAllFalse`.) -/
def zxrAllTrue : List Bool -> Bool
  | [] => true
  | false :: _restBits => false
  | true :: restBits => zxrAllTrue restBits

theorem zxrAllTrueAllOnesRow : (width : Nat) -> zxrAllTrue (zxpAllOnesRow width) = true
  | 0 => rfl
  | widthPred + 1 => zxrAllTrueAllOnesRow widthPred

theorem zxrAllTrueToAllOnesRow : (row : List Bool) -> zxrAllTrue row = true ->
    row = zxpAllOnesRow row.length
  | [], _hAllT => rfl
  | false :: _restBits, hAllT => Bool.noConfusion hAllT
  | true :: restBits, hAllT =>
      congrArg (fun innerRow => true :: innerRow) (zxrAllTrueToAllOnesRow restBits hAllT)

theorem zxrAllTrueCatSplitLeft : (frontRow backRow : List Bool) ->
    zxrAllTrue (zxpCat frontRow backRow) = true -> zxrAllTrue frontRow = true
  | [], _backRow, _hAllT => rfl
  | false :: _frontRest, _backRow, hAllT => Bool.noConfusion hAllT
  | true :: frontRest, backRow, hAllT => zxrAllTrueCatSplitLeft frontRest backRow hAllT

theorem zxrAllTrueCatSplitRight : (frontRow backRow : List Bool) ->
    zxrAllTrue (zxpCat frontRow backRow) = true -> zxrAllTrue backRow = true
  | [], _backRow, hAllT => hAllT
  | false :: _frontRest, _backRow, hAllT => Bool.noConfusion hAllT
  | true :: frontRest, backRow, hAllT => zxrAllTrueCatSplitRight frontRest backRow hAllT

theorem zxrAllTrueCatIntro : (frontRow backRow : List Bool) ->
    zxrAllTrue frontRow = true -> zxrAllTrue backRow = true ->
    zxrAllTrue (zxpCat frontRow backRow) = true
  | [], _backRow, _hFront, hBack => hBack
  | false :: _frontRest, _backRow, hFront, _hBack => Bool.noConfusion hFront
  | true :: frontRest, backRow, hFront, hBack =>
      zxrAllTrueCatIntro frontRest backRow hFront hBack

theorem zxrAllFalseCatSplitLeft : (frontRow backRow : List Bool) ->
    zxpAllFalse (zxpCat frontRow backRow) = true -> zxpAllFalse frontRow = true
  | [], _backRow, _hAllF => rfl
  | true :: _frontRest, _backRow, hAllF => Bool.noConfusion hAllF
  | false :: frontRest, backRow, hAllF => zxrAllFalseCatSplitLeft frontRest backRow hAllF

theorem zxrAllFalseCatSplitRight : (frontRow backRow : List Bool) ->
    zxpAllFalse (zxpCat frontRow backRow) = true -> zxpAllFalse backRow = true
  | [], _backRow, hAllF => hAllF
  | true :: _frontRest, _backRow, hAllF => Bool.noConfusion hAllF
  | false :: frontRest, backRow, hAllF => zxrAllFalseCatSplitRight frontRest backRow hAllF

theorem zxrAllFalseCatIntro : (frontRow backRow : List Bool) ->
    zxpAllFalse frontRow = true -> zxpAllFalse backRow = true ->
    zxpAllFalse (zxpCat frontRow backRow) = true
  | [], _backRow, _hFront, hBack => hBack
  | true :: _frontRest, _backRow, hFront, _hBack => Bool.noConfusion hFront
  | false :: frontRest, backRow, hFront, hBack =>
      zxrAllFalseCatIntro frontRest backRow hFront hBack

theorem zxrAllFalseDropN : (row : List Bool) -> zxpAllFalse row = true -> (count : Nat) ->
    zxpAllFalse (zxpDropN count row) = true
  | _row, hAllF, 0 => hAllF
  | [], hAllF, _countPred + 1 => hAllF
  | true :: _restBits, hAllF, _countPred + 1 => Bool.noConfusion hAllF
  | false :: restBits, hAllF, countPred + 1 => zxrAllFalseDropN restBits hAllF countPred

theorem zxrAllTrueTakeN : (row : List Bool) -> zxrAllTrue row = true -> (count : Nat) ->
    zxrAllTrue (zxpTakeN count row) = true
  | _row, _hAllT, 0 => rfl
  | [], _hAllT, _countPred + 1 => rfl
  | false :: _restBits, hAllT, _countPred + 1 => Bool.noConfusion hAllT
  | true :: restBits, hAllT, countPred + 1 => zxrAllTrueTakeN restBits hAllT countPred

theorem zxrAllTrueDropN : (row : List Bool) -> zxrAllTrue row = true -> (count : Nat) ->
    zxrAllTrue (zxpDropN count row) = true
  | _row, hAllT, 0 => hAllT
  | [], hAllT, _countPred + 1 => hAllT
  | false :: _restBits, hAllT, _countPred + 1 => Bool.noConfusion hAllT
  | true :: restBits, hAllT, countPred + 1 => zxrAllTrueDropN restBits hAllT countPred

/-- A row that is simultaneously all-false and all-true is empty (the mixed-colour
contradiction chunk of the fusion glue). -/
theorem zxrAllFalseAllTrueNil : (row : List Bool) -> zxpAllFalse row = true ->
    zxrAllTrue row = true -> row = []
  | [], _hAllF, _hAllT => rfl
  | true :: _restBits, hAllF, _hAllT => Bool.noConfusion hAllF
  | false :: _restBits, _hAllF, hAllT => Bool.noConfusion hAllT

/-- Concatenating all-ones rows (mirror of the seed's `zxpCatZeroZero`). -/
theorem zxrCatAllOnes : (frontWidth backWidth : Nat) ->
    zxpCat (zxpAllOnesRow frontWidth) (zxpAllOnesRow backWidth)
      = zxpAllOnesRow (frontWidth + backWidth)
  | 0, backWidth => by rw [Nat.zero_add]; rfl
  | frontPred + 1, backWidth => by
      show true :: zxpCat (zxpAllOnesRow frontPred) (zxpAllOnesRow backWidth)
        = zxpAllOnesRow (frontPred + 1 + backWidth)
      rw [Nat.succ_add frontPred backWidth]
      show true :: zxpCat (zxpAllOnesRow frontPred) (zxpAllOnesRow backWidth)
        = true :: zxpAllOnesRow (frontPred + backWidth)
      rw [zxrCatAllOnes frontPred backWidth]

/-- Taking only a PREFIX of the front block of a concatenation stays inside the front
block. -/
theorem zxrTakeNCatOfPrefix : (frontRow backRow : List Bool) ->
    (frontWidth extraLen : Nat) -> frontRow.length = frontWidth + extraLen ->
    zxpTakeN frontWidth (zxpCat frontRow backRow) = zxpTakeN frontWidth frontRow
  | _frontRow, _backRow, 0, _extraLen, _hLen => rfl
  | [], _backRow, frontPred + 1, extraLen, hLen => by
      rw [Nat.succ_add frontPred extraLen] at hLen
      exact nomatch hLen
  | headBit :: frontRest, backRow, frontPred + 1, extraLen, hLen => by
      show headBit :: zxpTakeN frontPred (zxpCat frontRest backRow)
        = headBit :: zxpTakeN frontPred frontRest
      rw [Nat.succ_add frontPred extraLen] at hLen
      rw [zxrTakeNCatOfPrefix frontRest backRow frontPred extraLen (Nat.succ.inj hLen)]

/-- Dropping only a PREFIX of the front block of a concatenation keeps the back block. -/
theorem zxrDropNCatOfPrefix : (frontRow backRow : List Bool) ->
    (frontWidth extraLen : Nat) -> frontRow.length = frontWidth + extraLen ->
    zxpDropN frontWidth (zxpCat frontRow backRow)
      = zxpCat (zxpDropN frontWidth frontRow) backRow
  | _frontRow, _backRow, 0, _extraLen, _hLen => rfl
  | [], _backRow, frontPred + 1, extraLen, hLen => by
      rw [Nat.succ_add frontPred extraLen] at hLen
      exact nomatch hLen
  | _headBit :: frontRest, backRow, frontPred + 1, extraLen, hLen => by
      show zxpDropN frontPred (zxpCat frontRest backRow)
        = zxpCat (zxpDropN frontPred frontRest) backRow
      rw [Nat.succ_add frontPred extraLen] at hLen
      exact zxrDropNCatOfPrefix frontRest backRow frontPred extraLen (Nat.succ.inj hLen)

/-! ### The row parity fold (the X/parity spider invariant) -/

/-- Parity (xor-fold) of a row. -/
def zxrRowParity : List Bool -> Bool
  | [] => false
  | headBit :: restBits => zxpXorB headBit (zxrRowParity restBits)

theorem zxrRowParityZeroRow : (width : Nat) -> zxrRowParity (zxpZeroRow width) = false
  | 0 => rfl
  | widthPred + 1 => by
      show zxpXorB false (zxrRowParity (zxpZeroRow widthPred)) = false
      rw [zxpXorBFalseLeft, zxrRowParityZeroRow widthPred]

theorem zxrRowParityCat : (frontRow backRow : List Bool) ->
    zxrRowParity (zxpCat frontRow backRow)
      = zxpXorB (zxrRowParity frontRow) (zxrRowParity backRow)
  | [], backRow => (zxpXorBFalseLeft (zxrRowParity backRow)).symm
  | headBit :: frontRest, backRow => by
      show zxpXorB headBit (zxrRowParity (zxpCat frontRest backRow))
        = zxpXorB (zxpXorB headBit (zxrRowParity frontRest)) (zxrRowParity backRow)
      rw [zxrRowParityCat frontRest backRow,
        zxpXorBAssoc headBit (zxrRowParity frontRest) (zxrRowParity backRow)]

theorem zxrRowParityXor : (firstRow secondRow : List Bool) ->
    firstRow.length = secondRow.length ->
    zxrRowParity (zxpRowXor firstRow secondRow)
      = zxpXorB (zxrRowParity firstRow) (zxrRowParity secondRow)
  | [], [], _hLen => rfl
  | [], _secondBit :: _secondRest, hLen => nomatch hLen
  | _firstBit :: _firstRest, [], hLen => nomatch hLen
  | firstBit :: firstRest, secondBit :: secondRest, hLen => by
      show zxpXorB (zxpXorB firstBit secondBit)
          (zxrRowParity (zxpRowXor firstRest secondRest))
        = zxpXorB (zxpXorB firstBit (zxrRowParity firstRest))
            (zxpXorB secondBit (zxrRowParity secondRest))
      rw [zxrRowParityXor firstRest secondRest (Nat.succ.inj hLen)]
      exact zxgXorBMedial firstBit secondBit (zxrRowParity firstRest)
        (zxrRowParity secondRest)

/-! ### Xor truth tables for the fusion glue -/

/-- Xor equal to false forces equality. -/
theorem zxrXorBEqOfXorFalse : (leftBit rightBit : Bool) ->
    zxpXorB leftBit rightBit = false -> leftBit = rightBit
  | false, false, _hXor => rfl
  | false, true, hXor => Bool.noConfusion hXor
  | true, false, hXor => Bool.noConfusion hXor
  | true, true, _hXor => rfl

/-- `u + (v + (u + v)) = 0` in F2 (the mid-bit witness cancellation). -/
theorem zxrXorBReturnFalse : (leftBit rightBit : Bool) ->
    zxpXorB leftBit (zxpXorB rightBit (zxpXorB leftBit rightBit)) = false
  | false, false => rfl
  | false, true => rfl
  | true, false => rfl
  | true, true => rfl

/-- `((u+v)+w) + (u+(v+w)) = 0` in F2 (both associations cancel — the X-fusion glue). -/
theorem zxrXorBBothPairsFalse : (firstBit secondBit thirdBit : Bool) ->
    zxpXorB (zxpXorB (zxpXorB firstBit secondBit) thirdBit)
        (zxpXorB firstBit (zxpXorB secondBit thirdBit)) = false
  | false, false, false => rfl
  | false, false, true => rfl
  | false, true, false => rfl
  | false, true, true => rfl
  | true, false, false => rfl
  | true, false, true => rfl
  | true, true, false => rfl
  | true, true, true => rfl

/-! ## Stage 1 — the spider span characterizations (all arities, induction on width)

The copy (Z) spider at total width `w` spans exactly {all-false, all-true}; the parity
(X) spider spans exactly the even-parity subspace.  These two theorems are the
`copy-of-copy is copy` engine room: every fusion soundness obligation reduces to them. -/

/-- COPY SPAN, forward: members of the Z-spider span are all-false or all-true. -/
theorem zxrCopySpanSound {width : Nat} {vector : List Bool}
    (hMem : ZxpMemSpan width (zxpSpiderCopyRows width) vector) :
    zxpAllFalse vector = true \/ zxrAllTrue vector = true := by
  induction hMem with
  | zero => exact Or.inl (zxpAllFalseZeroRow width)
  | pick row hRow hVec innerDisj =>
      cases width with
      | zero => exact nomatch hRow
      | succ widthPred =>
          have hRowEq : row = zxpAllOnesRow (widthPred + 1) := by
            cases hRow with
            | head => rfl
            | tail hRest => exact nomatch hRest
          have hVecLen := zxpMemSpanWidth (zxpSpiderCopyRowsWidth (widthPred + 1)) hVec
          cases innerDisj with
          | inl hAllF =>
              have hVecZero := zxpAllFalseToZeroRow _ hAllF
              rw [hRowEq, hVecZero, hVecLen,
                zxpRowXorZeroRight (zxpAllOnesRow (widthPred + 1)) (widthPred + 1)
                  (zxpAllOnesRowLength (widthPred + 1))]
              exact Or.inr (zxrAllTrueAllOnesRow (widthPred + 1))
          | inr hAllT =>
              have hVecOnes := zxrAllTrueToAllOnesRow _ hAllT
              rw [hRowEq, hVecOnes, hVecLen, zxpRowXorSelf (zxpAllOnesRow (widthPred + 1)),
                zxpAllOnesRowLength (widthPred + 1)]
              exact Or.inl (zxpAllFalseZeroRow (widthPred + 1))

/-- COPY SPAN, backward: all-false and all-true rows of the right length are members. -/
theorem zxrCopySpanComplete : (width : Nat) -> (vector : List Bool) ->
    vector.length = width ->
    (zxpAllFalse vector = true \/ zxrAllTrue vector = true) ->
    ZxpMemSpan width (zxpSpiderCopyRows width) vector := by
  intro width vector hLen hDisj
  cases hDisj with
  | inl hAllF =>
      have hVecZero := zxpAllFalseToZeroRow vector hAllF
      rw [hVecZero, hLen]
      exact ZxpMemSpan.zero
  | inr hAllT =>
      have hVecOnes := zxrAllTrueToAllOnesRow vector hAllT
      rw [hVecOnes, hLen]
      cases width with
      | zero => exact ZxpMemSpan.zero
      | succ widthPred =>
          have hPicked := ZxpMemSpan.pick (zxpAllOnesRow (widthPred + 1))
            (ZxpRowMem.head (zxpAllOnesRow (widthPred + 1)) [])
            (ZxpMemSpan.zero (width := widthPred + 1)
              (rows := zxpSpiderCopyRows (widthPred + 1)))
          rw [zxpRowXorZeroRight (zxpAllOnesRow (widthPred + 1)) (widthPred + 1)
            (zxpAllOnesRowLength (widthPred + 1))] at hPicked
          exact hPicked

/-- Every parity-spider generator row has even parity. -/
theorem zxrParityRowsRowEven : (width : Nat) -> (row : List Bool) ->
    ZxpRowMem row (zxpParityRows width) -> zxrRowParity row = false
  | 0, _row, hRow => nomatch hRow
  | 1, _row, hRow => nomatch hRow
  | widthPred + 2, row, hRow => by
      cases hRow with
      | head =>
          show zxpXorB true (zxpXorB true (zxrRowParity (zxpZeroRow widthPred))) = false
          rw [zxrRowParityZeroRow widthPred]
          rfl
      | tail hRest =>
          have hInner := zxpMapRowsMemInv (fun innerRow => false :: innerRow)
            (zxpParityRows (widthPred + 1)) hRest
          cases hInner with
          | intro sourceRow hBoth =>
              rw [hBoth.right]
              show zxpXorB false (zxrRowParity sourceRow) = false
              rw [zxpXorBFalseLeft,
                zxrParityRowsRowEven (widthPred + 1) sourceRow hBoth.left]

/-- PARITY SPAN, forward: members of the X-spider span have even parity. -/
theorem zxrParitySpanSound {width : Nat} {vector : List Bool}
    (hMem : ZxpMemSpan width (zxpParityRows width) vector) :
    zxrRowParity vector = false := by
  induction hMem with
  | zero => exact zxrRowParityZeroRow width
  | pick row hRow hVec innerParity =>
      rw [zxrRowParityXor row _ (by
          rw [zxpAllWidthRow (zxpParityRowsWidth width) hRow,
            zxpMemSpanWidth (zxpParityRowsWidth width) hVec]),
        zxrParityRowsRowEven width row hRow, innerParity]
      rfl

/-- PARITY SPAN, backward: every even-parity row of the right length is a member
(induction on the width; the head-true case flips the next bit through the leading
consecutive-pair generator).  The top-level match splits ONLY the width (`0 | 1 | _+2`,
the audited-clean `zxpParityRows` shape); the vector and head-bit splits live in `cases`
tactics — a ragged mixed-column pattern match here compiles to a propext-bearing
splitter. -/
theorem zxrParitySpanComplete : (width : Nat) -> (vector : List Bool) ->
    vector.length = width -> zxrRowParity vector = false ->
    ZxpMemSpan width (zxpParityRows width) vector
  | 0, vector, hLen, _hParity => by
      cases vector with
      | nil => exact ZxpMemSpan.zero
      | cons headBit restBits => exact nomatch hLen
  | 1, vector, hLen, hParity => by
      cases vector with
      | nil => exact nomatch hLen
      | cons headBit restBits =>
          cases restBits with
          | cons secondBit tailBits => exact Nat.noConfusion (Nat.succ.inj hLen)
          | nil =>
              have hHeadFalse : headBit = false := by
                have hParity2 : zxpXorB headBit false = false := hParity
                rw [zxpXorBFalseRight headBit] at hParity2
                exact hParity2
              rw [hHeadFalse]
              exact ZxpMemSpan.zero (width := 1) (rows := zxpParityRows 1)
  | widthPred + 2, vector, hLen, hParity => by
      cases vector with
      | nil => exact nomatch hLen
      | cons headBit restBits =>
          cases headBit with
          | false =>
              have hRestLen : restBits.length = widthPred + 1 := Nat.succ.inj hLen
              have hRestParity : zxrRowParity restBits = false := by
                have hParity2 : zxpXorB false (zxrRowParity restBits) = false := hParity
                rw [zxpXorBFalseLeft] at hParity2
                exact hParity2
              have hInnerMem := zxrParitySpanComplete (widthPred + 1) restBits hRestLen
                hRestParity
              have hMapped := zxpMapRowsSpanBwd (sourceWidth := widthPred + 1)
                (targetWidth := widthPred + 2) (fun innerRow => false :: innerRow) rfl
                (fun _firstRow _secondRow _hFirstLen _hSecondLen => rfl)
                (zxpParityRowsWidth (widthPred + 1)) hInnerMem
              exact zxpMemSpanWeaken (true :: true :: zxpZeroRow widthPred) hMapped
          | true =>
              cases restBits with
              | nil => exact Nat.noConfusion (Nat.succ.inj hLen)
              | cons secondBit tailBits =>
                  have hTailLen : tailBits.length = widthPred :=
                    Nat.succ.inj (Nat.succ.inj hLen)
                  have hFlipParity :
                      zxrRowParity (zxpXorB true secondBit :: tailBits) = false := by
                    show zxpXorB (zxpXorB true secondBit) (zxrRowParity tailBits) = false
                    rw [zxpXorBAssoc true secondBit (zxrRowParity tailBits)]
                    exact hParity
                  have hInnerMem := zxrParitySpanComplete (widthPred + 1)
                    (zxpXorB true secondBit :: tailBits)
                    (congrArg (fun innerValue => innerValue + 1) hTailLen) hFlipParity
                  have hMapped := zxpMapRowsSpanBwd (sourceWidth := widthPred + 1)
                    (targetWidth := widthPred + 2) (fun innerRow => false :: innerRow) rfl
                    (fun _firstRow _secondRow _hFirstLen _hSecondLen => rfl)
                    (zxpParityRowsWidth (widthPred + 1)) hInnerMem
                  have hWeakened := zxpMemSpanWeaken
                    (true :: true :: zxpZeroRow widthPred) hMapped
                  have hPicked := ZxpMemSpan.pick (true :: true :: zxpZeroRow widthPred)
                    (ZxpRowMem.head (true :: true :: zxpZeroRow widthPred) _) hWeakened
                  have hXorEq : zxpRowXor (true :: true :: zxpZeroRow widthPred)
                      (false :: zxpXorB true secondBit :: tailBits)
                      = true :: secondBit :: tailBits := by
                    show zxpXorB true false
                        :: zxpXorB true (zxpXorB true secondBit)
                        :: zxpRowXor (zxpZeroRow widthPred) tailBits
                      = true :: secondBit :: tailBits
                    rw [zxpRowXorZeroLeft tailBits widthPred hTailLen,
                      <- zxpXorBAssoc true true secondBit]
                    show true :: zxpXorB (zxpXorB true true) secondBit :: tailBits
                      = true :: secondBit :: tailBits
                    rw [zxpXorBSelf true, zxpXorBFalseLeft secondBit]
                  rw [hXorEq] at hPicked
                  exact hPicked

/-! ### The boundary-paired characterizations -/

/-- The copy-relation predicate: both boundary vectors share one constant bit value. -/
def ZxrCopyPair (domWidth codWidth : Nat) (domVec codVec : List Bool) : Prop :=
  domVec.length = domWidth /\ codVec.length = codWidth
    /\ (zxpAllFalse (zxpCat domVec codVec) = true
        \/ zxrAllTrue (zxpCat domVec codVec) = true)

/-- The add-relation predicate: the two boundary vectors have equal total parity. -/
def ZxrAddPair (domWidth codWidth : Nat) (domVec codVec : List Bool) : Prop :=
  domVec.length = domWidth /\ codVec.length = codWidth
    /\ zxrRowParity (zxpCat domVec codVec) = false

/-- The Z spider's relation IS the copy predicate, at every boundary. -/
theorem zxrCopyPairMemIff (domWidth codWidth : Nat) (domVec codVec : List Bool) :
    ZxpPairMem domWidth codWidth (zxpSpiderCopyRows (domWidth + codWidth)) domVec codVec
      <-> ZxrCopyPair domWidth codWidth domVec codVec := by
  refine Iff.intro ?_ ?_
  · intro hPair
    exact And.intro hPair.left (And.intro hPair.right.left
      (zxrCopySpanSound hPair.right.right))
  · intro hCopy
    refine And.intro hCopy.left (And.intro hCopy.right.left ?_)
    refine zxrCopySpanComplete (domWidth + codWidth) (zxpCat domVec codVec) ?_
      hCopy.right.right
    rw [zxpCatLength, hCopy.left, hCopy.right.left]

/-- The X spider's relation IS the add predicate, at every boundary. -/
theorem zxrAddPairMemIff (domWidth codWidth : Nat) (domVec codVec : List Bool) :
    ZxpPairMem domWidth codWidth (zxpParityRows (domWidth + codWidth)) domVec codVec
      <-> ZxrAddPair domWidth codWidth domVec codVec := by
  refine Iff.intro ?_ ?_
  · intro hPair
    exact And.intro hPair.left (And.intro hPair.right.left
      (zxrParitySpanSound hPair.right.right))
  · intro hAdd
    refine And.intro hAdd.left (And.intro hAdd.right.left ?_)
    refine zxrParitySpanComplete (domWidth + codWidth) (zxpCat domVec codVec) ?_
      hAdd.right.right
    rw [zxpCatLength, hAdd.left, hAdd.right.left]

/-! ## Stage 2 — THE FUSION ROW FAMILY (schema R1, both colours, all arities)

`topInputs`/`topSpares`/`botSpares`/`botOutputs` are the brief's `a`/`b`/`c`/`d`: the top
spider keeps `topInputs` boundary inputs and `topSpares` pass-down outputs; the bottom
spider keeps `botSpares` pass-through inputs and `botOutputs` boundary outputs; ONE wire
(the top spider's last output = the bottom spider's first input) fuses. -/

/-- One-wire Z fusion, LEFT side: `[[zSpider a (b+1), wire^c]] ; [[wire^b, zSpider (1+c) d]]`. -/
def zxrZFuseLhs (topInputs topSpares botSpares botOutputs : Nat) : ZxpDiagram :=
  { sourceArity := topInputs + botSpares
    layers := [ZxpCell.zSpider topInputs (topSpares + 1) :: zxpWireCells botSpares,
      zxpCatCells (zxpWireCells topSpares)
        [ZxpCell.zSpider (1 + botSpares) botOutputs]] }

/-- One-wire Z fusion, RIGHT side: `[[zSpider (a+c) (b+d)]]`. -/
def zxrZFuseRhs (topInputs topSpares botSpares botOutputs : Nat) : ZxpDiagram :=
  { sourceArity := topInputs + botSpares
    layers := [[ZxpCell.zSpider (topInputs + botSpares) (topSpares + botOutputs)]] }

/-- One-wire X fusion, LEFT side (colour mirror). -/
def zxrXFuseLhs (topInputs topSpares botSpares botOutputs : Nat) : ZxpDiagram :=
  { sourceArity := topInputs + botSpares
    layers := [ZxpCell.xSpider topInputs (topSpares + 1) :: zxpWireCells botSpares,
      zxpCatCells (zxpWireCells topSpares)
        [ZxpCell.xSpider (1 + botSpares) botOutputs]] }

/-- One-wire X fusion, RIGHT side (colour mirror). -/
def zxrXFuseRhs (topInputs topSpares botSpares botOutputs : Nat) : ZxpDiagram :=
  { sourceArity := topInputs + botSpares
    layers := [[ZxpCell.xSpider (topInputs + botSpares) (topSpares + botOutputs)]] }

/-! ### Boundary arities and well-formedness of the family -/

theorem zxrZFuseLhsCodArity (topInputs topSpares botSpares botOutputs : Nat) :
    zxpDiagramCodArity (zxrZFuseLhs topInputs topSpares botSpares botOutputs)
      = topSpares + botOutputs := by
  show zxpLayerCodArity (zxpCatCells (zxpWireCells topSpares)
      [ZxpCell.zSpider (1 + botSpares) botOutputs]) = topSpares + botOutputs
  rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
  rfl

theorem zxrZFuseRhsCodArity (topInputs topSpares botSpares botOutputs : Nat) :
    zxpDiagramCodArity (zxrZFuseRhs topInputs topSpares botSpares botOutputs)
      = topSpares + botOutputs := rfl

theorem zxrXFuseLhsCodArity (topInputs topSpares botSpares botOutputs : Nat) :
    zxpDiagramCodArity (zxrXFuseLhs topInputs topSpares botSpares botOutputs)
      = topSpares + botOutputs := by
  show zxpLayerCodArity (zxpCatCells (zxpWireCells topSpares)
      [ZxpCell.xSpider (1 + botSpares) botOutputs]) = topSpares + botOutputs
  rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
  rfl

theorem zxrXFuseRhsCodArity (topInputs topSpares botSpares botOutputs : Nat) :
    zxpDiagramCodArity (zxrXFuseRhs topInputs topSpares botSpares botOutputs)
      = topSpares + botOutputs := rfl

theorem zxrZFuseLhsWF (topInputs topSpares botSpares botOutputs : Nat) :
    ZxpDiagramWF (zxrZFuseLhs topInputs topSpares botSpares botOutputs) := by
  refine ZxpLayersWF.cons ?_ (ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _))
  · show topInputs + zxpLayerDomArity (zxpWireCells botSpares) = topInputs + botSpares
    rw [zxpWireCellsDomArity]
  · show zxpLayerDomArity (zxpCatCells (zxpWireCells topSpares)
        [ZxpCell.zSpider (1 + botSpares) botOutputs])
      = (topSpares + 1) + zxpLayerCodArity (zxpWireCells botSpares)
    rw [zxpCatCellsDomArity, zxpWireCellsDomArity, zxpWireCellsCodArity]
    show topSpares + (1 + botSpares) = (topSpares + 1) + botSpares
    exact (Nat.add_assoc topSpares 1 botSpares).symm

theorem zxrZFuseRhsWF (topInputs topSpares botSpares botOutputs : Nat) :
    ZxpDiagramWF (zxrZFuseRhs topInputs topSpares botSpares botOutputs) :=
  ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)

theorem zxrXFuseLhsWF (topInputs topSpares botSpares botOutputs : Nat) :
    ZxpDiagramWF (zxrXFuseLhs topInputs topSpares botSpares botOutputs) := by
  refine ZxpLayersWF.cons ?_ (ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _))
  · show topInputs + zxpLayerDomArity (zxpWireCells botSpares) = topInputs + botSpares
    rw [zxpWireCellsDomArity]
  · show zxpLayerDomArity (zxpCatCells (zxpWireCells topSpares)
        [ZxpCell.xSpider (1 + botSpares) botOutputs])
      = (topSpares + 1) + zxpLayerCodArity (zxpWireCells botSpares)
    rw [zxpCatCellsDomArity, zxpWireCellsDomArity, zxpWireCellsCodArity]
    show topSpares + (1 + botSpares) = (topSpares + 1) + botSpares
    exact (Nat.add_assoc topSpares 1 botSpares).symm

theorem zxrXFuseRhsWF (topInputs topSpares botSpares botOutputs : Nat) :
    ZxpDiagramWF (zxrXFuseRhs topInputs topSpares botSpares botOutputs) :=
  ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)

/-! ### Denotation normal forms: each side as an explicit compose/tensor of spider rows -/

/-- The top fusion layer denotes `spider (x) id`. -/
theorem zxrZFuseTopLayerEquiv (topInputs topSpares botSpares : Nat) :
    ZxpRelEquiv (topInputs + botSpares) ((topSpares + 1) + botSpares)
      (zxpLayerDenote
        (ZxpCell.zSpider topInputs (topSpares + 1) :: zxpWireCells botSpares))
      (zxpTensorRows topInputs (topSpares + 1) botSpares botSpares
        (zxpSpiderCopyRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares)) := by
  show ZxpRelEquiv (topInputs + botSpares) ((topSpares + 1) + botSpares)
    (zxpTensorRows topInputs (topSpares + 1)
      (zxpLayerDomArity (zxpWireCells botSpares))
      (zxpLayerCodArity (zxpWireCells botSpares))
      (zxpSpiderCopyRows (topInputs + (topSpares + 1)))
      (zxpLayerDenote (zxpWireCells botSpares)))
    (zxpTensorRows topInputs (topSpares + 1) botSpares botSpares
      (zxpSpiderCopyRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares))
  rw [zxpWireCellsDomArity, zxpWireCellsCodArity]
  exact zxpTensorRowsCong topInputs (topSpares + 1) botSpares botSpares
    (zxpSpiderCopyRowsWidth (topInputs + (topSpares + 1)))
    (zxpSpiderCopyRowsWidth (topInputs + (topSpares + 1)))
    (zxpAllWidthCast (by rw [zxpWireCellsDomArity, zxpWireCellsCodArity])
      (zxpLayerDenoteWidth (zxpWireCells botSpares)))
    (zxpIdRowsWidth botSpares)
    (zxpRelEquivRefl topInputs (topSpares + 1)
      (zxpSpiderCopyRows (topInputs + (topSpares + 1))))
    (zxpWireCellsDenoteId botSpares)

/-- The bottom fusion layer denotes `id (x) spider`. -/
theorem zxrZFuseBotLayerEquiv (topSpares botSpares botOutputs : Nat) :
    ZxpRelEquiv (topSpares + (1 + botSpares)) (topSpares + botOutputs)
      (zxpLayerDenote (zxpCatCells (zxpWireCells topSpares)
        [ZxpCell.zSpider (1 + botSpares) botOutputs]))
      (zxpTensorRows topSpares topSpares (1 + botSpares) botOutputs
        (zxpIdRows topSpares) (zxpSpiderCopyRows ((1 + botSpares) + botOutputs))) := by
  have hSplit := zxpLayerDenoteCatSplit (zxpWireCells topSpares)
    [ZxpCell.zSpider (1 + botSpares) botOutputs]
  rw [zxpWireCellsDomArity, zxpWireCellsCodArity] at hSplit
  refine zxpRelEquivTrans hSplit ?_
  exact zxpTensorRowsCong topSpares topSpares (1 + botSpares) botOutputs
    (zxpAllWidthCast (by rw [zxpWireCellsDomArity, zxpWireCellsCodArity])
      (zxpLayerDenoteWidth (zxpWireCells topSpares)))
    (zxpIdRowsWidth topSpares)
    (zxpLayerDenoteWidth [ZxpCell.zSpider (1 + botSpares) botOutputs])
    (zxpSpiderCopyRowsWidth ((1 + botSpares) + botOutputs))
    (zxpWireCellsDenoteId topSpares)
    (zxpTensorUnitRight (1 + botSpares) botOutputs
      (zxpSpiderCopyRows ((1 + botSpares) + botOutputs))
      (zxpSpiderCopyRowsWidth ((1 + botSpares) + botOutputs)))

/-- The X-colour top fusion layer (mirror). -/
theorem zxrXFuseTopLayerEquiv (topInputs topSpares botSpares : Nat) :
    ZxpRelEquiv (topInputs + botSpares) ((topSpares + 1) + botSpares)
      (zxpLayerDenote
        (ZxpCell.xSpider topInputs (topSpares + 1) :: zxpWireCells botSpares))
      (zxpTensorRows topInputs (topSpares + 1) botSpares botSpares
        (zxpParityRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares)) := by
  show ZxpRelEquiv (topInputs + botSpares) ((topSpares + 1) + botSpares)
    (zxpTensorRows topInputs (topSpares + 1)
      (zxpLayerDomArity (zxpWireCells botSpares))
      (zxpLayerCodArity (zxpWireCells botSpares))
      (zxpParityRows (topInputs + (topSpares + 1)))
      (zxpLayerDenote (zxpWireCells botSpares)))
    (zxpTensorRows topInputs (topSpares + 1) botSpares botSpares
      (zxpParityRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares))
  rw [zxpWireCellsDomArity, zxpWireCellsCodArity]
  exact zxpTensorRowsCong topInputs (topSpares + 1) botSpares botSpares
    (zxpParityRowsWidth (topInputs + (topSpares + 1)))
    (zxpParityRowsWidth (topInputs + (topSpares + 1)))
    (zxpAllWidthCast (by rw [zxpWireCellsDomArity, zxpWireCellsCodArity])
      (zxpLayerDenoteWidth (zxpWireCells botSpares)))
    (zxpIdRowsWidth botSpares)
    (zxpRelEquivRefl topInputs (topSpares + 1)
      (zxpParityRows (topInputs + (topSpares + 1))))
    (zxpWireCellsDenoteId botSpares)

/-- The X-colour bottom fusion layer (mirror). -/
theorem zxrXFuseBotLayerEquiv (topSpares botSpares botOutputs : Nat) :
    ZxpRelEquiv (topSpares + (1 + botSpares)) (topSpares + botOutputs)
      (zxpLayerDenote (zxpCatCells (zxpWireCells topSpares)
        [ZxpCell.xSpider (1 + botSpares) botOutputs]))
      (zxpTensorRows topSpares topSpares (1 + botSpares) botOutputs
        (zxpIdRows topSpares) (zxpParityRows ((1 + botSpares) + botOutputs))) := by
  have hSplit := zxpLayerDenoteCatSplit (zxpWireCells topSpares)
    [ZxpCell.xSpider (1 + botSpares) botOutputs]
  rw [zxpWireCellsDomArity, zxpWireCellsCodArity] at hSplit
  refine zxpRelEquivTrans hSplit ?_
  exact zxpTensorRowsCong topSpares topSpares (1 + botSpares) botOutputs
    (zxpAllWidthCast (by rw [zxpWireCellsDomArity, zxpWireCellsCodArity])
      (zxpLayerDenoteWidth (zxpWireCells topSpares)))
    (zxpIdRowsWidth topSpares)
    (zxpLayerDenoteWidth [ZxpCell.xSpider (1 + botSpares) botOutputs])
    (zxpParityRowsWidth ((1 + botSpares) + botOutputs))
    (zxpWireCellsDenoteId topSpares)
    (zxpTensorUnitRight (1 + botSpares) botOutputs
      (zxpParityRows ((1 + botSpares) + botOutputs))
      (zxpParityRowsWidth ((1 + botSpares) + botOutputs)))

/-- The whole Z-fusion LEFT side denotes `(spider (x) id) ; (id (x) spider)`. -/
theorem zxrZFuseLhsDenoteEquiv (topInputs topSpares botSpares botOutputs : Nat) :
    ZxpRelEquiv (topInputs + botSpares) (topSpares + botOutputs)
      (zxpDiagramDenote (zxrZFuseLhs topInputs topSpares botSpares botOutputs))
      (zxpComposeRows (topInputs + botSpares) ((topSpares + 1) + botSpares)
        (topSpares + botOutputs)
        (zxpTensorRows topInputs (topSpares + 1) botSpares botSpares
          (zxpSpiderCopyRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares))
        (zxpTensorRows topSpares topSpares (1 + botSpares) botOutputs
          (zxpIdRows topSpares)
          (zxpSpiderCopyRows ((1 + botSpares) + botOutputs)))) := by
  have hW1 : zxpLayerCodArity
      (ZxpCell.zSpider topInputs (topSpares + 1) :: zxpWireCells botSpares)
      = (topSpares + 1) + botSpares := by
    show (topSpares + 1) + zxpLayerCodArity (zxpWireCells botSpares)
      = (topSpares + 1) + botSpares
    rw [zxpWireCellsCodArity]
  have hW2 : zxpLayerCodArity (zxpCatCells (zxpWireCells topSpares)
      [ZxpCell.zSpider (1 + botSpares) botOutputs]) = topSpares + botOutputs := by
    rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
    rfl
  have hDenBotAll : ZxpAllWidth (((topSpares + 1) + botSpares) + (topSpares + botOutputs))
      (zxpLayerDenote (zxpCatCells (zxpWireCells topSpares)
        [ZxpCell.zSpider (1 + botSpares) botOutputs])) := by
    refine zxpAllWidthCast ?_ (zxpLayerDenoteWidth (zxpCatCells (zxpWireCells topSpares)
      [ZxpCell.zSpider (1 + botSpares) botOutputs]))
    rw [zxpCatCellsDomArity, zxpWireCellsDomArity, zxpCatCellsCodArity,
      zxpWireCellsCodArity]
    show (topSpares + (1 + botSpares)) + (topSpares + botOutputs)
      = ((topSpares + 1) + botSpares) + (topSpares + botOutputs)
    exact congrArg (fun innerWidth => innerWidth + (topSpares + botOutputs))
      (Nat.add_assoc topSpares 1 botSpares).symm
  have hDenTopAll : ZxpAllWidth
      ((topInputs + botSpares) + ((topSpares + 1) + botSpares))
      (zxpLayerDenote
        (ZxpCell.zSpider topInputs (topSpares + 1) :: zxpWireCells botSpares)) := by
    refine zxpAllWidthCast ?_ (zxpLayerDenoteWidth
      (ZxpCell.zSpider topInputs (topSpares + 1) :: zxpWireCells botSpares))
    show (topInputs + zxpLayerDomArity (zxpWireCells botSpares))
        + ((topSpares + 1) + zxpLayerCodArity (zxpWireCells botSpares))
      = (topInputs + botSpares) + ((topSpares + 1) + botSpares)
    rw [zxpWireCellsDomArity, zxpWireCellsCodArity]
  have hT1All := zxpTensorRowsWidth topInputs (topSpares + 1) botSpares botSpares
    (zxpSpiderCopyRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares)
    (zxpSpiderCopyRowsWidth (topInputs + (topSpares + 1))) (zxpIdRowsWidth botSpares)
  have hT2All : ZxpAllWidth (((topSpares + 1) + botSpares) + (topSpares + botOutputs))
      (zxpTensorRows topSpares topSpares (1 + botSpares) botOutputs
        (zxpIdRows topSpares) (zxpSpiderCopyRows ((1 + botSpares) + botOutputs))) :=
    zxpAllWidthCast
      (congrArg (fun innerWidth => innerWidth + (topSpares + botOutputs))
        (Nat.add_assoc topSpares 1 botSpares).symm)
      (zxpTensorRowsWidth topSpares topSpares (1 + botSpares) botOutputs
        (zxpIdRows topSpares) (zxpSpiderCopyRows ((1 + botSpares) + botOutputs))
        (zxpIdRowsWidth topSpares)
        (zxpSpiderCopyRowsWidth ((1 + botSpares) + botOutputs)))
  have hInnerAll := zxpComposeRowsWidth ((topSpares + 1) + botSpares)
    (topSpares + botOutputs) (topSpares + botOutputs)
    (zxpLayerDenote (zxpCatCells (zxpWireCells topSpares)
      [ZxpCell.zSpider (1 + botSpares) botOutputs]))
    (zxpIdRows (topSpares + botOutputs))
    hDenBotAll (zxpIdRowsWidth (topSpares + botOutputs))
  show ZxpRelEquiv (topInputs + botSpares) (topSpares + botOutputs)
    (zxpComposeRows (topInputs + botSpares)
      (zxpLayerCodArity
        (ZxpCell.zSpider topInputs (topSpares + 1) :: zxpWireCells botSpares))
      (zxpLayerCodArity (zxpCatCells (zxpWireCells topSpares)
        [ZxpCell.zSpider (1 + botSpares) botOutputs]))
      (zxpLayerDenote
        (ZxpCell.zSpider topInputs (topSpares + 1) :: zxpWireCells botSpares))
      (zxpComposeRows
        (zxpLayerCodArity
          (ZxpCell.zSpider topInputs (topSpares + 1) :: zxpWireCells botSpares))
        (zxpLayerCodArity (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.zSpider (1 + botSpares) botOutputs]))
        (zxpLayerCodArity (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.zSpider (1 + botSpares) botOutputs]))
        (zxpLayerDenote (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.zSpider (1 + botSpares) botOutputs]))
        (zxpIdRows (zxpLayerCodArity (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.zSpider (1 + botSpares) botOutputs])))))
    (zxpComposeRows (topInputs + botSpares) ((topSpares + 1) + botSpares)
      (topSpares + botOutputs)
      (zxpTensorRows topInputs (topSpares + 1) botSpares botSpares
        (zxpSpiderCopyRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares))
      (zxpTensorRows topSpares topSpares (1 + botSpares) botOutputs
        (zxpIdRows topSpares) (zxpSpiderCopyRows ((1 + botSpares) + botOutputs))))
  rw [hW1, hW2]
  refine zxpComposeRowsCong (topInputs + botSpares) ((topSpares + 1) + botSpares)
    (topSpares + botOutputs) hDenTopAll hT1All hInnerAll hT2All
    (zxrZFuseTopLayerEquiv topInputs topSpares botSpares) ?_
  refine zxpRelEquivTrans (zxpComposeIdRight ((topSpares + 1) + botSpares)
    (topSpares + botOutputs)
    (zxpLayerDenote (zxpCatCells (zxpWireCells topSpares)
      [ZxpCell.zSpider (1 + botSpares) botOutputs])) hDenBotAll) ?_
  exact zxpRelEquivCast (Nat.add_assoc topSpares 1 botSpares).symm rfl
    (zxrZFuseBotLayerEquiv topSpares botSpares botOutputs)

/-- The whole X-fusion LEFT side denotes `(spider (x) id) ; (id (x) spider)` (mirror). -/
theorem zxrXFuseLhsDenoteEquiv (topInputs topSpares botSpares botOutputs : Nat) :
    ZxpRelEquiv (topInputs + botSpares) (topSpares + botOutputs)
      (zxpDiagramDenote (zxrXFuseLhs topInputs topSpares botSpares botOutputs))
      (zxpComposeRows (topInputs + botSpares) ((topSpares + 1) + botSpares)
        (topSpares + botOutputs)
        (zxpTensorRows topInputs (topSpares + 1) botSpares botSpares
          (zxpParityRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares))
        (zxpTensorRows topSpares topSpares (1 + botSpares) botOutputs
          (zxpIdRows topSpares)
          (zxpParityRows ((1 + botSpares) + botOutputs)))) := by
  have hW1 : zxpLayerCodArity
      (ZxpCell.xSpider topInputs (topSpares + 1) :: zxpWireCells botSpares)
      = (topSpares + 1) + botSpares := by
    show (topSpares + 1) + zxpLayerCodArity (zxpWireCells botSpares)
      = (topSpares + 1) + botSpares
    rw [zxpWireCellsCodArity]
  have hW2 : zxpLayerCodArity (zxpCatCells (zxpWireCells topSpares)
      [ZxpCell.xSpider (1 + botSpares) botOutputs]) = topSpares + botOutputs := by
    rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
    rfl
  have hDenBotAll : ZxpAllWidth (((topSpares + 1) + botSpares) + (topSpares + botOutputs))
      (zxpLayerDenote (zxpCatCells (zxpWireCells topSpares)
        [ZxpCell.xSpider (1 + botSpares) botOutputs])) := by
    refine zxpAllWidthCast ?_ (zxpLayerDenoteWidth (zxpCatCells (zxpWireCells topSpares)
      [ZxpCell.xSpider (1 + botSpares) botOutputs]))
    rw [zxpCatCellsDomArity, zxpWireCellsDomArity, zxpCatCellsCodArity,
      zxpWireCellsCodArity]
    show (topSpares + (1 + botSpares)) + (topSpares + botOutputs)
      = ((topSpares + 1) + botSpares) + (topSpares + botOutputs)
    exact congrArg (fun innerWidth => innerWidth + (topSpares + botOutputs))
      (Nat.add_assoc topSpares 1 botSpares).symm
  have hDenTopAll : ZxpAllWidth
      ((topInputs + botSpares) + ((topSpares + 1) + botSpares))
      (zxpLayerDenote
        (ZxpCell.xSpider topInputs (topSpares + 1) :: zxpWireCells botSpares)) := by
    refine zxpAllWidthCast ?_ (zxpLayerDenoteWidth
      (ZxpCell.xSpider topInputs (topSpares + 1) :: zxpWireCells botSpares))
    show (topInputs + zxpLayerDomArity (zxpWireCells botSpares))
        + ((topSpares + 1) + zxpLayerCodArity (zxpWireCells botSpares))
      = (topInputs + botSpares) + ((topSpares + 1) + botSpares)
    rw [zxpWireCellsDomArity, zxpWireCellsCodArity]
  have hT1All := zxpTensorRowsWidth topInputs (topSpares + 1) botSpares botSpares
    (zxpParityRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares)
    (zxpParityRowsWidth (topInputs + (topSpares + 1))) (zxpIdRowsWidth botSpares)
  have hT2All : ZxpAllWidth (((topSpares + 1) + botSpares) + (topSpares + botOutputs))
      (zxpTensorRows topSpares topSpares (1 + botSpares) botOutputs
        (zxpIdRows topSpares) (zxpParityRows ((1 + botSpares) + botOutputs))) :=
    zxpAllWidthCast
      (congrArg (fun innerWidth => innerWidth + (topSpares + botOutputs))
        (Nat.add_assoc topSpares 1 botSpares).symm)
      (zxpTensorRowsWidth topSpares topSpares (1 + botSpares) botOutputs
        (zxpIdRows topSpares) (zxpParityRows ((1 + botSpares) + botOutputs))
        (zxpIdRowsWidth topSpares)
        (zxpParityRowsWidth ((1 + botSpares) + botOutputs)))
  have hInnerAll := zxpComposeRowsWidth ((topSpares + 1) + botSpares)
    (topSpares + botOutputs) (topSpares + botOutputs)
    (zxpLayerDenote (zxpCatCells (zxpWireCells topSpares)
      [ZxpCell.xSpider (1 + botSpares) botOutputs]))
    (zxpIdRows (topSpares + botOutputs))
    hDenBotAll (zxpIdRowsWidth (topSpares + botOutputs))
  show ZxpRelEquiv (topInputs + botSpares) (topSpares + botOutputs)
    (zxpComposeRows (topInputs + botSpares)
      (zxpLayerCodArity
        (ZxpCell.xSpider topInputs (topSpares + 1) :: zxpWireCells botSpares))
      (zxpLayerCodArity (zxpCatCells (zxpWireCells topSpares)
        [ZxpCell.xSpider (1 + botSpares) botOutputs]))
      (zxpLayerDenote
        (ZxpCell.xSpider topInputs (topSpares + 1) :: zxpWireCells botSpares))
      (zxpComposeRows
        (zxpLayerCodArity
          (ZxpCell.xSpider topInputs (topSpares + 1) :: zxpWireCells botSpares))
        (zxpLayerCodArity (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.xSpider (1 + botSpares) botOutputs]))
        (zxpLayerCodArity (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.xSpider (1 + botSpares) botOutputs]))
        (zxpLayerDenote (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.xSpider (1 + botSpares) botOutputs]))
        (zxpIdRows (zxpLayerCodArity (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.xSpider (1 + botSpares) botOutputs])))))
    (zxpComposeRows (topInputs + botSpares) ((topSpares + 1) + botSpares)
      (topSpares + botOutputs)
      (zxpTensorRows topInputs (topSpares + 1) botSpares botSpares
        (zxpParityRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares))
      (zxpTensorRows topSpares topSpares (1 + botSpares) botOutputs
        (zxpIdRows topSpares) (zxpParityRows ((1 + botSpares) + botOutputs))))
  rw [hW1, hW2]
  refine zxpComposeRowsCong (topInputs + botSpares) ((topSpares + 1) + botSpares)
    (topSpares + botOutputs) hDenTopAll hT1All hInnerAll hT2All
    (zxrXFuseTopLayerEquiv topInputs topSpares botSpares) ?_
  refine zxpRelEquivTrans (zxpComposeIdRight ((topSpares + 1) + botSpares)
    (topSpares + botOutputs)
    (zxpLayerDenote (zxpCatCells (zxpWireCells topSpares)
      [ZxpCell.xSpider (1 + botSpares) botOutputs])) hDenBotAll) ?_
  exact zxpRelEquivCast (Nat.add_assoc topSpares 1 botSpares).symm rfl
    (zxrXFuseBotLayerEquiv topSpares botSpares botOutputs)

/-- The Z-fusion RIGHT side denotes the fused copy spider. -/
theorem zxrZFuseRhsDenoteEquiv (topInputs topSpares botSpares botOutputs : Nat) :
    ZxpRelEquiv (topInputs + botSpares) (topSpares + botOutputs)
      (zxpDiagramDenote (zxrZFuseRhs topInputs topSpares botSpares botOutputs))
      (zxpSpiderCopyRows ((topInputs + botSpares) + (topSpares + botOutputs))) := by
  refine zxpRelEquivTrans (zxpComposeIdRight (topInputs + botSpares)
    (topSpares + botOutputs)
    (zxpLayerDenote
      [ZxpCell.zSpider (topInputs + botSpares) (topSpares + botOutputs)])
    (zxpLayerDenoteWidth
      [ZxpCell.zSpider (topInputs + botSpares) (topSpares + botOutputs)])) ?_
  exact zxpTensorUnitRight (topInputs + botSpares) (topSpares + botOutputs)
    (zxpSpiderCopyRows ((topInputs + botSpares) + (topSpares + botOutputs)))
    (zxpSpiderCopyRowsWidth ((topInputs + botSpares) + (topSpares + botOutputs)))

/-- The X-fusion RIGHT side denotes the fused parity spider (mirror). -/
theorem zxrXFuseRhsDenoteEquiv (topInputs topSpares botSpares botOutputs : Nat) :
    ZxpRelEquiv (topInputs + botSpares) (topSpares + botOutputs)
      (zxpDiagramDenote (zxrXFuseRhs topInputs topSpares botSpares botOutputs))
      (zxpParityRows ((topInputs + botSpares) + (topSpares + botOutputs))) := by
  refine zxpRelEquivTrans (zxpComposeIdRight (topInputs + botSpares)
    (topSpares + botOutputs)
    (zxpLayerDenote
      [ZxpCell.xSpider (topInputs + botSpares) (topSpares + botOutputs)])
    (zxpLayerDenoteWidth
      [ZxpCell.xSpider (topInputs + botSpares) (topSpares + botOutputs)])) ?_
  exact zxpTensorUnitRight (topInputs + botSpares) (topSpares + botOutputs)
    (zxpParityRows ((topInputs + botSpares) + (topSpares + botOutputs)))
    (zxpParityRowsWidth ((topInputs + botSpares) + (topSpares + botOutputs)))

/-- Parity of a singleton row. -/
theorem zxrRowParitySingle (bit : Bool) : zxrRowParity [bit] = bit := by
  show zxpXorB bit false = bit
  exact zxpXorBFalseRight bit

/-! ### THE CORE: copy-of-copy is copy (Z), add-of-add is add (X) — all arities

The one-wire composite is computed through `zxpComposeSpec` + `zxpTensorSpec` +
`zxpIdSpec`; the two boundary decompositions of the shared middle layer are reconciled by
the prefix take/drop surgery; the mid-bit chunk (length 1) either propagates the constant
copy value or carries the parity balance.  No kernel evaluation of unbounded instances —
this is the brief's pullback-shaped soundness argument made structural. -/

/-- The Z-fusion composite relates exactly the copy pairs. -/
theorem zxrZFuseCoreEquiv (topInputs topSpares botSpares botOutputs : Nat) :
    ZxpRelEquiv (topInputs + botSpares) (topSpares + botOutputs)
      (zxpComposeRows (topInputs + botSpares) ((topSpares + 1) + botSpares)
        (topSpares + botOutputs)
        (zxpTensorRows topInputs (topSpares + 1) botSpares botSpares
          (zxpSpiderCopyRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares))
        (zxpTensorRows topSpares topSpares (1 + botSpares) botOutputs
          (zxpIdRows topSpares) (zxpSpiderCopyRows ((1 + botSpares) + botOutputs))))
      (zxpSpiderCopyRows ((topInputs + botSpares) + (topSpares + botOutputs))) := by
  have hT1All := zxpTensorRowsWidth topInputs (topSpares + 1) botSpares botSpares
    (zxpSpiderCopyRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares)
    (zxpSpiderCopyRowsWidth (topInputs + (topSpares + 1))) (zxpIdRowsWidth botSpares)
  have hT2All : ZxpAllWidth (((topSpares + 1) + botSpares) + (topSpares + botOutputs))
      (zxpTensorRows topSpares topSpares (1 + botSpares) botOutputs
        (zxpIdRows topSpares) (zxpSpiderCopyRows ((1 + botSpares) + botOutputs))) :=
    zxpAllWidthCast
      (congrArg (fun innerWidth => innerWidth + (topSpares + botOutputs))
        (Nat.add_assoc topSpares 1 botSpares).symm)
      (zxpTensorRowsWidth topSpares topSpares (1 + botSpares) botOutputs
        (zxpIdRows topSpares) (zxpSpiderCopyRows ((1 + botSpares) + botOutputs))
        (zxpIdRowsWidth topSpares)
        (zxpSpiderCopyRowsWidth ((1 + botSpares) + botOutputs)))
  intro domVec codVec
  refine Iff.trans (zxpComposeSpec (topInputs + botSpares) ((topSpares + 1) + botSpares)
    (topSpares + botOutputs) _ _ hT1All hT2All domVec codVec) ?_
  refine Iff.trans ?_ (zxrCopyPairMemIff (topInputs + botSpares) (topSpares + botOutputs)
    domVec codVec).symm
  refine Iff.intro ?_ ?_
  · intro hExists
    obtain ⟨midVec, hTopPair, hBotPair⟩ := hExists
    have hTop := (zxpTensorSpec topInputs (topSpares + 1) botSpares botSpares
      (zxpSpiderCopyRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares)
      (zxpSpiderCopyRowsWidth (topInputs + (topSpares + 1))) (zxpIdRowsWidth botSpares)
      domVec midVec).mp hTopPair
    obtain ⟨topInVec, passInVec, topOutVec, passMidVec, hDomCat, hMidCatTop,
      hTopSpiderPair, hPassInPair⟩ := hTop
    have hBotCast := (zxpPairMemCast (Nat.add_assoc topSpares 1 botSpares) rfl).mp
      hBotPair
    have hBot := (zxpTensorSpec topSpares topSpares (1 + botSpares) botOutputs
      (zxpIdRows topSpares) (zxpSpiderCopyRows ((1 + botSpares) + botOutputs))
      (zxpIdRowsWidth topSpares) (zxpSpiderCopyRowsWidth ((1 + botSpares) + botOutputs))
      midVec codVec).mp hBotCast
    obtain ⟨passOutVec, botInVec, passCodVec, botOutVec, hMidCatBot, hCodCat,
      hPassOutPair, hBotSpiderPair⟩ := hBot
    have hTopCopy := (zxrCopyPairMemIff topInputs (topSpares + 1) topInVec topOutVec).mp
      hTopSpiderPair
    have hPassIn := (zxpIdSpec botSpares passInVec passMidVec).mp hPassInPair
    have hPassOut := (zxpIdSpec topSpares passOutVec passCodVec).mp hPassOutPair
    have hBotCopy := (zxrCopyPairMemIff (1 + botSpares) botOutputs botInVec
      botOutVec).mp hBotSpiderPair
    have hTopInLen : topInVec.length = topInputs := hTopCopy.left
    have hTopOutLen : topOutVec.length = topSpares + 1 := hTopCopy.right.left
    have hBotOutLen : botOutVec.length = botOutputs := hBotCopy.right.left
    have hPassInLen : passInVec.length = botSpares := hPassIn.right
    have hPassOutLen : passOutVec.length = topSpares := hPassOut.right
    have hMidEq : zxpCat topOutVec passMidVec = zxpCat passOutVec botInVec :=
      hMidCatTop.symm.trans hMidCatBot
    have hPassOutEq : passOutVec = zxpTakeN topSpares topOutVec :=
      (zxpTakeNCatExact passOutVec botInVec topSpares hPassOutLen).symm.trans
        ((congrArg (zxpTakeN topSpares) hMidEq.symm).trans
          (zxrTakeNCatOfPrefix topOutVec passMidVec topSpares 1 hTopOutLen))
    have hBotInEq : botInVec = zxpCat (zxpDropN topSpares topOutVec) passMidVec :=
      (zxpDropNCatExact passOutVec botInVec topSpares hPassOutLen).symm.trans
        ((congrArg (zxpDropN topSpares) hMidEq.symm).trans
          (zxrDropNCatOfPrefix topOutVec passMidVec topSpares 1 hTopOutLen))
    have hMidChunkLen : (zxpDropN topSpares topOutVec).length = 1 :=
      zxpDropNLength topOutVec topSpares 1 hTopOutLen
    refine And.intro ?_ (And.intro ?_ ?_)
    · rw [hDomCat, zxpCatLength, hTopInLen, hPassInLen]
    · rw [hCodCat, zxpCatLength, <- hPassOut.left, hPassOutLen, hBotOutLen]
    · cases hTopCopy.right.right with
      | inl hTopAllF =>
          cases hBotCopy.right.right with
          | inl hBotAllF =>
              have hTopInF := zxrAllFalseCatSplitLeft topInVec topOutVec hTopAllF
              have hTopOutF := zxrAllFalseCatSplitRight topInVec topOutVec hTopAllF
              have hBotInF := zxrAllFalseCatSplitLeft botInVec botOutVec hBotAllF
              have hBotOutF := zxrAllFalseCatSplitRight botInVec botOutVec hBotAllF
              have hBotInSplit : zxpAllFalse (zxpCat (zxpDropN topSpares topOutVec)
                  passMidVec) = true := by
                rw [<- hBotInEq]
                exact hBotInF
              have hPassMidF := zxrAllFalseCatSplitRight _ _ hBotInSplit
              refine Or.inl (zxrAllFalseCatIntro domVec codVec ?_ ?_)
              · rw [hDomCat]
                refine zxrAllFalseCatIntro _ _ hTopInF ?_
                rw [hPassIn.left]
                exact hPassMidF
              · rw [hCodCat]
                refine zxrAllFalseCatIntro _ _ ?_ hBotOutF
                rw [<- hPassOut.left, hPassOutEq]
                exact zxpAllFalseTakeN topOutVec hTopOutF topSpares
          | inr hBotAllT =>
              have hTopOutF := zxrAllFalseCatSplitRight topInVec topOutVec hTopAllF
              have hMidChunkF := zxrAllFalseDropN topOutVec hTopOutF topSpares
              have hBotInT := zxrAllTrueCatSplitLeft botInVec botOutVec hBotAllT
              have hBotInSplit : zxrAllTrue (zxpCat (zxpDropN topSpares topOutVec)
                  passMidVec) = true := by
                rw [<- hBotInEq]
                exact hBotInT
              have hMidChunkT := zxrAllTrueCatSplitLeft _ _ hBotInSplit
              have hMidChunkNil := zxrAllFalseAllTrueNil _ hMidChunkF hMidChunkT
              rw [hMidChunkNil] at hMidChunkLen
              exact nomatch hMidChunkLen
      | inr hTopAllT =>
          cases hBotCopy.right.right with
          | inl hBotAllF =>
              have hTopOutT := zxrAllTrueCatSplitRight topInVec topOutVec hTopAllT
              have hMidChunkT := zxrAllTrueDropN topOutVec hTopOutT topSpares
              have hBotInF := zxrAllFalseCatSplitLeft botInVec botOutVec hBotAllF
              have hBotInSplit : zxpAllFalse (zxpCat (zxpDropN topSpares topOutVec)
                  passMidVec) = true := by
                rw [<- hBotInEq]
                exact hBotInF
              have hMidChunkF := zxrAllFalseCatSplitLeft _ _ hBotInSplit
              have hMidChunkNil := zxrAllFalseAllTrueNil _ hMidChunkF hMidChunkT
              rw [hMidChunkNil] at hMidChunkLen
              exact nomatch hMidChunkLen
          | inr hBotAllT =>
              have hTopInT := zxrAllTrueCatSplitLeft topInVec topOutVec hTopAllT
              have hTopOutT := zxrAllTrueCatSplitRight topInVec topOutVec hTopAllT
              have hBotInT := zxrAllTrueCatSplitLeft botInVec botOutVec hBotAllT
              have hBotOutT := zxrAllTrueCatSplitRight botInVec botOutVec hBotAllT
              have hBotInSplit : zxrAllTrue (zxpCat (zxpDropN topSpares topOutVec)
                  passMidVec) = true := by
                rw [<- hBotInEq]
                exact hBotInT
              have hPassMidT := zxrAllTrueCatSplitRight _ _ hBotInSplit
              refine Or.inr (zxrAllTrueCatIntro domVec codVec ?_ ?_)
              · rw [hDomCat]
                refine zxrAllTrueCatIntro _ _ hTopInT ?_
                rw [hPassIn.left]
                exact hPassMidT
              · rw [hCodCat]
                refine zxrAllTrueCatIntro _ _ ?_ hBotOutT
                rw [<- hPassOut.left, hPassOutEq]
                exact zxrAllTrueTakeN topOutVec hTopOutT topSpares
  · intro hCopy
    have hDomLen : domVec.length = topInputs + botSpares := hCopy.left
    have hCodLen : codVec.length = topSpares + botOutputs := hCopy.right.left
    cases hCopy.right.right with
    | inl hAllF =>
        have hDomF := zxrAllFalseCatSplitLeft domVec codVec hAllF
        have hCodF := zxrAllFalseCatSplitRight domVec codVec hAllF
        refine Exists.intro (zxpZeroRow ((topSpares + 1) + botSpares))
          (And.intro ?_ ?_)
        · refine (zxpTensorSpec topInputs (topSpares + 1) botSpares botSpares
            (zxpSpiderCopyRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares)
            (zxpSpiderCopyRowsWidth (topInputs + (topSpares + 1)))
            (zxpIdRowsWidth botSpares) domVec
            (zxpZeroRow ((topSpares + 1) + botSpares))).mpr ?_
          refine Exists.intro (zxpTakeN topInputs domVec)
            (Exists.intro (zxpDropN topInputs domVec)
              (Exists.intro (zxpZeroRow (topSpares + 1))
                (Exists.intro (zxpZeroRow botSpares) ?_)))
          refine And.intro (zxpCatTakeDrop domVec topInputs botSpares hDomLen).symm
            (And.intro (zxpCatZeroZero (topSpares + 1) botSpares).symm
              (And.intro ?_ ?_))
          · refine (zxrCopyPairMemIff topInputs (topSpares + 1) _ _).mpr ?_
            refine And.intro (zxpTakeNLength domVec topInputs botSpares hDomLen)
              (And.intro (zxpZeroRowLength (topSpares + 1)) ?_)
            exact Or.inl (zxrAllFalseCatIntro _ _
              (zxpAllFalseTakeN domVec hDomF topInputs)
              (zxpAllFalseZeroRow (topSpares + 1)))
          · refine (zxpIdSpec botSpares _ _).mpr (And.intro ?_
              (zxpDropNLength domVec topInputs botSpares hDomLen))
            have hDropF := zxrAllFalseDropN domVec hDomF topInputs
            have hDropZero := zxpAllFalseToZeroRow _ hDropF
            rw [zxpDropNLength domVec topInputs botSpares hDomLen] at hDropZero
            exact hDropZero
        · refine (zxpPairMemCast (Nat.add_assoc topSpares 1 botSpares) rfl).mpr ?_
          refine (zxpTensorSpec topSpares topSpares (1 + botSpares) botOutputs
            (zxpIdRows topSpares) (zxpSpiderCopyRows ((1 + botSpares) + botOutputs))
            (zxpIdRowsWidth topSpares)
            (zxpSpiderCopyRowsWidth ((1 + botSpares) + botOutputs))
            (zxpZeroRow ((topSpares + 1) + botSpares)) codVec).mpr ?_
          refine Exists.intro (zxpZeroRow topSpares)
            (Exists.intro (zxpZeroRow (1 + botSpares))
              (Exists.intro (zxpTakeN topSpares codVec)
                (Exists.intro (zxpDropN topSpares codVec) ?_)))
          refine And.intro ?_
            (And.intro (zxpCatTakeDrop codVec topSpares botOutputs hCodLen).symm
              (And.intro ?_ ?_))
          · rw [zxpCatZeroZero topSpares (1 + botSpares)]
            exact congrArg zxpZeroRow (Nat.add_assoc topSpares 1 botSpares)
          · refine (zxpIdSpec topSpares _ _).mpr (And.intro ?_
              (zxpZeroRowLength topSpares))
            have hTakeF := zxpAllFalseTakeN codVec hCodF topSpares
            have hTakeZero := zxpAllFalseToZeroRow _ hTakeF
            rw [zxpTakeNLength codVec topSpares botOutputs hCodLen] at hTakeZero
            exact hTakeZero.symm
          · refine (zxrCopyPairMemIff (1 + botSpares) botOutputs _ _).mpr ?_
            refine And.intro (zxpZeroRowLength (1 + botSpares))
              (And.intro (zxpDropNLength codVec topSpares botOutputs hCodLen) ?_)
            exact Or.inl (zxrAllFalseCatIntro _ _
              (zxpAllFalseZeroRow (1 + botSpares))
              (zxrAllFalseDropN codVec hCodF topSpares))
    | inr hAllT =>
        have hDomT := zxrAllTrueCatSplitLeft domVec codVec hAllT
        have hCodT := zxrAllTrueCatSplitRight domVec codVec hAllT
        refine Exists.intro (zxpAllOnesRow ((topSpares + 1) + botSpares))
          (And.intro ?_ ?_)
        · refine (zxpTensorSpec topInputs (topSpares + 1) botSpares botSpares
            (zxpSpiderCopyRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares)
            (zxpSpiderCopyRowsWidth (topInputs + (topSpares + 1)))
            (zxpIdRowsWidth botSpares) domVec
            (zxpAllOnesRow ((topSpares + 1) + botSpares))).mpr ?_
          refine Exists.intro (zxpTakeN topInputs domVec)
            (Exists.intro (zxpDropN topInputs domVec)
              (Exists.intro (zxpAllOnesRow (topSpares + 1))
                (Exists.intro (zxpAllOnesRow botSpares) ?_)))
          refine And.intro (zxpCatTakeDrop domVec topInputs botSpares hDomLen).symm
            (And.intro (zxrCatAllOnes (topSpares + 1) botSpares).symm
              (And.intro ?_ ?_))
          · refine (zxrCopyPairMemIff topInputs (topSpares + 1) _ _).mpr ?_
            refine And.intro (zxpTakeNLength domVec topInputs botSpares hDomLen)
              (And.intro (zxpAllOnesRowLength (topSpares + 1)) ?_)
            exact Or.inr (zxrAllTrueCatIntro _ _
              (zxrAllTrueTakeN domVec hDomT topInputs)
              (zxrAllTrueAllOnesRow (topSpares + 1)))
          · refine (zxpIdSpec botSpares _ _).mpr (And.intro ?_
              (zxpDropNLength domVec topInputs botSpares hDomLen))
            have hDropT := zxrAllTrueDropN domVec hDomT topInputs
            have hDropOnes := zxrAllTrueToAllOnesRow _ hDropT
            rw [zxpDropNLength domVec topInputs botSpares hDomLen] at hDropOnes
            exact hDropOnes
        · refine (zxpPairMemCast (Nat.add_assoc topSpares 1 botSpares) rfl).mpr ?_
          refine (zxpTensorSpec topSpares topSpares (1 + botSpares) botOutputs
            (zxpIdRows topSpares) (zxpSpiderCopyRows ((1 + botSpares) + botOutputs))
            (zxpIdRowsWidth topSpares)
            (zxpSpiderCopyRowsWidth ((1 + botSpares) + botOutputs))
            (zxpAllOnesRow ((topSpares + 1) + botSpares)) codVec).mpr ?_
          refine Exists.intro (zxpAllOnesRow topSpares)
            (Exists.intro (zxpAllOnesRow (1 + botSpares))
              (Exists.intro (zxpTakeN topSpares codVec)
                (Exists.intro (zxpDropN topSpares codVec) ?_)))
          refine And.intro ?_
            (And.intro (zxpCatTakeDrop codVec topSpares botOutputs hCodLen).symm
              (And.intro ?_ ?_))
          · rw [zxrCatAllOnes topSpares (1 + botSpares)]
            exact congrArg zxpAllOnesRow (Nat.add_assoc topSpares 1 botSpares)
          · refine (zxpIdSpec topSpares _ _).mpr (And.intro ?_
              (zxpAllOnesRowLength topSpares))
            have hTakeT := zxrAllTrueTakeN codVec hCodT topSpares
            have hTakeOnes := zxrAllTrueToAllOnesRow _ hTakeT
            rw [zxpTakeNLength codVec topSpares botOutputs hCodLen] at hTakeOnes
            exact hTakeOnes.symm
          · refine (zxrCopyPairMemIff (1 + botSpares) botOutputs _ _).mpr ?_
            refine And.intro (zxpAllOnesRowLength (1 + botSpares))
              (And.intro (zxpDropNLength codVec topSpares botOutputs hCodLen) ?_)
            exact Or.inr (zxrAllTrueCatIntro _ _
              (zxrAllTrueAllOnesRow (1 + botSpares))
              (zxrAllTrueDropN codVec hCodT topSpares))

/-- The X-fusion composite relates exactly the add pairs (mirror; the mid bit carries
the parity balance `parity(topIn) + parity(passCod)`). -/
theorem zxrXFuseCoreEquiv (topInputs topSpares botSpares botOutputs : Nat) :
    ZxpRelEquiv (topInputs + botSpares) (topSpares + botOutputs)
      (zxpComposeRows (topInputs + botSpares) ((topSpares + 1) + botSpares)
        (topSpares + botOutputs)
        (zxpTensorRows topInputs (topSpares + 1) botSpares botSpares
          (zxpParityRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares))
        (zxpTensorRows topSpares topSpares (1 + botSpares) botOutputs
          (zxpIdRows topSpares) (zxpParityRows ((1 + botSpares) + botOutputs))))
      (zxpParityRows ((topInputs + botSpares) + (topSpares + botOutputs))) := by
  have hT1All := zxpTensorRowsWidth topInputs (topSpares + 1) botSpares botSpares
    (zxpParityRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares)
    (zxpParityRowsWidth (topInputs + (topSpares + 1))) (zxpIdRowsWidth botSpares)
  have hT2All : ZxpAllWidth (((topSpares + 1) + botSpares) + (topSpares + botOutputs))
      (zxpTensorRows topSpares topSpares (1 + botSpares) botOutputs
        (zxpIdRows topSpares) (zxpParityRows ((1 + botSpares) + botOutputs))) :=
    zxpAllWidthCast
      (congrArg (fun innerWidth => innerWidth + (topSpares + botOutputs))
        (Nat.add_assoc topSpares 1 botSpares).symm)
      (zxpTensorRowsWidth topSpares topSpares (1 + botSpares) botOutputs
        (zxpIdRows topSpares) (zxpParityRows ((1 + botSpares) + botOutputs))
        (zxpIdRowsWidth topSpares)
        (zxpParityRowsWidth ((1 + botSpares) + botOutputs)))
  intro domVec codVec
  refine Iff.trans (zxpComposeSpec (topInputs + botSpares) ((topSpares + 1) + botSpares)
    (topSpares + botOutputs) _ _ hT1All hT2All domVec codVec) ?_
  refine Iff.trans ?_ (zxrAddPairMemIff (topInputs + botSpares) (topSpares + botOutputs)
    domVec codVec).symm
  refine Iff.intro ?_ ?_
  · intro hExists
    obtain ⟨midVec, hTopPair, hBotPair⟩ := hExists
    have hTop := (zxpTensorSpec topInputs (topSpares + 1) botSpares botSpares
      (zxpParityRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares)
      (zxpParityRowsWidth (topInputs + (topSpares + 1))) (zxpIdRowsWidth botSpares)
      domVec midVec).mp hTopPair
    obtain ⟨topInVec, passInVec, topOutVec, passMidVec, hDomCat, hMidCatTop,
      hTopSpiderPair, hPassInPair⟩ := hTop
    have hBotCast := (zxpPairMemCast (Nat.add_assoc topSpares 1 botSpares) rfl).mp
      hBotPair
    have hBot := (zxpTensorSpec topSpares topSpares (1 + botSpares) botOutputs
      (zxpIdRows topSpares) (zxpParityRows ((1 + botSpares) + botOutputs))
      (zxpIdRowsWidth topSpares) (zxpParityRowsWidth ((1 + botSpares) + botOutputs))
      midVec codVec).mp hBotCast
    obtain ⟨passOutVec, botInVec, passCodVec, botOutVec, hMidCatBot, hCodCat,
      hPassOutPair, hBotSpiderPair⟩ := hBot
    have hTopAdd := (zxrAddPairMemIff topInputs (topSpares + 1) topInVec topOutVec).mp
      hTopSpiderPair
    have hPassIn := (zxpIdSpec botSpares passInVec passMidVec).mp hPassInPair
    have hPassOut := (zxpIdSpec topSpares passOutVec passCodVec).mp hPassOutPair
    have hBotAdd := (zxrAddPairMemIff (1 + botSpares) botOutputs botInVec
      botOutVec).mp hBotSpiderPair
    have hTopInLen : topInVec.length = topInputs := hTopAdd.left
    have hTopOutLen : topOutVec.length = topSpares + 1 := hTopAdd.right.left
    have hBotOutLen : botOutVec.length = botOutputs := hBotAdd.right.left
    have hPassInLen : passInVec.length = botSpares := hPassIn.right
    have hPassOutLen : passOutVec.length = topSpares := hPassOut.right
    have hMidEq : zxpCat topOutVec passMidVec = zxpCat passOutVec botInVec :=
      hMidCatTop.symm.trans hMidCatBot
    have hPassOutEq : passOutVec = zxpTakeN topSpares topOutVec :=
      (zxpTakeNCatExact passOutVec botInVec topSpares hPassOutLen).symm.trans
        ((congrArg (zxpTakeN topSpares) hMidEq.symm).trans
          (zxrTakeNCatOfPrefix topOutVec passMidVec topSpares 1 hTopOutLen))
    have hBotInEq : botInVec = zxpCat (zxpDropN topSpares topOutVec) passMidVec :=
      (zxpDropNCatExact passOutVec botInVec topSpares hPassOutLen).symm.trans
        ((congrArg (zxpDropN topSpares) hMidEq.symm).trans
          (zxrDropNCatOfPrefix topOutVec passMidVec topSpares 1 hTopOutLen))
    have hTopOutSplitParity : zxrRowParity topOutVec
        = zxpXorB (zxrRowParity (zxpTakeN topSpares topOutVec))
            (zxrRowParity (zxpDropN topSpares topOutVec)) := by
      have hParityCat := zxrRowParityCat (zxpTakeN topSpares topOutVec)
        (zxpDropN topSpares topOutVec)
      rw [zxpCatTakeDrop topOutVec topSpares 1 hTopOutLen] at hParityCat
      exact hParityCat
    have hTopEq : zxpXorB (zxrRowParity topInVec) (zxrRowParity topOutVec) = false := by
      have hRaw := hTopAdd.right.right
      rw [zxrRowParityCat] at hRaw
      exact hRaw
    have hBotEq : zxpXorB (zxrRowParity botInVec) (zxrRowParity botOutVec) = false := by
      have hRaw := hBotAdd.right.right
      rw [zxrRowParityCat] at hRaw
      exact hRaw
    have hBotInParity : zxrRowParity botInVec
        = zxpXorB (zxrRowParity (zxpDropN topSpares topOutVec))
            (zxrRowParity passMidVec) := by
      rw [hBotInEq, zxrRowParityCat]
    rw [hTopOutSplitParity] at hTopEq
    have hTopVal := zxrXorBEqOfXorFalse _ _ hTopEq
    rw [hBotInParity] at hBotEq
    have hBotVal := zxrXorBEqOfXorFalse _ _ hBotEq
    refine And.intro ?_ (And.intro ?_ ?_)
    · rw [hDomCat, zxpCatLength, hTopInLen, hPassInLen]
    · rw [hCodCat, zxpCatLength, <- hPassOut.left, hPassOutLen, hBotOutLen]
    · rw [zxrRowParityCat domVec codVec, hDomCat, hCodCat,
        zxrRowParityCat topInVec passInVec, zxrRowParityCat passCodVec botOutVec,
        hPassIn.left, <- hPassOut.left, hPassOutEq, hTopVal, <- hBotVal]
      exact zxrXorBBothPairsFalse (zxrRowParity (zxpTakeN topSpares topOutVec))
        (zxrRowParity (zxpDropN topSpares topOutVec)) (zxrRowParity passMidVec)
  · intro hAdd
    have hDomLen : domVec.length = topInputs + botSpares := hAdd.left
    have hCodLen : codVec.length = topSpares + botOutputs := hAdd.right.left
    have hDomParity : zxrRowParity domVec
        = zxpXorB (zxrRowParity (zxpTakeN topInputs domVec))
            (zxrRowParity (zxpDropN topInputs domVec)) := by
      have hParityCat := zxrRowParityCat (zxpTakeN topInputs domVec)
        (zxpDropN topInputs domVec)
      rw [zxpCatTakeDrop domVec topInputs botSpares hDomLen] at hParityCat
      exact hParityCat
    have hCodParity : zxrRowParity codVec
        = zxpXorB (zxrRowParity (zxpTakeN topSpares codVec))
            (zxrRowParity (zxpDropN topSpares codVec)) := by
      have hParityCat := zxrRowParityCat (zxpTakeN topSpares codVec)
        (zxpDropN topSpares codVec)
      rw [zxpCatTakeDrop codVec topSpares botOutputs hCodLen] at hParityCat
      exact hParityCat
    have hGiven : zxpXorB
        (zxpXorB (zxrRowParity (zxpTakeN topInputs domVec))
          (zxrRowParity (zxpDropN topInputs domVec)))
        (zxpXorB (zxrRowParity (zxpTakeN topSpares codVec))
          (zxrRowParity (zxpDropN topSpares codVec))) = false := by
      have hRaw := hAdd.right.right
      rw [zxrRowParityCat, hDomParity, hCodParity] at hRaw
      exact hRaw
    refine Exists.intro (zxpCat (zxpCat (zxpTakeN topSpares codVec)
      [zxpXorB (zxrRowParity (zxpTakeN topInputs domVec))
        (zxrRowParity (zxpTakeN topSpares codVec))])
      (zxpDropN topInputs domVec)) (And.intro ?_ ?_)
    · refine (zxpTensorSpec topInputs (topSpares + 1) botSpares botSpares
        (zxpParityRows (topInputs + (topSpares + 1))) (zxpIdRows botSpares)
        (zxpParityRowsWidth (topInputs + (topSpares + 1))) (zxpIdRowsWidth botSpares)
        domVec _).mpr ?_
      refine Exists.intro (zxpTakeN topInputs domVec)
        (Exists.intro (zxpDropN topInputs domVec)
          (Exists.intro (zxpCat (zxpTakeN topSpares codVec)
            [zxpXorB (zxrRowParity (zxpTakeN topInputs domVec))
              (zxrRowParity (zxpTakeN topSpares codVec))])
            (Exists.intro (zxpDropN topInputs domVec) ?_)))
      refine And.intro (zxpCatTakeDrop domVec topInputs botSpares hDomLen).symm
        (And.intro rfl (And.intro ?_ ?_))
      · refine (zxrAddPairMemIff topInputs (topSpares + 1) _ _).mpr ?_
        refine And.intro (zxpTakeNLength domVec topInputs botSpares hDomLen)
          (And.intro ?_ ?_)
        · rw [zxpCatLength, zxpTakeNLength codVec topSpares botOutputs hCodLen]
          rfl
        · rw [zxrRowParityCat, zxrRowParityCat, zxrRowParitySingle]
          exact zxrXorBReturnFalse (zxrRowParity (zxpTakeN topInputs domVec))
            (zxrRowParity (zxpTakeN topSpares codVec))
      · exact (zxpIdSpec botSpares _ _).mpr (And.intro rfl
          (zxpDropNLength domVec topInputs botSpares hDomLen))
    · refine (zxpPairMemCast (Nat.add_assoc topSpares 1 botSpares) rfl).mpr ?_
      refine (zxpTensorSpec topSpares topSpares (1 + botSpares) botOutputs
        (zxpIdRows topSpares) (zxpParityRows ((1 + botSpares) + botOutputs))
        (zxpIdRowsWidth topSpares) (zxpParityRowsWidth ((1 + botSpares) + botOutputs))
        _ codVec).mpr ?_
      refine Exists.intro (zxpTakeN topSpares codVec)
        (Exists.intro (zxpCat
          [zxpXorB (zxrRowParity (zxpTakeN topInputs domVec))
            (zxrRowParity (zxpTakeN topSpares codVec))]
          (zxpDropN topInputs domVec))
          (Exists.intro (zxpTakeN topSpares codVec)
            (Exists.intro (zxpDropN topSpares codVec) ?_)))
      refine And.intro (zxpCatAssoc (zxpTakeN topSpares codVec)
          [zxpXorB (zxrRowParity (zxpTakeN topInputs domVec))
            (zxrRowParity (zxpTakeN topSpares codVec))]
          (zxpDropN topInputs domVec))
        (And.intro (zxpCatTakeDrop codVec topSpares botOutputs hCodLen).symm
          (And.intro ?_ ?_))
      · exact (zxpIdSpec topSpares _ _).mpr (And.intro rfl
          (zxpTakeNLength codVec topSpares botOutputs hCodLen))
      · refine (zxrAddPairMemIff (1 + botSpares) botOutputs _ _).mpr ?_
        refine And.intro ?_
          (And.intro (zxpDropNLength codVec topSpares botOutputs hCodLen) ?_)
        · rw [zxpCatLength, zxpDropNLength domVec topInputs botSpares hDomLen]
          rfl
        · rw [zxrRowParityCat, zxrRowParityCat, zxrRowParitySingle,
            zxpXorBAssoc
              (zxpXorB (zxrRowParity (zxpTakeN topInputs domVec))
                (zxrRowParity (zxpTakeN topSpares codVec)))
              (zxrRowParity (zxpDropN topInputs domVec))
              (zxrRowParity (zxpDropN topSpares codVec)),
            <- zxgXorBMedial (zxrRowParity (zxpTakeN topInputs domVec))
              (zxrRowParity (zxpDropN topInputs domVec))
              (zxrRowParity (zxpTakeN topSpares codVec))
              (zxrRowParity (zxpDropN topSpares codVec))]
          exact hGiven

/-! ### The fusion bundles (the full soundness package per family member) -/

/-- SOUNDNESS OF THE Z FUSION ROW at every arity. -/
theorem zxrZFuseBundle (topInputs topSpares botSpares botOutputs : Nat) :
    ZxpConvBundle (zxrZFuseLhs topInputs topSpares botSpares botOutputs)
      (zxrZFuseRhs topInputs topSpares botSpares botOutputs) := by
  have hEquiv : ZxpRelEquiv (topInputs + botSpares) (topSpares + botOutputs)
      (zxpDiagramDenote (zxrZFuseLhs topInputs topSpares botSpares botOutputs))
      (zxpDiagramDenote (zxrZFuseRhs topInputs topSpares botSpares botOutputs)) :=
    zxpRelEquivTrans (zxrZFuseLhsDenoteEquiv topInputs topSpares botSpares botOutputs)
      (zxpRelEquivTrans (zxrZFuseCoreEquiv topInputs topSpares botSpares botOutputs)
        (zxpRelEquivSymm
          (zxrZFuseRhsDenoteEquiv topInputs topSpares botSpares botOutputs)))
  refine And.intro rfl (And.intro ?_ (And.intro
    (zxrZFuseLhsWF topInputs topSpares botSpares botOutputs)
    (And.intro (zxrZFuseRhsWF topInputs topSpares botSpares botOutputs) ?_)))
  · exact (zxrZFuseLhsCodArity topInputs topSpares botSpares botOutputs).trans
      (zxrZFuseRhsCodArity topInputs topSpares botSpares botOutputs).symm
  · exact zxpRelEquivCast rfl
      (zxrZFuseLhsCodArity topInputs topSpares botSpares botOutputs).symm hEquiv

/-- SOUNDNESS OF THE X FUSION ROW at every arity. -/
theorem zxrXFuseBundle (topInputs topSpares botSpares botOutputs : Nat) :
    ZxpConvBundle (zxrXFuseLhs topInputs topSpares botSpares botOutputs)
      (zxrXFuseRhs topInputs topSpares botSpares botOutputs) := by
  have hEquiv : ZxpRelEquiv (topInputs + botSpares) (topSpares + botOutputs)
      (zxpDiagramDenote (zxrXFuseLhs topInputs topSpares botSpares botOutputs))
      (zxpDiagramDenote (zxrXFuseRhs topInputs topSpares botSpares botOutputs)) :=
    zxpRelEquivTrans (zxrXFuseLhsDenoteEquiv topInputs topSpares botSpares botOutputs)
      (zxpRelEquivTrans (zxrXFuseCoreEquiv topInputs topSpares botSpares botOutputs)
        (zxpRelEquivSymm
          (zxrXFuseRhsDenoteEquiv topInputs topSpares botSpares botOutputs)))
  refine And.intro rfl (And.intro ?_ (And.intro
    (zxrXFuseLhsWF topInputs topSpares botSpares botOutputs)
    (And.intro (zxrXFuseRhsWF topInputs topSpares botSpares botOutputs) ?_)))
  · exact (zxrXFuseLhsCodArity topInputs topSpares botSpares botOutputs).trans
      (zxrXFuseRhsCodArity topInputs topSpares botSpares botOutputs).symm
  · exact zxpRelEquivCast rfl
      (zxrXFuseLhsCodArity topInputs topSpares botSpares botOutputs).symm hEquiv

/-! ## Stage 3 — THE EXTENDED CONGRUENCE `ZxrConv` (deliverable A)

Same shapes as the seed: window moves (every seed move embeds, PLUS the fusion family),
one padded-step constructor reusing `zxpPadDiagram` verbatim, groupoid closure. -/

/-- Extended window move: a seed move (published row or splitLayer), or a one-wire
fusion instance in either colour. -/
inductive ZxrWindowMove : ZxpDiagram -> ZxpDiagram -> Prop where
  | seed {firstWindow secondWindow : ZxpDiagram}
      (hMove : ZxpWindowMove firstWindow secondWindow) :
      ZxrWindowMove firstWindow secondWindow
  | zFuse (topInputs topSpares botSpares botOutputs : Nat) :
      ZxrWindowMove (zxrZFuseLhs topInputs topSpares botSpares botOutputs)
        (zxrZFuseRhs topInputs topSpares botSpares botOutputs)
  | xFuse (topInputs topSpares botSpares botOutputs : Nat) :
      ZxrWindowMove (zxrXFuseLhs topInputs topSpares botSpares botOutputs)
        (zxrXFuseRhs topInputs topSpares botSpares botOutputs)

/-- Every extended window move is sound (bundle form). -/
theorem zxrWindowMoveBundle {firstWindow secondWindow : ZxpDiagram}
    (hMove : ZxrWindowMove firstWindow secondWindow) :
    ZxpConvBundle firstWindow secondWindow := by
  cases hMove with
  | seed hSeedMove => exact zxpWindowMoveBundle hSeedMove
  | zFuse topInputs topSpares botSpares botOutputs =>
      exact zxrZFuseBundle topInputs topSpares botSpares botOutputs
  | xFuse topInputs topSpares botSpares botOutputs =>
      exact zxrXFuseBundle topInputs topSpares botSpares botOutputs

/-- One extended rewriting step: an extended window move fired inside the seed's pad
combinator (identical constructor shape to the seed's `ZxpStep`). -/
inductive ZxrStep : ZxpDiagram -> ZxpDiagram -> Prop where
  | pad (contextSource leftWires rightWires : Nat)
      (beforeLayers afterLayers : List (List ZxpCell))
      {firstWindow secondWindow : ZxpDiagram}
      (hMove : ZxrWindowMove firstWindow secondWindow)
      (hBeforeWF : ZxpLayersWF contextSource beforeLayers)
      (hBeforeCod : zxpLayersCodArity contextSource beforeLayers
        = leftWires + (firstWindow.sourceArity + rightWires))
      (hAfterWF : ZxpLayersWF
        (leftWires + (zxpDiagramCodArity firstWindow + rightWires)) afterLayers) :
      ZxrStep
        (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
          firstWindow)
        (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
          secondWindow)

/-- Padding preserves any sound window bundle (the seed's `zxpStepBundle` argument
factored over an arbitrary window bundle, so both the seed and the fusion moves ride
the same proof). -/
theorem zxrPadBundle (contextSource leftWires rightWires : Nat)
    (beforeLayers afterLayers : List (List ZxpCell))
    {firstWindow secondWindow : ZxpDiagram}
    (hWindowBundle : ZxpConvBundle firstWindow secondWindow)
    (hBeforeWF : ZxpLayersWF contextSource beforeLayers)
    (hBeforeCod : zxpLayersCodArity contextSource beforeLayers
      = leftWires + (firstWindow.sourceArity + rightWires))
    (hAfterWF : ZxpLayersWF
      (leftWires + (zxpDiagramCodArity firstWindow + rightWires)) afterLayers) :
    ZxpConvBundle
      (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
        firstWindow)
      (zxpPadDiagram contextSource leftWires rightWires beforeLayers afterLayers
        secondWindow) := by
  have hSourceEq : firstWindow.sourceArity = secondWindow.sourceArity :=
    hWindowBundle.left
  have hCodEq : zxpDiagramCodArity firstWindow = zxpDiagramCodArity secondWindow :=
    hWindowBundle.right.left
  have hFirstWF : ZxpDiagramWF firstWindow := hWindowBundle.right.right.left
  have hSecondWF : ZxpDiagramWF secondWindow := hWindowBundle.right.right.right.left
  have hEquiv := hWindowBundle.right.right.right.right
  have hBeforeCod2 : zxpLayersCodArity contextSource beforeLayers
      = leftWires + (secondWindow.sourceArity + rightWires) := by
    rw [hBeforeCod, hSourceEq]
  have hAfterWF2 : ZxpLayersWF
      (leftWires + (zxpDiagramCodArity secondWindow + rightWires)) afterLayers := by
    rw [<- hCodEq]
    exact hAfterWF
  have hPadWF1 := zxpPadDiagramWF contextSource leftWires rightWires beforeLayers
    afterLayers firstWindow hBeforeWF hBeforeCod hFirstWF hAfterWF
  have hPadWF2 := zxpPadDiagramWF contextSource leftWires rightWires beforeLayers
    afterLayers secondWindow hBeforeWF hBeforeCod2 hSecondWF hAfterWF2
  have hDecomp1 := zxpPadDiagramDenoteDecomp contextSource leftWires rightWires
    beforeLayers afterLayers firstWindow hBeforeWF hBeforeCod hFirstWF hAfterWF
  have hDecomp2 := zxpPadDiagramDenoteDecomp contextSource leftWires rightWires
    beforeLayers afterLayers secondWindow hBeforeWF hBeforeCod2 hSecondWF hAfterWF2
  rw [<- hSourceEq, <- hCodEq] at hDecomp2
  have hBeforeAll : ZxpAllWidth
      (contextSource + (leftWires + (firstWindow.sourceArity + rightWires)))
      (zxpLayersDenote contextSource beforeLayers) :=
    zxpAllWidthCast (by rw [hBeforeCod]) (zxpLayersDenoteWidth beforeLayers hBeforeWF)
  have hAfterAll := zxpLayersDenoteWidth afterLayers hAfterWF
  have hFirstDenAll := zxpDiagramDenoteWidth firstWindow hFirstWF
  have hSecondDenAll : ZxpAllWidth
      (firstWindow.sourceArity + zxpDiagramCodArity firstWindow)
      (zxpDiagramDenote secondWindow) :=
    zxpAllWidthCast (by rw [hSourceEq, hCodEq])
      (zxpDiagramDenoteWidth secondWindow hSecondWF)
  have hIdLeftAll := zxpIdRowsWidth leftWires
  have hIdRightAll := zxpIdRowsWidth rightWires
  have hInner1All := zxpTensorRowsWidth firstWindow.sourceArity
    (zxpDiagramCodArity firstWindow) rightWires rightWires
    (zxpDiagramDenote firstWindow) (zxpIdRows rightWires) hFirstDenAll hIdRightAll
  have hInner2All := zxpTensorRowsWidth firstWindow.sourceArity
    (zxpDiagramCodArity firstWindow) rightWires rightWires
    (zxpDiagramDenote secondWindow) (zxpIdRows rightWires) hSecondDenAll hIdRightAll
  have hTensor1All := zxpTensorRowsWidth leftWires leftWires
    (firstWindow.sourceArity + rightWires)
    (zxpDiagramCodArity firstWindow + rightWires) (zxpIdRows leftWires) _
    hIdLeftAll hInner1All
  have hTensor2All := zxpTensorRowsWidth leftWires leftWires
    (firstWindow.sourceArity + rightWires)
    (zxpDiagramCodArity firstWindow + rightWires) (zxpIdRows leftWires) _
    hIdLeftAll hInner2All
  have hMiddle : ZxpRelEquiv (leftWires + (firstWindow.sourceArity + rightWires))
      (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
      (zxpTensorRows leftWires leftWires
        (firstWindow.sourceArity + rightWires)
        (zxpDiagramCodArity firstWindow + rightWires)
        (zxpIdRows leftWires)
        (zxpTensorRows firstWindow.sourceArity (zxpDiagramCodArity firstWindow)
          rightWires rightWires (zxpDiagramDenote firstWindow) (zxpIdRows rightWires)))
      (zxpTensorRows leftWires leftWires
        (firstWindow.sourceArity + rightWires)
        (zxpDiagramCodArity firstWindow + rightWires)
        (zxpIdRows leftWires)
        (zxpTensorRows firstWindow.sourceArity (zxpDiagramCodArity firstWindow)
          rightWires rightWires (zxpDiagramDenote secondWindow)
          (zxpIdRows rightWires))) :=
    zxpTensorRowsCong leftWires leftWires (firstWindow.sourceArity + rightWires)
      (zxpDiagramCodArity firstWindow + rightWires)
      hIdLeftAll hIdLeftAll hInner1All hInner2All
      (zxpRelEquivRefl leftWires leftWires (zxpIdRows leftWires))
      (zxpTensorRowsCong firstWindow.sourceArity (zxpDiagramCodArity firstWindow)
        rightWires rightWires hFirstDenAll hSecondDenAll hIdRightAll hIdRightAll
        hEquiv
        (zxpRelEquivRefl rightWires rightWires (zxpIdRows rightWires)))
  have hCompose1All := zxpComposeRowsWidth
    (leftWires + (firstWindow.sourceArity + rightWires))
    (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
    (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
      afterLayers) _
    (zxpLayersDenote (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
      afterLayers)
    hTensor1All hAfterAll
  have hCompose2All := zxpComposeRowsWidth
    (leftWires + (firstWindow.sourceArity + rightWires))
    (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
    (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
      afterLayers) _
    (zxpLayersDenote (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
      afterLayers)
    hTensor2All hAfterAll
  have hMidCong : ZxpRelEquiv contextSource
      (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
        afterLayers)
      (zxpComposeRows contextSource (leftWires + (firstWindow.sourceArity + rightWires))
        (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
          afterLayers)
        (zxpLayersDenote contextSource beforeLayers)
        (zxpComposeRows (leftWires + (firstWindow.sourceArity + rightWires))
          (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
          (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
            afterLayers)
          (zxpTensorRows leftWires leftWires
            (firstWindow.sourceArity + rightWires)
            (zxpDiagramCodArity firstWindow + rightWires)
            (zxpIdRows leftWires)
            (zxpTensorRows firstWindow.sourceArity (zxpDiagramCodArity firstWindow)
              rightWires rightWires (zxpDiagramDenote firstWindow)
              (zxpIdRows rightWires)))
          (zxpLayersDenote (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
            afterLayers)))
      (zxpComposeRows contextSource (leftWires + (firstWindow.sourceArity + rightWires))
        (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
          afterLayers)
        (zxpLayersDenote contextSource beforeLayers)
        (zxpComposeRows (leftWires + (firstWindow.sourceArity + rightWires))
          (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
          (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
            afterLayers)
          (zxpTensorRows leftWires leftWires
            (firstWindow.sourceArity + rightWires)
            (zxpDiagramCodArity firstWindow + rightWires)
            (zxpIdRows leftWires)
            (zxpTensorRows firstWindow.sourceArity (zxpDiagramCodArity firstWindow)
              rightWires rightWires (zxpDiagramDenote secondWindow)
              (zxpIdRows rightWires)))
          (zxpLayersDenote (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
            afterLayers))) :=
    zxpComposeRowsCong contextSource (leftWires + (firstWindow.sourceArity + rightWires))
      (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
        afterLayers)
      hBeforeAll hBeforeAll hCompose1All hCompose2All
      (zxpRelEquivRefl contextSource
        (leftWires + (firstWindow.sourceArity + rightWires))
        (zxpLayersDenote contextSource beforeLayers))
      (zxpComposeRowsCong (leftWires + (firstWindow.sourceArity + rightWires))
        (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
        (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
          afterLayers)
        hTensor1All hTensor2All hAfterAll hAfterAll hMiddle
        (zxpRelEquivRefl (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
          (zxpLayersCodArity (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
            afterLayers)
          (zxpLayersDenote (leftWires + (zxpDiagramCodArity firstWindow + rightWires))
            afterLayers)))
  refine And.intro rfl (And.intro ?_ (And.intro hPadWF1 (And.intro hPadWF2 ?_)))
  · rw [zxpPadDiagramCodArity contextSource leftWires rightWires beforeLayers afterLayers
      firstWindow hBeforeCod,
      zxpPadDiagramCodArity contextSource leftWires rightWires beforeLayers afterLayers
        secondWindow hBeforeCod2, hCodEq]
  · refine zxpRelEquivCast rfl
      (zxpPadDiagramCodArity contextSource leftWires rightWires beforeLayers afterLayers
        firstWindow hBeforeCod).symm ?_
    exact zxpRelEquivTrans hDecomp1
      (zxpRelEquivTrans hMidCong (zxpRelEquivSymm hDecomp2))

/-- Soundness of one extended padded step. -/
theorem zxrStepBundle {firstDiagram secondDiagram : ZxpDiagram}
    (hStep : ZxrStep firstDiagram secondDiagram) :
    ZxpConvBundle firstDiagram secondDiagram := by
  cases hStep with
  | pad contextSource leftWires rightWires beforeLayers afterLayers hMove hBeforeWF
      hBeforeCod hAfterWF =>
      exact zxrPadBundle contextSource leftWires rightWires beforeLayers afterLayers
        (zxrWindowMoveBundle hMove) hBeforeWF hBeforeCod hAfterWF

/-- THE EXTENDED CONGRUENCE: fusion-aware steps under the seed's groupoid closure. -/
inductive ZxrConv : ZxpDiagram -> ZxpDiagram -> Prop where
  | step {firstDiagram secondDiagram : ZxpDiagram}
      (hStep : ZxrStep firstDiagram secondDiagram) : ZxrConv firstDiagram secondDiagram
  | refl (diagram : ZxpDiagram) (hWF : ZxpDiagramWF diagram) : ZxrConv diagram diagram
  | symm {firstDiagram secondDiagram : ZxpDiagram}
      (hConv : ZxrConv firstDiagram secondDiagram) : ZxrConv secondDiagram firstDiagram
  | trans {firstDiagram secondDiagram thirdDiagram : ZxpDiagram}
      (hFirst : ZxrConv firstDiagram secondDiagram)
      (hSecond : ZxrConv secondDiagram thirdDiagram) : ZxrConv firstDiagram thirdDiagram

/-- SOUNDNESS AT ALL ARITIES (deliverable B, the exact bundle shape of the seed's
`zxpConvSound`): extended-convertible diagrams share boundaries, are well-formed, and
denote the same F2 linear relation. -/
theorem zxrConvSound {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxrConv firstDiagram secondDiagram) :
    ZxpConvBundle firstDiagram secondDiagram := by
  induction hConv with
  | step hStep => exact zxrStepBundle hStep
  | refl diagram hWF =>
      exact And.intro rfl (And.intro rfl (And.intro hWF (And.intro hWF
        (zxpRelEquivRefl diagram.sourceArity (zxpDiagramCodArity diagram)
          (zxpDiagramDenote diagram)))))
  | symm _hConv innerBundle => exact zxpConvBundleSymm innerBundle
  | trans _hFirst _hSecond firstBundle secondBundle =>
      exact zxpConvBundleTrans firstBundle secondBundle

/-- THE REFUTATION BRIDGE for the extended congruence: extended convertibility forces
the executable span decision to fire `true`. -/
theorem zxrConvSpanEqB {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxrConv firstDiagram secondDiagram) :
    zxpSpanEqB (zxpDiagramDenote firstDiagram) (zxpDiagramDenote secondDiagram)
      = true := by
  have hBundle := zxrConvSound hConv
  exact zxpSpanEqBOfRelEquiv
    (zxpDiagramDenoteWidth firstDiagram hBundle.right.right.left)
    (zxpAllWidthCast (by rw [hBundle.left, hBundle.right.left])
      (zxpDiagramDenoteWidth secondDiagram hBundle.right.right.right.left))
    hBundle.right.right.right.right

/-- EVERY SEED CONVERSION EMBEDS: `ZxpConv` is a sub-congruence of `ZxrConv`. -/
theorem zxrOfZxpConv {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxpConv firstDiagram secondDiagram) :
    ZxrConv firstDiagram secondDiagram := by
  induction hConv with
  | step hStep =>
      cases hStep with
      | pad contextSource leftWires rightWires beforeLayers afterLayers hMove hBeforeWF
          hBeforeCod hAfterWF =>
          exact ZxrConv.step (ZxrStep.pad contextSource leftWires rightWires
            beforeLayers afterLayers (ZxrWindowMove.seed hMove) hBeforeWF hBeforeCod
            hAfterWF)
  | refl diagram hWF => exact ZxrConv.refl diagram hWF
  | symm _hConv innerConv => exact ZxrConv.symm innerConv
  | trans _hFirst _hSecond firstConv secondConv =>
      exact ZxrConv.trans firstConv secondConv

/-! ## Stage 4 — THE SEPARATOR DIES (deliverable C) -/

/-- THE REPAIR FIRE: the gate's machine-refuted pair NOW CONVERTS — the fused 3->1
Z spider reaches the chained pair by ONE Z-fusion instance at (2,0,1,1) in the empty
context. -/
theorem zxrFusedChainedConv : ZxrConv zxpZFusedTripleDiagram zxpZChainedPairDiagram := by
  have hStep : ZxrStep zxpZChainedPairDiagram zxpZFusedTripleDiagram :=
    ZxrStep.pad 3 0 0 [] [] (ZxrWindowMove.zFuse 2 0 1 1)
      (ZxpLayersWF.nil 3) rfl (ZxpLayersWF.nil _)
  exact ZxrConv.symm (ZxrConv.step hStep)

/-- The X-colour 4->1 chained triple: three layers of binary X spiders. -/
def zxrXChainedTripleDiagram : ZxpDiagram :=
  { sourceArity := 4
    layers := [[ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
      [ZxpCell.xSpider 2 1, ZxpCell.wire], [ZxpCell.xSpider 2 1]] }

/-- The fused 4->1 X spider. -/
def zxrXFusedQuadDiagram : ZxpDiagram :=
  { sourceArity := 4, layers := [[ZxpCell.xSpider 4 1]] }

/-- The X-colour 4->1 fire: the fused quad converts to the three-layer chain by TWO
X-fusion instances ((2,0,1,1) under the first chain layer, then (2,0,2,1) whole). -/
theorem zxrXQuadConv : ZxrConv zxrXFusedQuadDiagram zxrXChainedTripleDiagram := by
  have hStepInner : ZxrStep zxrXChainedTripleDiagram
      { sourceArity := 4
        layers := [[ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.xSpider 3 1]] } :=
    ZxrStep.pad 4 0 0 [[ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire]] []
      (ZxrWindowMove.xFuse 2 0 1 1)
      (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
  have hStepOuter : ZxrStep
      { sourceArity := 4
        layers := [[ZxpCell.xSpider 2 1, ZxpCell.wire, ZxpCell.wire],
          [ZxpCell.xSpider 3 1]] }
      zxrXFusedQuadDiagram :=
    ZxrStep.pad 4 0 0 [] [] (ZxrWindowMove.xFuse 2 0 2 1)
      (ZxpLayersWF.nil 4) rfl (ZxpLayersWF.nil _)
  exact ZxrConv.symm (ZxrConv.trans (ZxrConv.step hStepInner) (ZxrConv.step hStepOuter))

/-- PROPER EXTENSION PIN: the fusion pair is `ZxrConv`-convertible while the gate
machine-refuted its `ZxpConv`-convertibility — the extension is strict. -/
theorem zxrProperExtensionWitness :
    ZxrConv zxpZFusedTripleDiagram zxpZChainedPairDiagram
      /\ Not (ZxpConv zxpZFusedTripleDiagram zxpZChainedPairDiagram) :=
  And.intro zxrFusedChainedConv zxgFusedChainedNotConv

/-- Embed fire: the seed's Hopf derivation rides into the extended congruence. -/
theorem zxrHopfConvEmbedded :
    ZxrConv (zxpRowLhs ZxpRowTag.hopf) (zxpRowRhs ZxpRowTag.hopf) :=
  zxrOfZxpConv zxpHopfConv

/-! ## Stage 5 — THE GATE RE-RUN (deliverable D): the invariant analysis rebuilt

The arc law: refutation pass BEFORE any completeness push.  The gate's fold engine
generalizes verbatim: a per-cell weight is a `ZxrConv` invariant iff it is
wire-vanishing, seed-row balanced, AND balanced on every fusion instance of both
colours.  Then the adversarial hunt: the old separator is kernel-pinned DEAD, and the
whole weight family COLLAPSES to zero. -/

/-- Fold balance of a weight on every Z-fusion instance. -/
def ZxrZFuseBalancedWeight (cellWeight : ZxpCell -> Nat) : Prop :=
  (topInputs topSpares botSpares botOutputs : Nat) ->
    zxgLayersFold cellWeight
        (zxrZFuseLhs topInputs topSpares botSpares botOutputs).layers
      = zxgLayersFold cellWeight
          (zxrZFuseRhs topInputs topSpares botSpares botOutputs).layers

/-- Fold balance of a weight on every X-fusion instance. -/
def ZxrXFuseBalancedWeight (cellWeight : ZxpCell -> Nat) : Prop :=
  (topInputs topSpares botSpares botOutputs : Nat) ->
    zxgLayersFold cellWeight
        (zxrXFuseLhs topInputs topSpares botSpares botOutputs).layers
      = zxgLayersFold cellWeight
          (zxrXFuseRhs topInputs topSpares botSpares botOutputs).layers

/-- INVARIANCE, window level, extended move set. -/
theorem zxrWindowMoveFoldEq (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    (hZFuseBalanced : ZxrZFuseBalancedWeight cellWeight)
    (hXFuseBalanced : ZxrXFuseBalancedWeight cellWeight)
    {firstWindow secondWindow : ZxpDiagram}
    (hMove : ZxrWindowMove firstWindow secondWindow) :
    zxgLayersFold cellWeight firstWindow.layers
      = zxgLayersFold cellWeight secondWindow.layers := by
  cases hMove with
  | seed hSeedMove =>
      exact zxgWindowMoveFoldEq cellWeight hWireZero hRowsBalanced hSeedMove
  | zFuse topInputs topSpares botSpares botOutputs =>
      exact hZFuseBalanced topInputs topSpares botSpares botOutputs
  | xFuse topInputs topSpares botSpares botOutputs =>
      exact hXFuseBalanced topInputs topSpares botSpares botOutputs

/-- INVARIANCE, step level (the padded contexts cancel, as in the gate). -/
theorem zxrStepFoldEq (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    (hZFuseBalanced : ZxrZFuseBalancedWeight cellWeight)
    (hXFuseBalanced : ZxrXFuseBalancedWeight cellWeight)
    {firstDiagram secondDiagram : ZxpDiagram}
    (hStep : ZxrStep firstDiagram secondDiagram) :
    zxgDiagramFold cellWeight firstDiagram = zxgDiagramFold cellWeight secondDiagram := by
  cases hStep with
  | pad contextSource leftWires rightWires beforeLayers afterLayers hMove hBeforeWF
      hBeforeCod hAfterWF =>
      rename_i firstWindow secondWindow
      rw [zxgDiagramFoldPad cellWeight hWireZero contextSource leftWires rightWires
          beforeLayers afterLayers firstWindow,
        zxgDiagramFoldPad cellWeight hWireZero contextSource leftWires rightWires
          beforeLayers afterLayers secondWindow,
        zxrWindowMoveFoldEq cellWeight hWireZero hRowsBalanced hZFuseBalanced
          hXFuseBalanced hMove]

/-- INVARIANCE, full extended congruence: the gate's `zxgConvFoldEq` engine pattern
generalized to `ZxrConv` — any wire-vanishing weight balanced on ALL zxr moves
(including every fusion instance) is conserved. -/
theorem zxrConvFoldEq (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    (hZFuseBalanced : ZxrZFuseBalancedWeight cellWeight)
    (hXFuseBalanced : ZxrXFuseBalancedWeight cellWeight)
    {firstDiagram secondDiagram : ZxpDiagram}
    (hConv : ZxrConv firstDiagram secondDiagram) :
    zxgDiagramFold cellWeight firstDiagram = zxgDiagramFold cellWeight secondDiagram := by
  induction hConv with
  | step hStep =>
      exact zxrStepFoldEq cellWeight hWireZero hRowsBalanced hZFuseBalanced
        hXFuseBalanced hStep
  | refl diagram hWF => exact rfl
  | symm _hConv innerEq => exact innerEq.symm
  | trans _hFirst _hSecond firstEq secondEq => exact firstEq.trans secondEq

/-! ### The old separator is DEAD: kernel imbalance pins on the fusion family -/

/-- KERNEL PIN: the big-spider count of the Z-fusion (2,0,1,1) LEFT side is 0. -/
theorem zxrBigSpiderZFuseLhsFoldPin :
    zxgLayersFold zxgCellBigSpiderWeight (zxrZFuseLhs 2 0 1 1).layers = 0 := rfl

/-- KERNEL PIN: the big-spider count of the Z-fusion (2,0,1,1) RIGHT side is 1. -/
theorem zxrBigSpiderZFuseRhsFoldPin :
    zxgLayersFold zxgCellBigSpiderWeight (zxrZFuseRhs 2 0 1 1).layers = 1 := rfl

/-- THE OLD SEPARATOR DIES: the gate's refuting invariant (the big-spider count) is NOT
balanced on the Z-fusion family — the (2,0,1,1) instance builds a 4-leg spider out of
two 3-leg ones, so the engine's hypotheses now EXCLUDE it, exactly as the gate's repair
option (R1) demanded. -/
theorem zxrBigSpiderNotZFuseBalanced :
    Not (ZxrZFuseBalancedWeight zxgCellBigSpiderWeight) := fun hBalanced =>
  Nat.noConfusion (hBalanced 2 0 1 1 : (0 : Nat) = 1)

/-- The X-colour mirror: the big-spider count is not X-fusion balanced either. -/
theorem zxrBigSpiderNotXFuseBalanced :
    Not (ZxrXFuseBalancedWeight zxgCellBigSpiderWeight) := fun hBalanced =>
  Nat.noConfusion (hBalanced 2 0 1 1 : (0 : Nat) = 1)

/-- The plain Z-spider count dies on the fusion family too (2 spiders -> 1). -/
theorem zxrZCountNotZFuseBalanced :
    Not (ZxrZFuseBalancedWeight zxgCellZCountWeight) := fun hBalanced =>
  Nat.noConfusion (Nat.succ.inj (hBalanced 2 0 1 1 : (2 : Nat) = 1))

/-- The plain X-spider count dies on the X-fusion family. -/
theorem zxrXCountNotXFuseBalanced :
    Not (ZxrXFuseBalancedWeight zxgCellXCountWeight) := fun hBalanced =>
  Nat.noConfusion (Nat.succ.inj (hBalanced 2 0 1 1 : (2 : Nat) = 1))

/-! ### THE COLLAPSE: the whole per-cell weight family trivializes

Any wire-vanishing weight balanced on the fusion family satisfies the Cauchy-type
equation `f a (b+1) + f (1+c) d = f (a+c) (b+d)` on its spider values; over Nat the only
solution is the zero function (two descent arguments — no subtraction, no
multiplication, no order beyond the seed's structural `zxpNatLe`). -/

/-- `a <= a + k` for the structural comparator. -/
theorem zxrNatLeAddRight : (baseValue extraValue : Nat) ->
    zxpNatLe baseValue (baseValue + extraValue) = true
  | baseValue, 0 => zxpNatLeRefl baseValue
  | baseValue, extraPred + 1 =>
      zxpNatLeSuccRight baseValue (baseValue + extraPred)
        (zxrNatLeAddRight baseValue extraPred)

/-- `a <= x + a` for the structural comparator. -/
theorem zxrNatLeAddLeft : (extraValue baseValue : Nat) ->
    zxpNatLe baseValue (extraValue + baseValue) = true
  | extraValue, 0 => zxpNatLeZeroLeft (extraValue + 0)
  | extraValue, basePred + 1 => zxrNatLeAddLeft extraValue basePred

/-- Right-monotonicity of the structural comparator under addition. -/
theorem zxrNatLeAddRightMono {firstValue secondValue : Nat}
    (hLe : zxpNatLe firstValue secondValue = true) : (extraValue : Nat) ->
    zxpNatLe (firstValue + extraValue) (secondValue + extraValue) = true
  | 0 => hLe
  | extraPred + 1 => zxrNatLeAddRightMono hLe extraPred

/-- `n + 1 <= n` is false for the structural comparator. -/
theorem zxrNatLeSuccSelfFalse : (value : Nat) -> zxpNatLe (value + 1) value = false
  | 0 => rfl
  | valuePred + 1 => zxrNatLeSuccSelfFalse valuePred

/-- THE DESCENT: a Nat function that loses a fixed surplus at every successor step
forces the surplus to zero (else `stepFun n + n <= stepFun 0` collides with the
instance `n := stepFun 0 + 1`). -/
theorem zxrDescentForcesZero (stepFun : Nat -> Nat) (surplus : Nat)
    (hStep : (position : Nat) -> stepFun (position + 1) + surplus = stepFun position) :
    surplus = 0 := by
  cases surplus with
  | zero => rfl
  | succ surplusPred =>
      refine False.elim ?_
      have hDescends : (stepCount : Nat) ->
          zxpNatLe (stepFun stepCount + stepCount) (stepFun 0) = true := by
        intro stepCount
        induction stepCount with
        | zero => exact zxpNatLeRefl (stepFun 0 + 0)
        | succ stepPred innerLe =>
            have hStepEq := hStep stepPred
            have hShuffled : (stepFun (stepPred + 1) + 1) + surplusPred
                = stepFun stepPred :=
              (Nat.succ_add (stepFun (stepPred + 1)) surplusPred).trans hStepEq
            have hLeStep : zxpNatLe (stepFun (stepPred + 1) + 1) (stepFun stepPred)
                = true := by
              rw [<- hShuffled]
              exact zxrNatLeAddRight (stepFun (stepPred + 1) + 1) surplusPred
            have hRearrange : (stepFun (stepPred + 1) + 1) + stepPred
                = stepFun (stepPred + 1) + (stepPred + 1) :=
              Nat.succ_add (stepFun (stepPred + 1)) stepPred
            have hMono := zxrNatLeAddRightMono hLeStep stepPred
            rw [hRearrange] at hMono
            exact zxpNatLeTrans _ _ _ hMono innerLe
      have hCollision := hDescends (stepFun 0 + 1)
      have hInflate := zxrNatLeAddLeft (stepFun (stepFun 0 + 1)) (stepFun 0 + 1)
      have hAbsurd := zxpNatLeTrans _ _ _ hInflate hCollision
      rw [zxrNatLeSuccSelfFalse (stepFun 0)] at hAbsurd
      exact Bool.noConfusion hAbsurd

/-- THE FUSION-BALANCE COLLAPSE (abstract form): every Nat-valued spider weight
satisfying the fusion balance equation is identically zero. -/
theorem zxrFuseBalanceForcesZero (spiderWeight : Nat -> Nat -> Nat)
    (hBalance : (topInputs topSpares botSpares botOutputs : Nat) ->
      spiderWeight topInputs (topSpares + 1)
          + spiderWeight (1 + botSpares) botOutputs
        = spiderWeight (topInputs + botSpares) (topSpares + botOutputs)) :
    (domLegs codLegs : Nat) -> spiderWeight domLegs codLegs = 0 := by
  have hUnitSurplusZero : spiderWeight 1 0 = 0 := by
    refine zxrDescentForcesZero (fun columnIndex => spiderWeight 1 columnIndex)
      (spiderWeight 1 0) ?_
    intro position
    exact hBalance 1 position 0 0
  have hSecondSlotStep : (rowLegs columnPred : Nat) ->
      spiderWeight rowLegs (columnPred + 1) = spiderWeight rowLegs columnPred := by
    intro rowLegs columnPred
    have hInstance : spiderWeight rowLegs (columnPred + 1) + spiderWeight 1 0
        = spiderWeight rowLegs columnPred := hBalance rowLegs columnPred 0 0
    rw [hUnitSurplusZero] at hInstance
    exact hInstance
  have hSecondSlotInvariant : (rowLegs columnLegs : Nat) ->
      spiderWeight rowLegs columnLegs = spiderWeight rowLegs 0 := by
    intro rowLegs columnLegs
    induction columnLegs with
    | zero => rfl
    | succ columnPred innerEq => exact (hSecondSlotStep rowLegs columnPred).trans innerEq
  have hZeroColumnSurplusZero : spiderWeight 0 0 = 0 := by
    refine zxrDescentForcesZero (fun rowIndex => spiderWeight rowIndex 0)
      (spiderWeight 0 0) ?_
    intro position
    have hInstance : spiderWeight 0 1 + spiderWeight (1 + position) 0
        = spiderWeight position 0 := by
      have hRaw := hBalance 0 0 position 0
      rw [Nat.zero_add position] at hRaw
      exact hRaw
    rw [hSecondSlotInvariant 0 1,
      Nat.add_comm (spiderWeight 0 0) (spiderWeight (1 + position) 0)] at hInstance
    have hFlip : spiderWeight (position + 1) 0 = spiderWeight (1 + position) 0 :=
      congrArg (fun innerLegs => spiderWeight innerLegs 0) (Nat.add_comm position 1)
    rw [<- hFlip] at hInstance
    exact hInstance
  have hFirstSlotStep : (rowPred : Nat) ->
      spiderWeight (1 + rowPred) 0 = spiderWeight rowPred 0 := by
    intro rowPred
    have hInstance : spiderWeight 0 1 + spiderWeight (1 + rowPred) 0
        = spiderWeight rowPred 0 := by
      have hRaw := hBalance 0 0 rowPred 0
      rw [Nat.zero_add rowPred] at hRaw
      exact hRaw
    rw [hSecondSlotInvariant 0 1, hZeroColumnSurplusZero, Nat.zero_add] at hInstance
    exact hInstance
  have hFirstSlotInvariant : (rowLegs : Nat) ->
      spiderWeight rowLegs 0 = spiderWeight 0 0 := by
    intro rowLegs
    induction rowLegs with
    | zero => rfl
    | succ rowPred innerEq =>
        have hFlip : spiderWeight (rowPred + 1) 0 = spiderWeight (1 + rowPred) 0 :=
          congrArg (fun innerLegs => spiderWeight innerLegs 0) (Nat.add_comm rowPred 1)
        exact (hFlip.trans (hFirstSlotStep rowPred)).trans innerEq
  intro domLegs codLegs
  exact ((hSecondSlotInvariant domLegs codLegs).trans
    (hFirstSlotInvariant domLegs)).trans hZeroColumnSurplusZero

/-- Single-cell layer fold. -/
theorem zxrCellFoldSingle (cellWeight : ZxpCell -> Nat) (cell : ZxpCell) :
    zxgCellFold cellWeight [cell] = cellWeight cell := rfl

/-- Fold balance on the Z-fusion family normalizes to the Cauchy equation on the
Z-spider weights. -/
theorem zxrZFuseBalanceEquation (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hZFuseBalanced : ZxrZFuseBalancedWeight cellWeight)
    (topInputs topSpares botSpares botOutputs : Nat) :
    cellWeight (ZxpCell.zSpider topInputs (topSpares + 1))
        + cellWeight (ZxpCell.zSpider (1 + botSpares) botOutputs)
      = cellWeight (ZxpCell.zSpider (topInputs + botSpares)
          (topSpares + botOutputs)) := by
  have hRaw : (cellWeight (ZxpCell.zSpider topInputs (topSpares + 1))
        + zxgCellFold cellWeight (zxpWireCells botSpares))
      + zxgCellFold cellWeight (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.zSpider (1 + botSpares) botOutputs])
      = cellWeight (ZxpCell.zSpider (topInputs + botSpares) (topSpares + botOutputs)) :=
    hZFuseBalanced topInputs topSpares botSpares botOutputs
  rw [zxgCellFoldCat cellWeight (zxpWireCells topSpares)
      [ZxpCell.zSpider (1 + botSpares) botOutputs],
    zxgCellFoldWires cellWeight hWireZero botSpares,
    zxgCellFoldWires cellWeight hWireZero topSpares,
    zxrCellFoldSingle cellWeight (ZxpCell.zSpider (1 + botSpares) botOutputs),
    Nat.add_zero, Nat.zero_add] at hRaw
  exact hRaw

/-- Fold balance on the X-fusion family normalizes to the Cauchy equation on the
X-spider weights (mirror). -/
theorem zxrXFuseBalanceEquation (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hXFuseBalanced : ZxrXFuseBalancedWeight cellWeight)
    (topInputs topSpares botSpares botOutputs : Nat) :
    cellWeight (ZxpCell.xSpider topInputs (topSpares + 1))
        + cellWeight (ZxpCell.xSpider (1 + botSpares) botOutputs)
      = cellWeight (ZxpCell.xSpider (topInputs + botSpares)
          (topSpares + botOutputs)) := by
  have hRaw : (cellWeight (ZxpCell.xSpider topInputs (topSpares + 1))
        + zxgCellFold cellWeight (zxpWireCells botSpares))
      + zxgCellFold cellWeight (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.xSpider (1 + botSpares) botOutputs])
      = cellWeight (ZxpCell.xSpider (topInputs + botSpares) (topSpares + botOutputs)) :=
    hXFuseBalanced topInputs topSpares botSpares botOutputs
  rw [zxgCellFoldCat cellWeight (zxpWireCells topSpares)
      [ZxpCell.xSpider (1 + botSpares) botOutputs],
    zxgCellFoldWires cellWeight hWireZero botSpares,
    zxgCellFoldWires cellWeight hWireZero topSpares,
    zxrCellFoldSingle cellWeight (ZxpCell.xSpider (1 + botSpares) botOutputs),
    Nat.add_zero, Nat.zero_add] at hRaw
  exact hRaw

/-- Every wire-vanishing Z-fusion-balanced weight vanishes on ALL Z spiders. -/
theorem zxrZSpiderWeightZero (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hZFuseBalanced : ZxrZFuseBalancedWeight cellWeight)
    (domLegs codLegs : Nat) : cellWeight (ZxpCell.zSpider domLegs codLegs) = 0 :=
  zxrFuseBalanceForcesZero
    (fun rowLegs columnLegs => cellWeight (ZxpCell.zSpider rowLegs columnLegs))
    (fun topInputs topSpares botSpares botOutputs =>
      zxrZFuseBalanceEquation cellWeight hWireZero hZFuseBalanced topInputs topSpares
        botSpares botOutputs)
    domLegs codLegs

/-- Every wire-vanishing X-fusion-balanced weight vanishes on ALL X spiders. -/
theorem zxrXSpiderWeightZero (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hXFuseBalanced : ZxrXFuseBalancedWeight cellWeight)
    (domLegs codLegs : Nat) : cellWeight (ZxpCell.xSpider domLegs codLegs) = 0 :=
  zxrFuseBalanceForcesZero
    (fun rowLegs columnLegs => cellWeight (ZxpCell.xSpider rowLegs columnLegs))
    (fun topInputs topSpares botSpares botOutputs =>
      zxrXFuseBalanceEquation cellWeight hWireZero hXFuseBalanced topInputs topSpares
        botSpares botOutputs)
    domLegs codLegs

/-- THE COLLAPSE THEOREM: every wire-vanishing weight balanced on the WHOLE extended
move set is identically zero on every cell — the per-cell count family (where the old
separator lived) holds NO invariant information for `ZxrConv` at all.  (The crossing
weight dies against the seed's `xMonoidComm` row once the X spiders are zero.) -/
theorem zxrBalancedWeightCollapse (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    (hZFuseBalanced : ZxrZFuseBalancedWeight cellWeight)
    (hXFuseBalanced : ZxrXFuseBalancedWeight cellWeight) :
    (cell : ZxpCell) -> cellWeight cell = 0
  | ZxpCell.zSpider domLegs codLegs =>
      zxrZSpiderWeightZero cellWeight hWireZero hZFuseBalanced domLegs codLegs
  | ZxpCell.xSpider domLegs codLegs =>
      zxrXSpiderWeightZero cellWeight hWireZero hXFuseBalanced domLegs codLegs
  | ZxpCell.wire => hWireZero
  | ZxpCell.crossing => by
      have hCommRow : cellWeight ZxpCell.crossing + cellWeight (ZxpCell.xSpider 2 1)
          = cellWeight (ZxpCell.xSpider 2 1) :=
        hRowsBalanced ZxpRowTag.xMonoidComm
      rw [zxrXSpiderWeightZero cellWeight hWireZero hXFuseBalanced 2 1] at hCommRow
      exact hCommRow

/-- Corollary: any engine-admissible weight folds to the CONSTANT ZERO functional on
every diagram — the fold engine detects nothing on the extended calculus. -/
theorem zxrBalancedWeightFoldZero (cellWeight : ZxpCell -> Nat)
    (hWireZero : cellWeight ZxpCell.wire = 0)
    (hRowsBalanced : ZxgRowBalancedWeight cellWeight)
    (hZFuseBalanced : ZxrZFuseBalancedWeight cellWeight)
    (hXFuseBalanced : ZxrXFuseBalancedWeight cellWeight)
    (diagram : ZxpDiagram) : zxgDiagramFold cellWeight diagram = 0 := by
  have hCellZero := zxrBalancedWeightCollapse cellWeight hWireZero hRowsBalanced
    hZFuseBalanced hXFuseBalanced
  have hCellFoldZero : (cells : List ZxpCell) -> zxgCellFold cellWeight cells = 0 := by
    intro cells
    induction cells with
    | nil => rfl
    | cons headCell restCells innerEq =>
        show cellWeight headCell + zxgCellFold cellWeight restCells = 0
        rw [hCellZero headCell, innerEq]
  have hLayersFoldZero : (layers : List (List ZxpCell)) ->
      zxgLayersFold cellWeight layers = 0 := by
    intro layers
    induction layers with
    | nil => rfl
    | cons headLayer restLayers innerEq =>
        show zxgCellFold cellWeight headLayer + zxgLayersFold cellWeight restLayers = 0
        rw [hCellFoldZero headLayer, innerEq]
  exact hLayersFoldZero diagram.layers

/-! ## Stage 6 — THE BASE-COUNT DELTA RE-RUN (deliverable D, second leg)

The gate's Stage-2 mod-2 analysis extended to the fusion family AT ALL ARITIES: the
general delta lemmas `zxrZFuseDeltaGeneral`/`zxrXFuseDeltaGeneral` pin every fusion
instance's mod-2 delta on the 7-component base count vector to one of FOUR literal
vectors (two per colour, split by the parity of the spare wire count `botSpares +
topSpares`) — this is the PROVED SATURATION of the fusion family's contribution to the
delta row space.  The extended literal table spans the SAME 6-dimensional row space as
the gate's (`zxrExtendedDeltaSpanBasisPin`, kernel span decision), so the preserved
mod-2 functional lattice, re-enumerated over all 128 candidates against the extended
table (`zxrPreservedLatticeReclassified`), is STILL exactly {0, legs-parity}; the sole
survivor stays boundary-determined by the gate's
`zxgLegsParityFunctionalBoundaryDetermined` (a per-diagram statement, untouched by the
move-set extension) and is orthogonal to every fusion delta at every arity
(`zxrLegsParityOrthogonalZFuseDelta` / `zxrLegsParityOrthogonalXFuseDelta`). -/

/-- Wire-count fold over a wire layer counts the strands. -/
theorem zxrWireCountFoldWires : (strandCount : Nat) ->
    zxgCellFold zxgCellWireCountWeight (zxpWireCells strandCount) = strandCount
  | 0 => rfl
  | strandPred + 1 => by
      show 1 + zxgCellFold zxgCellWireCountWeight (zxpWireCells strandPred)
        = strandPred + 1
      rw [zxrWireCountFoldWires strandPred]
      exact Nat.add_comm 1 strandPred

/-- The base count vector of the Z-fusion LEFT side, all arities.  Components:
[zCount, xCount, wireCount, crossingCount, layerCount, zLegs, xLegs]. -/
theorem zxrZFuseLhsCountVector (topInputs topSpares botSpares botOutputs : Nat) :
    zxgCountVector (zxrZFuseLhs topInputs topSpares botSpares botOutputs)
      = [2, 0, botSpares + topSpares, 0, 2,
          (topInputs + (topSpares + 1)) + ((1 + botSpares) + botOutputs), 0] := by
  have hZCount : zxgLayersFold zxgCellZCountWeight
      (zxrZFuseLhs topInputs topSpares botSpares botOutputs).layers = 2 := by
    show (1 + zxgCellFold zxgCellZCountWeight (zxpWireCells botSpares))
        + zxgCellFold zxgCellZCountWeight (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.zSpider (1 + botSpares) botOutputs])
      = 2
    rw [zxgCellFoldWires zxgCellZCountWeight rfl botSpares,
      zxgCellFoldCat zxgCellZCountWeight (zxpWireCells topSpares)
        [ZxpCell.zSpider (1 + botSpares) botOutputs],
      zxgCellFoldWires zxgCellZCountWeight rfl topSpares]
    exact rfl
  have hXCount : zxgLayersFold zxgCellXCountWeight
      (zxrZFuseLhs topInputs topSpares botSpares botOutputs).layers = 0 := by
    show (0 + zxgCellFold zxgCellXCountWeight (zxpWireCells botSpares))
        + zxgCellFold zxgCellXCountWeight (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.zSpider (1 + botSpares) botOutputs])
      = 0
    rw [zxgCellFoldWires zxgCellXCountWeight rfl botSpares,
      zxgCellFoldCat zxgCellXCountWeight (zxpWireCells topSpares)
        [ZxpCell.zSpider (1 + botSpares) botOutputs],
      zxgCellFoldWires zxgCellXCountWeight rfl topSpares]
    exact rfl
  have hWireCount : zxgLayersFold zxgCellWireCountWeight
      (zxrZFuseLhs topInputs topSpares botSpares botOutputs).layers
      = botSpares + topSpares := by
    show (0 + zxgCellFold zxgCellWireCountWeight (zxpWireCells botSpares))
        + zxgCellFold zxgCellWireCountWeight (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.zSpider (1 + botSpares) botOutputs])
      = botSpares + topSpares
    rw [zxrWireCountFoldWires botSpares,
      zxgCellFoldCat zxgCellWireCountWeight (zxpWireCells topSpares)
        [ZxpCell.zSpider (1 + botSpares) botOutputs],
      zxrWireCountFoldWires topSpares,
      Nat.zero_add botSpares]
    exact rfl
  have hCrossCount : zxgLayersFold zxgCellCrossCountWeight
      (zxrZFuseLhs topInputs topSpares botSpares botOutputs).layers = 0 := by
    show (0 + zxgCellFold zxgCellCrossCountWeight (zxpWireCells botSpares))
        + zxgCellFold zxgCellCrossCountWeight (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.zSpider (1 + botSpares) botOutputs])
      = 0
    rw [zxgCellFoldWires zxgCellCrossCountWeight rfl botSpares,
      zxgCellFoldCat zxgCellCrossCountWeight (zxpWireCells topSpares)
        [ZxpCell.zSpider (1 + botSpares) botOutputs],
      zxgCellFoldWires zxgCellCrossCountWeight rfl topSpares]
    exact rfl
  have hZLegs : zxgLayersFold zxgCellZLegsWeight
      (zxrZFuseLhs topInputs topSpares botSpares botOutputs).layers
      = (topInputs + (topSpares + 1)) + ((1 + botSpares) + botOutputs) := by
    show ((topInputs + (topSpares + 1))
          + zxgCellFold zxgCellZLegsWeight (zxpWireCells botSpares))
        + zxgCellFold zxgCellZLegsWeight (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.zSpider (1 + botSpares) botOutputs])
      = (topInputs + (topSpares + 1)) + ((1 + botSpares) + botOutputs)
    rw [zxgCellFoldWires zxgCellZLegsWeight rfl botSpares,
      zxgCellFoldCat zxgCellZLegsWeight (zxpWireCells topSpares)
        [ZxpCell.zSpider (1 + botSpares) botOutputs],
      zxgCellFoldWires zxgCellZLegsWeight rfl topSpares,
      Nat.add_zero (topInputs + (topSpares + 1)),
      Nat.zero_add (zxgCellFold zxgCellZLegsWeight
        [ZxpCell.zSpider (1 + botSpares) botOutputs])]
    exact rfl
  have hXLegs : zxgLayersFold zxgCellXLegsWeight
      (zxrZFuseLhs topInputs topSpares botSpares botOutputs).layers = 0 := by
    show (0 + zxgCellFold zxgCellXLegsWeight (zxpWireCells botSpares))
        + zxgCellFold zxgCellXLegsWeight (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.zSpider (1 + botSpares) botOutputs])
      = 0
    rw [zxgCellFoldWires zxgCellXLegsWeight rfl botSpares,
      zxgCellFoldCat zxgCellXLegsWeight (zxpWireCells topSpares)
        [ZxpCell.zSpider (1 + botSpares) botOutputs],
      zxgCellFoldWires zxgCellXLegsWeight rfl topSpares]
    exact rfl
  show [zxgLayersFold zxgCellZCountWeight
      (zxrZFuseLhs topInputs topSpares botSpares botOutputs).layers,
    zxgLayersFold zxgCellXCountWeight
      (zxrZFuseLhs topInputs topSpares botSpares botOutputs).layers,
    zxgLayersFold zxgCellWireCountWeight
      (zxrZFuseLhs topInputs topSpares botSpares botOutputs).layers,
    zxgLayersFold zxgCellCrossCountWeight
      (zxrZFuseLhs topInputs topSpares botSpares botOutputs).layers,
    zxgLayerCount (zxrZFuseLhs topInputs topSpares botSpares botOutputs).layers,
    zxgLayersFold zxgCellZLegsWeight
      (zxrZFuseLhs topInputs topSpares botSpares botOutputs).layers,
    zxgLayersFold zxgCellXLegsWeight
      (zxrZFuseLhs topInputs topSpares botSpares botOutputs).layers]
    = [2, 0, botSpares + topSpares, 0, 2,
        (topInputs + (topSpares + 1)) + ((1 + botSpares) + botOutputs), 0]
  rw [hZCount, hXCount, hWireCount, hCrossCount, hZLegs, hXLegs]
  exact rfl

/-- The base count vector of the Z-fusion RIGHT side, all arities (pure reduction). -/
theorem zxrZFuseRhsCountVector (topInputs topSpares botSpares botOutputs : Nat) :
    zxgCountVector (zxrZFuseRhs topInputs topSpares botSpares botOutputs)
      = [1, 0, 0, 0, 1, (topInputs + botSpares) + (topSpares + botOutputs), 0] := rfl

/-- The base count vector of the X-fusion LEFT side, all arities (colour mirror). -/
theorem zxrXFuseLhsCountVector (topInputs topSpares botSpares botOutputs : Nat) :
    zxgCountVector (zxrXFuseLhs topInputs topSpares botSpares botOutputs)
      = [0, 2, botSpares + topSpares, 0, 2, 0,
          (topInputs + (topSpares + 1)) + ((1 + botSpares) + botOutputs)] := by
  have hZCount : zxgLayersFold zxgCellZCountWeight
      (zxrXFuseLhs topInputs topSpares botSpares botOutputs).layers = 0 := by
    show (0 + zxgCellFold zxgCellZCountWeight (zxpWireCells botSpares))
        + zxgCellFold zxgCellZCountWeight (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.xSpider (1 + botSpares) botOutputs])
      = 0
    rw [zxgCellFoldWires zxgCellZCountWeight rfl botSpares,
      zxgCellFoldCat zxgCellZCountWeight (zxpWireCells topSpares)
        [ZxpCell.xSpider (1 + botSpares) botOutputs],
      zxgCellFoldWires zxgCellZCountWeight rfl topSpares]
    exact rfl
  have hXCount : zxgLayersFold zxgCellXCountWeight
      (zxrXFuseLhs topInputs topSpares botSpares botOutputs).layers = 2 := by
    show (1 + zxgCellFold zxgCellXCountWeight (zxpWireCells botSpares))
        + zxgCellFold zxgCellXCountWeight (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.xSpider (1 + botSpares) botOutputs])
      = 2
    rw [zxgCellFoldWires zxgCellXCountWeight rfl botSpares,
      zxgCellFoldCat zxgCellXCountWeight (zxpWireCells topSpares)
        [ZxpCell.xSpider (1 + botSpares) botOutputs],
      zxgCellFoldWires zxgCellXCountWeight rfl topSpares]
    exact rfl
  have hWireCount : zxgLayersFold zxgCellWireCountWeight
      (zxrXFuseLhs topInputs topSpares botSpares botOutputs).layers
      = botSpares + topSpares := by
    show (0 + zxgCellFold zxgCellWireCountWeight (zxpWireCells botSpares))
        + zxgCellFold zxgCellWireCountWeight (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.xSpider (1 + botSpares) botOutputs])
      = botSpares + topSpares
    rw [zxrWireCountFoldWires botSpares,
      zxgCellFoldCat zxgCellWireCountWeight (zxpWireCells topSpares)
        [ZxpCell.xSpider (1 + botSpares) botOutputs],
      zxrWireCountFoldWires topSpares,
      Nat.zero_add botSpares]
    exact rfl
  have hCrossCount : zxgLayersFold zxgCellCrossCountWeight
      (zxrXFuseLhs topInputs topSpares botSpares botOutputs).layers = 0 := by
    show (0 + zxgCellFold zxgCellCrossCountWeight (zxpWireCells botSpares))
        + zxgCellFold zxgCellCrossCountWeight (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.xSpider (1 + botSpares) botOutputs])
      = 0
    rw [zxgCellFoldWires zxgCellCrossCountWeight rfl botSpares,
      zxgCellFoldCat zxgCellCrossCountWeight (zxpWireCells topSpares)
        [ZxpCell.xSpider (1 + botSpares) botOutputs],
      zxgCellFoldWires zxgCellCrossCountWeight rfl topSpares]
    exact rfl
  have hZLegs : zxgLayersFold zxgCellZLegsWeight
      (zxrXFuseLhs topInputs topSpares botSpares botOutputs).layers = 0 := by
    show (0 + zxgCellFold zxgCellZLegsWeight (zxpWireCells botSpares))
        + zxgCellFold zxgCellZLegsWeight (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.xSpider (1 + botSpares) botOutputs])
      = 0
    rw [zxgCellFoldWires zxgCellZLegsWeight rfl botSpares,
      zxgCellFoldCat zxgCellZLegsWeight (zxpWireCells topSpares)
        [ZxpCell.xSpider (1 + botSpares) botOutputs],
      zxgCellFoldWires zxgCellZLegsWeight rfl topSpares]
    exact rfl
  have hXLegs : zxgLayersFold zxgCellXLegsWeight
      (zxrXFuseLhs topInputs topSpares botSpares botOutputs).layers
      = (topInputs + (topSpares + 1)) + ((1 + botSpares) + botOutputs) := by
    show ((topInputs + (topSpares + 1))
          + zxgCellFold zxgCellXLegsWeight (zxpWireCells botSpares))
        + zxgCellFold zxgCellXLegsWeight (zxpCatCells (zxpWireCells topSpares)
          [ZxpCell.xSpider (1 + botSpares) botOutputs])
      = (topInputs + (topSpares + 1)) + ((1 + botSpares) + botOutputs)
    rw [zxgCellFoldWires zxgCellXLegsWeight rfl botSpares,
      zxgCellFoldCat zxgCellXLegsWeight (zxpWireCells topSpares)
        [ZxpCell.xSpider (1 + botSpares) botOutputs],
      zxgCellFoldWires zxgCellXLegsWeight rfl topSpares,
      Nat.add_zero (topInputs + (topSpares + 1)),
      Nat.zero_add (zxgCellFold zxgCellXLegsWeight
        [ZxpCell.xSpider (1 + botSpares) botOutputs])]
    exact rfl
  show [zxgLayersFold zxgCellZCountWeight
      (zxrXFuseLhs topInputs topSpares botSpares botOutputs).layers,
    zxgLayersFold zxgCellXCountWeight
      (zxrXFuseLhs topInputs topSpares botSpares botOutputs).layers,
    zxgLayersFold zxgCellWireCountWeight
      (zxrXFuseLhs topInputs topSpares botSpares botOutputs).layers,
    zxgLayersFold zxgCellCrossCountWeight
      (zxrXFuseLhs topInputs topSpares botSpares botOutputs).layers,
    zxgLayerCount (zxrXFuseLhs topInputs topSpares botSpares botOutputs).layers,
    zxgLayersFold zxgCellZLegsWeight
      (zxrXFuseLhs topInputs topSpares botSpares botOutputs).layers,
    zxgLayersFold zxgCellXLegsWeight
      (zxrXFuseLhs topInputs topSpares botSpares botOutputs).layers]
    = [0, 2, botSpares + topSpares, 0, 2, 0,
        (topInputs + (topSpares + 1)) + ((1 + botSpares) + botOutputs)]
  rw [hZCount, hXCount, hWireCount, hCrossCount, hZLegs, hXLegs]
  exact rfl

/-- The base count vector of the X-fusion RIGHT side, all arities (pure reduction). -/
theorem zxrXFuseRhsCountVector (topInputs topSpares botSpares botOutputs : Nat) :
    zxgCountVector (zxrXFuseRhs topInputs topSpares botSpares botOutputs)
      = [0, 1, 0, 0, 1, 0, (topInputs + botSpares) + (topSpares + botOutputs)] := rfl

/-- The exact Nat bookkeeping of Kissinger (sp): the two fused spiders carry the fused
spider's legs PLUS the two endpoints of the vanished shared wire. -/
theorem zxrFuseLegsShift (topInputs topSpares botSpares botOutputs : Nat) :
    (topInputs + (topSpares + 1)) + ((1 + botSpares) + botOutputs)
      = ((topInputs + botSpares) + (topSpares + botOutputs)) + 2 := by
  rw [zxgAddMedial topInputs (topSpares + 1) (1 + botSpares) botOutputs,
    Nat.add_comm 1 botSpares,
    <- Nat.add_assoc topInputs botSpares 1,
    Nat.succ_add topSpares botOutputs,
    Nat.succ_add (topInputs + botSpares) ((topSpares + botOutputs) + 1),
    <- Nat.add_assoc (topInputs + botSpares) (topSpares + botOutputs) 1]

/-- THE GENERAL Z-FUSION DELTA (proved saturation lemma, all arities): the mod-2 delta of
every Z-fusion instance on the base count vector is
`[1, 0, parity(spare wires), 0, 1, 0, 0]`. -/
theorem zxrZFuseDeltaGeneral (topInputs topSpares botSpares botOutputs : Nat) :
    zxgVectorDeltaMod2
        (zxgCountVector (zxrZFuseLhs topInputs topSpares botSpares botOutputs))
        (zxgCountVector (zxrZFuseRhs topInputs topSpares botSpares botOutputs))
      = [true, false, zxgParityB (botSpares + topSpares), false, true, false, false] := by
  rw [zxrZFuseLhsCountVector topInputs topSpares botSpares botOutputs,
    zxrZFuseRhsCountVector topInputs topSpares botSpares botOutputs]
  show [true, false,
      zxpXorB (zxgParityB (botSpares + topSpares)) false, false, true,
      zxpXorB
        (zxgParityB ((topInputs + (topSpares + 1)) + ((1 + botSpares) + botOutputs)))
        (zxgParityB ((topInputs + botSpares) + (topSpares + botOutputs))),
      false]
    = [true, false, zxgParityB (botSpares + topSpares), false, true, false, false]
  rw [zxrFuseLegsShift topInputs topSpares botSpares botOutputs,
    zxgParityBAdd ((topInputs + botSpares) + (topSpares + botOutputs)) 2,
    show zxgParityB 2 = false from rfl,
    zxpXorBFalseRight (zxgParityB ((topInputs + botSpares) + (topSpares + botOutputs))),
    zxpXorBSelf (zxgParityB ((topInputs + botSpares) + (topSpares + botOutputs))),
    zxpXorBFalseRight (zxgParityB (botSpares + topSpares))]

/-- THE GENERAL X-FUSION DELTA (proved saturation lemma, colour mirror). -/
theorem zxrXFuseDeltaGeneral (topInputs topSpares botSpares botOutputs : Nat) :
    zxgVectorDeltaMod2
        (zxgCountVector (zxrXFuseLhs topInputs topSpares botSpares botOutputs))
        (zxgCountVector (zxrXFuseRhs topInputs topSpares botSpares botOutputs))
      = [false, true, zxgParityB (botSpares + topSpares), false, true, false, false] := by
  rw [zxrXFuseLhsCountVector topInputs topSpares botSpares botOutputs,
    zxrXFuseRhsCountVector topInputs topSpares botSpares botOutputs]
  show [false, true,
      zxpXorB (zxgParityB (botSpares + topSpares)) false, false, true, false,
      zxpXorB
        (zxgParityB ((topInputs + (topSpares + 1)) + ((1 + botSpares) + botOutputs)))
        (zxgParityB ((topInputs + botSpares) + (topSpares + botOutputs)))]
    = [false, true, zxgParityB (botSpares + topSpares), false, true, false, false]
  rw [zxrFuseLegsShift topInputs topSpares botSpares botOutputs,
    zxgParityBAdd ((topInputs + botSpares) + (topSpares + botOutputs)) 2,
    show zxgParityB 2 = false from rfl,
    zxpXorBFalseRight (zxgParityB ((topInputs + botSpares) + (topSpares + botOutputs))),
    zxpXorBSelf (zxgParityB ((topInputs + botSpares) + (topSpares + botOutputs))),
    zxpXorBFalseRight (zxgParityB (botSpares + topSpares))]

/-- Z-fusion delta literal, even spare wires. -/
def zxrFuseDeltaZEven : List Bool := [true, false, false, false, true, false, false]

/-- Z-fusion delta literal, odd spare wires. -/
def zxrFuseDeltaZOdd : List Bool := [true, false, true, false, true, false, false]

/-- X-fusion delta literal, even spare wires. -/
def zxrFuseDeltaXEven : List Bool := [false, true, false, false, true, false, false]

/-- X-fusion delta literal, odd spare wires. -/
def zxrFuseDeltaXOdd : List Bool := [false, true, true, false, true, false, false]

/-- SATURATION, case form: every Z-fusion instance's delta is one of the two literals. -/
theorem zxrZFuseDeltaCases (topInputs topSpares botSpares botOutputs : Nat) :
    zxgVectorDeltaMod2
        (zxgCountVector (zxrZFuseLhs topInputs topSpares botSpares botOutputs))
        (zxgCountVector (zxrZFuseRhs topInputs topSpares botSpares botOutputs))
      = zxrFuseDeltaZEven
    \/ zxgVectorDeltaMod2
        (zxgCountVector (zxrZFuseLhs topInputs topSpares botSpares botOutputs))
        (zxgCountVector (zxrZFuseRhs topInputs topSpares botSpares botOutputs))
      = zxrFuseDeltaZOdd := by
  cases hSpareParity : zxgParityB (botSpares + topSpares) with
  | false =>
      refine Or.inl ?_
      rw [zxrZFuseDeltaGeneral topInputs topSpares botSpares botOutputs, hSpareParity]
      exact rfl
  | true =>
      refine Or.inr ?_
      rw [zxrZFuseDeltaGeneral topInputs topSpares botSpares botOutputs, hSpareParity]
      exact rfl

/-- SATURATION, case form: every X-fusion instance's delta is one of the two literals. -/
theorem zxrXFuseDeltaCases (topInputs topSpares botSpares botOutputs : Nat) :
    zxgVectorDeltaMod2
        (zxgCountVector (zxrXFuseLhs topInputs topSpares botSpares botOutputs))
        (zxgCountVector (zxrXFuseRhs topInputs topSpares botSpares botOutputs))
      = zxrFuseDeltaXEven
    \/ zxgVectorDeltaMod2
        (zxgCountVector (zxrXFuseLhs topInputs topSpares botSpares botOutputs))
        (zxgCountVector (zxrXFuseRhs topInputs topSpares botSpares botOutputs))
      = zxrFuseDeltaXOdd := by
  cases hSpareParity : zxgParityB (botSpares + topSpares) with
  | false =>
      refine Or.inl ?_
      rw [zxrXFuseDeltaGeneral topInputs topSpares botSpares botOutputs, hSpareParity]
      exact rfl
  | true =>
      refine Or.inr ?_
      rw [zxrXFuseDeltaGeneral topInputs topSpares botSpares botOutputs, hSpareParity]
      exact rfl

/-- THE EXTENDED DELTA TABLE: the gate's 35 generator rows plus the four fusion delta
literals (which saturate the whole fusion family by the case lemmas above). -/
def zxrExtendedDeltaTable : List (List Bool) :=
  zxpCatRows zxgFullDeltaTable
    [zxrFuseDeltaZEven, zxrFuseDeltaZOdd, zxrFuseDeltaXEven, zxrFuseDeltaXOdd]

/-- KERNEL PIN: the extended delta row space equals the gate's SAME 6-dimensional basis —
the fusion family adds moves but NO new mod-2 direction on the base count vector. -/
theorem zxrExtendedDeltaSpanBasisPin :
    zxpSpanEqB zxrExtendedDeltaTable zxgDeltaSpanBasis = true := rfl

/-- Classifier over the EXTENDED table: orthogonality holds exactly for the zero
functional and the legs-parity functional (the gate's classifier re-pointed). -/
def zxrIsPreservedExactlyLegsParityB : List (List Bool) -> Bool
  | [] => true
  | headFunctional :: restFunctionals =>
      cond (zxgBoolEqB (zxgIsOrthogonalToAllB headFunctional zxrExtendedDeltaTable)
          (cond (zxgRowEqB headFunctional zxgZeroFunctional) true
            (zxgRowEqB headFunctional zxgLegsParityFunctional)))
        (zxrIsPreservedExactlyLegsParityB restFunctionals) false

/-- KERNEL PIN: over ALL 128 mod-2 functionals on the base count vector, the preserved
lattice of the EXTENDED move set is still exactly {0, legs-parity} — and the gate already
proved the survivor boundary-determined (`zxgLegsParityFunctionalBoundaryDetermined`). -/
theorem zxrPreservedLatticeReclassified :
    zxrIsPreservedExactlyLegsParityB (zxgAllBoolVectors 7) = true := rfl

/-- The survivor is orthogonal to EVERY Z-fusion delta at every arity (general form,
through the saturation cases — not only the two literals in the table). -/
theorem zxrLegsParityOrthogonalZFuseDelta
    (topInputs topSpares botSpares botOutputs : Nat) :
    zxgDotB zxgLegsParityFunctional
        (zxgVectorDeltaMod2
          (zxgCountVector (zxrZFuseLhs topInputs topSpares botSpares botOutputs))
          (zxgCountVector (zxrZFuseRhs topInputs topSpares botSpares botOutputs)))
      = false := by
  cases zxrZFuseDeltaCases topInputs topSpares botSpares botOutputs with
  | inl hEven =>
      rw [hEven]
      exact rfl
  | inr hOdd =>
      rw [hOdd]
      exact rfl

/-- The survivor is orthogonal to EVERY X-fusion delta at every arity (colour mirror). -/
theorem zxrLegsParityOrthogonalXFuseDelta
    (topInputs topSpares botSpares botOutputs : Nat) :
    zxgDotB zxgLegsParityFunctional
        (zxgVectorDeltaMod2
          (zxgCountVector (zxrXFuseLhs topInputs topSpares botSpares botOutputs))
          (zxgCountVector (zxrXFuseRhs topInputs topSpares botSpares botOutputs)))
      = false := by
  cases zxrXFuseDeltaCases topInputs topSpares botSpares botOutputs with
  | inl hEven =>
      rw [hEven]
      exact rfl
  | inr hOdd =>
      rw [hOdd]
      exact rfl

/-! ## Stage 7 — extra fires: the recursion demos and the surviving FALSE case -/

/-- Unit absorption instance (the brief's R1 at `a = 0`): a Z unit feeding a 2->1
Z spider. -/
def zxrZUnitAbsorptionLhsDiagram : ZxpDiagram :=
  { sourceArity := 1
    layers := [[ZxpCell.zSpider 0 1, ZxpCell.wire], [ZxpCell.zSpider 2 1]] }

/-- Unit absorption result: the 1->1 Z spider (NOT yet the wire — that is the seed's
identity-spider row, one more step away). -/
def zxrZUnitAbsorptionRhsDiagram : ZxpDiagram :=
  { sourceArity := 1, layers := [[ZxpCell.zSpider 1 1]] }

/-- UNIT ABSORPTION FIRE: one Z-fusion instance at (0,0,1,1) — BSZ (A1) generalized,
`eta ; mu = id` at the spider level. -/
theorem zxrZUnitAbsorptionConv :
    ZxrConv zxrZUnitAbsorptionLhsDiagram zxrZUnitAbsorptionRhsDiagram :=
  ZxrConv.step (ZxrStep.pad 1 0 0 [] [] (ZxrWindowMove.zFuse 0 0 1 1)
    (ZxpLayersWF.nil 1) rfl (ZxpLayersWF.nil _))

/-- The k = 2 adjacent fusion pair: a 2->2 Z spider feeding a 2->1 Z spider on BOTH
wires. -/
def zxrZTwoWireChainedDiagram : ZxpDiagram :=
  { sourceArity := 2
    layers := [[ZxpCell.zSpider 2 2], [ZxpCell.zSpider 2 1]] }

/-- The k = 2 fused result per the (sp) bookkeeping: `(2+2)+(2+1) - 2*2 = 3` legs. -/
def zxrZTwoWireFusedDiagram : ZxpDiagram :=
  { sourceArity := 2, layers := [[ZxpCell.zSpider 2 1]] }

/-- THE k = 2 RECURSION DEMO (the brief's step (iii) made concrete): the two-shared-wire
fusion is DERIVED from the one-wire schema plus the seed rows — (1) fission the top
spider by reverse R1(2,0,0,2) exposing the hub pair `[[zSpider 1 2],[zSpider 2 1]]`;
(2) collapse the hub pair by the seed's `specialZ` row; (3) strip the leftover identity
layer by reverse `splitLayer`.  General k >= 2 iterates step (2). -/
theorem zxrTwoWireFusionDemo :
    ZxrConv zxrZTwoWireChainedDiagram zxrZTwoWireFusedDiagram := by
  have hFissionStep : ZxrStep
      { sourceArity := 2
        layers := [[ZxpCell.zSpider 2 1], [ZxpCell.zSpider 1 2], [ZxpCell.zSpider 2 1]] }
      zxrZTwoWireChainedDiagram :=
    ZxrStep.pad 2 0 0 [] [[ZxpCell.zSpider 2 1]] (ZxrWindowMove.zFuse 2 0 0 2)
      (ZxpLayersWF.nil 2) rfl (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  have hSpecialStep : ZxrStep
      { sourceArity := 2
        layers := [[ZxpCell.zSpider 2 1], [ZxpCell.zSpider 1 2], [ZxpCell.zSpider 2 1]] }
      { sourceArity := 2, layers := [[ZxpCell.zSpider 2 1], [ZxpCell.wire]] } :=
    ZxrStep.pad 2 0 0 [[ZxpCell.zSpider 2 1]] []
      (ZxrWindowMove.seed (ZxpWindowMove.row ZxpRowTag.specialZ))
      (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
  have hStripStep : ZxrStep zxrZTwoWireFusedDiagram
      { sourceArity := 2, layers := [[ZxpCell.zSpider 2 1], [ZxpCell.wire]] } :=
    ZxrStep.pad 2 0 0 [] []
      (ZxrWindowMove.seed (ZxpWindowMove.splitLayer [ZxpCell.zSpider 2 1] []))
      (ZxpLayersWF.nil 2) rfl (ZxpLayersWF.nil _)
  exact ZxrConv.trans (ZxrConv.symm (ZxrConv.step hFissionStep))
    (ZxrConv.trans (ZxrConv.step hSpecialStep) (ZxrConv.symm (ZxrConv.step hStripStep)))

/-- Kernel cross-check of the k = 2 demo pair: span-equal (the derivation is honest). -/
theorem zxrTwoWireSpanPin :
    zxpSpanEqB (zxpDiagramDenote zxrZTwoWireChainedDiagram)
      (zxpDiagramDenote zxrZTwoWireFusedDiagram) = true := rfl

/-- The 4->1 Z spider as a diagram (a big-arity primitive). -/
def zxrZPentaDiagram : ZxpDiagram :=
  { sourceArity := 4, layers := [[ZxpCell.zSpider 4 1]] }

/-- The 4->1 X spider as a diagram (colour mirror). -/
def zxrXPentaDiagram : ZxpDiagram :=
  { sourceArity := 4, layers := [[ZxpCell.xSpider 4 1]] }

/-- FALSE CASE at big arity: the two colours denote DIFFERENT subspaces of F2^5 — the
copy span is {00000, 11111}, the parity span is the even-weight subspace. -/
theorem zxrBigColourSpanDistinct :
    zxpSpanEqB (zxpDiagramDenote zxrZPentaDiagram) (zxpDiagramDenote zxrXPentaDiagram)
      = false := rfl

/-- NEGATIVE DIRECTION through the EXTENDED bridge: the refutation instrument survives
the repair — span-distinct diagrams stay non-convertible in `ZxrConv`. -/
theorem zxrBigColourNotConv : Not (ZxrConv zxrZPentaDiagram zxrXPentaDiagram) :=
  fun hConv =>
    Bool.noConfusion ((zxrConvSpanEqB hConv).symm.trans zxrBigColourSpanDistinct)

/-! ## Stage 8 — the gate verdict and the honesty markers

THE GATE RE-RUN VERDICT: outcome (b), GATE CLEAN.  What was checked, precisely:

1. THE OLD SEPARATOR IS DEAD (kernel): the big-spider count is unbalanced on the fusion
   family (`zxrBigSpiderNotZFuseBalanced` / `zxrBigSpiderNotXFuseBalanced`, from the
   (2,0,1,1) instance pins), as are the per-colour spider counts
   (`zxrZCountNotZFuseBalanced` / `zxrXCountNotXFuseBalanced`) — exactly what the gate's
   repair option (R1) demanded of a correct fusion extension.
2. THE WHOLE PER-CELL COUNT FAMILY COLLAPSES (all-arity proof, not an enumeration):
   every wire-vanishing per-cell Nat weight balanced on the extended move set is
   IDENTICALLY ZERO (`zxrBalancedWeightCollapse`, via the Cauchy-equation descent
   `zxrFuseBalanceForcesZero`), so its fold is the constant-zero functional on every
   diagram (`zxrBalancedWeightFoldZero`).  The family that produced BOTH prior
   refutations of this workstream holds NO invariant information for `ZxrConv`.
3. THE BASE COUNT VECTOR RE-RUN (mod 2): the general saturation lemmas
   `zxrZFuseDeltaGeneral` / `zxrXFuseDeltaGeneral` pin every fusion instance's delta to
   four literals; the extended table spans the gate's SAME 6-dimensional basis
   (`zxrExtendedDeltaSpanBasisPin`); the 128-functional enumeration re-classifies the
   preserved lattice as still exactly {0, legs-parity}
   (`zxrPreservedLatticeReclassified`); and the survivor is boundary-determined
   (`zxgLegsParityFunctionalBoundaryDetermined`, a per-diagram theorem untouched by the
   move-set extension) and orthogonal to every fusion delta at every arity
   (`zxrLegsParityOrthogonalZFuseDelta` / `zxrLegsParityOrthogonalXFuseDelta`).
4. NON-COUNT CANDIDATES from the literature brief, adjudicated: connected-component
   counts were dead BEFORE fusion — the seed's `hopf` row rewrites a connected diagram
   (`[[zSpider 1 2],[xSpider 2 1]]`) to a disconnected one
   (`[[zSpider 1 0],[xSpider 0 1]]`), so no connectivity-style quantity survives the
   SEED move set, let alone the extension (the brief's fused-quotient-multigraph
   invariant lives in the fusion-only SUB-calculus, which is not this calculus).
   Span-apex / internal-path-count quantities (the brief's specialness killer in
   Span(Mat R) semantics) die against the seed's `specialZ` / `specialX` rows — the
   semantics here is LinRel_F2, where specialness is SOUND (kernel-decided in the seed's
   `zxpRowBundle`).  Scalar 2-power exponents die by the seed's PROVED
   `zxpScalarCollapse` (LinRel_F2(0,0) is a singleton).  Interior-spider counts are
   termination measures, not invariants (brief item 5) — and indeed they are already
   unbalanced on the seed's `specialZ` row.
5. THE INSTRUMENT STILL WORKS: the extended refutation bridge `zxrConvSpanEqB` fires —
   span-distinct diagrams remain non-convertible (`zxrBigColourNotConv`), so the gate
   being clean is NOT vacuous soundness loss.

No separator was found; the calculus now contains the honest IH/Lafont presentation
PLUS the primitive-arity fusion family, and the literature says the quotient IS the
semantic one (Kissinger Thm 3.4; BSZ Thm 5.5 for IB = IH_Z2) — so refutation SHOULD be
impossible.  Completeness itself remains a separately-commissioned push. -/

/-- COMPLETENESS statement over the EXTENDED congruence (Kissinger 2204.14038 Thm 3.4
direction, scalar-erased): span-equal well-formed diagrams on matching boundaries are
`ZxrConv`-convertible.

OWNER FALSE — NOT PROVEN, NOT COMMISSIONED.  The invariant-first gate for THIS
statement ran CLEAN (Stage 8 header: the old separator is provably dead, the whole
per-cell count family provably collapses, the base count vector's preserved lattice is
still exactly the boundary-determined legs parity, and the brief's non-count candidates
are each dead against named seed rows).  THE CENSUS REQUIREMENT STANDS: any completeness
push over `ZxrConv` REQUIRES the normal-form census gate first — enumerate the Z-X
normal forms of Kissinger eq. (5)/(6) (basis-of-S with pivot structure, the CSS
correspondence of Thm 5.1) at small boundaries, machine-check that every census diagram
reaches its normal form by `ZxrConv` moves and that distinct normal forms have distinct
spans, and only then attempt the Lemma 3.2/3.3 induction (eliminate same-colour interior
wires by fusion, parallel Z-X pairs by the derived Hopf/(c) family, then the (sc)
change-of-basis).  What a push MAY now assume: the full one-wire fusion family at every
arity (both colours, `zxrZFuseBundle`/`zxrXFuseBundle` sound), its k-wire closure by the
Stage-7 recursion pattern, and every seed row through `zxrOfZxpConv`. -/
def zxrCompletenessStatement : Prop :=
  (firstDiagram secondDiagram : ZxpDiagram) ->
    ZxpDiagramWF firstDiagram -> ZxpDiagramWF secondDiagram ->
    firstDiagram.sourceArity = secondDiagram.sourceArity ->
    zxpDiagramCodArity firstDiagram = zxpDiagramCodArity secondDiagram ->
    ZxpRelEquiv firstDiagram.sourceArity (zxpDiagramCodArity firstDiagram)
      (zxpDiagramDenote firstDiagram) (zxpDiagramDenote secondDiagram) ->
    ZxrConv firstDiagram secondDiagram

/-- OWNER MARKER: completeness over `ZxrConv` is NOT proven (see
`zxrCompletenessStatement` for the census requirement any push must clear first). -/
def zxrCompletenessIsProven : Bool := false

/-- Repair marker: the arity-indexed fusion row family is shipped with ALL-ARITY
soundness (`zxrZFuseBundle` / `zxrXFuseBundle`) and the gate's refuted pair converts
(`zxrFusedChainedConv`). -/
def zxrHasAllArityFusionSoundness : Bool := true

/-- THE GATE RE-RUN VERDICT MARKER: outcome (b), CLEAN — the Stage-8 header records
precisely which kernel facts and all-arity theorems were checked; no separator for
`ZxrConv` was found, and `zxrCompletenessStatement` is minted owner-false. -/
def zxrGateVerdictIsClean : Bool := true

end FX1Poly.Polygraph.Omega.ZXPhaseFree
