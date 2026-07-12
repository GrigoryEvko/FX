import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithPivotMagnitudeDescent

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithClearingHalvesFromKeystone — both r27 clearing-sweep
    residuals VANISH into the shipped keystone (H2-SMITH r28, #2261)

r27 (`SmithPivotMagnitudeDescent`) reduced `SmithReduceCompleteDriverStatement` to the pair
(`SmithClearingOutputFindNone` = K1, the diagonal-half fuel-adequacy) + (`SmithClearingOutputOffDiagonalDivides`
= K2, the off-diagonal half).  r28 shows that pair is a REDUNDANT RE-SPLIT: BOTH K1 and K2 fall out of the
SHIPPED r22 keystone `SmithCascadeOutputMinorDivides` (⟺ `SmithCascadeLandedPivotDividesMinor`) using shipped
kit only — no fold-descent induction, no new gcd content.  The r27 sub-arc `SmithFoldDescendsOnNonzeroPivot`
is therefore SUBSUMED and retired: K1 no longer needs it.

**The keystone body** (spelled out in both K1/K2 and `SmithCascadeOutputMinorDivides` byte-identically) reads,
for the pivot-`p` clearing-position-sweep output `M'`:

    MatrixEntriesDivisibleByWithin (M'.diagonalEntryAt p) p M'

— the landed pivot divides every entry of `M'`'s `[p, ·)²` block.  From it:

  * **K2 vanishes** (`clearingOutputOffDiagonalDividesOfKeystone`).  Restrict the floor `p → p+1`
    (`matrixEntriesDivisibleByWithinLoMono`, `p ≤ p+1`), then read off the off-diagonal slice
    (`subBlockOffDiagonalDivisibleOfWithin`).  Three lines of shipped kit; no ideal argument.
  * **K1 vanishes** (`clearingOutputFindNoneOfKeystone`).  The find-loop over `[p+1, min h w)` reports `none`
    because the keystone gives the pivot dividing every later diagonal `M'.diagonalEntryAt laterIndex`
    (= `M'.entryAt laterIndex laterIndex`, defeq), which the Bool test `smithPivotDividesEntry` reports `true`
    (`smithPivotDividesEntryEncode`, the converse of the shipped `smithPivotDividesEntryDecode`), and a
    scan whose guard is always `true` runs to its `none` base (`smithFindNonDividingLaterDiagonalNoneOfAllDivide`,
    a mirror of the shipped `smithFindNonDividingLaterDiagonalNoneOfLaterZero`).

Composing both with the r27 `smithReduceCompleteDriverOfFindNoneAndOffDiagonal` gives
`SmithReduceCompleteDriverStatement` from `SmithCascadeOutputMinorDivides` ALONE
(`smithReduceCompleteDriverOfKeystoneViaHalves`) — recovering the r22
`smithReduceCompleteDriverOfOutputMinorDivides` through the r27 halves route, proving the two routes agree.

**HONEST SIZING — this inhabits NOTHING hypothesis-free.**  It is a DETOUR-RETIREMENT round.  The frontier is
UNCHANGED since r22: the single surviving wall is the keystone `SmithCascadeOutputMinorDivides` (⟺
`SmithCascadeLandedPivotDividesMinor`) — "the min-abs Euclid cascade lands the minor gcd", a standalone major
arc.  What r28 removes is the r27 (K1, K2) detour and the strictly-weaker `SmithFoldDescendsOnNonzeroPivot`
sub-arc; the wall is named IN THIS FILE (footer).  Additive only: r18–r27 stay byte-intact.

Raw Lean 4 + `Init`, STRUCTURAL only (Brick 2a inducts on the scan count; the rest is straight-line assembly
over shipped lemmas).  ASCII identifiers; no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithClearingHalvesFromKeystone.lean`. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## Brick 1 — K2 vanishes: the off-diagonal half is the keystone's off-diagonal slice -/

/-- **K2 ⟸ the keystone.**  The clearing-sweep output's off-diagonal `[p+1, ·)²` cells are all divisible by
the landed pivot: restrict the keystone's `[p, ·)²` block divisibility up to the `[p+1, ·)²` sub-block
(`matrixEntriesDivisibleByWithinLoMono`, `p ≤ p+1`), then drop the distinctness witness
(`subBlockOffDiagonalDivisibleOfWithin`).  The r22 "gcd-ideal off-diagonal wall" is a pure projection of the
keystone — no separate ideal argument. -/
theorem clearingOutputOffDiagonalDividesOfKeystone
    (outputDivides : SmithCascadeOutputMinorDivides) :
    SmithClearingOutputOffDiagonalDivides := by
  intro matrix pivotIndex height width isRect pRowLt pColLt
  exact subBlockOffDiagonalDivisibleOfWithin
    (matrixEntriesDivisibleByWithinLoMono (Nat.le_succ pivotIndex)
      (outputDivides matrix pivotIndex height width isRect pRowLt pColLt))

/-! ## Brick 2a — the find-`none` mirror: an all-dividing scan window runs to `none` -/

/-- **A scan whose every later diagonal the pivot divides reports `none`.**  When
`smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex) (matrix.diagonalEntryAt laterIndex) = true` for
every `laterIndex` in the window `[scanStart, scanStart + scanCount)`, the non-dividing scan finds nothing.
Structural on the scan count; the guard-`true` version of the shipped
`smithFindNonDividingLaterDiagonalNoneOfLaterZero` (the guard is supplied directly, not derived from zeros). -/
theorem smithFindNonDividingLaterDiagonalNoneOfAllDivide (matrix : IntMatrix) (pivotIndex : Nat) :
    ∀ (scanCount scanStart : Nat),
      (∀ laterIndex, scanStart ≤ laterIndex → laterIndex < scanStart + scanCount →
        smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
          (matrix.diagonalEntryAt laterIndex) = true) →
      smithFindNonDividingLaterDiagonal matrix pivotIndex scanCount scanStart = none := by
  intro scanCount
  induction scanCount with
  | zero => intro scanStart _; rfl
  | succ scanCount ih =>
      intro scanStart allDivide
      have hUnfold : smithFindNonDividingLaterDiagonal matrix pivotIndex (scanCount + 1) scanStart
          = if smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
                (matrix.diagonalEntryAt scanStart) then
              smithFindNonDividingLaterDiagonal matrix pivotIndex scanCount (scanStart + 1)
            else some scanStart := rfl
      rw [hUnfold]
      have guardTrue : smithPivotDividesEntry (matrix.diagonalEntryAt pivotIndex)
          (matrix.diagonalEntryAt scanStart) = true :=
        allDivide scanStart (Nat.le_refl scanStart)
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self scanStart)
            (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le scanCount)) scanStart))
      rw [if_pos guardTrue]
      have scanShiftEq : scanStart + 1 + scanCount = scanStart + (scanCount + 1) :=
        (Nat.succ_add scanStart scanCount).trans (Nat.add_succ scanStart scanCount).symm
      exact ih (scanStart + 1) (fun laterIndex laterGe laterLt =>
        allDivide laterIndex (Nat.le_of_succ_le laterGe)
          (Eq.mp (congrArg (laterIndex < ·) scanShiftEq) laterLt))

/-! ## Brick 2b — the encode bridge: `dividesExactly` ⟹ the Bool test is `true` -/

/-- **The Bool divisibility test encodes `dividesExactly`** — the converse of the shipped
`smithPivotDividesEntryDecode`.  When `pivotEntry` exactly divides `laterEntry`, the test
`smithPivotDividesEntry pivotEntry laterEntry` is `true`.  The `pivotEntry.natAbs == 0` arm forces
`laterEntry = 0` (`intZeroMul` on the zero pivot) so the tail `laterEntry.natAbs == 0` holds; the else arm
descends `dividesExactly` (defeq `IntDivides`) to Nat magnitude divisibility (`natDividesNatAbsOfIntDivides`)
and reads the counting remainder as zero (`natDividesRemainderIsZero` through `intMagnitudeRemainderAsCounting`,
needing the positive pivot `natNeZeroOfBeqZeroFalse`/`Nat.pos_of_ne_zero`). -/
theorem smithPivotDividesEntryEncode (pivotEntry laterEntry : Int)
    (divides : dividesExactly pivotEntry laterEntry) :
    smithPivotDividesEntry pivotEntry laterEntry = true := by
  unfold smithPivotDividesEntry
  cases hPivotZero : pivotEntry.natAbs == 0 with
  | true =>
      show (laterEntry.natAbs == 0) = true
      have pivotZero : pivotEntry = 0 :=
        intEqZeroOfNatAbsEqZero (natEqZeroOfBeqZeroTrue pivotEntry.natAbs hPivotZero)
      cases divides with
      | intro factor laterEq =>
          have laterZero : laterEntry = 0 :=
            laterEq.trans ((congrArg (· * factor) pivotZero).trans (intZeroMul factor))
          rw [laterZero]
          rfl
  | false =>
      show (intMagnitudeRemainder pivotEntry.natAbs laterEntry == 0) = true
      have pivotPos : 0 < pivotEntry.natAbs :=
        Nat.pos_of_ne_zero (natNeZeroOfBeqZeroFalse pivotEntry.natAbs hPivotZero)
      have remZero : intMagnitudeRemainder pivotEntry.natAbs laterEntry = 0 :=
        (intMagnitudeRemainderAsCounting pivotEntry.natAbs laterEntry).trans
          (natDividesRemainderIsZero pivotPos (natDividesNatAbsOfIntDivides divides))
      rw [remZero]
      rfl

/-! ## Brick 2c — K1 vanishes: the fuel-adequacy find-`none` is the keystone's diagonal reading -/

/-- **K1 ⟸ the keystone.**  The clearing-sweep output's non-dividing scan over `[p+1, min h w)` reports
`none`: the keystone gives the landed pivot dividing every `[p, ·)²` entry, so at each later diagonal slot
`(laterIndex, laterIndex)` it divides `M'.diagonalEntryAt laterIndex` (defeq `M'.entryAt laterIndex
laterIndex`), which `smithPivotDividesEntryEncode` reports `true`; the all-`true` scan runs to `none`
(`smithFindNonDividingLaterDiagonalNoneOfAllDivide`).  The r27 fuel-adequacy residual — the one that was to
ride the retired `SmithFoldDescendsOnNonzeroPivot` — dissolves into the keystone directly. -/
theorem clearingOutputFindNoneOfKeystone
    (outputDivides : SmithCascadeOutputMinorDivides) :
    SmithClearingOutputFindNone := by
  intro matrix pivotIndex height width isRect pRowLt pColLt
  apply smithFindNonDividingLaterDiagonalNoneOfAllDivide
  intro laterIndex laterGe _laterLt
  have pivotLeLater : pivotIndex ≤ laterIndex := Nat.le_of_succ_le laterGe
  exact smithPivotDividesEntryEncode _ _
    (outputDivides matrix pivotIndex height width isRect pRowLt pColLt
      laterIndex pivotLeLater laterIndex pivotLeLater)

/-! ## Brick 3 — the collapse: the driver from the keystone via the r27 halves -/

/-- **The corrected-driver totality from the keystone via the r27 halves route.**  Feed the two vanished
halves into the r27 seed reduction `smithReduceCompleteDriverOfFindNoneAndOffDiagonal`:
`SmithReduceCompleteDriverStatement` is inhabited GIVEN `SmithCascadeOutputMinorDivides` alone.  This RECOVERS
the r22 `smithReduceCompleteDriverOfOutputMinorDivides` through the r27 (K1, K2) presentation — proving the
r27 detour is equivalent to (not sharper than) the single shipped keystone. -/
theorem smithReduceCompleteDriverOfKeystoneViaHalves
    (outputDivides : SmithCascadeOutputMinorDivides) :
    SmithReduceCompleteDriverStatement :=
  smithReduceCompleteDriverOfFindNoneAndOffDiagonal
    (clearingOutputFindNoneOfKeystone outputDivides)
    (clearingOutputOffDiagonalDividesOfKeystone outputDivides)

/-! ## The surviving wall (named IN this file — NOT prose masquerading as a theorem)

This file inhabits NOTHING hypothesis-free.  It RETIRES the r27 detour: both r27 residuals — the diagonal-half
fuel-adequacy `SmithClearingOutputFindNone` (K1) and the off-diagonal half `SmithClearingOutputOffDiagonalDivides`
(K2) — are VANISHED into the shipped r22 keystone `SmithCascadeOutputMinorDivides` using shipped kit only
(`matrixEntriesDivisibleByWithinLoMono` + `subBlockOffDiagonalDivisibleOfWithin` for K2;
`smithFindNonDividingLaterDiagonalNoneOfAllDivide` + `smithPivotDividesEntryEncode` for K1).  The r27 sub-arc
`SmithFoldDescendsOnNonzeroPivot` (the cascade-inner strict-descent induction) is SUBSUMED — K1 no longer needs
it, and it is strictly weaker than the keystone (the pivot merely drops, vs. lands the gcd).

**THE ONE SURVIVING OBLIGATION, named EXACTLY** — `SmithReduceCompleteDriverStatement` is inhabited GIVEN
`SmithCascadeOutputMinorDivides` (⟺ `SmithCascadeLandedPivotDividesMinor`):

    the pivot-`p` clearing position sweep lands, at the pivot, a divisor of every entry of the input's
    (equivalently the output's) `[p, ·)` minor — its magnitude equals the minor gcd.

This is the "min-abs Euclid cascade computes the gcd" correctness — the r11+ wall, a STANDALONE MAJOR ARC,
UNCHANGED since r22.  Truth-probed elsewhere (`diag(6, 10, 8)` lands `2 = gcd`, cross zero, interior `30, 8`
even); not proven in general.

**Honest verdict.**  r28 does NOT move the frontier.  It removes the r27 (K1, K2) re-split and the
strictly-weaker fold-descent sub-arc, collapsing the corrected-driver totality back onto the single r22
keystone via `smithReduceCompleteDriverOfKeystoneViaHalves`.  No flip is fabricated; the honest pair is
`(SmithReduceCompleteDriverStatement ⟸ SmithCascadeOutputMinorDivides`, that keystone REFUTED AS STATED — `SmithLandedMagnitudeRefuted`, r33; RESTRICTED diagonal form OPEN)`.  The r18–r27
world stays byte-intact (additive only). -/

end FX1Poly.ComputerAlgebra
