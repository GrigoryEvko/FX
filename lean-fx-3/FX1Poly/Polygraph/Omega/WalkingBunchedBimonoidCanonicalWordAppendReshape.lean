import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordConvFold

/-! # Polygraph/Omega/WalkingBunchedBimonoidCanonicalWordAppendReshape — the FULL append-vs-vcomp reshape
`permWord (front ++ back) w ~ vcomp (permWord front w) (permWord back w)` (WP-PROP r16, B1)

★ **THE r15 APPEND RESIDUAL (gap (ii)), CLOSED at word granularity.**  r15
(`WalkingBunchedBimonoidCanonicalWordConvFold`) shipped part (a) of the append residual — the sigma-source boundary
reshape `bunchedBimonoidSigmaAtBoundaryReshapeConv` (`aWordPow w ~ boundarySource (sigmaAt w k)` under `k + 2 ≤
w`) — and named the remaining part (b) verbatim in
`fxBunchedBimonoid_appendReshapeGatedOnBoundaryAndValidityThreading`: *"threading it through the FRONT-induction of
`permWordAppendConv` via `vcompIdLeft_bridgedWithId`, carrying the `bunchedBimonoidMentionsOnlyBelow`
position-validity."*  This file delivers exactly that thread, assembling the full append reshape from four shipped
ingredients:

  * `bunchedBimonoidSigmaAtBoundaryReshapeConv` (r15 S4, part (a) — the sigma-source boundary reshape);
  * `vcompIdLeft_bridgedWithId` (`Omega/CongruenceWithId`, the `idCongr`-keyed unit bridge);
  * `StrictAxiomRel.vcompUnitLeft` / `StrictAxiomRel.vcompAssoc` (`Omega/StrictAxioms`, embedded `Or.inl` into the
    star scope via `bunchedBimonoidStrictAxiomEmbedsIntoStarScope`);
  * the `bunchedBimonoidMentionsOnlyBelow` head-validity `k < w - 1 → k + 2 ≤ w` (a two-line `Nat` bridge,
    re-derived propext-clean below — the `< w - 1` bound, NOT `< w`, is what `S4`'s `k + 2 ≤ w` demands).

The append reshape is a FRONT-induction (structural on `front`); `back` carries the position-validity, `front`
needs none (its head is threaded by pure `vcompCongrRight` / `vcompAssoc` congruence).  The nil-front case rests on
the standalone source-boundary reshape brick `bunchedBimonoidPermWordSourceReshapeConv` (a `back`-cases dispatch:
`[]` is `refl`, `k :: rest` is `S4` at the extracted `k + 2 ≤ w`).

## What this round is NOT (the honest scope)

The star does NOT flip: B1 lands the append reshape (gap (ii) fully narrowed to zero), one node short of the
four-case fold `combNormalizeFormConv`, itself short of `recCombConv` / `coxeterWordUnique` (only the last earns a
star-owner flip — B3).  The four star-owner markers (`StarAssembly`, `RiffleAssembly`, `CollisionCanonForm`,
`CoxeterUniqueness`) and the r15 residual marker
`fxBunchedBimonoid_appendReshapeGatedOnBoundaryAndValidityThreading` keep their names and `= false` values
byte-intact (cross-file, not edited — the r15 marker stays as the provenance anchor recording what B1 now closes).
This file records the delivery in a FRESH positive marker `fxBunchedBimonoid_permWordAppendReshapeShipped := true`.

Raw Lean 4 + Init; STRUCTURAL only (front-induction on the list, no fuel, no `WellFounded.fix`); ASCII-only.
Per-declaration `#assert_no_axioms` AND independent `#print axioms` gated in the audit twin.  Mirror of the Brauer
canonicity lane's `crossingWord` append — and genuinely wider (the Brauer word is a flat `List`, so its append IS
list append; the Omega `permWord` folds into real `CellExpr` vcomp trees, so this append reshape is genuine CONV
content, not a definitional coincidence). -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

/-! The append-reshape proof terms are pure congruence-constructor plumbing (axiom-free); only the width-3 matrix
truth-probe evaluates a cell, exceeding the default heartbeat budget — the raise is a compute allowance only
(uniform with the r6-r15 lane files). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # B1.arith — the propext-clean head-validity backbone (`k < w - 1 → k + 2 ≤ w`)
    # =========================================================================================

★ The `back` word carries `bunchedBimonoidMentionsOnlyBelow (w - 1) back = true` — every head `k` satisfies
`Nat.blt k (w - 1) = true`, i.e. `k < w - 1`, i.e. `k + 2 ≤ w` (the `S4` `inRange` demand).  The staircase's
own `boolAndLeft` / `natLtOfBlt` / `natLePred` helpers are `private`, so the three `Bool`/`Nat` steps are
re-derived here, propext-clean (full-enum `Bool` cases + structural `Nat.ble` recursion; no `Nat.sub` propext
leak, the bridge cases directly on `wordWidth`). -/

/-- Extract the LEFT conjunct of a `Bool` `&&` that is `true` — full-enum on the left flag (`false && _` is
`Bool.noConfusion`).  The `mentionsOnlyBelow` head-scan reads off through this. -/
private theorem bunchedBimonoidBoolAndLeftAppendReshape :
    (leftFlag rightFlag : Bool) → (leftFlag && rightFlag) = true → leftFlag = true
  | true, _, _ => rfl
  | false, _, conjTrue => Bool.noConfusion conjTrue

/-- `Nat.ble lower upper = true → lower ≤ upper` — structural on both arguments (`Nat.ble` reduces on
successors), zero `Nat.sub`.  The `≤`-from-`ble` half `natLtOfBlt` rests on. -/
private theorem bunchedBimonoidNatLeOfBleAppendReshape :
    (lower upper : Nat) → Nat.ble lower upper = true → lower ≤ upper
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, hble => Bool.noConfusion hble
  | lower + 1, upper + 1, hble => Nat.succ_le_succ (bunchedBimonoidNatLeOfBleAppendReshape lower upper hble)

/-- `Nat.blt lower upper = true → lower < upper` — `Nat.blt lower upper` is definitionally
`Nat.ble (lower + 1) upper`, so this is `natLeOfBle` at `lower + 1`. -/
private theorem bunchedBimonoidNatLtOfBltAppendReshape (lower upper : Nat)
    (hblt : Nat.blt lower upper = true) : lower < upper :=
  bunchedBimonoidNatLeOfBleAppendReshape (lower + 1) upper hblt

/-- ★ **THE HEAD-VALIDITY BRIDGE `k < w - 1 → k + 2 ≤ w`.**  Cases on `wordWidth` (NOT on the truncated `w - 1`,
avoiding the `Nat.sub` propext leak): `w = 0` makes `k < 0` absurd (`Nat.not_succ_le_zero`); `w = w' + 1` reduces
`w - 1` to `w'`, so `k < w'` is `k + 1 ≤ w'` and `Nat.succ_le_succ` lifts it to `k + 2 ≤ w' + 1`.  Exactly the
`k + 2 ≤ w` that `bunchedBimonoidSigmaAtBoundaryReshapeConv` (S4) needs from a `mentionsOnlyBelow (w - 1)` head. -/
private theorem bunchedBimonoidHeadValidInRangeAppendReshape :
    (headPosition wordWidth : Nat) → headPosition < wordWidth - 1 → headPosition + 2 ≤ wordWidth
  | headPosition, 0, headLt => absurd headLt (Nat.not_succ_le_zero headPosition)
  | _, _ + 1, headLt => Nat.succ_le_succ headLt

/-! # =========================================================================================
    # B1a — THE SOURCE-BOUNDARY RESHAPE FOR A WHOLE `back` WORD (the nil-front ingredient)
    # =========================================================================================

★ The nil-front case of the append reshape needs `aWordPow w ~ boundarySource (permWord back w)` — the flat word
converts to the source boundary of the `back`-word cell.  A `back`-cases dispatch (NO recursion): the empty word
`permWord [] w = id (aWordPow w)` has boundary `aWordPow w` on the nose (S0), so `refl`; a `k :: rest` word has
boundary `boundarySource (sigmaAt w k)` (the tail is invisible to `boundarySource`, S0), so the r15 S4 reshape
`bunchedBimonoidSigmaAtBoundaryReshapeConv` at the extracted head-validity `k + 2 ≤ w`. -/

/-- ★★ **THE `back`-WORD SOURCE-BOUNDARY RESHAPE.**  Under `mentionsOnlyBelow (w - 1) back = true`, the flat word
`aWordPow w` converts, over the star scope, to `boundarySource (permWord back w)`.  Cases on `back`: `[]` reshapes
to `boundarySource (id (aWordPow w)) = aWordPow w` by `refl`; `k :: rest` reshapes to `boundarySource (sigmaAt w k)`
(the cons-word's boundary reads off the head letter, tail-independent) by the r15 S4
`bunchedBimonoidSigmaAtBoundaryReshapeConv` at `k + 2 ≤ w`, extracted from the head certificate `Nat.blt k (w - 1)`
via `boolAndLeft` + `natLtOfBlt` + the head-validity bridge. -/
theorem bunchedBimonoidPermWordSourceReshapeConv (wordWidth : Nat) :
    (back : List Nat) →
    bunchedBimonoidMentionsOnlyBelow (wordWidth - 1) back = true →
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidAWordPow wordWidth)
      (boundarySource (bunchedBimonoidPermWord back wordWidth))
  | [], _ => SaturatedConvOverWithId.refl (bunchedBimonoidAWordPow wordWidth)
  | headK :: _restBack, backValid =>
      bunchedBimonoidSigmaAtBoundaryReshapeConv wordWidth headK
        (bunchedBimonoidHeadValidInRangeAppendReshape headK wordWidth
          (bunchedBimonoidNatLtOfBltAppendReshape headK (wordWidth - 1)
            (bunchedBimonoidBoolAndLeftAppendReshape _ _ backValid)))

/-! # =========================================================================================
    # B1b — THE FULL APPEND RESHAPE (the front-induction, gap (ii) CLOSED)
    # =========================================================================================

★ The append reshape, structural on `front`.  The nil-front case reshapes the leading identity via
`vcompIdLeft_bridgedWithId` fed by the source-boundary brick (B1a); the cons-front case is pure congruence —
`(headJ :: restFront) ++ back` reduces to `headJ :: (restFront ++ back)` on the nose (list append computes on the
head), so the head `sigmaAt w headJ` factors out by `vcompCongrRight` over the IH, then `vcompAssoc` re-brackets to
`vcomp (permWord (headJ :: restFront) w) (permWord back w)`.  No `succAdd` rewrite is needed (unlike the dim-1
`aWordPowSplitConv`), because list cons-append is definitional where Nat successor-add is not. -/

/-- ★★★ **THE FULL APPEND-VS-VCOMP RESHAPE (gap (ii), CLOSED).**  For any `front`, `back` with
`mentionsOnlyBelow (w - 1) back = true`, the folded word `permWord (front ++ back) w` converts, over the star scope,
to `vcomp (permWord front w) (permWord back w)`.  Structural on `front`:

  * `front = []`:  `permWord ([] ++ back) w = permWord back w`, and the target's leading factor `permWord [] w =
    id (aWordPow w)` is absorbed by `vcompIdLeft_bridgedWithId (permWord back w)` fed by the B1a source-boundary
    reshape `aWordPow w ~ boundarySource (permWord back w)` and the strict `vcompUnitLeft` row — then `symm`.
  * `front = headJ :: restFront`:  `permWord ((headJ :: restFront) ++ back) w = vcomp (sigmaAt w headJ)
    (permWord (restFront ++ back) w)`; `vcompCongrRight (sigmaAt w headJ)` threads the IH
    (`permWord (restFront ++ back) w ~ vcomp (permWord restFront w) (permWord back w)`), then the `symm` of the
    embedded `vcompAssoc` re-brackets to `vcomp (vcomp (sigmaAt w headJ) (permWord restFront w)) (permWord back w) =
    vcomp (permWord (headJ :: restFront) w) (permWord back w)`.

This is EXACTLY part (b) the r15 `fxBunchedBimonoid_appendReshapeGatedOnBoundaryAndValidityThreading` named —
threading the S4 boundary reshape through the front-induction, carrying the `mentionsOnlyBelow` position-validity.
With it, gap (ii) is closed; the four case bridges (COMMUTE / EXTEND / CANCEL / CARRY) can fold to
`combNormalizeFormConv` (B2).  The star does NOT flip. -/
theorem bunchedBimonoidPermWordAppendConv (wordWidth : Nat) :
    (front back : List Nat) →
    bunchedBimonoidMentionsOnlyBelow (wordWidth - 1) back = true →
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (bunchedBimonoidPermWord (front ++ back) wordWidth)
      (CellExpr.vcomp (bunchedBimonoidPermWord front wordWidth)
        (bunchedBimonoidPermWord back wordWidth))
  | [], back, backValid =>
      SaturatedConvOverWithId.symm
        (vcompIdLeft_bridgedWithId (bunchedBimonoidPermWord back wordWidth)
          (bunchedBimonoidPermWordSourceReshapeConv wordWidth back backValid)
          (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.vcompUnitLeft (bunchedBimonoidPermWord back wordWidth))))
  | headJ :: restFront, back, backValid =>
      SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrRight (bunchedBimonoidSigmaAt wordWidth headJ)
          (bunchedBimonoidPermWordAppendConv wordWidth restFront back backValid))
        (SaturatedConvOverWithId.symm
          (bunchedBimonoidStrictAxiomEmbedsIntoStarScope
            (StrictAxiomRel.vcompAssoc (bunchedBimonoidSigmaAt wordWidth headJ)
              (bunchedBimonoidPermWord restFront wordWidth)
              (bunchedBimonoidPermWord back wordWidth))))

/-! ## B1 truth-probe (the append reshape relates two cells of the same matrix; width 3) -/

/-- The append endpoints share their matrix at `front = [0]`, `back = [1, 0]`, width 3 (`rfl`): both
`permWord ([0] ++ [1, 0]) 3` and `vcomp (permWord [0] 3) (permWord [1, 0] 3)` evaluate to the reversal
`[[0,0,1],[0,1,0],[1,0,0]]` — the append reshape's matrix soundness (a CONV over the star scope implies equal
`Mat(N)`; this pins the converse necessary condition at the probe width). -/
theorem bunchedBimonoidPermWordAppendMatrixShared :
    bunchedBimonoidEvalCell (bunchedBimonoidPermWord ([0] ++ [1, 0]) 3)
      = bunchedBimonoidEvalCell
        (CellExpr.vcomp (bunchedBimonoidPermWord [0] 3) (bunchedBimonoidPermWord [1, 0] 3)) := rfl

/-! ## The B1 marker -/

/-- ★★★ **ESTABLISHED (B1) — the full append-vs-vcomp reshape is DELIVERED; the r15 append residual (gap (ii)) is
CLOSED.**  `= true` records `bunchedBimonoidPermWordAppendConv`
(`permWord (front ++ back) w ~ vcomp (permWord front w) (permWord back w)` under `mentionsOnlyBelow (w - 1) back`,
front-induction) and its nil-front ingredient `bunchedBimonoidPermWordSourceReshapeConv`
(`aWordPow w ~ boundarySource (permWord back w)`).  This is EXACTLY part (b) the r15
`fxBunchedBimonoid_appendReshapeGatedOnBoundaryAndValidityThreading` named — threading the S4 boundary reshape
(part (a)) through the front-induction via `vcompIdLeft_bridgedWithId`, carrying the position-validity; with r15's
S1/S2/S3/S4 the append reshape gap is now fully closed.  Matrix-soundness pinned at width 3
(`bunchedBimonoidPermWordAppendMatrixShared`).  The star does NOT flip (B1 is one node short of the four-case fold
`combNormalizeFormConv`, itself short of `recCombConv` / `coxeterWordUnique`); the four star-owner markers and the
r15 residual marker keep their names and `= false` values byte-intact (cross-file, not edited).  Zero-axiom
(per-decl `#assert_no_axioms` + independent `#print axioms` in the twin); STRUCTURAL only. -/
def fxBunchedBimonoid_permWordAppendReshapeShipped : Bool := true

end FX1Poly.Polygraph.Omega
