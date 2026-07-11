import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeTotalAssembly
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestLayout

/-! # Polygraph/TwoCategory/Amalgam/PushoutWhiskerHeadPrependMultiGap — the MULTI-GAP head-prepend whisker arm: a
`whiskerLeft` over an ARBITRARY multi-gap body factorization emits a genuinely MULTI-SLOT layout (WP-AMALG-2 r16, B2)

r15's whisker arms (`pushoutFactorizeWhiskerLeftGap` / `RightGap`) discharged the whisker case for a SINGLE-GAP body
(the induction's `gen` / `id` leaves) — `slotCount` STAYED 1 because the body sat undivided in one gap.  The r16
recon's leg 2(b) demands the general head-prepend: `whiskerLeft oneCell body` for an ARBITRARY multi-gap body
factorization, producing a layout whose slot count GROWS with the body.  This file ships that, at the pure-frame
granularity (the cast-free empty-gap-prepend vehicle), and PROBES `slotCount > 1` on a concrete framed multi-gap cell
FIRST.

## The head-prepend — the frame becomes a leading inert wall slot (cast-free)

Given a body factorization `(finalWall, pairs, domEq, codEq, conv)` of `body`, `whiskerLeft oneCell body` factors by
PREPENDING one empty-gap block `emptyGapPair oneCell` (leading wall `oneCell`, `nil` gap, identity payloads) to the
body's `pairs`, keeping `finalWall`.  Because `composePath nil X = X` DEFINITIONALLY, the prepended block's domain
contribution is exactly `composePath oneCell (gapDomLayout finalWall pairs)` — the domain of `whiskerLeft oneCell (…)`
on the nose — so the boundary casts are the plain `congrArg (composePath oneCell) …`, NO `composePath`-associativity
cast survives.  The convertibility strips the leading `id oneCell`-whisker (`whiskerLeft_conv_hcompIdLeading`) and
absorbs the empty gap by free identity collapse (`vcompIdLeft` + `whiskerLeftUnit`) — the shipped
`whiskerLeft_conv_emptyGapPrepend`.  The result has `slotCount = bodySlotCount + 1` — a GENUINE multi-slot layout.

## The merge-into-head-wall assoc tower (the recon's named "load-bearing missing piece")

Also shipped: `mergeFrameIntoHead` (the alternative that merges the frame into the HEAD gap's leading wall — the
CANONICAL merge) with its boundary assoc tower `gapDomLayout_mergeFrameIntoHead` / `gapCodLayout_mergeFrameIntoHead`
(both a single `composePath_assoc`, cast-clean).  These are the recon-named unbuilt pieces.  The CELL-level
merge-into-head surgery (relating `whiskerLeft oneCell (gapVcompLayout …)` to `gapVcompLayout … (mergeFrameIntoHead
…)`, which rides `whiskerLeftComp` through the `composePath`-associativity `castBoundary`) is the r17 canonical-reader
residual; this round ships the cast-FREE empty-gap-prepend as the multi-slot vehicle and the merge boundary tower for
the r17 merge.

## What STAYS WALLED (no flip)

This ships the `whiskerLeft` multi-gap head-prepend arm (cast-free) + the merge boundary tower.  It does NOT ship: the
CELL-level merge-into-head surgery (r17), the `whiskerRight` multi-gap trailing-frame append (needs the
`gapDomLayout`-into-`finalWall` distribution induction), the `s`-bearing frame's downstream wall-SHIFT (the
wire-changing case, leg 2(a'')).  `fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`; the masters STAY at
their walled values; #2043 does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The empty-gap inner absorption -/

/-- **The empty-gap inner absorption** — the doubly-`id`-whiskered `nil`-gap gadget `hcomp (vcomp (id nil) (id nil))
cell` collapses to `cell`, over ANY payload / signature / base relation.  The vertical composite `vcomp (id nil)
(id nil)` drops to `id nil` (`vcompIdLeft`); the `id nil` horizontal factor becomes a `nil`-left-whisker
(`whiskerLeft_conv_hcompIdLeading` reversed) which the unitor `whiskerLeftUnit` strips.  This is the free content of
the empty-gap prepend: the prepended `nil` gap carries no firing. -/
theorem emptyGapPrependInnerAbsorb {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode : signature.graph.Mode}
    {cellDom cellCod : ModalityPath signature.graph oneMode oneMode}
    (cell : RawTwoCellExpr signature cellDom cellCod) :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.hcomp
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.id (ModalityPath.nil oneMode))
          (RawTwoCellExpr.id (ModalityPath.nil oneMode)))
        cell)
      cell :=
  SaturatedConvOver.trans
    (SaturatedConvOver.hcompCongrLeft
      (SaturatedConvOver.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompIdLeft (RawTwoCellExpr.id (ModalityPath.nil oneMode)))))
      cell)
    (SaturatedConvOver.trans
      (SaturatedConvOver.symm (whiskerLeft_conv_hcompIdLeading (ModalityPath.nil oneMode) cell))
      (SaturatedConvOver.ofFull (TwoCellConvFull.whiskerLeftUnit cell)))

/-! ## The core head-prepend convertibility (cast-free) -/

/-- ★★★ **THE EMPTY-GAP HEAD-PREPEND CONVERTIBILITY (cast-free).**  `whiskerLeft oneCell (gapVcompLayout finalWall
pairs)` is saturated-convertible to `gapVcompLayout finalWall (emptyGapPair oneCell :: pairs)` — the layout with the
frame prepended as a fresh leading inert wall slot.  BOTH sides share the SAME boundary DEFINITIONALLY (the prepended
`nil` gap's `composePath nil` absorbs), so NO `castBoundary` appears.  The chain: strip the leading `oneCell`-whisker
(`whiskerLeft_conv_hcompIdLeading`), then re-insert the prepended empty gap by the reverse of
`emptyGapPrependInnerAbsorb` under `hcompCongrRight`.  Over ANY signature and base relation. -/
theorem whiskerLeft_conv_emptyGapPrepend {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode : signature.graph.Mode}
    (finalWall oneCell : ModalityPath signature.graph oneMode oneMode)
    (pairs : List (VcompGapPair signature oneMode)) :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.whiskerLeft oneCell (gapVcompLayout finalWall pairs))
      (gapVcompLayout finalWall (emptyGapPair oneCell :: pairs)) :=
  SaturatedConvOver.trans
    (whiskerLeft_conv_hcompIdLeading oneCell (gapVcompLayout finalWall pairs))
    (SaturatedConvOver.hcompCongrRight (RawTwoCellExpr.id oneCell)
      (SaturatedConvOver.symm (emptyGapPrependInnerAbsorb (gapVcompLayout finalWall pairs))))

/-! ## The reflexive factorization of a layout cell (the probe vehicle) -/

/-- ★ **The reflexive factorization of a layout cell.**  `gapVcompLayout finalWall pairs` (any wall/gap layout) is
its OWN factorization — the boundary casts are `rfl` (the cell's boundaries ARE the layout's), the convertibility is
`refl`.  The vehicle that turns a concrete `pairs` list into a genuine multi-gap body factorization for the whisker
head-prepend to consume. -/
def pushoutFactorizeOfLayout {signature : ModeSignature} (baseRel : CellRel signature)
    {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode)
    (pairs : List (VcompGapPair signature oneMode)) :
    PushoutLayoutFactorization baseRel (gapVcompLayout finalWall pairs) where
  finalWall := finalWall
  pairs := pairs
  domEq := rfl
  codEq := rfl
  conv := SaturatedConvOver.refl (gapVcompLayout finalWall pairs)

/-! ## THE MULTI-GAP HEAD-PREPEND WHISKER ARM -/

/-- ★★★ **THE `whiskerLeft` MULTI-GAP HEAD-PREPEND ARM.**  Given a factorization of an ARBITRARY body,
`whiskerLeft oneCell body` factors by prepending `emptyGapPair oneCell` (a leading inert wall slot) to the body's
`pairs`, keeping `finalWall`.  The boundary casts are the plain `congrArg (composePath oneCell) …` (NO associativity
cast — the prepended `nil` gap's `composePath nil` absorbs definitionally); the convertibility threads the body's own
`conv` under `whiskerLeftCongr`, pushes the frame past the boundary cast (`whiskerLeftCastBoundaryEq`), and re-inserts
the empty gap (`whiskerLeft_conv_emptyGapPrepend`).  The slot count is `bodySlotCount + 1` — a GENUINE multi-slot
layout, the r16 leg-2(b) upgrade over r15's single-gap whisker arm.  Over ANY signature and base relation. -/
def pushoutFactorizeWhiskerLeftMultiGap {signature : ModeSignature} (baseRel : CellRel signature)
    {oneMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph oneMode oneMode)
    {sourcePath targetPath : ModalityPath signature.graph oneMode oneMode}
    {body : RawTwoCellExpr signature sourcePath targetPath}
    (bodyFactorization : PushoutLayoutFactorization baseRel body) :
    PushoutLayoutFactorization baseRel (RawTwoCellExpr.whiskerLeft oneCell body) where
  finalWall := bodyFactorization.finalWall
  pairs := emptyGapPair oneCell :: bodyFactorization.pairs
  domEq := congrArg (composePath oneCell) bodyFactorization.domEq
  codEq := congrArg (composePath oneCell) bodyFactorization.codEq
  conv :=
    whiskerLeftCastBoundaryEq oneCell bodyFactorization.domEq bodyFactorization.codEq body ▸
      SaturatedConvOver.trans
        (SaturatedConvOver.whiskerLeftCongr oneCell bodyFactorization.conv)
        (whiskerLeft_conv_emptyGapPrepend bodyFactorization.finalWall oneCell bodyFactorization.pairs)

/-! ## The merge-into-head-wall assoc tower (the recon's named load-bearing piece) -/

/-- **Merge the frame into the HEAD gap's leading wall** — the CANONICAL merge alternative to the empty-gap prepend:
on `pair :: rest` fold `oneCell` into `pair.wall` (`composePath oneCell pair.wall`), keeping the gap; on `[]` a single
`emptyGapPair oneCell`.  This keeps the body's slot count (the frame does NOT open a fresh slot) — the canonical
firing-block form.  Its CELL-level surgery (relating `whiskerLeft` to this layout) rides `whiskerLeftComp` through the
`composePath`-associativity cast and is the r17 residual; its boundary tower is shipped below. -/
def mergeFrameIntoHead {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph oneMode oneMode) :
    List (VcompGapPair signature oneMode) → List (VcompGapPair signature oneMode)
  | [] => [emptyGapPair oneCell]
  | pair :: rest => { pair with wall := composePath oneCell pair.wall } :: rest

/-- ★★ **THE DOMAIN ASSOC LAW of the head-merge** (the recon-named "load-bearing missing piece", domain half).
`gapDomLayout finalWall (mergeFrameIntoHead oneCell pairs) = composePath oneCell (gapDomLayout finalWall pairs)` — the
frame merges into the head wall and re-associates out.  Structural on `pairs`: `[]` is `rfl` (`composePath nil` on the
`emptyGapPair`), `pair :: rest` is a single `composePath_assoc` (the merged wall `composePath oneCell pair.wall`
re-brackets against the rest of the domain layout).  Cast-clean — a 1-cell equality, no `castBoundary`. -/
theorem gapDomLayout_mergeFrameIntoHead {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (finalWall oneCell : ModalityPath signature.graph oneMode oneMode) :
    (pairs : List (VcompGapPair signature oneMode)) →
    gapDomLayout finalWall (mergeFrameIntoHead oneCell pairs)
      = composePath oneCell (gapDomLayout finalWall pairs)
  | [] => rfl
  | pair :: rest =>
      composePath_assoc oneCell pair.wall (composePath pair.gapDom (gapDomLayout finalWall rest))

/-- ★★ **THE CODOMAIN ASSOC LAW of the head-merge** (the recon-named piece, codomain half).  The `.gapCod` dual of
`gapDomLayout_mergeFrameIntoHead`. -/
theorem gapCodLayout_mergeFrameIntoHead {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (finalWall oneCell : ModalityPath signature.graph oneMode oneMode) :
    (pairs : List (VcompGapPair signature oneMode)) →
    gapCodLayout finalWall (mergeFrameIntoHead oneCell pairs)
      = composePath oneCell (gapCodLayout finalWall pairs)
  | [] => rfl
  | pair :: rest =>
      composePath_assoc oneCell pair.wall (composePath pair.gapCod (gapCodLayout finalWall rest))

/-! ## Concrete probe — slotCount > 1 on a framed multi-gap cell (FIRST) -/

/-- ★★★ **THE MULTI-GAP WITNESS — an `s`-frame over a genuine TWO-gap body.**  `whiskerLeft s` of the r7 two-gap
layout `[interleavedAssocGapPair, interleavedLeftUnitGapPair]` (a `mu`-associativity `t³ ⇒ t` in gap 1 and a left-unit
`t ⇒ t` in gap 2, at the REAL pushout signature) factors, via the multi-gap head-prepend, into a THREE-slot layout:
the `s`-frame slot plus the two body gaps.  A concrete, non-vacuous framed multi-gap cell. -/
def whiskerLeftMultiGapWitness :
    PushoutLayoutFactorization crossPairRealPushoutRel
      (RawTwoCellExpr.whiskerLeft monadPushSPath
        (gapVcompLayout pushoutTrivialWall [interleavedAssocGapPair, interleavedLeftUnitGapPair])) :=
  pushoutFactorizeWhiskerLeftMultiGap crossPairRealPushoutRel monadPushSPath
    (pushoutFactorizeOfLayout crossPairRealPushoutRel pushoutTrivialWall
      [interleavedAssocGapPair, interleavedLeftUnitGapPair])

/-- ★★★ **PROBE (slotCount > 1, FIRST).**  The multi-gap head-prepend witness has `pairs.length = 3` (`rfl`) — the
`s`-frame slot plus the two body gaps.  The genuine multi-slot layout the r15 single-gap whisker arm could not emit
(there `slotCount` stayed `1`).  This is the leg-2(b) deliverable, machine-checked. -/
theorem whiskerLeftMultiGapSlotCount : whiskerLeftMultiGapWitness.pairs.length = 3 := rfl

/-- ★ **The head-prepend grows the slot count by exactly one** — GENERAL: `whiskerLeft oneCell` of a body
factorization with `n` slots has `n + 1` slots (`rfl`, the prepended `emptyGapPair`).  The multi-slot invariant, over
any body / signature. -/
theorem pushoutFactorizeWhiskerLeftMultiGap_slotCount {signature : ModeSignature} (baseRel : CellRel signature)
    {oneMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph oneMode oneMode)
    {sourcePath targetPath : ModalityPath signature.graph oneMode oneMode}
    {body : RawTwoCellExpr signature sourcePath targetPath}
    (bodyFactorization : PushoutLayoutFactorization baseRel body) :
    (pushoutFactorizeWhiskerLeftMultiGap baseRel oneCell bodyFactorization).pairs.length
      = bodyFactorization.pairs.length + 1 := rfl

/-! ## Observability -/

-- The multi-gap head-prepend witness's slot count (expect `3`: the `s`-frame slot + the two body gaps).
#eval whiskerLeftMultiGapWitness.pairs.length

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the `whiskerLeft` MULTI-GAP head-prepend arm SHIPS (WP-AMALG-2 r16, B2).**  `= true`.
`pushoutFactorizeWhiskerLeftMultiGap` factors `whiskerLeft oneCell body` for an ARBITRARY multi-gap body
factorization by prepending `emptyGapPair oneCell` as a fresh leading inert wall slot — CAST-FREE (the prepended
`nil` gap's `composePath nil` absorbs definitionally, so the boundary casts are plain `congrArg (composePath
oneCell)`), via the head-prepend conv `whiskerLeft_conv_emptyGapPrepend` (strip the `oneCell`-whisker + re-insert the
empty gap by `emptyGapPrependInnerAbsorb`).  The slot count GROWS with the body
(`pushoutFactorizeWhiskerLeftMultiGap_slotCount`: `n → n + 1`).  Non-vacuous at the REAL pushout signature:
`whiskerLeftMultiGapWitness` (`s`-frame over the r7 two-gap `mu`-assoc + left-unit body) yields a THREE-slot layout
(`whiskerLeftMultiGapSlotCount`, `= 3` by `rfl`) — the genuine multi-slot layout r15's single-gap whisker arm could
not emit.  The recon-named merge-into-head-wall assoc tower also ships (`gapDomLayout_mergeFrameIntoHead` /
`gapCodLayout_mergeFrameIntoHead`, each a single `composePath_assoc`).

This does NOT ship the CANONICAL merge cell-surgery (relating `whiskerLeft` to `mergeFrameIntoHead`'s layout, riding
`whiskerLeftComp` through the `composePath`-associativity cast — r17), the `whiskerRight` multi-gap trailing-frame
append (needs the `gapDomLayout`-into-`finalWall` distribution induction), or the `s`-bearing frame's downstream
wall-shift (leg 2(a''), the wire-changing case).  `fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`;
`fxAmalg_hasFullSaturatedPushoutDispatch` / `fxAmalg_hasGeneralPushoutDispatch` STAY `false`.  #2043 does NOT close.
No fabricated flip.  `= true`. -/
def fxAmalg_hasWhiskerHeadPrependMultiGap : Bool := true

end FX1Poly.Polygraph.Amalgam
