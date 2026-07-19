import FX1Poly.Polygraph.Omega.ZXPhaseFree.SpiderRelationSeed
import FX1Poly.Polygraph.Omega.ZXPhaseFree.CompletenessGate
import FX1Poly.Polygraph.Omega.ZXPhaseFree.FusionRepair
import FX1Poly.Polygraph.Omega.ZXPhaseFree.NormalFormCensus
import FX1Poly.Polygraph.Omega.ZXPhaseFree.NormalFormLadder
import FX1Poly.Polygraph.Omega.ZXPhaseFree.ExchangeCompleteness

/-! # Polygraph/Omega/ZXPhaseFree/AbsorptionFlip — the leg-permutation engine (decided
half), THE WIRING WALL (named at its two minimal instances), and the absorption partials

The commissioned bill was (A) the leg-permutation engine, (B) the Kissinger Lemma
3.2/3.3 absorption induction over the census `zxnNormalForm`, (C) the completeness
flip `zxeCompletenessStatement` + the full decision.  Outcome, honestly:

## (A) DECIDED HALF — the within-spider leg-permutation engine

Everything a crossing can do TO THE LEGS OF ONE SPIDER is decided over `ZxeConv`,
at every position, every arity, both colours, both orientations:

* MIDDLE-PAIR FISSION/FUSION (`zxaMidMergeFuseZ/X`, `zxaMidForkFuseZ/X`): a binary
  merge (`spider 2 1`) at ANY wire position `passLeft` under a big same-colour
  spider fuses into it — `[[wire^p, s21, wire^q], [spider (p+1+q) d]] ~
  [[spider (p+2+q) d]]` — and dually a fork (`spider 1 2`) at any position over a
  big spider.  This strictly extends the shipped corner-only fusion family
  (`zxrZFuseLhs` links top-LAST-output to bottom-FIRST-input only): a three-case
  recursion on the pass-wire count — corner (fuse row), one-off-corner (THE ASSOC /
  COASSOC ROW re-brackets), general (fission + ONE right-first exchange + one
  splitLayer + descend) — exactly the general-k engine's recursion pattern one
  level up.
* SINGLE-CROSSING ABSORPTION at ANY adjacent leg pair
  (`zxaCrossingAbsorbInputZ/X`, `zxaCrossingAbsorbOutputZ/X`): a crossing whose
  BOTH legs are legs of one spider dies into it at every position — middle-pair
  fission isolates the pair into a binary spider, the (co)commutativity row kills
  the crossing, middle-pair fusion reabsorbs.
* ARBITRARY CROSSING WALKS (`ZxaSwapWalk`, `zxaWalkAbsorbInputZ/X`,
  `zxaWalkAbsorbOutputZ/X`): ANY sequence of adjacent-crossing layers acting on
  the legs of one spider absorbs, by induction on the walk — a spider's legs are
  routable to arbitrary positions relative to each other.  Fired at two fresh
  instances + a negative control (a crossing touching a NON-leg strand changes
  the relation: kernel span pin + non-convertibility).

## THE WALL — the missing wiring schema (named at its minimal instances)

The commissioned STRONGER half — conjugating a crossing past a spider so the
spider MOVES ACROSS A PASSIVE STRAND — is NOT derivable by any route found, and
this file names the obstruction precisely.  Every attack reduces to the
ONE-LEGGED CROSSING configuration: a crossing with one leg into a cell and one
leg to a passive/foreign strand, to which NO committed move applies (the
(co)commutativity rows need BOTH crossing legs on one spider; `bialgSquare` needs
the full four-spider sandwich, conjuring which needs unit/counit slides — which
ARE one-legged instances; `splitLayer`/exchange re-time but never re-order
strands; fusion is colour-local).  Three attack shapes were burned:
(1) comm/cocomm + corner/middle fission routes — blocked at the counit slide;
(2) compact-closed routes (cup = `Z01;Z12` = `X01;X12` by `cupCoincide`, yanking
    IS derivable from the corner-fusion family) — transposition re-lands on a
    one-legged crossing against a fork;
(3) `bialgSquare`-sandwich / 3-CNOT routes — conjuring the sandwich around a bare
    crossing needs the very slides being derived (circular).
Minimal blocking instances, minted owner-false with kernel span pins proving each
is semantically SOUND (candidate NEW MOVES in the r30 exchange style, not
refutation targets — the per-cell weight family is collapsed, so no counting
separator can exist): `zxaCounitSlideStatement` (`[[crossing],[Z10, wire]] ~
[[wire, Z10]]`) and `zxaSigmaInvolutionStatement` (`[[crossing],[crossing]] ~
[[wire, wire]]`).  CONSEQUENCE: the committed move set does not (yet) present the
free SYMMETRIC monoidal structure on the generators — sigma-involution,
Yang-Baxter, and one-legged naturality are all outside every found derivation.

## (B) PARTIALS — absorption statement minted, zero-generator instances land

`zxaAbsorptionStatement` (every WF diagram `ZxeConv`-converts to `zxnNormalForm`
of its own denotation) is minted OWNER FALSE.  What lands: the empty diagram at
boundary 0 (`zxaEmptyDiagramAbsorbed` — through the bialgebra bone) and a
zero-generator two-cell diagram (`zxaKillCreateAbsorbedFire` — one splitLayer +
one exchange land exactly on `zxnNormalForm 1 1` of its denotation).  BLOCKING
CONFIGURATION for everything beyond: every `zxnNormalForm` with a nonempty comb
(and already the identity-relation NF at boundary >= 1) embeds carrier crossings
whose two legs belong to DIFFERENT spiders (carrier tree vs strand chain) — the
one-legged configuration again.  (B) and hence (C) wait exactly on the wiring
schema above; `zxeCompletenessStatement` stays owner-false in its home file,
byte-intact, and `zxaHasFullDecision := false` records the honest (C) outcome.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; no `List.append`,
no `Int`, no `Nat.sub/div/mod/min/max`, no wildcard match arms over inductive
scrutinees. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.ZXPhaseFree

/-! ## Stage 0 — the mid-layer kit: one cell at an arbitrary wire position -/

/-- One cell at wire position `passLeft`, with `passRight` pass wires after it. -/
def zxaMidLayer (theCell : ZxpCell) (passLeft passRight : Nat) : List ZxpCell :=
  zxpCatCells (zxpWireCells passLeft) (theCell :: zxpWireCells passRight)

theorem zxaMidLayerDomArity (theCell : ZxpCell) (passLeft passRight : Nat) :
    zxpLayerDomArity (zxaMidLayer theCell passLeft passRight)
      = passLeft + (zxpCellDomArity theCell + passRight) := by
  show zxpLayerDomArity (zxpCatCells (zxpWireCells passLeft)
      (theCell :: zxpWireCells passRight))
    = passLeft + (zxpCellDomArity theCell + passRight)
  rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
  show passLeft + (zxpCellDomArity theCell + zxpLayerDomArity (zxpWireCells passRight))
    = passLeft + (zxpCellDomArity theCell + passRight)
  rw [zxpWireCellsDomArity]

theorem zxaMidLayerCodArity (theCell : ZxpCell) (passLeft passRight : Nat) :
    zxpLayerCodArity (zxaMidLayer theCell passLeft passRight)
      = passLeft + (zxpCellCodArity theCell + passRight) := by
  show zxpLayerCodArity (zxpCatCells (zxpWireCells passLeft)
      (theCell :: zxpWireCells passRight))
    = passLeft + (zxpCellCodArity theCell + passRight)
  rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
  show passLeft + (zxpCellCodArity theCell + zxpLayerCodArity (zxpWireCells passRight))
    = passLeft + (zxpCellCodArity theCell + passRight)
  rw [zxpWireCellsCodArity]

/-- Two adjacent wire blocks concatenate into one. -/
theorem zxaWiresWiresCat (frontCount backCount : Nat) (restCells : List ZxpCell) :
    zxpCatCells (zxpWireCells frontCount)
        (zxpCatCells (zxpWireCells backCount) restCells)
      = zxpCatCells (zxpWireCells (frontCount + backCount)) restCells := by
  rw [<- zxnCatCellsAssoc, zxnWireCellsCat]

/-- Re-associate a singleton-cell block into cons form. -/
theorem zxaCatMidCells (passLeft : Nat) (theCell : ZxpCell) (restCells : List ZxpCell) :
    zxpCatCells (zxpCatCells (zxpWireCells passLeft) [theCell]) restCells
      = zxpCatCells (zxpWireCells passLeft) (theCell :: restCells) := by
  rw [zxnCatCellsAssoc]
  rfl

/-- A wire directly after a wire block folds into the block. -/
theorem zxaWiresConsWire (frontCount : Nat) (restCells : List ZxpCell) :
    zxpCatCells (zxpWireCells frontCount) (ZxpCell.wire :: restCells)
      = zxpCatCells (zxpWireCells (frontCount + 1)) restCells := by
  show zxpCatCells (zxpWireCells frontCount)
      (zxpCatCells (zxpWireCells 1) restCells)
    = zxpCatCells (zxpWireCells (frontCount + 1)) restCells
  rw [zxaWiresWiresCat]

/-- The two-in-front shuffle: `a + (b + c) = (b + a) + c`. -/
theorem zxaShuffleFront (frontValue midValue tailValue : Nat) :
    frontValue + (midValue + tailValue) = (midValue + frontValue) + tailValue :=
  (Nat.add_assoc frontValue midValue tailValue).symm.trans
    (congrArg (fun innerValue => innerValue + tailValue)
      (Nat.add_comm frontValue midValue))

/-- Fire a bare window move as a conversion (empty context pad dissolves). -/
theorem zxaMoveConv {firstWindow secondWindow : ZxpDiagram}
    (hMove : ZxeWindowMove firstWindow secondWindow) :
    ZxeConv firstWindow secondWindow := by
  have hBundle := zxeWindowMoveBundle hMove
  have hStep := ZxeStep.pad firstWindow.sourceArity 0 0 [] [] hMove
    (ZxpLayersWF.nil _) (Nat.zero_add (firstWindow.sourceArity + 0)).symm
    (ZxpLayersWF.nil _)
  rw [zxpPadDiagramIdentityAt firstWindow.sourceArity firstWindow rfl,
    zxpPadDiagramIdentityAt firstWindow.sourceArity secondWindow hBundle.left.symm]
    at hStep
  exact ZxeConv.step hStep

/-! ## Stage 1 — MIDDLE-PAIR FISSION/FUSION, input side (merge under a big spider)

`[[wire^p, spider21, wire^q], [spider (p+(1+q)) d]] ~ [[spider (p+(2+q)) d]]` by
recursion on `p`: `p = 0` is the corner fuse row; `p = 1` re-brackets by THE ASSOC
ROW then corner-fuses twice; `p >= 2` fissions the bottom at its first input,
merges the disjoint right-first middle with ONE EXCHANGE, re-splits left-first,
and descends. -/

theorem zxaMidMergeFuseZ (botOutputs passRight : Nat) : (passLeft : Nat) ->
    ZxeConv
      { sourceArity := passLeft + (2 + passRight)
        layers := [zxaMidLayer (ZxpCell.zSpider 2 1) passLeft passRight,
          [ZxpCell.zSpider (passLeft + (1 + passRight)) botOutputs]] }
      { sourceArity := passLeft + (2 + passRight)
        layers := [[ZxpCell.zSpider (passLeft + (2 + passRight)) botOutputs]] }
  | 0 => by
      have hConv : ZxeConv
          { sourceArity := 2 + passRight
            layers := [ZxpCell.zSpider 2 1 :: zxpWireCells passRight,
              [ZxpCell.zSpider (1 + passRight) botOutputs]] }
          { sourceArity := 2 + passRight
            layers := [[ZxpCell.zSpider (2 + passRight) (0 + botOutputs)]] } :=
        zxaMoveConv (ZxeWindowMove.base
          (ZxrWindowMove.zFuse 2 0 passRight botOutputs))
      rw [Nat.zero_add botOutputs] at hConv
      have hSrc : (0 : Nat) + (2 + passRight) = 2 + passRight :=
        Nat.zero_add (2 + passRight)
      have hMid : (0 : Nat) + (1 + passRight) = 1 + passRight :=
        Nat.zero_add (1 + passRight)
      rw [hSrc, hMid]
      exact hConv
  | 1 => by
      have hIdxTwo : 2 + passRight = 1 + (1 + passRight) := Nat.add_assoc 1 1 passRight
      have hIdxThree : 1 + (2 + passRight) = 3 + passRight :=
        (Nat.add_assoc 1 2 passRight).symm
      rw [show (1 : Nat) + (1 + passRight) = 2 + passRight from hIdxTwo.symm]
      -- E0 = [[w, Z21, w^q], [Z(2+q, d)]] : fission the bottom at its first input
      have hFission : ZxeConv
          { sourceArity := 1 + (2 + passRight)
            layers := [zxaMidLayer (ZxpCell.zSpider 2 1) 1 passRight,
              ZxpCell.zSpider 2 1 :: zxpWireCells passRight,
              [ZxpCell.zSpider (1 + passRight) botOutputs]] }
          { sourceArity := 1 + (2 + passRight)
            layers := [zxaMidLayer (ZxpCell.zSpider 2 1) 1 passRight,
              [ZxpCell.zSpider (2 + passRight) (0 + botOutputs)]] } :=
        zxeStepConv (1 + (2 + passRight))
          [zxaMidLayer (ZxpCell.zSpider 2 1) 1 passRight] []
          (ZxeWindowMove.base (ZxrWindowMove.zFuse 2 0 passRight botOutputs))
          (ZxpLayersWF.cons
            (zxaMidLayerDomArity (ZxpCell.zSpider 2 1) 1 passRight)
            (ZxpLayersWF.nil _))
          (by
            show zxpLayerCodArity (zxaMidLayer (ZxpCell.zSpider 2 1) 1 passRight)
              = 2 + passRight
            rw [zxaMidLayerCodArity]
            exact hIdxTwo.symm)
          (ZxpLayersWF.nil _)
      rw [Nat.zero_add botOutputs] at hFission
      -- E1 ~ E2 : the assoc row (backward) re-brackets the two merges
      have hAssocStep := ZxeConv.step (ZxeStep.pad (1 + (2 + passRight)) 0 passRight []
        [[ZxpCell.zSpider (1 + passRight) botOutputs]]
        (ZxeWindowMove.base (ZxrWindowMove.seed (ZxpWindowMove.row ZxpRowTag.zMonoidAssoc)))
        (ZxpLayersWF.nil _)
        (hIdxThree.trans (Nat.zero_add (3 + passRight)).symm)
        (ZxpLayersWF.cons (Nat.zero_add (1 + passRight)).symm (ZxpLayersWF.nil _)))
      have hAssoc : ZxeConv
          { sourceArity := 1 + (2 + passRight)
            layers := [zxaMidLayer (ZxpCell.zSpider 2 1) 1 passRight,
              ZxpCell.zSpider 2 1 :: zxpWireCells passRight,
              [ZxpCell.zSpider (1 + passRight) botOutputs]] }
          { sourceArity := 1 + (2 + passRight)
            layers := [ZxpCell.zSpider 2 1 :: ZxpCell.wire :: zxpWireCells passRight,
              ZxpCell.zSpider 2 1 :: zxpWireCells passRight,
              [ZxpCell.zSpider (1 + passRight) botOutputs]] } :=
        ZxeConv.symm hAssocStep
      -- E2 ~ E3 : corner-fuse the exposed pair (whiskered zFuse 2 0 1 1)
      have hCornerPair : ZxeConv
          { sourceArity := 1 + (2 + passRight)
            layers := [ZxpCell.zSpider 2 1 :: ZxpCell.wire :: zxpWireCells passRight,
              ZxpCell.zSpider 2 1 :: zxpWireCells passRight,
              [ZxpCell.zSpider (1 + passRight) botOutputs]] }
          { sourceArity := 1 + (2 + passRight)
            layers := [ZxpCell.zSpider 3 1 :: zxpWireCells passRight,
              [ZxpCell.zSpider (1 + passRight) botOutputs]] } :=
        ZxeConv.step (ZxeStep.pad (1 + (2 + passRight)) 0 passRight []
          [[ZxpCell.zSpider (1 + passRight) botOutputs]]
          (ZxeWindowMove.base (ZxrWindowMove.zFuse 2 0 1 1))
          (ZxpLayersWF.nil _)
          (hIdxThree.trans (Nat.zero_add (3 + passRight)).symm)
          (ZxpLayersWF.cons (Nat.zero_add (1 + passRight)).symm (ZxpLayersWF.nil _)))
      -- E3 ~ E4 : the final corner fuse
      have hFinal : ZxeConv
          { sourceArity := 3 + passRight
            layers := [ZxpCell.zSpider 3 1 :: zxpWireCells passRight,
              [ZxpCell.zSpider (1 + passRight) botOutputs]] }
          { sourceArity := 3 + passRight
            layers := [[ZxpCell.zSpider (3 + passRight) (0 + botOutputs)]] } :=
        zxaMoveConv (ZxeWindowMove.base
          (ZxrWindowMove.zFuse 3 0 passRight botOutputs))
      rw [Nat.zero_add botOutputs, <- hIdxThree] at hFinal
      exact ZxeConv.trans (ZxeConv.symm hFission)
        (ZxeConv.trans hAssoc (ZxeConv.trans hCornerPair hFinal))
  | passPred + 2 => by
      have hIdxBot : (passPred + 2) + (1 + passRight)
          = 2 + (passPred + (1 + passRight)) :=
        (zxaShuffleFront 2 passPred (1 + passRight)).symm
      have hIdxSrc : 2 + (passPred + (2 + passRight))
          = (passPred + 2) + (2 + passRight) :=
        zxaShuffleFront 2 passPred (2 + passRight)
      have hIdxLift : 1 + (passPred + (2 + passRight))
          = (passPred + 1) + (2 + passRight) :=
        zxaShuffleFront 1 passPred (2 + passRight)
      have hIdxDown : 1 + (passPred + (1 + passRight))
          = (passPred + 1) + (1 + passRight) :=
        zxaShuffleFront 1 passPred (1 + passRight)
      rw [hIdxBot]
      -- D0 : fission the bottom at its first input
      have hFission : ZxeConv
          { sourceArity := (passPred + 2) + (2 + passRight)
            layers := [zxaMidLayer (ZxpCell.zSpider 2 1) (passPred + 2) passRight,
              ZxpCell.zSpider 2 1 :: zxpWireCells (passPred + (1 + passRight)),
              [ZxpCell.zSpider (1 + (passPred + (1 + passRight))) botOutputs]] }
          { sourceArity := (passPred + 2) + (2 + passRight)
            layers := [zxaMidLayer (ZxpCell.zSpider 2 1) (passPred + 2) passRight,
              [ZxpCell.zSpider (2 + (passPred + (1 + passRight))) (0 + botOutputs)]] } :=
        zxeStepConv ((passPred + 2) + (2 + passRight))
          [zxaMidLayer (ZxpCell.zSpider 2 1) (passPred + 2) passRight] []
          (ZxeWindowMove.base
            (ZxrWindowMove.zFuse 2 0 (passPred + (1 + passRight)) botOutputs))
          (ZxpLayersWF.cons
            (zxaMidLayerDomArity (ZxpCell.zSpider 2 1) (passPred + 2) passRight)
            (ZxpLayersWF.nil _))
          (by
            show zxpLayerCodArity
                (zxaMidLayer (ZxpCell.zSpider 2 1) (passPred + 2) passRight)
              = 2 + (passPred + (1 + passRight))
            rw [zxaMidLayerCodArity]
            exact hIdxBot)
          (ZxpLayersWF.nil _)
      rw [Nat.zero_add botOutputs] at hFission
      -- D1 ~ D2 : ONE EXCHANGE merges the disjoint right-first middle pair
      have hDomMid : zxpLayerDomArity
          (zxaMidLayer (ZxpCell.zSpider 2 1) passPred passRight)
          = passPred + (2 + passRight) :=
        zxaMidLayerDomArity (ZxpCell.zSpider 2 1) passPred passRight
      have hCodMid : zxpLayerCodArity
          (zxaMidLayer (ZxpCell.zSpider 2 1) passPred passRight)
          = passPred + (1 + passRight) :=
        zxaMidLayerCodArity (ZxpCell.zSpider 2 1) passPred passRight
      have hDomMerge : zxpLayerDomArity [ZxpCell.zSpider 2 1] = 2 := rfl
      have hExchange : ZxeConv
          { sourceArity := 2 + zxpLayerDomArity
              (zxaMidLayer (ZxpCell.zSpider 2 1) passPred passRight)
            layers := [zxpCatCells (zxpWireCells 2)
                (zxaMidLayer (ZxpCell.zSpider 2 1) passPred passRight),
              zxpCatCells [ZxpCell.zSpider 2 1]
                (zxpWireCells (zxpLayerCodArity
                  (zxaMidLayer (ZxpCell.zSpider 2 1) passPred passRight)))] }
          { sourceArity := 2 + zxpLayerDomArity
              (zxaMidLayer (ZxpCell.zSpider 2 1) passPred passRight)
            layers := [zxpCatCells [ZxpCell.zSpider 2 1]
                (zxaMidLayer (ZxpCell.zSpider 2 1) passPred passRight)] } :=
        zxeExchangeConv [ZxpCell.zSpider 2 1]
          (zxaMidLayer (ZxpCell.zSpider 2 1) passPred passRight)
      rw [hDomMid, hCodMid, hIdxSrc] at hExchange
      have hExchangeLifted : ZxeConv
          { sourceArity := (passPred + 2) + (2 + passRight)
            layers := [zxaMidLayer (ZxpCell.zSpider 2 1) (passPred + 2) passRight,
              ZxpCell.zSpider 2 1 :: zxpWireCells (passPred + (1 + passRight)),
              [ZxpCell.zSpider (1 + (passPred + (1 + passRight))) botOutputs]] }
          { sourceArity := (passPred + 2) + (2 + passRight)
            layers := [zxpCatCells [ZxpCell.zSpider 2 1]
                (zxaMidLayer (ZxpCell.zSpider 2 1) passPred passRight),
              [ZxpCell.zSpider (1 + (passPred + (1 + passRight))) botOutputs]] } :=
        zxeLiftConv ((passPred + 2) + (2 + passRight)) []
          [[ZxpCell.zSpider (1 + (passPred + (1 + passRight))) botOutputs]]
          hExchange (ZxpLayersWF.nil _) rfl
          (by
            show ZxpLayersWF (zxpLayerCodArity (zxpCatCells [ZxpCell.zSpider 2 1]
              (zxpWireCells (passPred + (1 + passRight)))))
              [[ZxpCell.zSpider (1 + (passPred + (1 + passRight))) botOutputs]]
            rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
            exact ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
      -- D2 ~ D3 : one splitLayer re-splits the merged middle LEFT-FIRST
      have hSplit : ZxeConv
          { sourceArity := (passPred + 2) + (2 + passRight)
            layers := [zxpCatCells [ZxpCell.zSpider 2 1]
                (zxaMidLayer (ZxpCell.zSpider 2 1) passPred passRight),
              [ZxpCell.zSpider (1 + (passPred + (1 + passRight))) botOutputs]] }
          { sourceArity := (passPred + 2) + (2 + passRight)
            layers := [zxpCatCells [ZxpCell.zSpider 2 1]
                (zxpWireCells (passPred + (2 + passRight))),
              ZxpCell.wire :: zxaMidLayer (ZxpCell.zSpider 2 1) passPred passRight,
              [ZxpCell.zSpider (1 + (passPred + (1 + passRight))) botOutputs]] } := by
        have hRaw := zxeStepConv ((passPred + 2) + (2 + passRight)) []
          [[ZxpCell.zSpider (1 + (passPred + (1 + passRight))) botOutputs]]
          (ZxeWindowMove.base (ZxrWindowMove.seed (ZxpWindowMove.splitLayer
            [ZxpCell.zSpider 2 1]
            (zxaMidLayer (ZxpCell.zSpider 2 1) passPred passRight))))
          (ZxpLayersWF.nil _)
          (by
            show (passPred + 2) + (2 + passRight)
              = zxpLayerDomArity [ZxpCell.zSpider 2 1]
                + zxpLayerDomArity (zxaMidLayer (ZxpCell.zSpider 2 1) passPred passRight)
            rw [hDomMid, hDomMerge]
            exact hIdxSrc.symm)
          (by
            show ZxpLayersWF (zxpLayerCodArity (zxpCatCells [ZxpCell.zSpider 2 1]
              (zxaMidLayer (ZxpCell.zSpider 2 1) passPred passRight)))
              [[ZxpCell.zSpider (1 + (passPred + (1 + passRight))) botOutputs]]
            rw [zxpCatCellsCodArity, hCodMid]
            exact ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
        rw [hDomMid] at hRaw
        exact hRaw
      -- D3 ~ D4 : descend (the recursion at passPred + 1)
      have hInner := zxaMidMergeFuseZ botOutputs passRight (passPred + 1)
      rw [<- hIdxDown] at hInner
      have hInnerLifted : ZxeConv
          { sourceArity := (passPred + 2) + (2 + passRight)
            layers := [zxpCatCells [ZxpCell.zSpider 2 1]
                (zxpWireCells (passPred + (2 + passRight))),
              ZxpCell.wire :: zxaMidLayer (ZxpCell.zSpider 2 1) passPred passRight,
              [ZxpCell.zSpider (1 + (passPred + (1 + passRight))) botOutputs]] }
          { sourceArity := (passPred + 2) + (2 + passRight)
            layers := [zxpCatCells [ZxpCell.zSpider 2 1]
                (zxpWireCells (passPred + (2 + passRight))),
              [ZxpCell.zSpider ((passPred + 1) + (2 + passRight)) botOutputs]] } := by
        have hRaw := zxeLiftConv ((passPred + 2) + (2 + passRight))
          [zxpCatCells [ZxpCell.zSpider 2 1]
            (zxpWireCells (passPred + (2 + passRight)))] [] hInner
          (ZxpLayersWF.cons
            (by
              show zxpLayerDomArity (zxpCatCells [ZxpCell.zSpider 2 1]
                (zxpWireCells (passPred + (2 + passRight))))
                = (passPred + 2) + (2 + passRight)
              rw [zxpCatCellsDomArity, zxpWireCellsDomArity, hDomMerge]
              exact hIdxSrc)
            (ZxpLayersWF.nil _))
          (by
            show zxpLayerCodArity (zxpCatCells [ZxpCell.zSpider 2 1]
              (zxpWireCells (passPred + (2 + passRight))))
              = (passPred + 1) + (2 + passRight)
            rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
            exact hIdxLift)
          (ZxpLayersWF.nil _)
        rw [zxpCatLayersNilRight] at hRaw
        exact hRaw
      -- D4 ~ D5 : the final corner fuse
      have hFinal : ZxeConv
          { sourceArity := 2 + (passPred + (2 + passRight))
            layers := [ZxpCell.zSpider 2 1
                :: zxpWireCells (passPred + (2 + passRight)),
              [ZxpCell.zSpider (1 + (passPred + (2 + passRight))) botOutputs]] }
          { sourceArity := 2 + (passPred + (2 + passRight))
            layers := [[ZxpCell.zSpider (2 + (passPred + (2 + passRight)))
              (0 + botOutputs)]] } :=
        zxaMoveConv (ZxeWindowMove.base
          (ZxrWindowMove.zFuse 2 0 (passPred + (2 + passRight)) botOutputs))
      rw [Nat.zero_add botOutputs, hIdxSrc, hIdxLift] at hFinal
      exact ZxeConv.trans (ZxeConv.symm hFission)
        (ZxeConv.trans hExchangeLifted (ZxeConv.trans hSplit
          (ZxeConv.trans hInnerLifted hFinal)))

/-- The X colour mirror of the middle-pair merge fusion. -/
theorem zxaMidMergeFuseX (botOutputs passRight : Nat) : (passLeft : Nat) ->
    ZxeConv
      { sourceArity := passLeft + (2 + passRight)
        layers := [zxaMidLayer (ZxpCell.xSpider 2 1) passLeft passRight,
          [ZxpCell.xSpider (passLeft + (1 + passRight)) botOutputs]] }
      { sourceArity := passLeft + (2 + passRight)
        layers := [[ZxpCell.xSpider (passLeft + (2 + passRight)) botOutputs]] }
  | 0 => by
      have hConv : ZxeConv
          { sourceArity := 2 + passRight
            layers := [ZxpCell.xSpider 2 1 :: zxpWireCells passRight,
              [ZxpCell.xSpider (1 + passRight) botOutputs]] }
          { sourceArity := 2 + passRight
            layers := [[ZxpCell.xSpider (2 + passRight) (0 + botOutputs)]] } :=
        zxaMoveConv (ZxeWindowMove.base
          (ZxrWindowMove.xFuse 2 0 passRight botOutputs))
      rw [Nat.zero_add botOutputs] at hConv
      have hSrc : (0 : Nat) + (2 + passRight) = 2 + passRight :=
        Nat.zero_add (2 + passRight)
      have hMid : (0 : Nat) + (1 + passRight) = 1 + passRight :=
        Nat.zero_add (1 + passRight)
      rw [hSrc, hMid]
      exact hConv
  | 1 => by
      have hIdxTwo : 2 + passRight = 1 + (1 + passRight) := Nat.add_assoc 1 1 passRight
      have hIdxThree : 1 + (2 + passRight) = 3 + passRight :=
        (Nat.add_assoc 1 2 passRight).symm
      rw [show (1 : Nat) + (1 + passRight) = 2 + passRight from hIdxTwo.symm]
      have hFission : ZxeConv
          { sourceArity := 1 + (2 + passRight)
            layers := [zxaMidLayer (ZxpCell.xSpider 2 1) 1 passRight,
              ZxpCell.xSpider 2 1 :: zxpWireCells passRight,
              [ZxpCell.xSpider (1 + passRight) botOutputs]] }
          { sourceArity := 1 + (2 + passRight)
            layers := [zxaMidLayer (ZxpCell.xSpider 2 1) 1 passRight,
              [ZxpCell.xSpider (2 + passRight) (0 + botOutputs)]] } :=
        zxeStepConv (1 + (2 + passRight))
          [zxaMidLayer (ZxpCell.xSpider 2 1) 1 passRight] []
          (ZxeWindowMove.base (ZxrWindowMove.xFuse 2 0 passRight botOutputs))
          (ZxpLayersWF.cons
            (zxaMidLayerDomArity (ZxpCell.xSpider 2 1) 1 passRight)
            (ZxpLayersWF.nil _))
          (by
            show zxpLayerCodArity (zxaMidLayer (ZxpCell.xSpider 2 1) 1 passRight)
              = 2 + passRight
            rw [zxaMidLayerCodArity]
            exact hIdxTwo.symm)
          (ZxpLayersWF.nil _)
      rw [Nat.zero_add botOutputs] at hFission
      have hAssocStep := ZxeConv.step (ZxeStep.pad (1 + (2 + passRight)) 0 passRight []
        [[ZxpCell.xSpider (1 + passRight) botOutputs]]
        (ZxeWindowMove.base (ZxrWindowMove.seed (ZxpWindowMove.row ZxpRowTag.xMonoidAssoc)))
        (ZxpLayersWF.nil _)
        (hIdxThree.trans (Nat.zero_add (3 + passRight)).symm)
        (ZxpLayersWF.cons (Nat.zero_add (1 + passRight)).symm (ZxpLayersWF.nil _)))
      have hAssoc : ZxeConv
          { sourceArity := 1 + (2 + passRight)
            layers := [zxaMidLayer (ZxpCell.xSpider 2 1) 1 passRight,
              ZxpCell.xSpider 2 1 :: zxpWireCells passRight,
              [ZxpCell.xSpider (1 + passRight) botOutputs]] }
          { sourceArity := 1 + (2 + passRight)
            layers := [ZxpCell.xSpider 2 1 :: ZxpCell.wire :: zxpWireCells passRight,
              ZxpCell.xSpider 2 1 :: zxpWireCells passRight,
              [ZxpCell.xSpider (1 + passRight) botOutputs]] } :=
        ZxeConv.symm hAssocStep
      have hCornerPair : ZxeConv
          { sourceArity := 1 + (2 + passRight)
            layers := [ZxpCell.xSpider 2 1 :: ZxpCell.wire :: zxpWireCells passRight,
              ZxpCell.xSpider 2 1 :: zxpWireCells passRight,
              [ZxpCell.xSpider (1 + passRight) botOutputs]] }
          { sourceArity := 1 + (2 + passRight)
            layers := [ZxpCell.xSpider 3 1 :: zxpWireCells passRight,
              [ZxpCell.xSpider (1 + passRight) botOutputs]] } :=
        ZxeConv.step (ZxeStep.pad (1 + (2 + passRight)) 0 passRight []
          [[ZxpCell.xSpider (1 + passRight) botOutputs]]
          (ZxeWindowMove.base (ZxrWindowMove.xFuse 2 0 1 1))
          (ZxpLayersWF.nil _)
          (hIdxThree.trans (Nat.zero_add (3 + passRight)).symm)
          (ZxpLayersWF.cons (Nat.zero_add (1 + passRight)).symm (ZxpLayersWF.nil _)))
      have hFinal : ZxeConv
          { sourceArity := 3 + passRight
            layers := [ZxpCell.xSpider 3 1 :: zxpWireCells passRight,
              [ZxpCell.xSpider (1 + passRight) botOutputs]] }
          { sourceArity := 3 + passRight
            layers := [[ZxpCell.xSpider (3 + passRight) (0 + botOutputs)]] } :=
        zxaMoveConv (ZxeWindowMove.base
          (ZxrWindowMove.xFuse 3 0 passRight botOutputs))
      rw [Nat.zero_add botOutputs, <- hIdxThree] at hFinal
      exact ZxeConv.trans (ZxeConv.symm hFission)
        (ZxeConv.trans hAssoc (ZxeConv.trans hCornerPair hFinal))
  | passPred + 2 => by
      have hIdxBot : (passPred + 2) + (1 + passRight)
          = 2 + (passPred + (1 + passRight)) :=
        (zxaShuffleFront 2 passPred (1 + passRight)).symm
      have hIdxSrc : 2 + (passPred + (2 + passRight))
          = (passPred + 2) + (2 + passRight) :=
        zxaShuffleFront 2 passPred (2 + passRight)
      have hIdxLift : 1 + (passPred + (2 + passRight))
          = (passPred + 1) + (2 + passRight) :=
        zxaShuffleFront 1 passPred (2 + passRight)
      have hIdxDown : 1 + (passPred + (1 + passRight))
          = (passPred + 1) + (1 + passRight) :=
        zxaShuffleFront 1 passPred (1 + passRight)
      rw [hIdxBot]
      have hFission : ZxeConv
          { sourceArity := (passPred + 2) + (2 + passRight)
            layers := [zxaMidLayer (ZxpCell.xSpider 2 1) (passPred + 2) passRight,
              ZxpCell.xSpider 2 1 :: zxpWireCells (passPred + (1 + passRight)),
              [ZxpCell.xSpider (1 + (passPred + (1 + passRight))) botOutputs]] }
          { sourceArity := (passPred + 2) + (2 + passRight)
            layers := [zxaMidLayer (ZxpCell.xSpider 2 1) (passPred + 2) passRight,
              [ZxpCell.xSpider (2 + (passPred + (1 + passRight))) (0 + botOutputs)]] } :=
        zxeStepConv ((passPred + 2) + (2 + passRight))
          [zxaMidLayer (ZxpCell.xSpider 2 1) (passPred + 2) passRight] []
          (ZxeWindowMove.base
            (ZxrWindowMove.xFuse 2 0 (passPred + (1 + passRight)) botOutputs))
          (ZxpLayersWF.cons
            (zxaMidLayerDomArity (ZxpCell.xSpider 2 1) (passPred + 2) passRight)
            (ZxpLayersWF.nil _))
          (by
            show zxpLayerCodArity
                (zxaMidLayer (ZxpCell.xSpider 2 1) (passPred + 2) passRight)
              = 2 + (passPred + (1 + passRight))
            rw [zxaMidLayerCodArity]
            exact hIdxBot)
          (ZxpLayersWF.nil _)
      rw [Nat.zero_add botOutputs] at hFission
      have hDomMid : zxpLayerDomArity
          (zxaMidLayer (ZxpCell.xSpider 2 1) passPred passRight)
          = passPred + (2 + passRight) :=
        zxaMidLayerDomArity (ZxpCell.xSpider 2 1) passPred passRight
      have hCodMid : zxpLayerCodArity
          (zxaMidLayer (ZxpCell.xSpider 2 1) passPred passRight)
          = passPred + (1 + passRight) :=
        zxaMidLayerCodArity (ZxpCell.xSpider 2 1) passPred passRight
      have hDomMerge : zxpLayerDomArity [ZxpCell.xSpider 2 1] = 2 := rfl
      have hExchange : ZxeConv
          { sourceArity := 2 + zxpLayerDomArity
              (zxaMidLayer (ZxpCell.xSpider 2 1) passPred passRight)
            layers := [zxpCatCells (zxpWireCells 2)
                (zxaMidLayer (ZxpCell.xSpider 2 1) passPred passRight),
              zxpCatCells [ZxpCell.xSpider 2 1]
                (zxpWireCells (zxpLayerCodArity
                  (zxaMidLayer (ZxpCell.xSpider 2 1) passPred passRight)))] }
          { sourceArity := 2 + zxpLayerDomArity
              (zxaMidLayer (ZxpCell.xSpider 2 1) passPred passRight)
            layers := [zxpCatCells [ZxpCell.xSpider 2 1]
                (zxaMidLayer (ZxpCell.xSpider 2 1) passPred passRight)] } :=
        zxeExchangeConv [ZxpCell.xSpider 2 1]
          (zxaMidLayer (ZxpCell.xSpider 2 1) passPred passRight)
      rw [hDomMid, hCodMid, hIdxSrc] at hExchange
      have hExchangeLifted : ZxeConv
          { sourceArity := (passPred + 2) + (2 + passRight)
            layers := [zxaMidLayer (ZxpCell.xSpider 2 1) (passPred + 2) passRight,
              ZxpCell.xSpider 2 1 :: zxpWireCells (passPred + (1 + passRight)),
              [ZxpCell.xSpider (1 + (passPred + (1 + passRight))) botOutputs]] }
          { sourceArity := (passPred + 2) + (2 + passRight)
            layers := [zxpCatCells [ZxpCell.xSpider 2 1]
                (zxaMidLayer (ZxpCell.xSpider 2 1) passPred passRight),
              [ZxpCell.xSpider (1 + (passPred + (1 + passRight))) botOutputs]] } :=
        zxeLiftConv ((passPred + 2) + (2 + passRight)) []
          [[ZxpCell.xSpider (1 + (passPred + (1 + passRight))) botOutputs]]
          hExchange (ZxpLayersWF.nil _) rfl
          (by
            show ZxpLayersWF (zxpLayerCodArity (zxpCatCells [ZxpCell.xSpider 2 1]
              (zxpWireCells (passPred + (1 + passRight)))))
              [[ZxpCell.xSpider (1 + (passPred + (1 + passRight))) botOutputs]]
            rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
            exact ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
      have hSplit : ZxeConv
          { sourceArity := (passPred + 2) + (2 + passRight)
            layers := [zxpCatCells [ZxpCell.xSpider 2 1]
                (zxaMidLayer (ZxpCell.xSpider 2 1) passPred passRight),
              [ZxpCell.xSpider (1 + (passPred + (1 + passRight))) botOutputs]] }
          { sourceArity := (passPred + 2) + (2 + passRight)
            layers := [zxpCatCells [ZxpCell.xSpider 2 1]
                (zxpWireCells (passPred + (2 + passRight))),
              ZxpCell.wire :: zxaMidLayer (ZxpCell.xSpider 2 1) passPred passRight,
              [ZxpCell.xSpider (1 + (passPred + (1 + passRight))) botOutputs]] } := by
        have hRaw := zxeStepConv ((passPred + 2) + (2 + passRight)) []
          [[ZxpCell.xSpider (1 + (passPred + (1 + passRight))) botOutputs]]
          (ZxeWindowMove.base (ZxrWindowMove.seed (ZxpWindowMove.splitLayer
            [ZxpCell.xSpider 2 1]
            (zxaMidLayer (ZxpCell.xSpider 2 1) passPred passRight))))
          (ZxpLayersWF.nil _)
          (by
            show (passPred + 2) + (2 + passRight)
              = zxpLayerDomArity [ZxpCell.xSpider 2 1]
                + zxpLayerDomArity (zxaMidLayer (ZxpCell.xSpider 2 1) passPred passRight)
            rw [hDomMid, hDomMerge]
            exact hIdxSrc.symm)
          (by
            show ZxpLayersWF (zxpLayerCodArity (zxpCatCells [ZxpCell.xSpider 2 1]
              (zxaMidLayer (ZxpCell.xSpider 2 1) passPred passRight)))
              [[ZxpCell.xSpider (1 + (passPred + (1 + passRight))) botOutputs]]
            rw [zxpCatCellsCodArity, hCodMid]
            exact ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
        rw [hDomMid] at hRaw
        exact hRaw
      have hInner := zxaMidMergeFuseX botOutputs passRight (passPred + 1)
      rw [<- hIdxDown] at hInner
      have hInnerLifted : ZxeConv
          { sourceArity := (passPred + 2) + (2 + passRight)
            layers := [zxpCatCells [ZxpCell.xSpider 2 1]
                (zxpWireCells (passPred + (2 + passRight))),
              ZxpCell.wire :: zxaMidLayer (ZxpCell.xSpider 2 1) passPred passRight,
              [ZxpCell.xSpider (1 + (passPred + (1 + passRight))) botOutputs]] }
          { sourceArity := (passPred + 2) + (2 + passRight)
            layers := [zxpCatCells [ZxpCell.xSpider 2 1]
                (zxpWireCells (passPred + (2 + passRight))),
              [ZxpCell.xSpider ((passPred + 1) + (2 + passRight)) botOutputs]] } := by
        have hRaw := zxeLiftConv ((passPred + 2) + (2 + passRight))
          [zxpCatCells [ZxpCell.xSpider 2 1]
            (zxpWireCells (passPred + (2 + passRight)))] [] hInner
          (ZxpLayersWF.cons
            (by
              show zxpLayerDomArity (zxpCatCells [ZxpCell.xSpider 2 1]
                (zxpWireCells (passPred + (2 + passRight))))
                = (passPred + 2) + (2 + passRight)
              rw [zxpCatCellsDomArity, zxpWireCellsDomArity, hDomMerge]
              exact hIdxSrc)
            (ZxpLayersWF.nil _))
          (by
            show zxpLayerCodArity (zxpCatCells [ZxpCell.xSpider 2 1]
              (zxpWireCells (passPred + (2 + passRight))))
              = (passPred + 1) + (2 + passRight)
            rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
            exact hIdxLift)
          (ZxpLayersWF.nil _)
        rw [zxpCatLayersNilRight] at hRaw
        exact hRaw
      have hFinal : ZxeConv
          { sourceArity := 2 + (passPred + (2 + passRight))
            layers := [ZxpCell.xSpider 2 1
                :: zxpWireCells (passPred + (2 + passRight)),
              [ZxpCell.xSpider (1 + (passPred + (2 + passRight))) botOutputs]] }
          { sourceArity := 2 + (passPred + (2 + passRight))
            layers := [[ZxpCell.xSpider (2 + (passPred + (2 + passRight)))
              (0 + botOutputs)]] } :=
        zxaMoveConv (ZxeWindowMove.base
          (ZxrWindowMove.xFuse 2 0 (passPred + (2 + passRight)) botOutputs))
      rw [Nat.zero_add botOutputs, hIdxSrc, hIdxLift] at hFinal
      exact ZxeConv.trans (ZxeConv.symm hFission)
        (ZxeConv.trans hExchangeLifted (ZxeConv.trans hSplit
          (ZxeConv.trans hInnerLifted hFinal)))

/-! ## Stage 2 — MIDDLE-PAIR FISSION/FUSION, output side (fork over a big spider)

`[[spider a (p+(1+q))], [wire^p, spider12, wire^q]] ~ [[spider a (p+(2+q))]]` by
recursion on `q`: `q = 0` is the corner fuse; `q = 1` re-brackets by THE COASSOC
ROW; `q >= 2` fissions the top at its last output, one exchange, one splitLayer,
descend. -/

theorem zxaMidForkFuseZ (topInputs passLeft : Nat) : (passRight : Nat) ->
    ZxeConv
      { sourceArity := topInputs
        layers := [[ZxpCell.zSpider topInputs (passLeft + (1 + passRight))],
          zxaMidLayer (ZxpCell.zSpider 1 2) passLeft passRight] }
      { sourceArity := topInputs
        layers := [[ZxpCell.zSpider topInputs (passLeft + (2 + passRight))]] }
  | 0 => zxaMoveConv (ZxeWindowMove.base (ZxrWindowMove.zFuse topInputs passLeft 0 2))
  | 1 => by
      -- E0 : fission the top spider at its last output (corner fuse backward)
      have hFission : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs (passLeft + 1)],
              zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2],
              zxaMidLayer (ZxpCell.zSpider 1 2) passLeft 1] }
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs (passLeft + 2)],
              zxaMidLayer (ZxpCell.zSpider 1 2) passLeft 1] } :=
        zxeStepConv topInputs [] [zxaMidLayer (ZxpCell.zSpider 1 2) passLeft 1]
          (ZxeWindowMove.base (ZxrWindowMove.zFuse topInputs passLeft 0 2))
          (ZxpLayersWF.nil _) rfl
          (by
            show ZxpLayersWF (zxpLayerCodArity (zxpCatCells (zxpWireCells passLeft)
              [ZxpCell.zSpider (1 + 0) 2]))
              [zxaMidLayer (ZxpCell.zSpider 1 2) passLeft 1]
            rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
            exact ZxpLayersWF.cons
              (zxaMidLayerDomArity (ZxpCell.zSpider 1 2) passLeft 1)
              (ZxpLayersWF.nil _))
      -- E1 ~ E2 : THE COASSOC ROW moves the second fork one strand right
      have hCoassoc : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs (passLeft + 1)],
              zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2],
              zxaMidLayer (ZxpCell.zSpider 1 2) passLeft 1] }
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs (passLeft + 1)],
              zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2],
              zxpCatCells (zxpWireCells passLeft)
                (ZxpCell.wire :: [ZxpCell.zSpider 1 2])] } :=
        ZxeConv.step (ZxeStep.pad topInputs passLeft 0
          [[ZxpCell.zSpider topInputs (passLeft + 1)]] []
          (ZxeWindowMove.base (ZxrWindowMove.seed
            (ZxpWindowMove.row ZxpRowTag.zComonoidCoassoc)))
          (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _))
      rw [zxaWiresConsWire passLeft [ZxpCell.zSpider 1 2]] at hCoassoc
      -- E2 ~ E3 : corner-fuse the first fork back in
      have hFuseOne : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs (passLeft + 1)],
              zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2],
              zxpCatCells (zxpWireCells (passLeft + 1)) [ZxpCell.zSpider 1 2]] }
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs (passLeft + 2)],
              zxpCatCells (zxpWireCells (passLeft + 1)) [ZxpCell.zSpider 1 2]] } :=
        zxeStepConv topInputs []
          [zxpCatCells (zxpWireCells (passLeft + 1)) [ZxpCell.zSpider 1 2]]
          (ZxeWindowMove.base (ZxrWindowMove.zFuse topInputs passLeft 0 2))
          (ZxpLayersWF.nil _) rfl
          (by
            show ZxpLayersWF (zxpLayerCodArity (zxpCatCells (zxpWireCells passLeft)
              [ZxpCell.zSpider (1 + 0) 2]))
              [zxpCatCells (zxpWireCells (passLeft + 1)) [ZxpCell.zSpider 1 2]]
            rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
            refine ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _)
            rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
            rfl)
      -- E3 ~ E4 : corner-fuse the moved fork
      have hFinal : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs (passLeft + 2)],
              zxpCatCells (zxpWireCells (passLeft + 1)) [ZxpCell.zSpider 1 2]] }
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs (passLeft + 3)]] } :=
        zxaMoveConv (ZxeWindowMove.base
          (ZxrWindowMove.zFuse topInputs (passLeft + 1) 0 2))
      exact ZxeConv.trans (ZxeConv.symm hFission)
        (ZxeConv.trans hCoassoc (ZxeConv.trans hFuseOne hFinal))
  | passRightPred + 2 => by
      have hIdxTail : (passLeft + 2) + passRightPred
          = passLeft + (2 + passRightPred) :=
        Nat.add_assoc passLeft 2 passRightPred
      have hIdxSpare : (passLeft + 1) + passRightPred
          = passLeft + (1 + passRightPred) :=
        Nat.add_assoc passLeft 1 passRightPred
      -- D0 : fission the top spider at its last output (corner fuse backward)
      have hFission : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs
                ((passLeft + (1 + passRightPred)) + 1)],
              zxpCatCells (zxpWireCells (passLeft + (1 + passRightPred)))
                [ZxpCell.zSpider 1 2],
              zxaMidLayer (ZxpCell.zSpider 1 2) passLeft (passRightPred + 2)] }
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs
                ((passLeft + (1 + passRightPred)) + 2)],
              zxaMidLayer (ZxpCell.zSpider 1 2) passLeft (passRightPred + 2)] } :=
        zxeStepConv topInputs []
          [zxaMidLayer (ZxpCell.zSpider 1 2) passLeft (passRightPred + 2)]
          (ZxeWindowMove.base
            (ZxrWindowMove.zFuse topInputs (passLeft + (1 + passRightPred)) 0 2))
          (ZxpLayersWF.nil _) rfl
          (by
            show ZxpLayersWF (zxpLayerCodArity (zxpCatCells
              (zxpWireCells (passLeft + (1 + passRightPred)))
              [ZxpCell.zSpider (1 + 0) 2]))
              [zxaMidLayer (ZxpCell.zSpider 1 2) passLeft (passRightPred + 2)]
            rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
            exact ZxpLayersWF.cons
              (zxaMidLayerDomArity (ZxpCell.zSpider 1 2) passLeft (passRightPred + 2))
              (ZxpLayersWF.nil _))
      -- D1 ~ D2 : ONE EXCHANGE merges the disjoint right-first fork pair
      have hDomL : zxpLayerDomArity
          (zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2])
          = passLeft + 1 := by
        rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
        rfl
      have hCodL : zxpLayerCodArity
          (zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2])
          = passLeft + 2 := by
        rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
        rfl
      have hDomR : zxpLayerDomArity
          (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.zSpider 1 2])
          = passRightPred + 1 := by
        rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
        rfl
      have hCodR : zxpLayerCodArity
          (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.zSpider 1 2])
          = passRightPred + 2 := by
        rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
        rfl
      have hIdxWinSrc : (passLeft + 1) + (passRightPred + 1)
          = (passLeft + (1 + passRightPred)) + 1 :=
        (Nat.add_assoc (passLeft + 1) passRightPred 1).symm.trans
          (congrArg (fun innerValue => innerValue + 1) hIdxSpare)
      have hExchange : ZxeConv
          { sourceArity := zxpLayerDomArity
                (zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2])
              + zxpLayerDomArity
                (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.zSpider 1 2])
            layers := [zxpCatCells (zxpWireCells (zxpLayerDomArity
                (zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2])))
                (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.zSpider 1 2]),
              zxpCatCells (zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2])
                (zxpWireCells (zxpLayerCodArity
                  (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.zSpider 1 2])))] }
          { sourceArity := zxpLayerDomArity
                (zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2])
              + zxpLayerDomArity
                (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.zSpider 1 2])
            layers := [zxpCatCells
                (zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2])
                (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.zSpider 1 2])] } :=
        zxeExchangeConv
          (zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2])
          (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.zSpider 1 2])
      rw [hDomL, hDomR, hCodR, hIdxWinSrc,
        zxaWiresWiresCat (passLeft + 1) passRightPred [ZxpCell.zSpider 1 2],
        hIdxSpare,
        zxaCatMidCells passLeft (ZxpCell.zSpider 1 2)
          (zxpWireCells (passRightPred + 2))] at hExchange
      have hExchangeLifted : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs
                ((passLeft + (1 + passRightPred)) + 1)],
              zxpCatCells (zxpWireCells (passLeft + (1 + passRightPred)))
                [ZxpCell.zSpider 1 2],
              zxaMidLayer (ZxpCell.zSpider 1 2) passLeft (passRightPred + 2)] }
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs
                ((passLeft + (1 + passRightPred)) + 1)],
              zxpCatCells
                (zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2])
                (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.zSpider 1 2])] } :=
        zxeLiftConv topInputs
          [[ZxpCell.zSpider topInputs ((passLeft + (1 + passRightPred)) + 1)]] []
          hExchange
          (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
      -- D2 ~ D3 : one splitLayer re-splits the fork pair LEFT-FIRST
      have hSplit : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs
                ((passLeft + (1 + passRightPred)) + 1)],
              zxpCatCells
                (zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2])
                (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.zSpider 1 2])] }
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs
                ((passLeft + (1 + passRightPred)) + 1)],
              zxaMidLayer (ZxpCell.zSpider 1 2) passLeft (passRightPred + 1),
              zxpCatCells (zxpWireCells (passLeft + (2 + passRightPred)))
                [ZxpCell.zSpider 1 2]] } := by
        have hRaw : ZxeConv
            { sourceArity := topInputs
              layers := [[ZxpCell.zSpider topInputs
                  ((passLeft + (1 + passRightPred)) + 1)],
                zxpCatCells
                  (zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2])
                  (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.zSpider 1 2])] }
            { sourceArity := topInputs
              layers := [[ZxpCell.zSpider topInputs
                  ((passLeft + (1 + passRightPred)) + 1)],
                zxpCatCells
                  (zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2])
                  (zxpWireCells (zxpLayerDomArity
                    (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.zSpider 1 2]))),
                zxpCatCells (zxpWireCells (zxpLayerCodArity
                    (zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2])))
                  (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.zSpider 1 2])] } :=
          zxeStepConv topInputs
            [[ZxpCell.zSpider topInputs ((passLeft + (1 + passRightPred)) + 1)]] []
            (ZxeWindowMove.base (ZxrWindowMove.seed (ZxpWindowMove.splitLayer
              (zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2])
              (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.zSpider 1 2]))))
            (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
            (by
              show zxpLayerCodArity
                  [ZxpCell.zSpider topInputs ((passLeft + (1 + passRightPred)) + 1)]
                = zxpLayerDomArity
                    (zxpCatCells (zxpWireCells passLeft) [ZxpCell.zSpider 1 2])
                  + zxpLayerDomArity
                    (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.zSpider 1 2])
              rw [hDomL, hDomR, hIdxWinSrc]
              rfl)
            (ZxpLayersWF.nil _)
        rw [hDomR, hCodL,
          zxaCatMidCells passLeft (ZxpCell.zSpider 1 2)
            (zxpWireCells (passRightPred + 1)),
          zxaWiresWiresCat (passLeft + 2) passRightPred [ZxpCell.zSpider 1 2],
          hIdxTail] at hRaw
        exact hRaw
      -- D3 ~ D4 : descend (the recursion at passRightPred + 1)
      have hInnerLifted : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs
                ((passLeft + (1 + passRightPred)) + 1)],
              zxaMidLayer (ZxpCell.zSpider 1 2) passLeft (passRightPred + 1),
              zxpCatCells (zxpWireCells (passLeft + (2 + passRightPred)))
                [ZxpCell.zSpider 1 2]] }
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs
                (passLeft + (2 + (passRightPred + 1)))],
              zxpCatCells (zxpWireCells (passLeft + (2 + passRightPred)))
                [ZxpCell.zSpider 1 2]] } := by
        have hRaw := zxeLiftConv topInputs []
          [zxpCatCells (zxpWireCells (passLeft + (2 + passRightPred)))
            [ZxpCell.zSpider 1 2]]
          (zxaMidForkFuseZ topInputs passLeft (passRightPred + 1))
          (ZxpLayersWF.nil _) rfl
          (by
            show ZxpLayersWF (zxpLayerCodArity
              (zxaMidLayer (ZxpCell.zSpider 1 2) passLeft (passRightPred + 1)))
              [zxpCatCells (zxpWireCells (passLeft + (2 + passRightPred)))
                [ZxpCell.zSpider 1 2]]
            rw [zxaMidLayerCodArity]
            refine ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _)
            rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
            rfl)
        exact hRaw
      -- D4 ~ D5 : the final corner fuse
      have hFinal : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs
                ((passLeft + (2 + passRightPred)) + 1)],
              zxpCatCells (zxpWireCells (passLeft + (2 + passRightPred)))
                [ZxpCell.zSpider 1 2]] }
          { sourceArity := topInputs
            layers := [[ZxpCell.zSpider topInputs
                ((passLeft + (2 + passRightPred)) + 2)]] } :=
        zxaMoveConv (ZxeWindowMove.base
          (ZxrWindowMove.zFuse topInputs (passLeft + (2 + passRightPred)) 0 2))
      exact ZxeConv.trans (ZxeConv.symm hFission)
        (ZxeConv.trans hExchangeLifted (ZxeConv.trans hSplit
          (ZxeConv.trans hInnerLifted hFinal)))

/-- The X colour mirror of the middle-pair fork fusion. -/
theorem zxaMidForkFuseX (topInputs passLeft : Nat) : (passRight : Nat) ->
    ZxeConv
      { sourceArity := topInputs
        layers := [[ZxpCell.xSpider topInputs (passLeft + (1 + passRight))],
          zxaMidLayer (ZxpCell.xSpider 1 2) passLeft passRight] }
      { sourceArity := topInputs
        layers := [[ZxpCell.xSpider topInputs (passLeft + (2 + passRight))]] }
  | 0 => zxaMoveConv (ZxeWindowMove.base (ZxrWindowMove.xFuse topInputs passLeft 0 2))
  | 1 => by
      have hFission : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs (passLeft + 1)],
              zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2],
              zxaMidLayer (ZxpCell.xSpider 1 2) passLeft 1] }
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs (passLeft + 2)],
              zxaMidLayer (ZxpCell.xSpider 1 2) passLeft 1] } :=
        zxeStepConv topInputs [] [zxaMidLayer (ZxpCell.xSpider 1 2) passLeft 1]
          (ZxeWindowMove.base (ZxrWindowMove.xFuse topInputs passLeft 0 2))
          (ZxpLayersWF.nil _) rfl
          (by
            show ZxpLayersWF (zxpLayerCodArity (zxpCatCells (zxpWireCells passLeft)
              [ZxpCell.xSpider (1 + 0) 2]))
              [zxaMidLayer (ZxpCell.xSpider 1 2) passLeft 1]
            rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
            exact ZxpLayersWF.cons
              (zxaMidLayerDomArity (ZxpCell.xSpider 1 2) passLeft 1)
              (ZxpLayersWF.nil _))
      have hCoassoc : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs (passLeft + 1)],
              zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2],
              zxaMidLayer (ZxpCell.xSpider 1 2) passLeft 1] }
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs (passLeft + 1)],
              zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2],
              zxpCatCells (zxpWireCells passLeft)
                (ZxpCell.wire :: [ZxpCell.xSpider 1 2])] } :=
        ZxeConv.step (ZxeStep.pad topInputs passLeft 0
          [[ZxpCell.xSpider topInputs (passLeft + 1)]] []
          (ZxeWindowMove.base (ZxrWindowMove.seed
            (ZxpWindowMove.row ZxpRowTag.xComonoidCoassoc)))
          (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _))
      rw [zxaWiresConsWire passLeft [ZxpCell.xSpider 1 2]] at hCoassoc
      have hFuseOne : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs (passLeft + 1)],
              zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2],
              zxpCatCells (zxpWireCells (passLeft + 1)) [ZxpCell.xSpider 1 2]] }
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs (passLeft + 2)],
              zxpCatCells (zxpWireCells (passLeft + 1)) [ZxpCell.xSpider 1 2]] } :=
        zxeStepConv topInputs []
          [zxpCatCells (zxpWireCells (passLeft + 1)) [ZxpCell.xSpider 1 2]]
          (ZxeWindowMove.base (ZxrWindowMove.xFuse topInputs passLeft 0 2))
          (ZxpLayersWF.nil _) rfl
          (by
            show ZxpLayersWF (zxpLayerCodArity (zxpCatCells (zxpWireCells passLeft)
              [ZxpCell.xSpider (1 + 0) 2]))
              [zxpCatCells (zxpWireCells (passLeft + 1)) [ZxpCell.xSpider 1 2]]
            rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
            refine ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _)
            rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
            rfl)
      have hFinal : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs (passLeft + 2)],
              zxpCatCells (zxpWireCells (passLeft + 1)) [ZxpCell.xSpider 1 2]] }
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs (passLeft + 3)]] } :=
        zxaMoveConv (ZxeWindowMove.base
          (ZxrWindowMove.xFuse topInputs (passLeft + 1) 0 2))
      exact ZxeConv.trans (ZxeConv.symm hFission)
        (ZxeConv.trans hCoassoc (ZxeConv.trans hFuseOne hFinal))
  | passRightPred + 2 => by
      have hIdxTail : (passLeft + 2) + passRightPred
          = passLeft + (2 + passRightPred) :=
        Nat.add_assoc passLeft 2 passRightPred
      have hIdxSpare : (passLeft + 1) + passRightPred
          = passLeft + (1 + passRightPred) :=
        Nat.add_assoc passLeft 1 passRightPred
      have hFission : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs
                ((passLeft + (1 + passRightPred)) + 1)],
              zxpCatCells (zxpWireCells (passLeft + (1 + passRightPred)))
                [ZxpCell.xSpider 1 2],
              zxaMidLayer (ZxpCell.xSpider 1 2) passLeft (passRightPred + 2)] }
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs
                ((passLeft + (1 + passRightPred)) + 2)],
              zxaMidLayer (ZxpCell.xSpider 1 2) passLeft (passRightPred + 2)] } :=
        zxeStepConv topInputs []
          [zxaMidLayer (ZxpCell.xSpider 1 2) passLeft (passRightPred + 2)]
          (ZxeWindowMove.base
            (ZxrWindowMove.xFuse topInputs (passLeft + (1 + passRightPred)) 0 2))
          (ZxpLayersWF.nil _) rfl
          (by
            show ZxpLayersWF (zxpLayerCodArity (zxpCatCells
              (zxpWireCells (passLeft + (1 + passRightPred)))
              [ZxpCell.xSpider (1 + 0) 2]))
              [zxaMidLayer (ZxpCell.xSpider 1 2) passLeft (passRightPred + 2)]
            rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
            exact ZxpLayersWF.cons
              (zxaMidLayerDomArity (ZxpCell.xSpider 1 2) passLeft (passRightPred + 2))
              (ZxpLayersWF.nil _))
      have hDomL : zxpLayerDomArity
          (zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2])
          = passLeft + 1 := by
        rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
        rfl
      have hCodL : zxpLayerCodArity
          (zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2])
          = passLeft + 2 := by
        rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
        rfl
      have hDomR : zxpLayerDomArity
          (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.xSpider 1 2])
          = passRightPred + 1 := by
        rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
        rfl
      have hCodR : zxpLayerCodArity
          (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.xSpider 1 2])
          = passRightPred + 2 := by
        rw [zxpCatCellsCodArity, zxpWireCellsCodArity]
        rfl
      have hIdxWinSrc : (passLeft + 1) + (passRightPred + 1)
          = (passLeft + (1 + passRightPred)) + 1 :=
        (Nat.add_assoc (passLeft + 1) passRightPred 1).symm.trans
          (congrArg (fun innerValue => innerValue + 1) hIdxSpare)
      have hExchange : ZxeConv
          { sourceArity := zxpLayerDomArity
                (zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2])
              + zxpLayerDomArity
                (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.xSpider 1 2])
            layers := [zxpCatCells (zxpWireCells (zxpLayerDomArity
                (zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2])))
                (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.xSpider 1 2]),
              zxpCatCells (zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2])
                (zxpWireCells (zxpLayerCodArity
                  (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.xSpider 1 2])))] }
          { sourceArity := zxpLayerDomArity
                (zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2])
              + zxpLayerDomArity
                (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.xSpider 1 2])
            layers := [zxpCatCells
                (zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2])
                (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.xSpider 1 2])] } :=
        zxeExchangeConv
          (zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2])
          (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.xSpider 1 2])
      rw [hDomL, hDomR, hCodR, hIdxWinSrc,
        zxaWiresWiresCat (passLeft + 1) passRightPred [ZxpCell.xSpider 1 2],
        hIdxSpare,
        zxaCatMidCells passLeft (ZxpCell.xSpider 1 2)
          (zxpWireCells (passRightPred + 2))] at hExchange
      have hExchangeLifted : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs
                ((passLeft + (1 + passRightPred)) + 1)],
              zxpCatCells (zxpWireCells (passLeft + (1 + passRightPred)))
                [ZxpCell.xSpider 1 2],
              zxaMidLayer (ZxpCell.xSpider 1 2) passLeft (passRightPred + 2)] }
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs
                ((passLeft + (1 + passRightPred)) + 1)],
              zxpCatCells
                (zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2])
                (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.xSpider 1 2])] } :=
        zxeLiftConv topInputs
          [[ZxpCell.xSpider topInputs ((passLeft + (1 + passRightPred)) + 1)]] []
          hExchange
          (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _)
      have hSplit : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs
                ((passLeft + (1 + passRightPred)) + 1)],
              zxpCatCells
                (zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2])
                (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.xSpider 1 2])] }
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs
                ((passLeft + (1 + passRightPred)) + 1)],
              zxaMidLayer (ZxpCell.xSpider 1 2) passLeft (passRightPred + 1),
              zxpCatCells (zxpWireCells (passLeft + (2 + passRightPred)))
                [ZxpCell.xSpider 1 2]] } := by
        have hRaw : ZxeConv
            { sourceArity := topInputs
              layers := [[ZxpCell.xSpider topInputs
                  ((passLeft + (1 + passRightPred)) + 1)],
                zxpCatCells
                  (zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2])
                  (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.xSpider 1 2])] }
            { sourceArity := topInputs
              layers := [[ZxpCell.xSpider topInputs
                  ((passLeft + (1 + passRightPred)) + 1)],
                zxpCatCells
                  (zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2])
                  (zxpWireCells (zxpLayerDomArity
                    (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.xSpider 1 2]))),
                zxpCatCells (zxpWireCells (zxpLayerCodArity
                    (zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2])))
                  (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.xSpider 1 2])] } :=
          zxeStepConv topInputs
            [[ZxpCell.xSpider topInputs ((passLeft + (1 + passRightPred)) + 1)]] []
            (ZxeWindowMove.base (ZxrWindowMove.seed (ZxpWindowMove.splitLayer
              (zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2])
              (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.xSpider 1 2]))))
            (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
            (by
              show zxpLayerCodArity
                  [ZxpCell.xSpider topInputs ((passLeft + (1 + passRightPred)) + 1)]
                = zxpLayerDomArity
                    (zxpCatCells (zxpWireCells passLeft) [ZxpCell.xSpider 1 2])
                  + zxpLayerDomArity
                    (zxpCatCells (zxpWireCells passRightPred) [ZxpCell.xSpider 1 2])
              rw [hDomL, hDomR, hIdxWinSrc]
              rfl)
            (ZxpLayersWF.nil _)
        rw [hDomR, hCodL,
          zxaCatMidCells passLeft (ZxpCell.xSpider 1 2)
            (zxpWireCells (passRightPred + 1)),
          zxaWiresWiresCat (passLeft + 2) passRightPred [ZxpCell.xSpider 1 2],
          hIdxTail] at hRaw
        exact hRaw
      have hInnerLifted : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs
                ((passLeft + (1 + passRightPred)) + 1)],
              zxaMidLayer (ZxpCell.xSpider 1 2) passLeft (passRightPred + 1),
              zxpCatCells (zxpWireCells (passLeft + (2 + passRightPred)))
                [ZxpCell.xSpider 1 2]] }
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs
                (passLeft + (2 + (passRightPred + 1)))],
              zxpCatCells (zxpWireCells (passLeft + (2 + passRightPred)))
                [ZxpCell.xSpider 1 2]] } := by
        have hRaw := zxeLiftConv topInputs []
          [zxpCatCells (zxpWireCells (passLeft + (2 + passRightPred)))
            [ZxpCell.xSpider 1 2]]
          (zxaMidForkFuseX topInputs passLeft (passRightPred + 1))
          (ZxpLayersWF.nil _) rfl
          (by
            show ZxpLayersWF (zxpLayerCodArity
              (zxaMidLayer (ZxpCell.xSpider 1 2) passLeft (passRightPred + 1)))
              [zxpCatCells (zxpWireCells (passLeft + (2 + passRightPred)))
                [ZxpCell.xSpider 1 2]]
            rw [zxaMidLayerCodArity]
            refine ZxpLayersWF.cons ?_ (ZxpLayersWF.nil _)
            rw [zxpCatCellsDomArity, zxpWireCellsDomArity]
            rfl)
        exact hRaw
      have hFinal : ZxeConv
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs
                ((passLeft + (2 + passRightPred)) + 1)],
              zxpCatCells (zxpWireCells (passLeft + (2 + passRightPred)))
                [ZxpCell.xSpider 1 2]] }
          { sourceArity := topInputs
            layers := [[ZxpCell.xSpider topInputs
                ((passLeft + (2 + passRightPred)) + 2)]] } :=
        zxaMoveConv (ZxeWindowMove.base
          (ZxrWindowMove.xFuse topInputs (passLeft + (2 + passRightPred)) 0 2))
      exact ZxeConv.trans (ZxeConv.symm hFission)
        (ZxeConv.trans hExchangeLifted (ZxeConv.trans hSplit
          (ZxeConv.trans hInnerLifted hFinal)))

/-! ## Stage 3 — SINGLE-CROSSING ABSORPTION at any adjacent leg pair

A crossing whose BOTH legs are legs of one spider dies into it at every position:
middle-pair fission isolates the leg pair into a binary spider, the
(co)commutativity row kills the crossing, middle-pair fusion reabsorbs. -/

theorem zxaCrossingAbsorbInputZ (passLeft passRight botOutputs : Nat) :
    ZxeConv
      { sourceArity := passLeft + (2 + passRight)
        layers := [zxaMidLayer ZxpCell.crossing passLeft passRight,
          [ZxpCell.zSpider (passLeft + (2 + passRight)) botOutputs]] }
      { sourceArity := passLeft + (2 + passRight)
        layers := [[ZxpCell.zSpider (passLeft + (2 + passRight)) botOutputs]] } := by
  have hDomSwap : zxpLayerDomArity (zxaMidLayer ZxpCell.crossing passLeft passRight)
      = passLeft + (2 + passRight) :=
    zxaMidLayerDomArity ZxpCell.crossing passLeft passRight
  have hCodSwap : zxpLayerCodArity (zxaMidLayer ZxpCell.crossing passLeft passRight)
      = passLeft + (2 + passRight) :=
    zxaMidLayerCodArity ZxpCell.crossing passLeft passRight
  have hFission := zxaMidMergeFuseZ botOutputs passRight passLeft
  have hFissionLifted : ZxeConv
      { sourceArity := passLeft + (2 + passRight)
        layers := [zxaMidLayer ZxpCell.crossing passLeft passRight,
          [ZxpCell.zSpider (passLeft + (2 + passRight)) botOutputs]] }
      { sourceArity := passLeft + (2 + passRight)
        layers := [zxaMidLayer ZxpCell.crossing passLeft passRight,
          zxaMidLayer (ZxpCell.zSpider 2 1) passLeft passRight,
          [ZxpCell.zSpider (passLeft + (1 + passRight)) botOutputs]] } :=
    zxeLiftConv (passLeft + (2 + passRight))
      [zxaMidLayer ZxpCell.crossing passLeft passRight] []
      (ZxeConv.symm hFission)
      (ZxpLayersWF.cons hDomSwap (ZxpLayersWF.nil _))
      hCodSwap (ZxpLayersWF.nil _)
  have hComm : ZxeConv
      { sourceArity := passLeft + (2 + passRight)
        layers := [zxaMidLayer ZxpCell.crossing passLeft passRight,
          zxaMidLayer (ZxpCell.zSpider 2 1) passLeft passRight,
          [ZxpCell.zSpider (passLeft + (1 + passRight)) botOutputs]] }
      { sourceArity := passLeft + (2 + passRight)
        layers := [zxaMidLayer (ZxpCell.zSpider 2 1) passLeft passRight,
          [ZxpCell.zSpider (passLeft + (1 + passRight)) botOutputs]] } :=
    ZxeConv.step (ZxeStep.pad (passLeft + (2 + passRight)) passLeft passRight []
      [[ZxpCell.zSpider (passLeft + (1 + passRight)) botOutputs]]
      (ZxeWindowMove.base (ZxrWindowMove.seed (ZxpWindowMove.row ZxpRowTag.zMonoidComm)))
      (ZxpLayersWF.nil _) rfl
      (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)))
  exact ZxeConv.trans hFissionLifted (ZxeConv.trans hComm hFission)

/-- The X colour mirror of the input-side crossing absorption. -/
theorem zxaCrossingAbsorbInputX (passLeft passRight botOutputs : Nat) :
    ZxeConv
      { sourceArity := passLeft + (2 + passRight)
        layers := [zxaMidLayer ZxpCell.crossing passLeft passRight,
          [ZxpCell.xSpider (passLeft + (2 + passRight)) botOutputs]] }
      { sourceArity := passLeft + (2 + passRight)
        layers := [[ZxpCell.xSpider (passLeft + (2 + passRight)) botOutputs]] } := by
  have hDomSwap : zxpLayerDomArity (zxaMidLayer ZxpCell.crossing passLeft passRight)
      = passLeft + (2 + passRight) :=
    zxaMidLayerDomArity ZxpCell.crossing passLeft passRight
  have hCodSwap : zxpLayerCodArity (zxaMidLayer ZxpCell.crossing passLeft passRight)
      = passLeft + (2 + passRight) :=
    zxaMidLayerCodArity ZxpCell.crossing passLeft passRight
  have hFission := zxaMidMergeFuseX botOutputs passRight passLeft
  have hFissionLifted : ZxeConv
      { sourceArity := passLeft + (2 + passRight)
        layers := [zxaMidLayer ZxpCell.crossing passLeft passRight,
          [ZxpCell.xSpider (passLeft + (2 + passRight)) botOutputs]] }
      { sourceArity := passLeft + (2 + passRight)
        layers := [zxaMidLayer ZxpCell.crossing passLeft passRight,
          zxaMidLayer (ZxpCell.xSpider 2 1) passLeft passRight,
          [ZxpCell.xSpider (passLeft + (1 + passRight)) botOutputs]] } :=
    zxeLiftConv (passLeft + (2 + passRight))
      [zxaMidLayer ZxpCell.crossing passLeft passRight] []
      (ZxeConv.symm hFission)
      (ZxpLayersWF.cons hDomSwap (ZxpLayersWF.nil _))
      hCodSwap (ZxpLayersWF.nil _)
  have hComm : ZxeConv
      { sourceArity := passLeft + (2 + passRight)
        layers := [zxaMidLayer ZxpCell.crossing passLeft passRight,
          zxaMidLayer (ZxpCell.xSpider 2 1) passLeft passRight,
          [ZxpCell.xSpider (passLeft + (1 + passRight)) botOutputs]] }
      { sourceArity := passLeft + (2 + passRight)
        layers := [zxaMidLayer (ZxpCell.xSpider 2 1) passLeft passRight,
          [ZxpCell.xSpider (passLeft + (1 + passRight)) botOutputs]] } :=
    ZxeConv.step (ZxeStep.pad (passLeft + (2 + passRight)) passLeft passRight []
      [[ZxpCell.xSpider (passLeft + (1 + passRight)) botOutputs]]
      (ZxeWindowMove.base (ZxrWindowMove.seed (ZxpWindowMove.row ZxpRowTag.xMonoidComm)))
      (ZxpLayersWF.nil _) rfl
      (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)))
  exact ZxeConv.trans hFissionLifted (ZxeConv.trans hComm hFission)

theorem zxaCrossingAbsorbOutputZ (topInputs passLeft passRight : Nat) :
    ZxeConv
      { sourceArity := topInputs
        layers := [[ZxpCell.zSpider topInputs (passLeft + (2 + passRight))],
          zxaMidLayer ZxpCell.crossing passLeft passRight] }
      { sourceArity := topInputs
        layers := [[ZxpCell.zSpider topInputs (passLeft + (2 + passRight))]] } := by
  have hDomSwap : zxpLayerDomArity (zxaMidLayer ZxpCell.crossing passLeft passRight)
      = passLeft + (2 + passRight) :=
    zxaMidLayerDomArity ZxpCell.crossing passLeft passRight
  have hFission := zxaMidForkFuseZ topInputs passLeft passRight
  have hFissionLifted : ZxeConv
      { sourceArity := topInputs
        layers := [[ZxpCell.zSpider topInputs (passLeft + (2 + passRight))],
          zxaMidLayer ZxpCell.crossing passLeft passRight] }
      { sourceArity := topInputs
        layers := [[ZxpCell.zSpider topInputs (passLeft + (1 + passRight))],
          zxaMidLayer (ZxpCell.zSpider 1 2) passLeft passRight,
          zxaMidLayer ZxpCell.crossing passLeft passRight] } :=
    zxeLiftConv topInputs [] [zxaMidLayer ZxpCell.crossing passLeft passRight]
      (ZxeConv.symm hFission)
      (ZxpLayersWF.nil _) rfl
      (ZxpLayersWF.cons hDomSwap (ZxpLayersWF.nil _))
  have hCocomm : ZxeConv
      { sourceArity := topInputs
        layers := [[ZxpCell.zSpider topInputs (passLeft + (1 + passRight))],
          zxaMidLayer (ZxpCell.zSpider 1 2) passLeft passRight,
          zxaMidLayer ZxpCell.crossing passLeft passRight] }
      { sourceArity := topInputs
        layers := [[ZxpCell.zSpider topInputs (passLeft + (1 + passRight))],
          zxaMidLayer (ZxpCell.zSpider 1 2) passLeft passRight] } :=
    ZxeConv.step (ZxeStep.pad topInputs passLeft passRight
      [[ZxpCell.zSpider topInputs (passLeft + (1 + passRight))]] []
      (ZxeWindowMove.base (ZxrWindowMove.seed
        (ZxpWindowMove.row ZxpRowTag.zComonoidCocomm)))
      (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _))
  exact ZxeConv.trans hFissionLifted (ZxeConv.trans hCocomm hFission)

/-- The X colour mirror of the output-side crossing absorption. -/
theorem zxaCrossingAbsorbOutputX (topInputs passLeft passRight : Nat) :
    ZxeConv
      { sourceArity := topInputs
        layers := [[ZxpCell.xSpider topInputs (passLeft + (2 + passRight))],
          zxaMidLayer ZxpCell.crossing passLeft passRight] }
      { sourceArity := topInputs
        layers := [[ZxpCell.xSpider topInputs (passLeft + (2 + passRight))]] } := by
  have hDomSwap : zxpLayerDomArity (zxaMidLayer ZxpCell.crossing passLeft passRight)
      = passLeft + (2 + passRight) :=
    zxaMidLayerDomArity ZxpCell.crossing passLeft passRight
  have hFission := zxaMidForkFuseX topInputs passLeft passRight
  have hFissionLifted : ZxeConv
      { sourceArity := topInputs
        layers := [[ZxpCell.xSpider topInputs (passLeft + (2 + passRight))],
          zxaMidLayer ZxpCell.crossing passLeft passRight] }
      { sourceArity := topInputs
        layers := [[ZxpCell.xSpider topInputs (passLeft + (1 + passRight))],
          zxaMidLayer (ZxpCell.xSpider 1 2) passLeft passRight,
          zxaMidLayer ZxpCell.crossing passLeft passRight] } :=
    zxeLiftConv topInputs [] [zxaMidLayer ZxpCell.crossing passLeft passRight]
      (ZxeConv.symm hFission)
      (ZxpLayersWF.nil _) rfl
      (ZxpLayersWF.cons hDomSwap (ZxpLayersWF.nil _))
  have hCocomm : ZxeConv
      { sourceArity := topInputs
        layers := [[ZxpCell.xSpider topInputs (passLeft + (1 + passRight))],
          zxaMidLayer (ZxpCell.xSpider 1 2) passLeft passRight,
          zxaMidLayer ZxpCell.crossing passLeft passRight] }
      { sourceArity := topInputs
        layers := [[ZxpCell.xSpider topInputs (passLeft + (1 + passRight))],
          zxaMidLayer (ZxpCell.xSpider 1 2) passLeft passRight] } :=
    ZxeConv.step (ZxeStep.pad topInputs passLeft passRight
      [[ZxpCell.xSpider topInputs (passLeft + (1 + passRight))]] []
      (ZxeWindowMove.base (ZxrWindowMove.seed
        (ZxpWindowMove.row ZxpRowTag.xComonoidCocomm)))
      (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)) rfl (ZxpLayersWF.nil _))
  exact ZxeConv.trans hFissionLifted (ZxeConv.trans hCocomm hFission)

/-! ## Stage 4 — ARBITRARY CROSSING WALKS on the legs of one spider -/

/-- A crossing walk over `strandCount` strands: a list of layers, each one adjacent
crossing at some position (`wire^p, crossing, wire^q` with `p + 2 + q` fitting the
strand count). -/
inductive ZxaSwapWalk (strandCount : Nat) : List (List ZxpCell) -> Prop where
  | nil : ZxaSwapWalk strandCount []
  | cons (passLeft passRight : Nat) {restLayers : List (List ZxpCell)}
      (hFit : passLeft + (2 + passRight) = strandCount)
      (hRest : ZxaSwapWalk strandCount restLayers) :
      ZxaSwapWalk strandCount
        (zxaMidLayer ZxpCell.crossing passLeft passRight :: restLayers)

/-- Walk layers are well-formed at the strand count (each layer is n -> n). -/
theorem zxaSwapWalkWF {strandCount : Nat} : {walkLayers : List (List ZxpCell)} ->
    ZxaSwapWalk strandCount walkLayers -> ZxpLayersWF strandCount walkLayers := by
  intro walkLayers hWalk
  induction hWalk with
  | nil => exact ZxpLayersWF.nil _
  | cons passLeft passRight hFit _hRest innerIH =>
      refine ZxpLayersWF.cons ?_ ?_
      · rw [show zxpLayerDomArity (zxaMidLayer ZxpCell.crossing passLeft passRight)
            = passLeft + (2 + passRight)
          from zxaMidLayerDomArity ZxpCell.crossing passLeft passRight]
        exact hFit
      · rw [show zxpLayerCodArity (zxaMidLayer ZxpCell.crossing passLeft passRight)
            = passLeft + (2 + passRight)
          from zxaMidLayerCodArity ZxpCell.crossing passLeft passRight, hFit]
        exact innerIH

/-- THE OUTPUT-LEG WALK ABSORPTION (Z): any crossing walk on the output legs of one
Z-spider absorbs into it — the legs route to arbitrary relative positions. -/
theorem zxaWalkAbsorbOutputZ (topInputs strandCount : Nat)
    {walkLayers : List (List ZxpCell)} (hWalk : ZxaSwapWalk strandCount walkLayers) :
    ZxeConv
      { sourceArity := topInputs
        layers := [ZxpCell.zSpider topInputs strandCount] :: walkLayers }
      { sourceArity := topInputs
        layers := [[ZxpCell.zSpider topInputs strandCount]] } := by
  induction hWalk with
  | nil => exact ZxeConv.refl _ (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  | cons passLeft passRight hFit hRest innerIH =>
      rename_i restLayers
      subst hFit
      have hSwapLifted : ZxeConv
          { sourceArity := topInputs
            layers := [ZxpCell.zSpider topInputs (passLeft + (2 + passRight))]
              :: zxaMidLayer ZxpCell.crossing passLeft passRight :: restLayers }
          { sourceArity := topInputs
            layers := [ZxpCell.zSpider topInputs (passLeft + (2 + passRight))]
              :: restLayers } :=
        zxeLiftConv topInputs [] restLayers
          (zxaCrossingAbsorbOutputZ topInputs passLeft passRight)
          (ZxpLayersWF.nil _) rfl
          (by
            show ZxpLayersWF
              (zxpLayerCodArity (zxaMidLayer ZxpCell.crossing passLeft passRight))
              restLayers
            rw [show zxpLayerCodArity (zxaMidLayer ZxpCell.crossing passLeft passRight)
                = passLeft + (2 + passRight)
              from zxaMidLayerCodArity ZxpCell.crossing passLeft passRight]
            exact zxaSwapWalkWF hRest)
      exact ZxeConv.trans hSwapLifted innerIH

/-- THE OUTPUT-LEG WALK ABSORPTION (X), the colour mirror. -/
theorem zxaWalkAbsorbOutputX (topInputs strandCount : Nat)
    {walkLayers : List (List ZxpCell)} (hWalk : ZxaSwapWalk strandCount walkLayers) :
    ZxeConv
      { sourceArity := topInputs
        layers := [ZxpCell.xSpider topInputs strandCount] :: walkLayers }
      { sourceArity := topInputs
        layers := [[ZxpCell.xSpider topInputs strandCount]] } := by
  induction hWalk with
  | nil => exact ZxeConv.refl _ (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  | cons passLeft passRight hFit hRest innerIH =>
      rename_i restLayers
      subst hFit
      have hSwapLifted : ZxeConv
          { sourceArity := topInputs
            layers := [ZxpCell.xSpider topInputs (passLeft + (2 + passRight))]
              :: zxaMidLayer ZxpCell.crossing passLeft passRight :: restLayers }
          { sourceArity := topInputs
            layers := [ZxpCell.xSpider topInputs (passLeft + (2 + passRight))]
              :: restLayers } :=
        zxeLiftConv topInputs [] restLayers
          (zxaCrossingAbsorbOutputX topInputs passLeft passRight)
          (ZxpLayersWF.nil _) rfl
          (by
            show ZxpLayersWF
              (zxpLayerCodArity (zxaMidLayer ZxpCell.crossing passLeft passRight))
              restLayers
            rw [show zxpLayerCodArity (zxaMidLayer ZxpCell.crossing passLeft passRight)
                = passLeft + (2 + passRight)
              from zxaMidLayerCodArity ZxpCell.crossing passLeft passRight]
            exact zxaSwapWalkWF hRest)
      exact ZxeConv.trans hSwapLifted innerIH

/-- THE INPUT-LEG WALK ABSORPTION (Z): any crossing walk feeding the input legs of
one Z-spider absorbs into it. -/
theorem zxaWalkAbsorbInputZ (strandCount botOutputs : Nat)
    {walkLayers : List (List ZxpCell)} (hWalk : ZxaSwapWalk strandCount walkLayers) :
    ZxeConv
      { sourceArity := strandCount
        layers := zxpCatLayers walkLayers
          [[ZxpCell.zSpider strandCount botOutputs]] }
      { sourceArity := strandCount
        layers := [[ZxpCell.zSpider strandCount botOutputs]] } := by
  induction hWalk with
  | nil => exact ZxeConv.refl _ (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  | cons passLeft passRight hFit hRest innerIH =>
      rename_i restLayers
      subst hFit
      have hCodSwap : zxpLayerCodArity (zxaMidLayer ZxpCell.crossing passLeft passRight)
          = passLeft + (2 + passRight) :=
        zxaMidLayerCodArity ZxpCell.crossing passLeft passRight
      have hDomSwap : zxpLayerDomArity (zxaMidLayer ZxpCell.crossing passLeft passRight)
          = passLeft + (2 + passRight) :=
        zxaMidLayerDomArity ZxpCell.crossing passLeft passRight
      have hLifted : ZxeConv
          { sourceArity := passLeft + (2 + passRight)
            layers := zxaMidLayer ZxpCell.crossing passLeft passRight
              :: zxpCatLayers restLayers
                [[ZxpCell.zSpider (passLeft + (2 + passRight)) botOutputs]] }
          { sourceArity := passLeft + (2 + passRight)
            layers := [zxaMidLayer ZxpCell.crossing passLeft passRight,
              [ZxpCell.zSpider (passLeft + (2 + passRight)) botOutputs]] } := by
        have hRaw := zxeLiftConv (passLeft + (2 + passRight))
          [zxaMidLayer ZxpCell.crossing passLeft passRight] [] innerIH
          (ZxpLayersWF.cons hDomSwap (ZxpLayersWF.nil _))
          hCodSwap (ZxpLayersWF.nil _)
        rw [zxpCatLayersNilRight] at hRaw
        exact hRaw
      exact ZxeConv.trans hLifted
        (zxaCrossingAbsorbInputZ passLeft passRight botOutputs)

/-- THE INPUT-LEG WALK ABSORPTION (X), the colour mirror. -/
theorem zxaWalkAbsorbInputX (strandCount botOutputs : Nat)
    {walkLayers : List (List ZxpCell)} (hWalk : ZxaSwapWalk strandCount walkLayers) :
    ZxeConv
      { sourceArity := strandCount
        layers := zxpCatLayers walkLayers
          [[ZxpCell.xSpider strandCount botOutputs]] }
      { sourceArity := strandCount
        layers := [[ZxpCell.xSpider strandCount botOutputs]] } := by
  induction hWalk with
  | nil => exact ZxeConv.refl _ (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  | cons passLeft passRight hFit hRest innerIH =>
      rename_i restLayers
      subst hFit
      have hCodSwap : zxpLayerCodArity (zxaMidLayer ZxpCell.crossing passLeft passRight)
          = passLeft + (2 + passRight) :=
        zxaMidLayerCodArity ZxpCell.crossing passLeft passRight
      have hDomSwap : zxpLayerDomArity (zxaMidLayer ZxpCell.crossing passLeft passRight)
          = passLeft + (2 + passRight) :=
        zxaMidLayerDomArity ZxpCell.crossing passLeft passRight
      have hLifted : ZxeConv
          { sourceArity := passLeft + (2 + passRight)
            layers := zxaMidLayer ZxpCell.crossing passLeft passRight
              :: zxpCatLayers restLayers
                [[ZxpCell.xSpider (passLeft + (2 + passRight)) botOutputs]] }
          { sourceArity := passLeft + (2 + passRight)
            layers := [zxaMidLayer ZxpCell.crossing passLeft passRight,
              [ZxpCell.xSpider (passLeft + (2 + passRight)) botOutputs]] } := by
        have hRaw := zxeLiftConv (passLeft + (2 + passRight))
          [zxaMidLayer ZxpCell.crossing passLeft passRight] [] innerIH
          (ZxpLayersWF.cons hDomSwap (ZxpLayersWF.nil _))
          hCodSwap (ZxpLayersWF.nil _)
        rw [zxpCatLayersNilRight] at hRaw
        exact hRaw
      exact ZxeConv.trans hLifted
        (zxaCrossingAbsorbInputX passLeft passRight botOutputs)

/-! ## Stage 5 — engine fires + the negative control -/

/-- FIRE 1: a fresh two-step walk on the output legs of `zSpider 1 3` absorbs —
the legs are routed through positions (0 1) then (1 2) and nothing changes. -/
theorem zxaWalkOutputZFire :
    ZxeConv
      { sourceArity := 1
        layers := [[ZxpCell.zSpider 1 3], [ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 1, layers := [[ZxpCell.zSpider 1 3]] } :=
  zxaWalkAbsorbOutputZ 1 3
    (ZxaSwapWalk.cons 0 1 rfl (ZxaSwapWalk.cons 1 0 rfl ZxaSwapWalk.nil))

/-- FIRE 2: a fresh mid-position crossing feeding the inputs of `xSpider 4 1`
absorbs. -/
theorem zxaWalkInputXFire :
    ZxeConv
      { sourceArity := 4
        layers := [[ZxpCell.wire, ZxpCell.crossing, ZxpCell.wire],
          [ZxpCell.xSpider 4 1]] }
      { sourceArity := 4, layers := [[ZxpCell.xSpider 4 1]] } :=
  zxaWalkAbsorbInputX 4 1 (ZxaSwapWalk.cons 1 1 rfl ZxaSwapWalk.nil)

/-- NEGATIVE CONTROL (kernel): a crossing touching a NON-leg strand is NOT
absorbable — it changes the relation (the two legs here are one fork output and
one passive strand). -/
theorem zxaPassiveCrossingSpanDistinct :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 2
          layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire],
            [ZxpCell.wire, ZxpCell.crossing]] })
      (zxpDiagramDenote
        { sourceArity := 2
          layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire]] }) = false := rfl

/-- NEGATIVE CONTROL, refutation form: the passive-strand crossing pair is not
`ZxeConv`-convertible (via the refutation bridge). -/
theorem zxaPassiveCrossingNotConv :
    Not (ZxeConv
      { sourceArity := 2
        layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire],
          [ZxpCell.wire, ZxpCell.crossing]] }
      { sourceArity := 2, layers := [[ZxpCell.zSpider 1 2, ZxpCell.wire]] }) :=
  fun hConv =>
    Bool.noConfusion ((zxeConvSpanEqB hConv).symm.trans zxaPassiveCrossingSpanDistinct)

/-! ## Stage 6 — THE WIRING WALL: the missing slide schema, named owner-false

The commissioned passive-strand conjugation is blocked at the ONE-LEGGED CROSSING
configuration.  Its two minimal generating instances are minted as owner-false
statements, each with a kernel span pin proving semantic soundness — candidate
NEW MOVES in the r30 exchange style (span-sound + invisible to the collapsed
per-cell weight family), NOT refutation targets. -/

/-- THE COUNIT SLIDE (minimal one-legged instance, Z form; the X form and the
unit/state mirrors are the evident variants): a crossing dies against a discard
on its first output.  NOT derivable by any route found from
{rows, splitLayer, exchange, fusion}: the (co)comm rows need BOTH crossing legs
on one spider, `bialgSquare` needs the four-spider sandwich whose conjuring needs
this very slide, and splitLayer/exchange never re-order strands. -/
def zxaCounitSlideStatement : Prop :=
  ZxeConv
    { sourceArity := 2
      layers := [[ZxpCell.crossing], [ZxpCell.zSpider 1 0, ZxpCell.wire]] }
    { sourceArity := 2, layers := [[ZxpCell.wire, ZxpCell.zSpider 1 0]] }

/-- SIGMA INVOLUTION (the other minimal wiring instance): two stacked crossings
are the identity.  Same blocking configuration: no committed move consumes a
crossing whose legs do not both enter one spider. -/
def zxaSigmaInvolutionStatement : Prop :=
  ZxeConv
    { sourceArity := 2, layers := [[ZxpCell.crossing], [ZxpCell.crossing]] }
    { sourceArity := 2, layers := [[ZxpCell.wire, ZxpCell.wire]] }

/-- Kernel span pin: the counit slide is semantically SOUND (both sides denote the
same relation) — a candidate new move, not a refutation target. -/
theorem zxaCounitSlideSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 2
          layers := [[ZxpCell.crossing], [ZxpCell.zSpider 1 0, ZxpCell.wire]] })
      (zxpDiagramDenote
        { sourceArity := 2
          layers := [[ZxpCell.wire, ZxpCell.zSpider 1 0]] }) = true := rfl

/-- Kernel span pin: sigma involution is semantically SOUND. -/
theorem zxaSigmaInvolutionSpanPin :
    zxpSpanEqB
      (zxpDiagramDenote
        { sourceArity := 2
          layers := [[ZxpCell.crossing], [ZxpCell.crossing]] })
      (zxpDiagramDenote
        { sourceArity := 2
          layers := [[ZxpCell.wire, ZxpCell.wire]] }) = true := rfl

/-- OWNER MARKER (FALSE): the passive-strand crossing slide family
(`zxaCounitSlideStatement`, `zxaSigmaInvolutionStatement`, and with them
Yang-Baxter and full sigma-naturality) is NOT proven over `ZxeConv` — and not
refuted: both instances are span-sound (pins above) and the whole per-cell
counting family is collapsed (`zxeBalancedWeightCollapse`), so no counting
separator can exist.  Three attack shapes were burned (see the file header);
every route lands on the one-legged crossing.  The honest next move is an
r30-style NEW MOVE family (sigma naturality as gated window moves with
structural soundness) — after which the within-spider engine above plus the
absorption induction below become the route to completeness. -/
def zxaCrossingSlideIsProven : Bool := false

/-! ## Stage 7 — (B) absorption partials + the owner-false statement -/

/-- THE ABSORPTION STATEMENT (Kissinger Lemma 3.2/3.3 over the census normal
form): every well-formed diagram `ZxeConv`-converts to `zxnNormalForm` of its own
denotation.  OWNER FALSE — NOT PROVEN.  Blocking configuration: every normal form
with a nonempty comb (already the identity-relation NF at boundary >= 1) embeds
carrier crossings whose legs belong to a Z-tree AND an X-chain — one-legged
configurations, walled above.  What lands below: the boundary-0 empty diagram and
a zero-generator two-cell instance.  NOTE the residual beyond this statement for
completeness: span-equal generator LISTS must also produce convertible normal
forms (`zxnNormalForm` is generator-list-indexed, not subspace-indexed). -/
def zxaAbsorptionStatement : Prop :=
  (diagram : ZxpDiagram) -> ZxpDiagramWF diagram ->
    ZxeConv diagram
      (zxnNormalForm diagram.sourceArity (zxpDiagramCodArity diagram)
        (zxpDiagramDenote diagram))

/-- OWNER MARKER (FALSE): the absorption induction is not proven. -/
def zxaAbsorptionIsProven : Bool := false

/-- (B) BASE CASE: the empty diagram at boundary 0 converts to the normal form of
its own denotation (through the bialgebra bone, with empty-wire-layer insertions). -/
theorem zxaEmptyDiagramAbsorbed :
    ZxeConv { sourceArity := 0, layers := [] }
      (zxnNormalForm 0 0
        (zxpDiagramDenote { sourceArity := 0, layers := [] })) := by
  have hBoneBack : ZxeConv { sourceArity := 0, layers := [] }
      { sourceArity := 0
        layers := [[ZxpCell.xSpider 0 1], [ZxpCell.zSpider 1 0]] } :=
    ZxeConv.symm (zxaMoveConv (ZxeWindowMove.base (ZxrWindowMove.seed
      (ZxpWindowMove.row ZxpRowTag.bialgBone))))
  have hStripOne : ZxeConv
      { sourceArity := 0
        layers := [[ZxpCell.xSpider 0 1], [ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers := [[], [ZxpCell.xSpider 0 1], [ZxpCell.zSpider 1 0]] } :=
    zxeLiftConv 0 [] [[ZxpCell.zSpider 1 0]]
      (ZxeConv.symm (zxeStripLeadingWireLayer [ZxpCell.xSpider 0 1]))
      (ZxpLayersWF.nil _) rfl
      (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _))
  have hStripTwo : ZxeConv
      { sourceArity := 0
        layers := [[], [ZxpCell.xSpider 0 1], [ZxpCell.zSpider 1 0]] }
      { sourceArity := 0
        layers := [[], [], [ZxpCell.xSpider 0 1], [ZxpCell.zSpider 1 0]] } :=
    zxeLiftConv 0 [] [[ZxpCell.xSpider 0 1], [ZxpCell.zSpider 1 0]]
      (ZxeConv.symm (zxeStripLeadingWireLayer []))
      (ZxpLayersWF.nil _) rfl
      (ZxpLayersWF.cons rfl (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)))
  have hBoneFwd : ZxeConv
      { sourceArity := 0
        layers := [[], [], [ZxpCell.xSpider 0 1], [ZxpCell.zSpider 1 0]] }
      { sourceArity := 0, layers := [[], []] } :=
    zxeStepConv 0 [[], []] []
      (ZxeWindowMove.base (ZxrWindowMove.seed (ZxpWindowMove.row ZxpRowTag.bialgBone)))
      (ZxpLayersWF.cons rfl (ZxpLayersWF.cons rfl (ZxpLayersWF.nil _)))
      rfl (ZxpLayersWF.nil _)
  exact ZxeConv.trans hBoneBack
    (ZxeConv.trans hStripOne (ZxeConv.trans hStripTwo hBoneFwd))

/-- (B) ZERO-GENERATOR FIRE: a two-cell kill-create diagram converts to
`zxnNormalForm` of its own denotation (which computes to the empty generator
list) — one splitLayer plus one exchange land exactly on `init ; kill`. -/
theorem zxaKillCreateAbsorbedFire :
    ZxeConv
      { sourceArity := 1
        layers := [[ZxpCell.xSpider 1 0], [ZxpCell.xSpider 0 1]] }
      (zxnNormalForm 1 1 (zxpDiagramDenote
        { sourceArity := 1
          layers := [[ZxpCell.xSpider 1 0], [ZxpCell.xSpider 0 1]] })) := by
  have hMerge : ZxeConv
      { sourceArity := 1
        layers := [[ZxpCell.xSpider 1 0, ZxpCell.xSpider 0 1]] }
      { sourceArity := 1
        layers := [[ZxpCell.xSpider 1 0], [ZxpCell.xSpider 0 1]] } :=
    zxaMoveConv (ZxeWindowMove.base (ZxrWindowMove.seed
      (ZxpWindowMove.splitLayer [ZxpCell.xSpider 1 0] [ZxpCell.xSpider 0 1])))
  have hExchangeBack : ZxeConv
      { sourceArity := 1
        layers := [[ZxpCell.wire, ZxpCell.xSpider 0 1],
          [ZxpCell.xSpider 1 0, ZxpCell.wire]] }
      { sourceArity := 1
        layers := [[ZxpCell.xSpider 1 0, ZxpCell.xSpider 0 1]] } :=
    zxeExchangeConv [ZxpCell.xSpider 1 0] [ZxpCell.xSpider 0 1]
  exact ZxeConv.symm (ZxeConv.trans hExchangeBack hMerge)

/-! ## Stage 8 — the honest marker ledger -/

/-- MARKER: the within-spider leg-permutation engine is DECIDED over `ZxeConv` —
middle-pair fission/fusion at every position both sides both colours
(`zxaMidMergeFuseZ/X`, `zxaMidForkFuseZ/X`), single-crossing absorption at every
adjacent leg pair both orientations both colours (`zxaCrossingAbsorb{Input,Output}{Z,X}`),
and arbitrary crossing walks (`zxaWalkAbsorb{Input,Output}{Z,X}`), with two fresh
fires and a kernel negative control.  The commissioned PASSIVE-STRAND half is
walled at `zxaCrossingSlideIsProven := false`. -/
def zxaHasLegPermutationEngine : Bool := true

/-- MARKER (FALSE): THE FULL PHASE-FREE DECISION did not flip this round.
`zxeCompletenessStatement` stays owner-false in its home file (byte-intact); the
(C) flip needs (i) the wiring schema (`zxaCrossingSlideIsProven`), then (ii) the
absorption induction (`zxaAbsorptionIsProven`) plus the generator-list transport
noted on `zxaAbsorptionStatement`.  No inhabitant of `zxeCompletenessStatement`
and no unconditional decision instance exist in this development. -/
def zxaHasFullDecision : Bool := false

end FX1Poly.Polygraph.Omega.ZXPhaseFree
