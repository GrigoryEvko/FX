import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedRelationFamily
import FX1Poly.Polygraph.TwoCategory.Amalgam.RealCoprojection

/-! # Polygraph/TwoCategory/Amalgam/MonadReseat — the FIXED-pair reseat of the walking-monad decider onto the
reconstructed signature (MODE-ADMIT r3)

`DeciderReseat.lean` machine-documented the JAM: the shipped real decider `monadSaturatedTwoCellDecision` lives
over the BESPOKE `monadModeSignature` (carrier `MonadMode` / `MonadModality` / `MonadTwoCell`), while a computad
pushout needs a decider over the RECONSTRUCTED `monadComputad.toModeSignature` (carrier `Fin 1` / a `Fin`-subtype
/ `ReconstructedTwoCell`).  Those carriers are field-by-field DISTINCT Types, so a literal `=` is impossible; the
0/1-skeleton half of the equivalence ships (`monadComputadGraphEquiv`), and the `twoCell`-inclusive transport was
scoped as the fib-3-coupled multi-brick.

r3's finding SHARPENS that framing.  The reseat is a FIXED-pair translation
`(monadComputad.toModeSignature, monadModeSignature)`, and its FORWARD half is fib-3-DECOUPLED: it needs a
finite generator data-iso plus a structural cell functor plus a `recInto` conv-transport, NONE of which decides
2-cell equality modulo the 3-cell laws (the actual content of `fxMode_hasDecidableTwoCellEquality`).

## The reseat maps (FORWARD: reconstructed ==> bespoke)

  * **`reseatPath`** — the induced 1-cell functor.  Because `monadComputad` has ONE mode and ONE endo-generator,
    a reconstructed path `t^n` maps to the bespoke `t`-power `monadT^n` by IGNORING the (constant) mode/modality
    data and counting length — so it REDUCES definitionally (`reseatPath reconNil = nil point`,
    `reseatPath reconT = monadT`, `reseatPath reconTT = monadTThenT`, each by `rfl`).
  * **`reseatGen`** — THE crux (the `twoCellEquiv` forward half).  A reconstructed generating 2-cell
    `ReconstructedTwoCell p q = ⟨index, ⟨hlhs, hrhs⟩⟩` maps to `MonadTwoCell (reseatPath p) (reseatPath q)`:
    index `0` to `eta`, index `1` to `mu`, each cast to the boundary the interpreter witnesses pin down.  The
    dependent Sigma witness is collapsed through `reseatPath` FIRST (`reseatInterp`), so the boundary equality is
    extracted by a NON-dependent `Option.some.inj` — sidestepping the HEq/Sigma-injection propext landmine.  NO
    2-cell equality decision is used: this is why the forward reseat is fib-3-DECOUPLED.
  * **`reseatCell`** — the free 2-cell functor lifting `reseatGen` over the whole `RawTwoCellExpr` grammar
    (`gen` via `reseatGen`, `id`/`vcomp` cast-free, the two whisker cases through the single `castBoundary`
    reconciling `reseatPath (composePath ..)` with `composePath (reseatPath ..) (reseatPath ..)`).

## The conv transport + the reconstructed decider (the MODE-ADMIT r4 PLAN)

r3 (this file) ships the forward FUNCTOR only; the forward CONV TRANSPORT is the r4 target.  DESIGN (the r4
declarations that discharge it are added in the commits below; the honesty markers at the file foot are the
authoritative shipped/walled ledger):

  * **`reseatCell_preservesConv`** (P1a linchpin) — `reseatCell` preserves the COMPLETED free-strict-2-category
    convertibility, `TwoCellConvFull monadComputad.toModeSignature a b ==> TwoCellConvFull monadModeSignature
    (reseatCell a) (reseatCell b)`, by induction over all thirteen `TwoCellConvFull` constructors (and, in the
    `ofConv` case, over the free `TwoCellConv` and the twelve `TwoCellStep` rewrites).  The reseat analogue of the
    shipped `mapTwoCellConvFull`, ported arm-for-arm; `TwoCellConvFull` is LAW-FREE and purely structural, so no
    arm needs a monad coherence — the residual is pure cast LABOR, as the r3 markers claim.
  * **`MonadLawRelReconstructed`** — the walking monad's three laws stated over the reconstructed signature as a
    `CellRel monadComputad.toModeSignature`, mirroring the bespoke `MonadLawRel` rows at reconstructed boundaries.
  * **`reseatCell_reconLeftUnit` / `reseatCell_reconRightUnit` / `reseatCell_reconAssoc` / `reseatCell_reconIdT`**
    — the three propositional law-cell equalities `reseatCell reconLawCell = bespokeLawCell` (the r3 "second
    obstruction": read off the generator inversions `reseatGen_unit_isEta` / `reseatGen_mult_isMu` plus a
    reflexive-`castBoundary` collapse, NOT `rfl`).
  * **`reseatConvForward`** — `SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed a b
    ==> SaturatedConvOver monadModeSignature MonadLawRel (reseatCell a) (reseatCell b)` by `recInto`: each
    reconstructed congruence constructor maps to its `reseatCell`-image bespoke constructor, the three
    reconstructed rows to the three bespoke rows.  This is the FORWARD (isFalse-leg) direction of the conv-iff.
  * **`monadReconRefutes`** — the reseat's isFalse leg made literal: a reconstructed candidate pair whose
    `reseatCell`-images the bespoke decider refutes is refuted at the reconstructed signature, by transporting a
    hypothetical reconstructed conv forward into the refuted bespoke conv.

## The walled leg (the honest residual)

The FULL two-sided `DecidableSaturatedConvForRel monadComputad.toModeSignature MonadLawRelReconstructed` also
needs the isTrue leg: `bespoke-conv (reseatCell a) (reseatCell b) ==> reconstructed-conv a b`.  Running `recInto`
backward lands on `reseatCell a` / `reseatCell b`, so concluding about `a` / `b` needs the round-trip
`reseatCellInv (reseatCell a) = a` — cast-heavy because `reseatPath` is only PROPOSITIONALLY a monoid
homomorphism (the whisker `castBoundary` threading), a genuine multi-lemma file.  It is LABOR, not undecidability;
the honesty markers below are the ledger of which legs ship (`fxAmalg_hasReseatConvTransport` = the forward half)
and which stay walled (`fxAmalg_hasReconstructionDecoderReseat` in `DeciderReseat.lean` — the full two-sided
decider — and `fxModeAdmit_hasRenamingDeciderTransport` in `ModeAdmit.lean`).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The induced 1-cell functor: reconstructed `t`-powers ==> bespoke `t`-powers -/

/-- ★ **The reseat 1-cell functor** — a reconstructed monad path `t^n` (over `monadComputad.toModeGraph`, one
mode / one endo-generator) maps to the bespoke `t`-power (over `monadGraph`) by COUNTING length: `nil` to `nil`,
`cons` to `cons MonadModality.t`, ignoring the (constant, single-inhabitant) mode and modality data.  This
IGNORING is what makes it reduce definitionally on concrete paths — the key to the crux forward gen map below. -/
def reseatPath {sourceMode targetMode : Fin 1}
    (path : ModalityPath monadComputad.toModeGraph sourceMode targetMode) :
    ModalityPath monadGraph MonadMode.point MonadMode.point :=
  match path with
  | ModalityPath.nil _ => ModalityPath.nil (graph := monadGraph) MonadMode.point
  | ModalityPath.cons _ rest =>
      ModalityPath.cons (graph := monadGraph) MonadModality.t (reseatPath rest)

/-- Smoke: the reconstructed identity path at `point` maps to the bespoke identity path (`rfl`). -/
theorem reseatPath_nil :
    reseatPath (ModalityPath.nil (graph := monadComputad.toModeGraph) ⟨0, by decide⟩)
      = ModalityPath.nil (graph := monadGraph) MonadMode.point := rfl

/-- ★ Smoke: the reconstructed `t`-path (`monadComputadReconstructedT`) maps to the bespoke `monadT` (`rfl` — the
generator embedding lines up definitionally). -/
theorem reseatPath_reconT : reseatPath monadComputadReconstructedT = monadT := rfl

/-! ## Collapsing the dependent interpreter witness through `reseatPath` -/

/-- Collapse a `interpretWordFrom` result through `reseatPath` — the dependent Sigma is forgotten (its target
mode is always `point`), leaving a NON-dependent `Option (ModalityPath monadGraph point point)`.  Applying this
to a `ReconstructedTwoCell` interpreter witness BEFORE `Option.some.inj` extracts the boundary equality without
any HEq/Sigma-injection (the propext landmine the recon flagged). -/
def reseatInterp {src : Fin 1}
    (result : Option (Sigma (fun targetMode : Fin 1 =>
      ModalityPath monadComputad.toModeGraph src targetMode))) :
    Option (ModalityPath monadGraph MonadMode.point MonadMode.point) :=
  result.map (fun sig => reseatPath sig.snd)

/-! ## The boundary cast on bespoke 2-cell generators -/

/-- Cast a bespoke `MonadTwoCell` across equalities of its parallel boundary 1-cells (a double `Eq.rec`) — the
`MonadTwoCell`-level analogue of `RawTwoCellExpr.castBoundary`, used to move `eta` / `mu` onto the `reseatPath`
boundary the interpreter witnesses pin down. -/
def castMonadTwoCell {firstPath firstPath' secondPath secondPath' : ModalityPath monadGraph
      MonadMode.point MonadMode.point}
    (hfirst : firstPath = firstPath') (hsecond : secondPath = secondPath')
    (cell : MonadTwoCell firstPath secondPath) : MonadTwoCell firstPath' secondPath' :=
  hfirst ▸ hsecond ▸ cell

/-! ## THE CRUX — the forward generator translation (`twoCellEquiv`, forward half)

The reconstructed monad 2-generators are index `0` (`eta`, words `[] => [t]`) and index `1` (`mu`, words
`[t,t] => [t]`).  A `ReconstructedTwoCell p q = ⟨index, ⟨hlhs, hrhs⟩⟩` therefore forces, via its interpreter
witnesses, `(reseatPath p, reseatPath q)` to be exactly the `eta` / `mu` bespoke boundary; `reseatGen` casts the
matching bespoke generator onto it.  The mode variables are cased to `⟨0, _⟩` (the sole `Fin 1` inhabitant,
propext-free via `Nat.not_lt_zero`) so the `interpretWordFrom` `dite`s reduce; the index is cased over `Fin 2`. -/

/-- ★★ **The crux: the forward generator translation** — a reconstructed generating 2-cell maps to the bespoke
`MonadTwoCell` at the `reseatPath`-image boundary.  Index `0` to `eta`, index `1` to `mu`, cast onto the
boundary the interpreter witnesses `hlhs` / `hrhs` pin down (extracted through `reseatInterp` + `Option.some.inj`,
propext-free).  NO 2-cell equality is decided — the fib-3-decoupling made concrete. -/
def reseatGen : {sourceMode targetMode : Fin 1} →
    {sourcePath targetPath : ModalityPath monadComputad.toModeGraph sourceMode targetMode} →
    monadComputad.ReconstructedTwoCell sourcePath targetPath →
    MonadTwoCell (reseatPath sourcePath) (reseatPath targetPath)
  | ⟨0, _⟩, ⟨0, _⟩, _, _, ⟨⟨0, _⟩, hlhs, hrhs⟩ =>
      castMonadTwoCell
        (Option.some.inj (congrArg reseatInterp hlhs))
        (Option.some.inj (congrArg reseatInterp hrhs))
        MonadTwoCell.eta
  | ⟨0, _⟩, ⟨0, _⟩, _, _, ⟨⟨1, _⟩, hlhs, hrhs⟩ =>
      castMonadTwoCell
        (Option.some.inj (congrArg reseatInterp hlhs))
        (Option.some.inj (congrArg reseatInterp hrhs))
        MonadTwoCell.mu
  | ⟨0, _⟩, ⟨0, _⟩, _, _, ⟨⟨count + 2, isLt⟩, _⟩ =>
      False.elim (Nat.not_lt_zero count (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLt)))
  | ⟨count + 1, isLt⟩, _, _, _, _ =>
      False.elim (Nat.not_lt_zero count (Nat.lt_of_succ_lt_succ isLt))
  | ⟨0, _⟩, ⟨count + 1, isLt⟩, _, _, _ =>
      False.elim (Nat.not_lt_zero count (Nat.lt_of_succ_lt_succ isLt))

/-! ## Non-vacuity — the crux fires on the reconstructed monad unit -/

/-- Boundary inversion: the bespoke `MonadTwoCell` at the unit boundary `(id_point, t)` is UNIQUELY `eta` (`mu`
lives at `(t·t, t)`, discharged by the `nil`/`cons` boundary noConfusion).  The reduction-free handle for the
crux's non-vacuity: `reseatGen` produces a boundary cast that does not reduce definitionally, so the fact that it
lands on `eta` is read off the codomain's uniqueness, not off the (stuck) matcher. -/
theorem monadTwoCellAtUnit_isEta
    (cell : MonadTwoCell (ModalityPath.nil (graph := monadGraph) MonadMode.point) monadT) :
    cell = MonadTwoCell.eta := by
  cases cell with
  | eta => rfl

/-- ★ **Non-vacuity of the crux** — `reseatGen` on the reconstructed monad unit
(`monadComputadReconstructsUnit`, a REAL 2-generator index `0`) IS the bespoke `eta`.  Its boundary
`(reseatPath reconNil, reseatPath reconT)` is DEFINITIONALLY `(nil point, monadT)`, so `reseatGen`'s value
inhabits `MonadTwoCell (nil point) monadT`, whose sole inhabitant is `eta` (`monadTwoCellAtUnit_isEta`).
Witnesses the forward `twoCellEquiv` genuinely maps a real reconstructed generator to the SEPARATING bespoke
generator (the codomain read, since the boundary-cast blocks the matcher's definitional reduction). -/
theorem reseatGen_unit_isEta :
    reseatGen monadComputadReconstructsUnit = MonadTwoCell.eta :=
  monadTwoCellAtUnit_isEta (reseatGen monadComputadReconstructsUnit)

/-- The reconstructed `t·t` 1-cell — the interpreter's image of the endo-generator word `[t, t]` (the domain of
the reconstructed multiplication). -/
def monadComputadReconstructedTT :
    ModalityPath monadComputad.toModeGraph (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1) :=
  ModalityPath.cons
    (⟨⟨0, by decide⟩, rfl⟩ : monadComputad.Modality ⟨0, by decide⟩ ⟨0, by decide⟩)
    monadComputadReconstructedT

/-- The **reconstructed monad multiplication** — 2-generator index `1` of `monadComputad` inhabits
`ReconstructedTwoCell` at the boundary `(t·t, t)`: the interpreter sends `lhs = [t, t]` to
`monadComputadReconstructedTT` and `rhs = [t]` to `monadComputadReconstructedT`, both by `rfl`.  The second real
generator to verify the forward `twoCellEquiv`. -/
def monadComputadReconstructsMult :
    monadComputad.ReconstructedTwoCell monadComputadReconstructedTT monadComputadReconstructedT :=
  ⟨⟨1, by decide⟩, ⟨rfl, rfl⟩⟩

/-- ★ Smoke: the reconstructed `t·t` path maps to the bespoke `monadTThenT` (`rfl`). -/
theorem reseatPath_reconTT : reseatPath monadComputadReconstructedTT = monadTThenT := rfl

/-- Boundary inversion: the bespoke `MonadTwoCell` at the multiplication boundary `(t·t, t)` is UNIQUELY `mu`
(`eta` lives at `(id, t)`, discharged by the `cons`/`nil` boundary noConfusion). -/
theorem monadTwoCellAtMult_isMu (cell : MonadTwoCell monadTThenT monadT) : cell = MonadTwoCell.mu := by
  cases cell with
  | mu => rfl

/-- ★ **The crux on the SECOND generator** — `reseatGen` on the reconstructed monad multiplication IS the bespoke
`mu`.  Its boundary `(reseatPath reconTT, reseatPath reconT)` is DEFINITIONALLY `(monadTThenT, monadT)`, whose
sole `MonadTwoCell` inhabitant is `mu` (`monadTwoCellAtMult_isMu`).  Together with `reseatGen_unit_isEta` the
forward `twoCellEquiv` is verified on BOTH monad generators. -/
theorem reseatGen_mult_isMu :
    reseatGen monadComputadReconstructsMult = MonadTwoCell.mu :=
  monadTwoCellAtMult_isMu (reseatGen monadComputadReconstructsMult)

/-! ## The induced monoid-homomorphism law of `reseatPath` (the whisker-cast ingredient) -/

/-- ★ **`reseatPath` is a monoid homomorphism** — it distributes over reconstructed path composition (PROPOSITIONALLY:
`composePath` recurses on its first argument, base `rfl`, `cons` step `congrArg`).  The equality the two whisker
cases of `reseatCell` thread through `castBoundary`, exactly as `mapPath_composePath` feeds `mapCellAlong`. -/
theorem reseatPath_composePath :
    {sourceMode middleMode targetMode : Fin 1} →
    (first : ModalityPath monadComputad.toModeGraph sourceMode middleMode) →
    (second : ModalityPath monadComputad.toModeGraph middleMode targetMode) →
    reseatPath (composePath first second)
      = composePath (reseatPath first) (reseatPath second)
  | _, _, _, ModalityPath.nil _, _ => rfl
  | _, _, _, ModalityPath.cons _ rest, second =>
      show ModalityPath.cons (graph := monadGraph) MonadModality.t (reseatPath (composePath rest second))
          = ModalityPath.cons (graph := monadGraph) MonadModality.t
              (composePath (reseatPath rest) (reseatPath second)) from
        congrArg (ModalityPath.cons (graph := monadGraph) MonadModality.t)
          (reseatPath_composePath rest second)

/-! ## The forward free 2-cell functor: reconstructed cells ==> bespoke cells -/

/-- ★★ **The forward reseat cell functor** — lift `reseatGen` over the whole `RawTwoCellExpr` grammar: a
reconstructed free 2-cell over `monadComputad.toModeSignature` transports to a bespoke free 2-cell over
`monadModeSignature`, boundaries carried by `reseatPath`.  `gen` via the crux `reseatGen`; `id` / `vcomp`
CAST-FREE (boundaries coincide definitionally); the two whisker cases through the single `castBoundary
(reseatPath_composePath ..)` reconciling `reseatPath (composePath ..)` with `composePath (reseatPath ..)
(reseatPath ..)` — the exact shape of `mapCellAlong`, but landing in the BESPOKE signature (which is NOT a
computad `toModeSignature`, so `mapCellAlong` cannot produce it — the reseat's reason to exist). -/
def reseatCell {sourceMode targetMode : Fin 1}
    {sourcePath targetPath : ModalityPath monadComputad.toModeGraph sourceMode targetMode}
    (cell : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath) :
    RawTwoCellExpr monadModeSignature (reseatPath sourcePath) (reseatPath targetPath) :=
  match cell with
  | RawTwoCellExpr.gen generator => RawTwoCellExpr.gen (reseatGen generator)
  | RawTwoCellExpr.id path =>
      RawTwoCellExpr.id (signature := monadModeSignature) (reseatPath path)
  | RawTwoCellExpr.vcomp cellAlpha cellBeta =>
      RawTwoCellExpr.vcomp (reseatCell cellAlpha) (reseatCell cellBeta)
  | @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell oneCellG oneCellH body =>
      RawTwoCellExpr.castBoundary
        (reseatPath_composePath oneCell oneCellG).symm
        (reseatPath_composePath oneCell oneCellH).symm
        (RawTwoCellExpr.whiskerLeft (reseatPath oneCell) (reseatCell body))
  | @RawTwoCellExpr.whiskerRight _ _ _ _ oneCellF oneCellG oneCell body =>
      RawTwoCellExpr.castBoundary
        (reseatPath_composePath oneCellF oneCell).symm
        (reseatPath_composePath oneCellG oneCell).symm
        (RawTwoCellExpr.whiskerRight (reseatPath oneCell) (reseatCell body))

/-- Smoke: `reseatCell` on a bare generator IS `gen (reseatGen ..)` (`rfl`) — the functor's `gen` clause. -/
theorem reseatCell_gen {sourceMode targetMode : Fin 1}
    {sourcePath targetPath : ModalityPath monadComputad.toModeGraph sourceMode targetMode}
    (generator : monadComputad.ReconstructedTwoCell sourcePath targetPath) :
    reseatCell (RawTwoCellExpr.gen generator) = RawTwoCellExpr.gen (reseatGen generator) := rfl

/-! ## P1a — the reseat cast kit (signature-generic `Eq.rec` lemmas, re-derived in-file)

`ConvFullFunctor.lean` (home of `mapTwoCellConvFull`, the template this port mirrors) is NOT in this file's import
cone, and its `castBoundaryCongr` / whisker-cast lemmas collide by fully-qualified name with the reachable
`WhiskerReframing` / `MonadWhiskerNormalizeCases` copies (so importing it is a name clash).  These nine generic
`Eq.rec` lemmas (all `cases; rfl`) are therefore re-derived here under a private `ReseatCastKit` namespace, matching
ConvFullFunctor's exact statements, so the `reseatCell` functoriality port below is self-contained and clash-free. -/

namespace ReseatCastKit

/-- A cell EQUALITY yields a (reflexive) completed convertibility. -/
theorem convFullOfCellEq {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (cellsEqual : cellAlpha = cellBeta) : TwoCellConvFull signature cellAlpha cellBeta := by
  cases cellsEqual; exact TwoCellConvFull.refl _

/-- Casting both sides of a `TwoCellConvFull` by the same boundary equalities preserves it. -/
theorem castBoundaryCongr {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} :
    TwoCellConvFull signature cellAlpha cellBeta →
    TwoCellConvFull signature
      (RawTwoCellExpr.castBoundary hsource htarget cellAlpha)
      (RawTwoCellExpr.castBoundary hsource htarget cellBeta) := by
  cases hsource; cases htarget; exact id

/-- Casting an identity 2-cell is an identity 2-cell. -/
theorem castBoundaryId {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {path path' : ModalityPath signature.graph sourceMode targetMode} (hpath : path = path') :
    RawTwoCellExpr.castBoundary hpath hpath (RawTwoCellExpr.id path) = RawTwoCellExpr.id path' := by
  cases hpath; rfl

/-- Casting a vertical composite distributes over the factors. -/
theorem castBoundaryVcomp {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellF' oneCellG oneCellG' oneCellH oneCellH' : ModalityPath signature.graph sourceMode targetMode}
    (hF : oneCellF = oneCellF') (hG : oneCellG = oneCellG') (hH : oneCellH = oneCellH')
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH) :
    RawTwoCellExpr.castBoundary hF hH (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = RawTwoCellExpr.vcomp
          (RawTwoCellExpr.castBoundary hF hG cellAlpha) (RawTwoCellExpr.castBoundary hG hH cellBeta) := by
  cases hF; cases hG; cases hH; rfl

/-- Two nested boundary casts compose into one. -/
theorem castBoundaryTrans {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' sourcePath'' targetPath targetPath' targetPath'' :
      ModalityPath signature.graph sourceMode targetMode}
    (h1s : sourcePath = sourcePath') (h1t : targetPath = targetPath')
    (h2s : sourcePath' = sourcePath'') (h2t : targetPath' = targetPath'')
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    RawTwoCellExpr.castBoundary h2s h2t (RawTwoCellExpr.castBoundary h1s h1t cell)
      = RawTwoCellExpr.castBoundary (h1s.trans h2s) (h1t.trans h2t) cell := by
  cases h1s; cases h1t; cases h2s; cases h2t; rfl

/-- Left-whiskering pushes past a boundary cast. -/
theorem whiskerLeftCastBoundary {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode)
    {oneCellG oneCellG' oneCellH oneCellH' : ModalityPath signature.graph middleMode targetMode}
    (hG : oneCellG = oneCellG') (hH : oneCellH = oneCellH')
    (body : RawTwoCellExpr signature oneCellG oneCellH) :
    RawTwoCellExpr.whiskerLeft oneCell (RawTwoCellExpr.castBoundary hG hH body)
      = RawTwoCellExpr.castBoundary (congrArg (composePath oneCell) hG) (congrArg (composePath oneCell) hH)
          (RawTwoCellExpr.whiskerLeft oneCell body) := by
  cases hG; cases hH; rfl

/-- Right-whiskering pushes past a boundary cast. -/
theorem whiskerRightCastBoundary {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellF oneCellF' oneCellG oneCellG' : ModalityPath signature.graph sourceMode middleMode}
    (oneCell : ModalityPath signature.graph middleMode targetMode)
    (hF : oneCellF = oneCellF') (hG : oneCellG = oneCellG')
    (body : RawTwoCellExpr signature oneCellF oneCellG) :
    RawTwoCellExpr.whiskerRight oneCell (RawTwoCellExpr.castBoundary hF hG body)
      = RawTwoCellExpr.castBoundary (congrArg (fun path => composePath path oneCell) hF)
          (congrArg (fun path => composePath path oneCell) hG)
          (RawTwoCellExpr.whiskerRight oneCell body) := by
  cases hF; cases hG; rfl

/-- Transport a left-whiskering along an EQUALITY of its 1-cell (ConvFullFunctor's `hCell` orientation). -/
theorem whiskerLeftPathCongr {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCell oneCell' : ModalityPath signature.graph sourceMode middleMode}
    {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode}
    (hCell : oneCell = oneCell') (body : RawTwoCellExpr signature oneCellG oneCellH) :
    RawTwoCellExpr.whiskerLeft oneCell' body
      = RawTwoCellExpr.castBoundary (congrArg (fun path => composePath path oneCellG) hCell)
          (congrArg (fun path => composePath path oneCellH) hCell)
          (RawTwoCellExpr.whiskerLeft oneCell body) := by
  cases hCell; rfl

/-- Transport a right-whiskering along an EQUALITY of its 1-cell. -/
theorem whiskerRightPathCongr {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCell oneCell' : ModalityPath signature.graph middleMode targetMode}
    {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode}
    (hCell : oneCell = oneCell') (body : RawTwoCellExpr signature oneCellF oneCellG) :
    RawTwoCellExpr.whiskerRight oneCell' body
      = RawTwoCellExpr.castBoundary (congrArg (composePath oneCellF) hCell)
          (congrArg (composePath oneCellG) hCell)
          (RawTwoCellExpr.whiskerRight oneCell body) := by
  cases hCell; rfl

end ReseatCastKit

/-! ## P1a — `reseatCell` per-constructor reduction lemmas (mirroring `mapCellAlong_*`, all `rfl` / `cases; rfl`) -/

/-- `reseatCell` on an identity 2-cell (`rfl`). -/
theorem reseatCell_id {sourceMode targetMode : Fin 1}
    (path : ModalityPath monadComputad.toModeGraph sourceMode targetMode) :
    reseatCell (RawTwoCellExpr.id path)
      = RawTwoCellExpr.id (signature := monadModeSignature) (reseatPath path) := rfl

/-- `reseatCell` on a vertical composite (`rfl`, cast-free). -/
theorem reseatCell_vcomp {sourceMode targetMode : Fin 1}
    {oneCellF oneCellG oneCellH : ModalityPath monadComputad.toModeGraph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr monadComputad.toModeSignature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr monadComputad.toModeSignature oneCellG oneCellH) :
    reseatCell (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = RawTwoCellExpr.vcomp (reseatCell cellAlpha) (reseatCell cellBeta) := rfl

/-- `reseatCell` on a left whiskering — the single `reseatPath_composePath` cast (`rfl`). -/
theorem reseatCell_whiskerLeft {sourceMode middleMode targetMode : Fin 1}
    (oneCell : ModalityPath monadComputad.toModeGraph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath monadComputad.toModeGraph middleMode targetMode}
    (body : RawTwoCellExpr monadComputad.toModeSignature oneCellG oneCellH) :
    reseatCell (RawTwoCellExpr.whiskerLeft oneCell body)
      = RawTwoCellExpr.castBoundary
          (reseatPath_composePath oneCell oneCellG).symm
          (reseatPath_composePath oneCell oneCellH).symm
          (RawTwoCellExpr.whiskerLeft (reseatPath oneCell) (reseatCell body)) := rfl

/-- `reseatCell` on a right whiskering — the single `reseatPath_composePath` cast (`rfl`). -/
theorem reseatCell_whiskerRight {sourceMode middleMode targetMode : Fin 1}
    {oneCellF oneCellG : ModalityPath monadComputad.toModeGraph sourceMode middleMode}
    (oneCell : ModalityPath monadComputad.toModeGraph middleMode targetMode)
    (body : RawTwoCellExpr monadComputad.toModeSignature oneCellF oneCellG) :
    reseatCell (RawTwoCellExpr.whiskerRight oneCell body)
      = RawTwoCellExpr.castBoundary
          (reseatPath_composePath oneCellF oneCell).symm
          (reseatPath_composePath oneCellG oneCell).symm
          (RawTwoCellExpr.whiskerRight (reseatPath oneCell) (reseatCell body)) := rfl

/-- `reseatCell` commutes with `castBoundary` (both `Eq.rec`; `cases` the equalities). -/
theorem reseatCell_castBoundary {sourceMode targetMode : Fin 1}
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath monadComputad.toModeGraph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath) :
    reseatCell (RawTwoCellExpr.castBoundary hsource htarget cell)
      = RawTwoCellExpr.castBoundary (congrArg reseatPath hsource) (congrArg reseatPath htarget)
          (reseatCell cell) := by
  cases hsource; cases htarget; rfl

/-- `reseatCell` commutes with the derived Godement product `hcomp` up to one boundary cast. -/
theorem reseatCell_hcomp {sourceMode middleMode targetMode : Fin 1}
    {oneCellFDom oneCellFCod : ModalityPath monadComputad.toModeGraph sourceMode middleMode}
    {oneCellGDom oneCellGCod : ModalityPath monadComputad.toModeGraph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr monadComputad.toModeSignature oneCellFDom oneCellFCod)
    (cellBeta : RawTwoCellExpr monadComputad.toModeSignature oneCellGDom oneCellGCod) :
    reseatCell (RawTwoCellExpr.hcomp cellAlpha cellBeta)
      = RawTwoCellExpr.castBoundary
          (reseatPath_composePath oneCellFDom oneCellGDom).symm
          (reseatPath_composePath oneCellFCod oneCellGCod).symm
          (RawTwoCellExpr.hcomp (reseatCell cellAlpha) (reseatCell cellBeta)) := by
  show RawTwoCellExpr.vcomp (reseatCell (RawTwoCellExpr.whiskerRight oneCellGDom cellAlpha))
      (reseatCell (RawTwoCellExpr.whiskerLeft oneCellFCod cellBeta)) = _
  exact (ReseatCastKit.castBoundaryVcomp
    (reseatPath_composePath oneCellFDom oneCellGDom).symm
    (reseatPath_composePath oneCellFCod oneCellGDom).symm
    (reseatPath_composePath oneCellFCod oneCellGCod).symm
    (RawTwoCellExpr.whiskerRight (reseatPath oneCellGDom) (reseatCell cellAlpha))
    (RawTwoCellExpr.whiskerLeft (reseatPath oneCellFCod) (reseatCell cellBeta))).symm

/-- `reseatCell` through `whiskerLeft ∘ whiskerLeft`. -/
theorem reseatCell_whiskerLeft_whiskerLeft {sm mm1 mm2 tm : Fin 1}
    (oneCellOuter : ModalityPath monadComputad.toModeGraph sm mm1)
    (oneCellInner : ModalityPath monadComputad.toModeGraph mm1 mm2)
    {bodyDom bodyCod : ModalityPath monadComputad.toModeGraph mm2 tm}
    (body : RawTwoCellExpr monadComputad.toModeSignature bodyDom bodyCod) :
    reseatCell (RawTwoCellExpr.whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body))
      = RawTwoCellExpr.castBoundary
          ((congrArg (composePath (reseatPath oneCellOuter))
              (reseatPath_composePath oneCellInner bodyDom).symm).trans
            (reseatPath_composePath oneCellOuter (composePath oneCellInner bodyDom)).symm)
          ((congrArg (composePath (reseatPath oneCellOuter))
              (reseatPath_composePath oneCellInner bodyCod).symm).trans
            (reseatPath_composePath oneCellOuter (composePath oneCellInner bodyCod)).symm)
          (RawTwoCellExpr.whiskerLeft (reseatPath oneCellOuter)
            (RawTwoCellExpr.whiskerLeft (reseatPath oneCellInner)
              (reseatCell body))) :=
  (reseatCell_whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body)).trans
    ((congrArg (RawTwoCellExpr.castBoundary _ _)
        ((congrArg (RawTwoCellExpr.whiskerLeft (reseatPath oneCellOuter))
            (reseatCell_whiskerLeft oneCellInner body)).trans
          (ReseatCastKit.whiskerLeftCastBoundary (reseatPath oneCellOuter) _ _
            (RawTwoCellExpr.whiskerLeft (reseatPath oneCellInner)
              (reseatCell body))))).trans
      (ReseatCastKit.castBoundaryTrans _ _ _ _ _))

/-- `reseatCell` through `whiskerRight ∘ whiskerRight`. -/
theorem reseatCell_whiskerRight_whiskerRight {sm mm1 mm2 tm : Fin 1}
    {bodyDom bodyCod : ModalityPath monadComputad.toModeGraph sm mm1}
    (oneCellInner : ModalityPath monadComputad.toModeGraph mm1 mm2)
    (oneCellOuter : ModalityPath monadComputad.toModeGraph mm2 tm)
    (body : RawTwoCellExpr monadComputad.toModeSignature bodyDom bodyCod) :
    reseatCell (RawTwoCellExpr.whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body))
      = RawTwoCellExpr.castBoundary
          ((congrArg (fun path => composePath path (reseatPath oneCellOuter))
              (reseatPath_composePath bodyDom oneCellInner).symm).trans
            (reseatPath_composePath (composePath bodyDom oneCellInner) oneCellOuter).symm)
          ((congrArg (fun path => composePath path (reseatPath oneCellOuter))
              (reseatPath_composePath bodyCod oneCellInner).symm).trans
            (reseatPath_composePath (composePath bodyCod oneCellInner) oneCellOuter).symm)
          (RawTwoCellExpr.whiskerRight (reseatPath oneCellOuter)
            (RawTwoCellExpr.whiskerRight (reseatPath oneCellInner)
              (reseatCell body))) :=
  (reseatCell_whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body)).trans
    ((congrArg (RawTwoCellExpr.castBoundary _ _)
        ((congrArg (RawTwoCellExpr.whiskerRight (reseatPath oneCellOuter))
            (reseatCell_whiskerRight oneCellInner body)).trans
          (ReseatCastKit.whiskerRightCastBoundary (reseatPath oneCellOuter) _ _
            (RawTwoCellExpr.whiskerRight (reseatPath oneCellInner)
              (reseatCell body))))).trans
      (ReseatCastKit.castBoundaryTrans _ _ _ _ _))

/-- `reseatCell` through `whiskerLeft ∘ whiskerRight`. -/
theorem reseatCell_whiskerLeft_whiskerRight {sm ms mt tm : Fin 1}
    (leftWhisker : ModalityPath monadComputad.toModeGraph sm ms)
    {bodyDom bodyCod : ModalityPath monadComputad.toModeGraph ms mt}
    (rightWhisker : ModalityPath monadComputad.toModeGraph mt tm)
    (body : RawTwoCellExpr monadComputad.toModeSignature bodyDom bodyCod) :
    reseatCell (RawTwoCellExpr.whiskerLeft leftWhisker (RawTwoCellExpr.whiskerRight rightWhisker body))
      = RawTwoCellExpr.castBoundary
          ((congrArg (composePath (reseatPath leftWhisker))
              (reseatPath_composePath bodyDom rightWhisker).symm).trans
            (reseatPath_composePath leftWhisker (composePath bodyDom rightWhisker)).symm)
          ((congrArg (composePath (reseatPath leftWhisker))
              (reseatPath_composePath bodyCod rightWhisker).symm).trans
            (reseatPath_composePath leftWhisker (composePath bodyCod rightWhisker)).symm)
          (RawTwoCellExpr.whiskerLeft (reseatPath leftWhisker)
            (RawTwoCellExpr.whiskerRight (reseatPath rightWhisker)
              (reseatCell body))) :=
  (reseatCell_whiskerLeft leftWhisker (RawTwoCellExpr.whiskerRight rightWhisker body)).trans
    ((congrArg (RawTwoCellExpr.castBoundary _ _)
        ((congrArg (RawTwoCellExpr.whiskerLeft (reseatPath leftWhisker))
            (reseatCell_whiskerRight rightWhisker body)).trans
          (ReseatCastKit.whiskerLeftCastBoundary (reseatPath leftWhisker) _ _
            (RawTwoCellExpr.whiskerRight (reseatPath rightWhisker)
              (reseatCell body))))).trans
      (ReseatCastKit.castBoundaryTrans _ _ _ _ _))

/-- `reseatCell` through `whiskerRight ∘ whiskerLeft`. -/
theorem reseatCell_whiskerRight_whiskerLeft {sm ms mt tm : Fin 1}
    (leftWhisker : ModalityPath monadComputad.toModeGraph sm ms)
    {bodyDom bodyCod : ModalityPath monadComputad.toModeGraph ms mt}
    (rightWhisker : ModalityPath monadComputad.toModeGraph mt tm)
    (body : RawTwoCellExpr monadComputad.toModeSignature bodyDom bodyCod) :
    reseatCell (RawTwoCellExpr.whiskerRight rightWhisker (RawTwoCellExpr.whiskerLeft leftWhisker body))
      = RawTwoCellExpr.castBoundary
          ((congrArg (fun path => composePath path (reseatPath rightWhisker))
              (reseatPath_composePath leftWhisker bodyDom).symm).trans
            (reseatPath_composePath (composePath leftWhisker bodyDom) rightWhisker).symm)
          ((congrArg (fun path => composePath path (reseatPath rightWhisker))
              (reseatPath_composePath leftWhisker bodyCod).symm).trans
            (reseatPath_composePath (composePath leftWhisker bodyCod) rightWhisker).symm)
          (RawTwoCellExpr.whiskerRight (reseatPath rightWhisker)
            (RawTwoCellExpr.whiskerLeft (reseatPath leftWhisker)
              (reseatCell body))) :=
  (reseatCell_whiskerRight rightWhisker (RawTwoCellExpr.whiskerLeft leftWhisker body)).trans
    ((congrArg (RawTwoCellExpr.castBoundary _ _)
        ((congrArg (RawTwoCellExpr.whiskerRight (reseatPath rightWhisker))
            (reseatCell_whiskerLeft leftWhisker body)).trans
          (ReseatCastKit.whiskerRightCastBoundary (reseatPath rightWhisker) _ _
            (RawTwoCellExpr.whiskerLeft (reseatPath leftWhisker)
              (reseatCell body))))).trans
      (ReseatCastKit.castBoundaryTrans _ _ _ _ _))

/-! ## P1a — the forward conv functoriality: `reseatCell` preserves the free rewrites, then the completed conv -/

/-- ★ `reseatCell` preserves the twelve free 3-cell rewrites — each `TwoCellStep` over the reconstructed signature
maps to a completed convertibility between the `reseatCell`-images.  Arm-for-arm the port of `mapTwoCellStep`. -/
theorem reseatTwoCellStep {sourceMode targetMode : monadComputad.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadComputad.toModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath}
    (step : TwoCellStep monadComputad.toModeSignature cellAlpha cellBeta) :
    TwoCellConvFull monadModeSignature (reseatCell cellAlpha) (reseatCell cellBeta) := by
  induction step with
  | vcompIdLeft cellA =>
      exact TwoCellConvFull.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft (reseatCell cellA)))
  | vcompIdRight cellA =>
      exact TwoCellConvFull.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdRight (reseatCell cellA)))
  | vcompAssoc cellA cellB cellC =>
      exact TwoCellConvFull.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompAssoc (reseatCell cellA) (reseatCell cellB) (reseatCell cellC)))
  | whiskerLeftId oneCell path =>
      simp only [reseatCell_whiskerLeft, reseatCell_id]
      exact TwoCellConvFull.trans
        (ReseatCastKit.castBoundaryCongr
          (reseatPath_composePath oneCell path).symm
          (reseatPath_composePath oneCell path).symm
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep
            (@TwoCellStep.whiskerLeftId monadModeSignature _ _ _
              (reseatPath oneCell) (reseatPath path)))))
        (ReseatCastKit.convFullOfCellEq (ReseatCastKit.castBoundaryId
          (reseatPath_composePath oneCell path).symm))
  | whiskerRightId path oneCell =>
      simp only [reseatCell_whiskerRight, reseatCell_id]
      exact TwoCellConvFull.trans
        (ReseatCastKit.castBoundaryCongr
          (reseatPath_composePath path oneCell).symm
          (reseatPath_composePath path oneCell).symm
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep
            (@TwoCellStep.whiskerRightId monadModeSignature _ _ _
              (reseatPath path) (reseatPath oneCell)))))
        (ReseatCastKit.convFullOfCellEq (ReseatCastKit.castBoundaryId
          (reseatPath_composePath path oneCell).symm))
  | whiskerLeftVcomp oneCell cellB cellC =>
      exact TwoCellConvFull.trans
        (ReseatCastKit.castBoundaryCongr _ _
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep
            (TwoCellStep.whiskerLeftVcomp (reseatPath oneCell)
              (reseatCell cellB) (reseatCell cellC)))))
        (ReseatCastKit.convFullOfCellEq (ReseatCastKit.castBoundaryVcomp _ _ _ _ _))
  | whiskerRightVcomp oneCell cellA cellB =>
      exact TwoCellConvFull.trans
        (ReseatCastKit.castBoundaryCongr _ _
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep
            (TwoCellStep.whiskerRightVcomp (reseatPath oneCell)
              (reseatCell cellA) (reseatCell cellB)))))
        (ReseatCastKit.convFullOfCellEq (ReseatCastKit.castBoundaryVcomp _ _ _ _ _))
  | vcompCongrLeft cellB _ ih =>
      exact TwoCellConvFull.vcompCongrLeft (reseatCell cellB) ih
  | vcompCongrRight cellA _ ih =>
      exact TwoCellConvFull.vcompCongrRight (reseatCell cellA) ih
  | whiskerLeftCongr oneCell _ ih =>
      exact ReseatCastKit.castBoundaryCongr _ _
        (TwoCellConvFull.whiskerLeftCongr (reseatPath oneCell) ih)
  | whiskerRightCongr oneCell _ ih =>
      exact ReseatCastKit.castBoundaryCongr _ _
        (TwoCellConvFull.whiskerRightCongr (reseatPath oneCell) ih)
  | interchange cellA cellAUpper cellB cellBUpper =>
      simp only [reseatCell_hcomp, reseatCell_vcomp]
      refine TwoCellConvFull.trans
        (ReseatCastKit.castBoundaryCongr _ _
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep
            (TwoCellStep.interchange (reseatCell cellA) (reseatCell cellAUpper)
              (reseatCell cellB) (reseatCell cellBUpper))))) ?_
      exact ReseatCastKit.convFullOfCellEq (ReseatCastKit.castBoundaryVcomp _ _ _ _ _)

/-- `reseatCell` preserves the free `TwoCellConv` closure: a step via `reseatTwoCellStep`, `refl`/`symm`/`trans`
structurally.  Port of `mapTwoCellConv`. -/
theorem reseatTwoCellConv {sourceMode targetMode : monadComputad.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadComputad.toModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath}
    (conv : TwoCellConv monadComputad.toModeSignature cellAlpha cellBeta) :
    TwoCellConvFull monadModeSignature (reseatCell cellAlpha) (reseatCell cellBeta) := by
  induction conv with
  | ofStep step => exact reseatTwoCellStep step
  | refl cell => exact TwoCellConvFull.refl (reseatCell cell)
  | symm _ ih => exact TwoCellConvFull.symm ih
  | trans _ _ ih1 ih2 => exact TwoCellConvFull.trans ih1 ih2

/-- ★★ **P1a linchpin — `reseatCell` preserves the COMPLETED convertibility.**  `TwoCellConvFull` over the
reconstructed `monadComputad.toModeSignature` transports along `reseatCell` to the bespoke `monadModeSignature`.
Induction over all thirteen `TwoCellConvFull` constructors, arm-for-arm the port of `mapTwoCellConvFull` (the
`ofConv` case reuses `reseatTwoCellConv`; the whisker-functoriality laws reconcile `reseatCell`'s cast with the
same-named target law through `castBoundaryCongr` + `castBoundaryId` / `castBoundaryVcomp` / `whiskerLeftCastBoundary`
/ `whiskerLeftPathCongr` / `castBoundaryTrans`; the four one-hole congruences thread the inductive hypothesis; the
`whiskerLeftUnit` case is definitional).  NO arm needs a monad coherence — `TwoCellConvFull` is law-free, so the
residual is pure cast LABOR. -/
theorem reseatCell_preservesConv {sourceMode targetMode : monadComputad.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadComputad.toModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath}
    (convFull : TwoCellConvFull monadComputad.toModeSignature cellAlpha cellBeta) :
    TwoCellConvFull monadModeSignature (reseatCell cellAlpha) (reseatCell cellBeta) := by
  induction convFull with
  | ofConv conv => exact reseatTwoCellConv conv
  | whiskerLeftUnit body => exact TwoCellConvFull.whiskerLeftUnit (reseatCell body)
  | whiskerRightUnit body =>
      rename_i sourceMode targetMode oneCellDom oneCellCod
      refine TwoCellConvFull.trans (ReseatCastKit.convFullOfCellEq ?_)
        (TwoCellConvFull.trans
          (ReseatCastKit.castBoundaryCongr
            (reseatPath_composePath oneCellDom (identityPath targetMode)).symm
            (reseatPath_composePath oneCellCod (identityPath targetMode)).symm
            (TwoCellConvFull.whiskerRightUnit (reseatCell body)))
          (ReseatCastKit.convFullOfCellEq ?_))
      · exact reseatCell_whiskerRight (identityPath targetMode) body
      · exact (ReseatCastKit.castBoundaryTrans _ _ _ _ _).trans
          (reseatCell_castBoundary _ _ body).symm
  | whiskerLeftComp oneCellOuter oneCellInner body =>
      rename_i oneCellDom oneCellCod
      refine TwoCellConvFull.trans (ReseatCastKit.convFullOfCellEq ?_)
        (TwoCellConvFull.trans
          (ReseatCastKit.castBoundaryCongr
            ((congrArg (fun path => composePath path (reseatPath oneCellDom))
                (reseatPath_composePath oneCellOuter oneCellInner).symm).trans
              (reseatPath_composePath (composePath oneCellOuter oneCellInner) oneCellDom).symm)
            ((congrArg (fun path => composePath path (reseatPath oneCellCod))
                (reseatPath_composePath oneCellOuter oneCellInner).symm).trans
              (reseatPath_composePath (composePath oneCellOuter oneCellInner) oneCellCod).symm)
            (TwoCellConvFull.whiskerLeftComp (reseatPath oneCellOuter)
              (reseatPath oneCellInner) (reseatCell body)))
          (ReseatCastKit.convFullOfCellEq ?_))
      · exact (reseatCell_whiskerLeft (composePath oneCellOuter oneCellInner) body).trans
          ((congrArg (RawTwoCellExpr.castBoundary _ _)
            (ReseatCastKit.whiskerLeftPathCongr
              (reseatPath_composePath oneCellOuter oneCellInner).symm
              (reseatCell body))).trans
            (ReseatCastKit.castBoundaryTrans _ _ _ _ _))
      · refine Eq.trans ?_ (reseatCell_castBoundary _ _
          (RawTwoCellExpr.whiskerLeft oneCellOuter (RawTwoCellExpr.whiskerLeft oneCellInner body))).symm
        refine Eq.trans ?_ (congrArg (RawTwoCellExpr.castBoundary _ _)
          (reseatCell_whiskerLeft_whiskerLeft oneCellOuter oneCellInner body).symm)
        exact (ReseatCastKit.castBoundaryTrans _ _ _ _ _).trans
          (ReseatCastKit.castBoundaryTrans _ _ _ _ _).symm
  | whiskerRightComp oneCellInner oneCellOuter body =>
      rename_i oneCellDom oneCellCod
      refine TwoCellConvFull.trans (ReseatCastKit.convFullOfCellEq ?_)
        (TwoCellConvFull.trans
          (ReseatCastKit.castBoundaryCongr
            ((congrArg (composePath (reseatPath oneCellDom))
                (reseatPath_composePath oneCellInner oneCellOuter).symm).trans
              (reseatPath_composePath oneCellDom (composePath oneCellInner oneCellOuter)).symm)
            ((congrArg (composePath (reseatPath oneCellCod))
                (reseatPath_composePath oneCellInner oneCellOuter).symm).trans
              (reseatPath_composePath oneCellCod (composePath oneCellInner oneCellOuter)).symm)
            (TwoCellConvFull.whiskerRightComp (reseatPath oneCellInner)
              (reseatPath oneCellOuter) (reseatCell body)))
          (ReseatCastKit.convFullOfCellEq ?_))
      · exact (reseatCell_whiskerRight (composePath oneCellInner oneCellOuter) body).trans
          ((congrArg (RawTwoCellExpr.castBoundary _ _)
            (ReseatCastKit.whiskerRightPathCongr
              (reseatPath_composePath oneCellInner oneCellOuter).symm
              (reseatCell body))).trans
            (ReseatCastKit.castBoundaryTrans _ _ _ _ _))
      · refine Eq.trans ?_ (reseatCell_castBoundary _ _
          (RawTwoCellExpr.whiskerRight oneCellOuter (RawTwoCellExpr.whiskerRight oneCellInner body))).symm
        refine Eq.trans ?_ (congrArg (RawTwoCellExpr.castBoundary _ _)
          (reseatCell_whiskerRight_whiskerRight oneCellInner oneCellOuter body).symm)
        exact (ReseatCastKit.castBoundaryTrans _ _ _ _ _).trans
          (ReseatCastKit.castBoundaryTrans _ _ _ _ _).symm
  | whiskerExchange leftWhisker rightWhisker body =>
      rename_i bodyDom bodyCod
      refine TwoCellConvFull.trans (ReseatCastKit.convFullOfCellEq ?_)
        (TwoCellConvFull.trans
          (ReseatCastKit.castBoundaryCongr
            ((congrArg (composePath (reseatPath leftWhisker))
                (reseatPath_composePath bodyDom rightWhisker).symm).trans
              (reseatPath_composePath leftWhisker (composePath bodyDom rightWhisker)).symm)
            ((congrArg (composePath (reseatPath leftWhisker))
                (reseatPath_composePath bodyCod rightWhisker).symm).trans
              (reseatPath_composePath leftWhisker (composePath bodyCod rightWhisker)).symm)
            (TwoCellConvFull.whiskerExchange (reseatPath leftWhisker)
              (reseatPath rightWhisker) (reseatCell body)))
          (ReseatCastKit.convFullOfCellEq ?_))
      · exact reseatCell_whiskerLeft_whiskerRight leftWhisker rightWhisker body
      · refine Eq.trans ?_ (reseatCell_castBoundary _ _
          (RawTwoCellExpr.whiskerRight rightWhisker (RawTwoCellExpr.whiskerLeft leftWhisker body))).symm
        refine Eq.trans ?_ (congrArg (RawTwoCellExpr.castBoundary _ _)
          (reseatCell_whiskerRight_whiskerLeft leftWhisker rightWhisker body).symm)
        exact (ReseatCastKit.castBoundaryTrans _ _ _ _ _).trans
          (ReseatCastKit.castBoundaryTrans _ _ _ _ _).symm
  | vcompCongrLeft cellBeta _ ih => exact TwoCellConvFull.vcompCongrLeft (reseatCell cellBeta) ih
  | vcompCongrRight cellAlpha _ ih => exact TwoCellConvFull.vcompCongrRight (reseatCell cellAlpha) ih
  | whiskerLeftCongr oneCell _ ih =>
      exact ReseatCastKit.castBoundaryCongr _ _
        (TwoCellConvFull.whiskerLeftCongr (reseatPath oneCell) ih)
  | whiskerRightCongr oneCell _ ih =>
      exact ReseatCastKit.castBoundaryCongr _ _
        (TwoCellConvFull.whiskerRightCongr (reseatPath oneCell) ih)
  | refl cell => exact TwoCellConvFull.refl (reseatCell cell)
  | symm _ ih => exact TwoCellConvFull.symm ih
  | trans _ _ ih1 ih2 => exact TwoCellConvFull.trans ih1 ih2

/-! ## P2 — the reconstructed monad law cells + the reconstructed law relation -/

/-- The reconstructed monad unit `eta` as a free 2-cell `id ⇒ t` over `monadComputad.toModeSignature`. -/
def reconEta :
    RawTwoCellExpr monadComputad.toModeSignature
      (ModalityPath.nil (graph := monadComputad.toModeGraph) (⟨0, by decide⟩ : Fin 1))
      monadComputadReconstructedT :=
  RawTwoCellExpr.gen monadComputadReconstructsUnit

/-- The reconstructed monad multiplication `mu` as a free 2-cell `t·t ⇒ t`. -/
def reconMu :
    RawTwoCellExpr monadComputad.toModeSignature
      monadComputadReconstructedTT monadComputadReconstructedT :=
  RawTwoCellExpr.gen monadComputadReconstructsMult

/-- The reconstructed identity 2-cell on `t` (the RHS of both unit laws). -/
def reconIdTCell :
    RawTwoCellExpr monadComputad.toModeSignature
      monadComputadReconstructedT monadComputadReconstructedT :=
  RawTwoCellExpr.id (signature := monadComputad.toModeSignature) monadComputadReconstructedT

/-- The reconstructed left-unit composite `mu . (eta |> t)` — a 2-cell `t ⇒ t`. -/
def reconLeftUnitCell :
    RawTwoCellExpr monadComputad.toModeSignature
      monadComputadReconstructedT monadComputadReconstructedT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := monadComputad.toModeSignature)
      monadComputadReconstructedT reconEta)
    reconMu

/-- The reconstructed right-unit composite `mu . (t <| eta)` — a 2-cell `t ⇒ t`. -/
def reconRightUnitCell :
    RawTwoCellExpr monadComputad.toModeSignature
      monadComputadReconstructedT monadComputadReconstructedT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := monadComputad.toModeSignature)
      monadComputadReconstructedT reconEta)
    reconMu

/-- The reconstructed left-associativity composite `mu . (mu |> t)` — a 2-cell `t·t·t ⇒ t`. -/
def reconAssocLeftCell :
    RawTwoCellExpr monadComputad.toModeSignature
      (composePath monadComputadReconstructedTT monadComputadReconstructedT)
      monadComputadReconstructedT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := monadComputad.toModeSignature)
      monadComputadReconstructedT reconMu)
    reconMu

/-- The reconstructed right-associativity composite `mu . (t <| mu)` — a 2-cell `t·t·t ⇒ t` (source
`t·(t·t)` DEFINITIONALLY `(t·t)·t`). -/
def reconAssocRightCell :
    RawTwoCellExpr monadComputad.toModeSignature
      (composePath monadComputadReconstructedTT monadComputadReconstructedT)
      monadComputadReconstructedT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := monadComputad.toModeSignature)
      monadComputadReconstructedT reconMu)
    reconMu

/-- ★ **The reconstructed walking-monad law relation** — the three monad laws stated over the RECONSTRUCTED
signature `monadComputad.toModeSignature` as a `CellRel`, the reconstructed mirror of the bespoke `MonadLawRel`.
The base relation for `reseatConvForward`. -/
inductive MonadLawRelReconstructed :
    {sourceMode targetMode : monadComputad.toModeSignature.graph.Mode} →
    {sourcePath targetPath : ModalityPath monadComputad.toModeSignature.graph sourceMode targetMode} →
    RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath →
    RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath → Prop where
  /-- The reconstructed left-unit law `mu . (eta |> t) ~ id_t`. -/
  | leftUnit : MonadLawRelReconstructed reconLeftUnitCell reconIdTCell
  /-- The reconstructed right-unit law `mu . (t <| eta) ~ id_t`. -/
  | rightUnit : MonadLawRelReconstructed reconRightUnitCell reconIdTCell
  /-- The reconstructed associativity law `mu . (mu |> t) ~ mu . (t <| mu)`. -/
  | assoc : MonadLawRelReconstructed reconAssocLeftCell reconAssocRightCell

/-! ## P2 — the propositional law-cell equalities `reseatCell reconLawCell = bespokeLawCell`

The r3 "second obstruction": `reseatCell` of a reconstructed law cell is only PROPOSITIONALLY the bespoke law
cell.  The whisker `castBoundary`s collapse definitionally (every path is a `t`-power, so `reseatPath_composePath`
on them is `rfl`), and `reseatPath reconT` reduces to `monadT` — so `reseatCell reconLawCell` reduces DEFINITIONALLY
to the bespoke shape with `reseatGen`-image generators, leaving exactly the two generator inversions
(`reseatGen_unit_isEta` / `reseatGen_mult_isMu`) as the residual rewrites. -/

/-- `reseatCell` of the reconstructed unit IS the bespoke unit 2-cell (the `eta` inversion). -/
theorem reseatCell_reconEta : reseatCell reconEta = monadUnitTwoCell :=
  congrArg RawTwoCellExpr.gen reseatGen_unit_isEta

/-- `reseatCell` of the reconstructed multiplication IS the bespoke multiplication 2-cell (the `mu` inversion). -/
theorem reseatCell_reconMu : reseatCell reconMu = monadMulTwoCell :=
  congrArg RawTwoCellExpr.gen reseatGen_mult_isMu

/-- `reseatCell` of the reconstructed identity 2-cell IS the bespoke identity 2-cell (`rfl`: `reseatPath reconT`
reduces to `monadT`). -/
theorem reseatCell_reconIdT : reseatCell reconIdTCell = monadIdTCell := rfl

/-! The law-cell bridge is taken at the CONV level (not as a raw `reseatCell reconLawCell = bespokeLawCell`
equality — the dependent generator rewrite through `composePath nil`-collapsed whisker boundaries is brittle).
Each reconstructed law composite reseats DEFINITIONALLY to the bespoke shape carrying `reseatCell`-image generators
(the `castBoundary`s collapse — `reseatPath_composePath` on `t`-powers is `rfl` — and `reseatPath reconT` reduces
to `monadT`); the two generator inversions `reseatCell_reconEta` / `reseatCell_reconMu` are lifted to
`TwoCellConvFull` by `convFullOfCellEq`, then whiskered / vcomp'd through `SaturatedConvOver`'s own congruences to
reach the bespoke law composite, and chained with the bespoke `MonadLawRel` row. -/

/-- The reconstructed left-unit law holds in the bespoke saturated conv, at the `reseatCell`-image boundary. -/
theorem reconLeftUnitConv :
    SaturatedConvOver monadModeSignature MonadLawRel (reseatCell reconLeftUnitCell) (reseatCell reconIdTCell) :=
  SaturatedConvOver.trans
    (SaturatedConvOver.trans
      (SaturatedConvOver.vcompCongrLeft (reseatCell reconMu)
        (SaturatedConvOver.whiskerRightCongr monadT
          (SaturatedConvOver.ofFull (ReseatCastKit.convFullOfCellEq reseatCell_reconEta))))
      (SaturatedConvOver.vcompCongrRight (RawTwoCellExpr.whiskerRight monadT monadUnitTwoCell)
        (SaturatedConvOver.ofFull (ReseatCastKit.convFullOfCellEq reseatCell_reconMu))))
    (SaturatedConvOver.ofRelation MonadLawRel.leftUnit)

/-- The reconstructed right-unit law holds in the bespoke saturated conv. -/
theorem reconRightUnitConv :
    SaturatedConvOver monadModeSignature MonadLawRel (reseatCell reconRightUnitCell) (reseatCell reconIdTCell) :=
  SaturatedConvOver.trans
    (SaturatedConvOver.trans
      (SaturatedConvOver.vcompCongrLeft (reseatCell reconMu)
        (SaturatedConvOver.whiskerLeftCongr monadT
          (SaturatedConvOver.ofFull (ReseatCastKit.convFullOfCellEq reseatCell_reconEta))))
      (SaturatedConvOver.vcompCongrRight (RawTwoCellExpr.whiskerLeft monadT monadUnitTwoCell)
        (SaturatedConvOver.ofFull (ReseatCastKit.convFullOfCellEq reseatCell_reconMu))))
    (SaturatedConvOver.ofRelation MonadLawRel.rightUnit)

/-- The reconstructed associativity law holds in the bespoke saturated conv. -/
theorem reconAssocConv :
    SaturatedConvOver monadModeSignature MonadLawRel
      (reseatCell reconAssocLeftCell) (reseatCell reconAssocRightCell) :=
  SaturatedConvOver.trans
    (SaturatedConvOver.trans
      (SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrLeft (reseatCell reconMu)
          (SaturatedConvOver.whiskerRightCongr monadT
            (SaturatedConvOver.ofFull (ReseatCastKit.convFullOfCellEq reseatCell_reconMu))))
        (SaturatedConvOver.vcompCongrRight (RawTwoCellExpr.whiskerRight monadT monadMulTwoCell)
          (SaturatedConvOver.ofFull (ReseatCastKit.convFullOfCellEq reseatCell_reconMu))))
      (SaturatedConvOver.ofRelation MonadLawRel.assoc))
    (SaturatedConvOver.symm
      (SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrLeft (reseatCell reconMu)
          (SaturatedConvOver.whiskerLeftCongr monadT
            (SaturatedConvOver.ofFull (ReseatCastKit.convFullOfCellEq reseatCell_reconMu))))
        (SaturatedConvOver.vcompCongrRight (RawTwoCellExpr.whiskerLeft monadT monadMulTwoCell)
          (SaturatedConvOver.ofFull (ReseatCastKit.convFullOfCellEq reseatCell_reconMu)))))

/-! ## P2 — the FORWARD conv transport + the isFalse-leg refutation -/

/-- The absorbing congruence for the reseat forward transport — the reconstructed mirror of `mapCellAlongCongruence`:
`ofFull` via the P1a functoriality `reseatCell_preservesConv`; `ofRelation` via the three law-cell equalities; the
two `vcomp` congruences cast-free; the two `whisker` congruences through `SaturatedConvOver.castBoundaryCongr`
(since `reseatCell` of a whiskering carries the `reseatPath_composePath` cast); `refl`/`symm`/`trans` structural. -/
def reseatCongruence :
    IsSaturatedCongruence monadComputad.toModeSignature MonadLawRelReconstructed
      (fun cellA cellB =>
        SaturatedConvOver monadModeSignature MonadLawRel (reseatCell cellA) (reseatCell cellB)) where
  ofFull full := SaturatedConvOver.ofFull (reseatCell_preservesConv full)
  ofRelation row :=
    match row with
    | MonadLawRelReconstructed.leftUnit => reconLeftUnitConv
    | MonadLawRelReconstructed.rightUnit => reconRightUnitConv
    | MonadLawRelReconstructed.assoc => reconAssocConv
  vcompCongrLeft {_ _ _ _ _ _ _ cellBeta} ih := SaturatedConvOver.vcompCongrLeft (reseatCell cellBeta) ih
  vcompCongrRight {_ _ _ _ _ cellAlpha _ _} ih := SaturatedConvOver.vcompCongrRight (reseatCell cellAlpha) ih
  whiskerLeftCongr {_ _ _ oneCell _ _ _ _} ih :=
    SaturatedConvOver.castBoundaryCongr _ _ (SaturatedConvOver.whiskerLeftCongr (reseatPath oneCell) ih)
  whiskerRightCongr {_ _ _ _ _ oneCell _ _} ih :=
    SaturatedConvOver.castBoundaryCongr _ _ (SaturatedConvOver.whiskerRightCongr (reseatPath oneCell) ih)
  refl cell := SaturatedConvOver.refl (reseatCell cell)
  symm ih := SaturatedConvOver.symm ih
  trans ihLeft ihRight := SaturatedConvOver.trans ihLeft ihRight

/-- ★★ **The FORWARD reseat conv transport** — a reconstructed saturated convertibility transports along
`reseatCell` to the bespoke image: `SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed a b
==> SaturatedConvOver monadModeSignature MonadLawRel (reseatCell a) (reseatCell b)`.  Via the universal property
`SaturatedConvOver.recInto` with `reseatCongruence`.  The isFalse-leg direction of the reconstructed decider. -/
theorem reseatConvForward {sourceMode targetMode : monadComputad.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadComputad.toModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath}
    (conv : SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed cellAlpha cellBeta) :
    SaturatedConvOver monadModeSignature MonadLawRel (reseatCell cellAlpha) (reseatCell cellBeta) :=
  SaturatedConvOver.recInto reseatCongruence conv

/-- ★ **The reseat's isFalse leg, made literal** — a reconstructed candidate pair whose `reseatCell`-images the
bespoke walking-monad decider refutes is refuted at the reconstructed signature: any hypothetical reconstructed
convertibility would transport forward (`reseatConvForward`) into the refuted bespoke convertibility. -/
theorem monadReconRefutes {sourceMode targetMode : monadComputad.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadComputad.toModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath}
    (refuted : ¬ SaturatedConvOver monadModeSignature MonadLawRel (reseatCell cellAlpha) (reseatCell cellBeta)) :
    ¬ SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed cellAlpha cellBeta :=
  fun conv => refuted (reseatConvForward conv)

/-! ## Observability -/

-- The reconstructed `t·t` path has length 2 (two `t`-generators): expect `2`.
#eval monadComputadReconstructedTT.length
-- Its `reseatPath`-image also has length 2 (`reseatPath` counts length): expect `2`.
#eval (reseatPath monadComputadReconstructedTT).length
-- The reconstructed multiplication is 2-generator index `1`: expect `1`.
#eval monadComputadReconstructsMult.val.val
-- The reconstructed unit is 2-generator index `0`: expect `0`.
#eval monadComputadReconstructsUnit.val.val

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the FORWARD reseat FUNCTOR ships, and it is fib-3-DECOUPLED (MODE-ADMIT r3).**  The
FIXED-pair `(monadComputad.toModeSignature, monadModeSignature)` reseat's forward half is BUILT and zero-axiom:
the 1-cell functor `reseatPath` (reconstructed `t`-powers to bespoke `t`-powers, reducing definitionally —
`reseatPath_reconT` / `reseatPath_reconTT` by `rfl`), the dependent-witness collapse `reseatInterp`, the boundary
cast `castMonadTwoCell`, THE CRUX `reseatGen` (the `twoCellEquiv` FORWARD half: a reconstructed generating 2-cell
maps to `eta` / `mu` at the interpreter-pinned boundary), verified on BOTH generators
(`reseatGen_unit_isEta`, `reseatGen_mult_isMu`, read off the codomain's boundary uniqueness), and the free 2-cell
functor `reseatCell` (lifting `reseatGen` over the whole grammar, `gen`/`id`/`vcomp` + the two whisker
`castBoundary` cases through `reseatPath_composePath`).

This SHARPENS `DeciderReseat.lean`'s framing (`fxAmalg_hasReconstructionDecoderReseat`, "coupled to
`fxMode_hasDecidableTwoCellEquality` (fib-3)"): the forward reseat decides NO 2-cell equality modulo the 3-cell
laws — it is a finite generator data-iso (`reseatGen` cases the 2-generator index over `Fin 2`) plus a structural
cell functor.  So the reseat is fib-3-DECOUPLED; the residual is cast LABOR, not undecidability.  `= true`. -/
def fxAmalg_hasForwardReseatFunctor : Bool := true

/-- ★★ **Honesty marker (`true`, MODE-ADMIT r4) — the FORWARD reseat CONV TRANSPORT SHIPS.**  The forward conv
transport `SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed a b ==> SaturatedConvOver
monadModeSignature MonadLawRel (reseatCell a) (reseatCell b)` is now BUILT (`reseatConvForward`, `recInto` into the
`reseatCell`-image congruence `reseatCongruence`).  Its linchpin is `reseatCell` preserving `TwoCellConvFull` —
the thirteen-constructor structural functoriality `reseatCell_preservesConv`, the reseat analogue of the shipped
`mapTwoCellConvFull` ported arm-for-arm (untypable via `mapCellAlong` because `monadModeSignature` is not a
`_.toModeSignature`, so re-derived here; `TwoCellConvFull` is law-free, so no arm needs a monad coherence — pure
cast LABOR, as predicted).  The r3 "second obstruction" (`reseatCell reconLawCell` only PROPOSITIONALLY the bespoke
law cell) is discharged at the CONV level: the three law-cell bridges `reconLeftUnitConv` / `reconRightUnitConv` /
`reconAssocConv` lift the generator inversions `reseatCell_reconEta` / `reseatCell_reconMu` through
`SaturatedConvOver`'s own congruences to the bespoke `MonadLawRel` rows.  The `monadReconRefutes` isFalse leg is
literal.  fib-3-DECOUPLED (no 2-cell equality modulo the 3-cell laws is decided), all `Eq.rec` / no `HEq`.  The
FULL two-sided decider (`fxAmalg_hasReconstructionDecoderReseat` in `DeciderReseat.lean`,
`fxModeAdmit_hasRenamingDeciderTransport` in `ModeAdmit.lean`) additionally needs the isTrue leg's BACKWARD
round-trip `reseatCellInv (reseatCell a) = a` — the remaining walled labor.  `= true`. -/
def fxAmalg_hasReseatConvTransport : Bool := true

/-- ★ **Honesty marker (`false`) — the WIRED inheritance pipeline (recognise → witness → transport → decide) is
NOT one term yet (r4: the isFalse HALF now ships).**  MODE-ADMIT r2 ships recognise (`admitByRowAware`) →
registered-family retrieval (running the bespoke decider on the walker's OWN cells); r3 ships the forward reseat
FUNCTOR (`reseatCell`); r4 ships the forward CONV TRANSPORT (`reseatConvForward`) and thereby the isFalse leg of a
reconstructed-signature decision literally (`monadReconRefutes`: a reconstructed pair whose `reseatCell`-images the
bespoke decider refutes is refuted at the reconstructed signature).  What remains for a SINGLE term that decides a
CANDIDATE's own reconstructed pair (both verdicts) is the isTrue leg: the backward functor `reseatCellInv` + the
round-trip `reseatCellInv (reseatCell a) = a` + the reverse conv induction (the P1a mirror over `reseatCellInv`) —
a genuine multi-lemma inverse-functor file, bounded cast LABOR (all `Eq.rec`, fib-3-decoupled), NOT a mathematical
wall.  Until it ships the pipeline decides only the isFalse direction of a candidate's reconstructed pair (plus
recognise + retrieve for the registered walkers).  `= false`. -/
def fxModeAdmit_hasWiredInheritancePipeline : Bool := false

end FX1Poly.Polygraph.Amalgam
