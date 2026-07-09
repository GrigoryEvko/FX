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

/-- ★ **Honesty marker (`false`) — the reseat CONV TRANSPORT (hence the reconstructed decider) is the LABOR
residual.**  Transporting a verdict onto `monadComputad.toModeSignature` needs the FORWARD conv transport
`SaturatedConvOver monadComputad.toModeSignature baseRel a b ==> SaturatedConvOver monadModeSignature MonadLawRel
(reseatCell a) (reseatCell b)` (`recInto` into the `reseatCell`-image congruence), whose linchpin is
`reseatCell` preserving `TwoCellConvFull` — the 12-constructor structural functoriality (the `whiskerLeftComp` /
`whiskerRightComp` / `whiskerExchange` cases carry `composePath`-associativity `castBoundary` reconciliations).
The shipped analogue `mapCellAlong_preservesConvUnconditional` (via `mapTwoCellConvFull`) does exactly this for a
`ComputadMorphismTwo`, but CANNOT be reused: `reseatCell` lands in the BESPOKE `monadModeSignature`, which is not
a `_.toModeSignature`, so it is not a `mapCellAlong`.  A second obstruction: `reseatGen` produces a boundary cast
that does not reduce definitionally (the matcher stalls on the dependent motive), so `reseatCell (reconLawCell) =
bespokeLawCell` is PROPOSITIONAL (read off the generator inversions + a reflexive-`castBoundary` collapse), not
`rfl` — threading it through the three law rows is further labor.  Both are cast LABOR (all `Eq.rec`, no `HEq`,
since after `reseatPath` both cells live at one signature), fib-3-DECOUPLED — NOT undecidability.  The isTrue leg
additionally needs the BACKWARD round-trip `reseatCellInv (reseatCell a) = a`.  Until the functoriality ships,
`fxAmalg_hasReconstructionDecoderReseat` (`DeciderReseat.lean`) and `fxModeAdmit_hasRenamingDeciderTransport`
(`ModeAdmit.lean`) stay `false`.  `= false`. -/
def fxAmalg_hasReseatConvTransport : Bool := false

/-- ★ **Honesty marker (`false`) — the WIRED inheritance pipeline (recognise → witness → transport → decide) is
NOT one term yet.**  MODE-ADMIT r2 ships recognise (`admitByRowAware`) → registered-family retrieval (running the
bespoke decider on the walker's OWN cells); r3 ships the forward reseat FUNCTOR (`reseatCell`), the missing
"transport" leg's forward half.  Wiring the four legs into a single term that RECOGNISES a presented mode theory,
witnesses the reseat, TRANSPORTS a candidate's cells to the bespoke decider, and returns a verdict on the
CANDIDATE's own reconstructed cells requires the `fxAmalg_hasReseatConvTransport` functoriality above (the isFalse
leg) and the backward round-trip (the isTrue leg).  Until both ship the pipeline cannot decide a candidate's
reconstructed pair, only recognise + retrieve.  `= false`. -/
def fxModeAdmit_hasWiredInheritancePipeline : Bool := false

end FX1Poly.Polygraph.Amalgam
