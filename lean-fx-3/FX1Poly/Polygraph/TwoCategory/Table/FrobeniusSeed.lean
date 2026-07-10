import FX1Poly.Polygraph.TwoCategory.Table.ContextClosure

/-! # Polygraph/TwoCategory/Table/FrobeniusSeed — the symbolic Frobenius spider congruence over the generic
carrier + the SUFFIX-congruence corollary (POLY-TAB r0, the SEED instantiation + FALSIFIABILITY CHECK)

`Frobenius/SpiderPresentation.lean` shipped the special-commutative-Frobenius presentation VALUE-LEVEL (the
thirteen rows as `BrauerRelation` words over `List BrauerAtom`), and explicitly DEFERRED the symbolic congruence:
`fxFrob_hasSymbolicSaturatedConvOver = false`, "the `ModeSignature` (one self-dual object + self-dual 1-cell `t`)
+ `FrobeniusLawRel : CellRel` + `SaturatedConvOver` instance (mirroring `Amalgam/SaturatedOver.lean`'s monad
exemplar) are deferred".  This file ships that seed — the Frobenius walker BORN on the generic
`SaturatedConvOver` carrier (`ContextClosure.lean` / `SaturatedOver.lean`), not as a bespoke inductive.

## The signature (one object, one self-dual endo-1-cell `t`)

Same underlying quiver as the walking monad — one mode `point`, one endo-generator `t : point -> point` — with
FOUR generating 2-cells:

  * `mult   : t.t => t`   (multiplication mu),
  * `comult : t => t.t`   (comultiplication delta),
  * `unit   : id => t`    (unit eta),
  * `counit : t => id`    (counit epsilon).

## The law relation (the r10-relevant core rows, POLY-TAB r0)

`FrobeniusLawRel` carries FOUR rows — the fragment that exercises the row-suffix wall the word-carrier route hit:

  * `unitLeft`  `mult . (unit |> t) ~ id_t`             (left unit),
  * `frobLeft`  `(mult |> t) . (t <| comult) ~ comult . mult`   (the Carboni-Walters "S=X" Frobenius law),
  * `frobRight` `(t <| mult) . (comult |> t) ~ comult . mult`   (the other orientation),
  * `special`   `comult . mult ~ id_t` ... i.e. `mult . comult ~ id_t` (the diamond=1 special law).

The remaining nine Frobenius rows (associativity, coassociativity, the counit laws, commutativity,
Yang-Baxter, involution) are POLY-TAB-1 wave work — each is another `FrobeniusLawRel` constructor with a concrete
`t`-power cell pair; none needs new machinery.

## THE FALSIFIABILITY CHECK (the r10 wall)

`Frobenius/SpiderCrossingRerun.lean` walled `RowSuffixCongruence` at the constructor level
(`fxFrob_hasRowLevelSuffixCongruence = false`) and named the fix: "only a table REDESIGN (a suffix-parametric
firing, `prefix ++ row ++ suffix`) would open it".  `SaturatedConvOver` IS that redesign.
`frobeniusSpiderConv_suffixCongruence` (below) is the walled brick's exact conclusion shape landed in ONE
constructor (`whiskerRightCongr`), non-vacuously (a genuine Frobenius `frobLeft` row whiskered by a suffix stays
convertible).  If it had NOT fallen out, this file would instead document the friction; it FELL OUT.

## Definitional-boundary note

Every law cell is a concrete `t`-power composite, so `composePath` associativity (`t.(t.t) = (t.t).t`) holds
DEFINITIONALLY (as the monad exemplar `MonadSaturatedConv.lean` already relies on) — no `HEq` / `castBoundary`
friction arises, exactly the `medium`-flagged risk that did NOT materialize.

Raw Lean 4 + Init; the signature and law relation are inductives, the corollaries are single generic
constructors, so every declaration is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.
Additive: nothing outside `Table/` is touched.  Per-declaration `#assert_no_axioms` in the audit twin. -/

namespace FX1Poly.Polygraph

open FX1Poly.Polygraph.Amalgam

/-! ## The walking-spider quiver: one object, one self-dual endo-generator -/

/-- The single mode (0-cell) of the walking Frobenius spider. -/
inductive FrobeniusMode where
  /-- The unique self-dual object. -/
  | point

/-- The single generating modality (1-cell): the self-dual endo-generator `t : point -> point`. -/
inductive FrobeniusModality : FrobeniusMode → FrobeniusMode → Type where
  /-- The generating endo-1-cell `t`. -/
  | t : FrobeniusModality FrobeniusMode.point FrobeniusMode.point

/-- The walking-spider quiver: one mode, one endo-modality. -/
def frobeniusGraph : ModeGraph where
  Mode := FrobeniusMode
  Modality := FrobeniusModality

/-- The generating endo-1-cell `t` as the length-1 path. -/
def frobeniusT : ModalityPath frobeniusGraph FrobeniusMode.point FrobeniusMode.point :=
  singletonModalityPath FrobeniusModality.t

/-- The composite 1-cell `t.t` (length 2) — the source of `mult`, the target of `comult`. -/
def frobeniusTThenT : ModalityPath frobeniusGraph FrobeniusMode.point FrobeniusMode.point :=
  composePath frobeniusT frobeniusT

/-! ## The four generating 2-cells -/

/-- The four generating 2-cells of the walking Frobenius spider — multiplication, comultiplication, unit, counit,
between parallel `t`-power paths.  These are the GENERATORS only; the doctrine LAWS are `FrobeniusLawRel`. -/
inductive FrobeniusTwoCell :
    {sourceMode targetMode : FrobeniusMode} →
    ModalityPath frobeniusGraph sourceMode targetMode →
    ModalityPath frobeniusGraph sourceMode targetMode → Type where
  /-- The **multiplication** `mult : t.t => t`. -/
  | mult : FrobeniusTwoCell frobeniusTThenT frobeniusT
  /-- The **comultiplication** `comult : t => t.t`. -/
  | comult : FrobeniusTwoCell frobeniusT frobeniusTThenT
  /-- The **unit** `unit : id_point => t`. -/
  | unit : FrobeniusTwoCell (ModalityPath.nil (graph := frobeniusGraph) FrobeniusMode.point) frobeniusT
  /-- The **counit** `counit : t => id_point`. -/
  | counit : FrobeniusTwoCell frobeniusT (ModalityPath.nil (graph := frobeniusGraph) FrobeniusMode.point)

/-- ★ The **walking Frobenius spider mode signature** — one object, one self-dual endo-1-cell `t`, and the four
mult / comult / unit / counit 2-cell generators.  The signature the symbolic Frobenius congruence rides. -/
def frobeniusModeSignature : ModeSignature where
  graph := frobeniusGraph
  twoCell := fun firstPath secondPath => FrobeniusTwoCell firstPath secondPath

/-! ## The generators + the law composites as free 2-cells -/

/-- The generator `mult` as a free 2-cell `t.t => t`. -/
def frobeniusMultCell : RawTwoCellExpr frobeniusModeSignature frobeniusTThenT frobeniusT :=
  RawTwoCellExpr.gen FrobeniusTwoCell.mult

/-- The generator `comult` as a free 2-cell `t => t.t`. -/
def frobeniusComultCell : RawTwoCellExpr frobeniusModeSignature frobeniusT frobeniusTThenT :=
  RawTwoCellExpr.gen FrobeniusTwoCell.comult

/-- The generator `unit` as a free 2-cell `id => t`. -/
def frobeniusUnitCell :
    RawTwoCellExpr frobeniusModeSignature
      (ModalityPath.nil (graph := frobeniusGraph) FrobeniusMode.point) frobeniusT :=
  RawTwoCellExpr.gen FrobeniusTwoCell.unit

/-- The generator `counit` as a free 2-cell `t => id`. -/
def frobeniusCounitCell :
    RawTwoCellExpr frobeniusModeSignature frobeniusT
      (ModalityPath.nil (graph := frobeniusGraph) FrobeniusMode.point) :=
  RawTwoCellExpr.gen FrobeniusTwoCell.counit

/-- The identity 2-cell on `t` (the RHS of the unit and special laws). -/
def frobeniusIdTCell : RawTwoCellExpr frobeniusModeSignature frobeniusT frobeniusT :=
  RawTwoCellExpr.id (signature := frobeniusModeSignature) frobeniusT

/-- The **left-unit composite** `mult . (unit |> t) : t => t` — the unit whiskered on the right by `t`, then the
multiplication.  The `unitLeft` law asserts it is `id_t`. -/
def frobeniusUnitLeftCell : RawTwoCellExpr frobeniusModeSignature frobeniusT frobeniusT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := frobeniusModeSignature) frobeniusT frobeniusUnitCell)
    frobeniusMultCell

/-- The **Frobenius "S=X" left composite** `(mult |> t) . (t <| comult) : t.t => t.t` — comultiply the right
strand (`t <| comult`), then multiply the left pair (`mult |> t`). -/
def frobeniusLeftLhsCell : RawTwoCellExpr frobeniusModeSignature frobeniusTThenT frobeniusTThenT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerLeft (signature := frobeniusModeSignature) frobeniusT frobeniusComultCell)
    (RawTwoCellExpr.whiskerRight (signature := frobeniusModeSignature) frobeniusT frobeniusMultCell)

/-- The **Frobenius "S=X" right composite** `(t <| mult) . (comult |> t) : t.t => t.t` — the other orientation. -/
def frobeniusRightLhsCell : RawTwoCellExpr frobeniusModeSignature frobeniusTThenT frobeniusTThenT :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.whiskerRight (signature := frobeniusModeSignature) frobeniusT frobeniusComultCell)
    (RawTwoCellExpr.whiskerLeft (signature := frobeniusModeSignature) frobeniusT frobeniusMultCell)

/-- The **Frobenius "H element"** `comult . mult : t.t => t.t` — the shared RHS of both Frobenius orientations. -/
def frobeniusHCell : RawTwoCellExpr frobeniusModeSignature frobeniusTThenT frobeniusTThenT :=
  RawTwoCellExpr.vcomp frobeniusMultCell frobeniusComultCell

/-- The **special composite** `comult . mult : t => t` reading `t => t.t => t` — the diamond.  The `special` law
asserts it is `id_t`. -/
def frobeniusSpecialCell : RawTwoCellExpr frobeniusModeSignature frobeniusT frobeniusT :=
  RawTwoCellExpr.vcomp frobeniusComultCell frobeniusMultCell

/-! ## The Frobenius law relation (the r10-relevant core rows) -/

/-- ★ The **walking Frobenius spider's core laws as a `CellRel`** — the fragment that exercises the row-suffix
wall: left unit, the two Frobenius "S=X" orientations, and the special law.  The base relation for which
`SaturatedConvOver frobeniusModeSignature FrobeniusLawRel` is the symbolic Frobenius spider congruence.  The
remaining nine rows of the special-Frobenius presentation are POLY-TAB-1 additions (each another constructor). -/
inductive FrobeniusLawRel :
    {sourceMode targetMode : FrobeniusMode} →
    {sourcePath targetPath : ModalityPath frobeniusGraph sourceMode targetMode} →
    RawTwoCellExpr frobeniusModeSignature sourcePath targetPath →
    RawTwoCellExpr frobeniusModeSignature sourcePath targetPath → Prop where
  /-- The left-unit law `mult . (unit |> t) ~ id_t`. -/
  | unitLeft : FrobeniusLawRel frobeniusUnitLeftCell frobeniusIdTCell
  /-- The Frobenius "S=X" law `(mult |> t) . (t <| comult) ~ comult . mult` (Carboni-Walters). -/
  | frobLeft : FrobeniusLawRel frobeniusLeftLhsCell frobeniusHCell
  /-- The Frobenius law, other orientation `(t <| mult) . (comult |> t) ~ comult . mult`. -/
  | frobRight : FrobeniusLawRel frobeniusRightLhsCell frobeniusHCell
  /-- The special law `comult . mult ~ id_t` (diamond = 1). -/
  | special : FrobeniusLawRel frobeniusSpecialCell frobeniusIdTCell

/-- ★ The **symbolic walking-Frobenius-spider 2-cell convertibility** — the generic saturated convertibility at
`FrobeniusLawRel`.  This is the r2 deliverable `Frobenius/SpiderPresentation.lean` deferred
(`fxFrob_hasSymbolicSaturatedConvOver`), now BORN on the generic carrier with zero bespoke inductive. -/
abbrev FrobeniusSpiderConv {sourceMode targetMode : FrobeniusMode}
    {sourcePath targetPath : ModalityPath frobeniusGraph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr frobeniusModeSignature sourcePath targetPath) : Prop :=
  SaturatedConvOver frobeniusModeSignature FrobeniusLawRel cellAlpha cellBeta

/-! ## The four laws hold in the symbolic congruence -/

/-- The left-unit law holds symbolically. -/
theorem frobeniusUnitLeftHolds : FrobeniusSpiderConv frobeniusUnitLeftCell frobeniusIdTCell :=
  SaturatedConvOver.ofRelation FrobeniusLawRel.unitLeft

/-- The Frobenius "S=X" law holds symbolically. -/
theorem frobeniusFrobLeftHolds : FrobeniusSpiderConv frobeniusLeftLhsCell frobeniusHCell :=
  SaturatedConvOver.ofRelation FrobeniusLawRel.frobLeft

/-- The other Frobenius orientation holds symbolically. -/
theorem frobeniusFrobRightHolds : FrobeniusSpiderConv frobeniusRightLhsCell frobeniusHCell :=
  SaturatedConvOver.ofRelation FrobeniusLawRel.frobRight

/-- The special law holds symbolically. -/
theorem frobeniusSpecialHolds : FrobeniusSpiderConv frobeniusSpecialCell frobeniusIdTCell :=
  SaturatedConvOver.ofRelation FrobeniusLawRel.special

/-- The two Frobenius orientations are convertible to EACH OTHER (both collapse to `comult . mult`), chaining the
two "S=X" rows through the shared `H` element — a genuine derived Frobenius coherence. -/
theorem frobeniusOrientationsCohere : FrobeniusSpiderConv frobeniusLeftLhsCell frobeniusRightLhsCell :=
  SaturatedConvOver.trans (SaturatedConvOver.ofRelation FrobeniusLawRel.frobLeft)
    (SaturatedConvOver.symm (SaturatedConvOver.ofRelation FrobeniusLawRel.frobRight))

/-! ## THE FALSIFIABILITY CHECK — the row-suffix congruence FALLS OUT -/

/-- ★★ **The Frobenius row-SUFFIX congruence — the r10 wall, DISSOLVED.**  A symbolic Frobenius convertibility
whiskered by any in-scope suffix stays a symbolic Frobenius convertibility.  This is the exact conclusion shape
of the walled `RowSuffixCongruence` (`Frobenius/SpiderCrossingRerun.lean`,
`fxFrob_hasRowLevelSuffixCongruence = false`) — but here it is ONE generic constructor, because the free-2-cell
carrier never bakes a prefix into a firing.  The word-carried `SpiderConvRows` could not re-fire a row past a
common suffix; `SaturatedConvOver.whiskerRightCongr` fires the suffix as a first-class congruence.  FALSIFIABILITY:
this was the check the recon flagged `medium` (the B->A rebase risk); it FELL OUT. -/
theorem frobeniusSpiderConv_suffixCongruence {sourceMode middleMode targetMode : FrobeniusMode}
    {oneCellF oneCellG : ModalityPath frobeniusGraph sourceMode middleMode}
    (suffix1Cell : ModalityPath frobeniusGraph middleMode targetMode)
    {cellAlpha cellAlpha' : RawTwoCellExpr frobeniusModeSignature oneCellF oneCellG}
    (conv : FrobeniusSpiderConv cellAlpha cellAlpha') :
    FrobeniusSpiderConv (RawTwoCellExpr.whiskerRight suffix1Cell cellAlpha)
      (RawTwoCellExpr.whiskerRight suffix1Cell cellAlpha') :=
  SaturatedConvOver.suffixCongruence suffix1Cell conv

/-- ★ The row-PREFIX congruence — the dual half, also one generic constructor. -/
theorem frobeniusSpiderConv_prefixCongruence {sourceMode middleMode targetMode : FrobeniusMode}
    (prefix1Cell : ModalityPath frobeniusGraph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath frobeniusGraph middleMode targetMode}
    {cellBeta cellBeta' : RawTwoCellExpr frobeniusModeSignature oneCellG oneCellH}
    (conv : FrobeniusSpiderConv cellBeta cellBeta') :
    FrobeniusSpiderConv (RawTwoCellExpr.whiskerLeft prefix1Cell cellBeta)
      (RawTwoCellExpr.whiskerLeft prefix1Cell cellBeta') :=
  SaturatedConvOver.prefixCongruence prefix1Cell conv

/-- ★ **Non-vacuity of the falsifiability check** — a GENUINE Frobenius `frobLeft` row, whiskered on the right by
`t`, is a symbolic Frobenius convertibility.  This is exactly what the walled `RowSuffixCongruence` could not
produce: a real law fired past a suffix, landing back in the congruence.  The suffix-congruence corollary is
populated, not empty. -/
theorem frobeniusSuffixCongruence_nonVacuous :
    FrobeniusSpiderConv
      (RawTwoCellExpr.whiskerRight (signature := frobeniusModeSignature) frobeniusT frobeniusLeftLhsCell)
      (RawTwoCellExpr.whiskerRight (signature := frobeniusModeSignature) frobeniusT frobeniusHCell) :=
  frobeniusSpiderConv_suffixCongruence frobeniusT frobeniusFrobLeftHolds

/-! ## The Eq-valued invariant fold, demonstrated at the Frobenius seed -/

/-- ★ **The invariant fold, instantiated at the Frobenius seed (a `size`-based sanity demo).**  The T3c fold
`rowConvInvariant_foldEq` needs no bespoke plumbing — feeding it any invariant plus its six preservation legs
yields invariance across the whole symbolic Frobenius congruence.  Here the demo invariant is the constant `Unit`
map, whose every leg is `rfl`; the real value-level Frobenius invariant (`extraSpiderDiagramOf`, over the word
carrier) is the POLY-TAB-1 instance once the B->A word interpreter is wired. -/
theorem frobeniusConstInvariant_fold {sourceMode targetMode : FrobeniusMode}
    {sourcePath targetPath : ModalityPath frobeniusGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr frobeniusModeSignature sourcePath targetPath}
    (conv : FrobeniusSpiderConv cellAlpha cellBeta) :
    (fun (_ : RawTwoCellExpr frobeniusModeSignature sourcePath targetPath) => ()) cellAlpha
      = (fun _ => ()) cellBeta :=
  rowConvInvariant_foldEq
    (invariantOf := fun _ => ())
    (fullPreserves := fun _ => rfl)
    (rowsPreserve := fun _ => rfl)
    (vcompLeftPreserves := fun _ => rfl)
    (vcompRightPreserves := fun _ => rfl)
    (prefixPreserves := fun _ => rfl)
    (suffixPreserves := fun _ => rfl)
    conv

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the symbolic Frobenius spider `SaturatedConvOver` congruence SHIPS (POLY-TAB r0, T3b).**
The walking-Frobenius-spider signature (`frobeniusModeSignature`: one self-dual object + endo-1-cell `t`, four
mult / comult / unit / counit generators), the core law relation (`FrobeniusLawRel`: unitLeft, frobLeft, frobRight,
special), and the symbolic congruence `FrobeniusSpiderConv = SaturatedConvOver frobeniusModeSignature
FrobeniusLawRel` are shipped, with all four laws holding and the derived orientation-coherence.  This is the r2
deliverable `Frobenius/SpiderPresentation.lean` deferred (`fxFrob_hasSymbolicSaturatedConvOver`), landed on the
generic carrier with ZERO bespoke inductive.  The remaining nine special-Frobenius rows are POLY-TAB-1 additions.
`= true`. -/
def fxTab_hasFrobeniusSymbolicCongruence : Bool := true

/-- ★★ **Honesty marker — the FALSIFIABILITY CHECK PASSED: the r10 row-suffix wall dissolves at Frobenius.**
`frobeniusSpiderConv_suffixCongruence` lands the walled `RowSuffixCongruence` conclusion in ONE generic
constructor, non-vacuously (`frobeniusSuffixCongruence_nonVacuous`: a real `frobLeft` row fired past a `t`
suffix).  The `medium`-flagged `HEq`/`castBoundary` friction did NOT materialize — every law cell is a concrete
`t`-power composite, so `composePath` associativity is definitional.  The row-suffix congruence the word-carried
`SpiderConvRows` structurally lacked (`fxFrob_hasRowLevelSuffixCongruence = false`) is free on the free-2-cell
carrier.  `= true`. -/
def fxTab_frobeniusSuffixCongruenceFallsOut : Bool := true

end FX1Poly.Polygraph
