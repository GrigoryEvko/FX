import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedOver

/-! # Polygraph/TwoCategory/Table/ContextClosure — the relation-level contextual-closure operator + the
generic invariant-fold (POLY-TAB r0, the SEED)

This is the GENERIC half of the table-driven polygraph layer (task #2228 / INT-SIG-ALIGN #2079).  It packages
the T2b decision (the contextual closure is a RELATION-LEVEL fact — no new inductive) and the T3c decision (the
per-walker soundness legs are instance pairs of ONE fold), both directly over the shipped generic saturated
convertibility `SaturatedConvOver` (`Amalgam/SaturatedOver.lean`).

## T2b — the contextual closure carries NO enumerated context (Baader-Nipkow / CoLoR)

`SaturatedConvOver`'s `ofRelation` fires a base-relation row at a FIXED parallel boundary — it carries no
context.  ALL contextual closure is supplied by the four SEPARATE one-hole congruence constructors
(`vcompCongrLeft`, `vcompCongrRight`, `whiskerLeftCongr`, `whiskerRightCongr`).  So "a row in any context" is
already derivable and needs no new inductive: `contextClosureRel signature baseRel` is DEFINED as
`SaturatedConvOver signature baseRel` itself, and the package below exposes the closure's algebraic laws — the
intro rules (row / prefix / suffix / vcomp / equivalence), MONOTONICITY (the closure is order-preserving), and
IDEMPOTENCE (closing a closed relation adds nothing — the "rewrite relations form a complete lattice" fact,
Baader-Nipkow *Term Rewriting and All That* Def. 4.2.2).  This is the relation-transformer `red u v := exists
l r c s, In (l,r) R and u = fill c (sub s l) and v = fill c (sub s r)` (CoLoR), with the whisker/vcomp closures
playing the `fill` (context) role and `ofFull` playing the `sub` (structural-law) role.

The load-bearing corollary the whole Frobenius r10 wall reduces to: the SUFFIX congruence — a row-generated
convertibility whiskered by a suffix stays row-generated — is `whiskerRightCongr`, ONE constructor
(`SaturatedConvOver.suffixCongruence` below).  The Frobenius `SpiderConvRows` route walled precisely because its
word-carrier baked the prefix into every firing constructor (`SpiderCrossingRerun.lean`,
`fxFrob_hasRowLevelSuffixCongruence = false`); the generic never bakes context into a firing, so both prefix
(`prefixCongruence`) and suffix (`suffixCongruence`) are free.

## T3c — the generic invariant fold (Guiraud-Malbos polygraphic derivations)

A polygraphic derivation / termination invariant is "uniquely determined by its values on the generators" and
compatible with the closure by the Leibniz law (Guiraud-Malbos, *Polygraphs of finite derivation type*).  Its
mechanized shape is `SaturatedConvOver.recInto`: any target relation `targetRel` that ABSORBS both the free
convertibility and the base rows (an `IsSaturatedCongruence`) receives a map out of `SaturatedConvOver`.  Two
value forms ship here:

  * **`rowConvInvariant_foldRel`** — the RELATIONAL (Prop / `CellRel`-valued) form: `recInto` re-exposed under the
    fold name.  A `ThueCongruence`-valued invariant instantiates `targetRel := fun a b => cong (inv a) (inv b)`.
  * **`rowConvInvariant_foldEq`** — the Eq-valued specialization: for `targetRel := fun a b => inv a = inv b` the
    `refl`/`symm`/`trans` legs collapse to `rfl`/`Eq.symm`/`Eq.trans`, so the caller supplies ONLY the six genuine
    preservation legs (`ofFull` + rows + the four contexts).  This is the T3c "instance pair" made literal — the
    per-walker soundness legs (`spiderConv_partitionSound`, `quadCohesionParity_satConv`, ...) become one
    `(invariantOf, rowsPreserve, + four context legs)` value.

Raw Lean 4 + Init; every declaration is a `def`/`theorem` built from the shipped generic constructors and
`recInto`, so it is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Additive: nothing
in `Amalgam/` or the walker lanes is touched.  Per-declaration `#assert_no_axioms` in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The relation-level contextual-closure operator (T2b, option ii — no new inductive) -/

/-- The **contextual-closure operator** on a base law relation — `contextClosureRel signature baseRel` is the
least relation containing `baseRel` closed under the four one-hole contexts (prefix / suffix / vcomp) and the
free convertibility, taken up to reflexive-symmetric-transitive closure.  It is DEFINED as the shipped generic
`SaturatedConvOver signature baseRel` (option ii — the context closure is a relation-level fact, not a new
inductive); the package below is its algebra. -/
def contextClosureRel (signature : ModeSignature) (baseRel : CellRel signature) : CellRel signature :=
  fun cellAlpha cellBeta => SaturatedConvOver signature baseRel cellAlpha cellBeta

/-- Intro: a base-relation row enters the closure at its fixed boundary (context-free). -/
theorem contextClosureRel.ofRow {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (row : baseRel cellAlpha cellBeta) :
    contextClosureRel signature baseRel cellAlpha cellBeta :=
  SaturatedConvOver.ofRelation row

/-- Intro: the closure is closed under a common PREFIX (left whiskering). -/
theorem contextClosureRel.underPrefix {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (prefix1Cell : ModalityPath signature.graph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode}
    {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH}
    (closed : contextClosureRel signature baseRel cellBeta cellBeta') :
    contextClosureRel signature baseRel
      (RawTwoCellExpr.whiskerLeft prefix1Cell cellBeta) (RawTwoCellExpr.whiskerLeft prefix1Cell cellBeta') :=
  SaturatedConvOver.whiskerLeftCongr prefix1Cell closed

/-- Intro: the closure is closed under a common SUFFIX (right whiskering).  This is the exact brick the Frobenius
word-carrier route walled (`RowSuffixCongruence`), here ONE constructor. -/
theorem contextClosureRel.underSuffix {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode}
    (suffix1Cell : ModalityPath signature.graph middleMode targetMode)
    {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG}
    (closed : contextClosureRel signature baseRel cellAlpha cellAlpha') :
    contextClosureRel signature baseRel
      (RawTwoCellExpr.whiskerRight suffix1Cell cellAlpha) (RawTwoCellExpr.whiskerRight suffix1Cell cellAlpha') :=
  SaturatedConvOver.whiskerRightCongr suffix1Cell closed

/-- Intro: the closure is closed in the LEFT factor of a vertical composite. -/
theorem contextClosureRel.underVcompLeft {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG}
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH)
    (closed : contextClosureRel signature baseRel cellAlpha cellAlpha') :
    contextClosureRel signature baseRel
      (RawTwoCellExpr.vcomp cellAlpha cellBeta) (RawTwoCellExpr.vcomp cellAlpha' cellBeta) :=
  SaturatedConvOver.vcompCongrLeft cellBeta closed

/-- Intro: the closure is closed in the RIGHT factor of a vertical composite. -/
theorem contextClosureRel.underVcompRight {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH}
    (closed : contextClosureRel signature baseRel cellBeta cellBeta') :
    contextClosureRel signature baseRel
      (RawTwoCellExpr.vcomp cellAlpha cellBeta) (RawTwoCellExpr.vcomp cellAlpha cellBeta') :=
  SaturatedConvOver.vcompCongrRight cellAlpha closed

/-- The closure is reflexive. -/
theorem contextClosureRel.isReflexive {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    contextClosureRel signature baseRel cell cell :=
  SaturatedConvOver.refl cell

/-- The closure is symmetric. -/
theorem contextClosureRel.isSymmetric {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (closed : contextClosureRel signature baseRel cellAlpha cellBeta) :
    contextClosureRel signature baseRel cellBeta cellAlpha :=
  SaturatedConvOver.symm closed

/-- The closure is transitive. -/
theorem contextClosureRel.isTransitive {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta cellGamma : RawTwoCellExpr signature sourcePath targetPath}
    (leftClosed : contextClosureRel signature baseRel cellAlpha cellBeta)
    (rightClosed : contextClosureRel signature baseRel cellBeta cellGamma) :
    contextClosureRel signature baseRel cellAlpha cellGamma :=
  SaturatedConvOver.trans leftClosed rightClosed

/-! ## Monotonicity and idempotence — the closure operator is a complete-lattice closure -/

/-- **Monotonicity of the closure** — a pointwise-larger base relation yields a pointwise-larger closure.  Proved
by the universal property: the target `SaturatedConvOver signature baseRelLarger` absorbs the smaller closure
because each smaller row maps up through `rowsInclude`. -/
theorem SaturatedConvOver.monotone {signature : ModeSignature}
    {baseRelSmaller baseRelLarger : CellRel signature}
    (rowsInclude : {sourceMode targetMode : signature.graph.Mode} →
        {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
        {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} →
        baseRelSmaller cellAlpha cellBeta → baseRelLarger cellAlpha cellBeta)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (closed : SaturatedConvOver signature baseRelSmaller cellAlpha cellBeta) :
    SaturatedConvOver signature baseRelLarger cellAlpha cellBeta :=
  SaturatedConvOver.recInto
    { ofFull := fun full => SaturatedConvOver.ofFull full
      ofRelation := fun row => SaturatedConvOver.ofRelation (rowsInclude row)
      vcompCongrLeft := fun ih => SaturatedConvOver.vcompCongrLeft _ ih
      vcompCongrRight := fun ih => SaturatedConvOver.vcompCongrRight _ ih
      whiskerLeftCongr := fun ih => SaturatedConvOver.whiskerLeftCongr _ ih
      whiskerRightCongr := fun ih => SaturatedConvOver.whiskerRightCongr _ ih
      refl := fun cell => SaturatedConvOver.refl cell
      symm := fun ih => SaturatedConvOver.symm ih
      trans := fun ihLeft ihRight => SaturatedConvOver.trans ihLeft ihRight }
    closed

/-- **Idempotence of the closure** — closing the closure of a relation adds nothing: `SaturatedConvOver` over
`contextClosureRel signature baseRel` collapses back to `SaturatedConvOver signature baseRel`.  The `ofRelation`
leg is the IDENTITY because `contextClosureRel signature baseRel a b` is DEFINITIONALLY `SaturatedConvOver
signature baseRel a b`.  This is the "rewrite relations form a complete lattice" lattice fact. -/
theorem contextClosureRel.isIdempotent {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (twiceClosed : SaturatedConvOver signature (contextClosureRel signature baseRel) cellAlpha cellBeta) :
    SaturatedConvOver signature baseRel cellAlpha cellBeta :=
  SaturatedConvOver.recInto
    { ofFull := fun full => SaturatedConvOver.ofFull full
      ofRelation := fun alreadyClosed => alreadyClosed
      vcompCongrLeft := fun ih => SaturatedConvOver.vcompCongrLeft _ ih
      vcompCongrRight := fun ih => SaturatedConvOver.vcompCongrRight _ ih
      whiskerLeftCongr := fun ih => SaturatedConvOver.whiskerLeftCongr _ ih
      whiskerRightCongr := fun ih => SaturatedConvOver.whiskerRightCongr _ ih
      refl := fun cell => SaturatedConvOver.refl cell
      symm := fun ih => SaturatedConvOver.symm ih
      trans := fun ihLeft ihRight => SaturatedConvOver.trans ihLeft ihRight }
    twiceClosed

/-! ## The generic suffix / prefix congruences over an ARBITRARY base relation -/

/-- ★ **The generic SUFFIX congruence** — a saturated convertibility whiskered by any suffix stays saturated,
over ANY signature and ANY base relation.  ONE constructor (`whiskerRightCongr`).  This is the carrier-independent
dissolution of the Frobenius `RowSuffixCongruence` wall: the word-carried row program could not re-fire a row past
a common suffix (`SpiderCrossingRerun.lean`), but the free-2-cell carrier never bakes the suffix into a firing, so
the suffix congruence is a single generator. -/
theorem SaturatedConvOver.suffixCongruence {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode}
    (suffix1Cell : ModalityPath signature.graph middleMode targetMode)
    {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG}
    (conv : SaturatedConvOver signature baseRel cellAlpha cellAlpha') :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.whiskerRight suffix1Cell cellAlpha) (RawTwoCellExpr.whiskerRight suffix1Cell cellAlpha') :=
  SaturatedConvOver.whiskerRightCongr suffix1Cell conv

/-- ★ **The generic PREFIX congruence** — a saturated convertibility whiskered by any prefix stays saturated, over
ANY signature and ANY base relation.  ONE constructor (`whiskerLeftCongr`). -/
theorem SaturatedConvOver.prefixCongruence {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (prefix1Cell : ModalityPath signature.graph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode}
    {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH}
    (conv : SaturatedConvOver signature baseRel cellBeta cellBeta') :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.whiskerLeft prefix1Cell cellBeta) (RawTwoCellExpr.whiskerLeft prefix1Cell cellBeta') :=
  SaturatedConvOver.whiskerLeftCongr prefix1Cell conv

/-! ## The generic invariant fold (T3c) — both value forms -/

/-- ★ **The relational invariant fold** — the T3c "row-conv invariant" as `recInto`: any target `CellRel` that
absorbs the base rows in every context (an `IsSaturatedCongruence`) is respected by the whole saturated
convertibility.  A `ThueCongruence`-valued invariant instantiates `targetRel := fun a b => cong (inv a) (inv b)`
and supplies the six preservation legs plus the congruence's own equivalence as the `IsSaturatedCongruence`
fields. -/
theorem rowConvInvariant_foldRel {signature : ModeSignature} {baseRel targetRel : CellRel signature}
    (rowsPreserveInEveryContext : IsSaturatedCongruence signature baseRel targetRel)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (conv : SaturatedConvOver signature baseRel cellAlpha cellBeta) :
    targetRel cellAlpha cellBeta :=
  SaturatedConvOver.recInto rowsPreserveInEveryContext conv

/-- ★ **The Eq-valued invariant fold** — the T3c instance-pair made literal.  For an invariant `invariantOf : Cell
-> Carrier`, if `invariantOf` is preserved by the free convertibility, by each base row, and by each of the four
one-hole contexts, then it is invariant across the whole saturated convertibility.  The `refl`/`symm`/`trans`
legs collapse to `rfl`/`Eq.symm`/`Eq.trans` automatically — the caller supplies ONLY the six genuine legs.  Every
per-walker soundness leg (`spiderConv_partitionSound`, `cohesionParity_satConv`, the matching invariance) becomes
one call to this fold. -/
theorem rowConvInvariant_foldEq {signature : ModeSignature} {baseRel : CellRel signature}
    {Carrier : Type}
    (invariantOf : {sourceMode targetMode : signature.graph.Mode} →
        {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
        RawTwoCellExpr signature sourcePath targetPath → Carrier)
    (fullPreserves : {sourceMode targetMode : signature.graph.Mode} →
        {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
        {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} →
        TwoCellConvFull signature cellAlpha cellBeta → invariantOf cellAlpha = invariantOf cellBeta)
    (rowsPreserve : {sourceMode targetMode : signature.graph.Mode} →
        {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
        {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath} →
        baseRel cellAlpha cellBeta → invariantOf cellAlpha = invariantOf cellBeta)
    (vcompLeftPreserves : {sourceMode targetMode : signature.graph.Mode} →
        {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode} →
        {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG} →
        {cellBeta : RawTwoCellExpr signature oneCellG oneCellH} →
        invariantOf cellAlpha = invariantOf cellAlpha' →
        invariantOf (RawTwoCellExpr.vcomp cellAlpha cellBeta)
          = invariantOf (RawTwoCellExpr.vcomp cellAlpha' cellBeta))
    (vcompRightPreserves : {sourceMode targetMode : signature.graph.Mode} →
        {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode} →
        {cellAlpha : RawTwoCellExpr signature oneCellF oneCellG} →
        {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH} →
        invariantOf cellBeta = invariantOf cellBeta' →
        invariantOf (RawTwoCellExpr.vcomp cellAlpha cellBeta)
          = invariantOf (RawTwoCellExpr.vcomp cellAlpha cellBeta'))
    (prefixPreserves : {sourceMode middleMode targetMode : signature.graph.Mode} →
        {oneCell : ModalityPath signature.graph sourceMode middleMode} →
        {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode} →
        {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH} →
        invariantOf cellBeta = invariantOf cellBeta' →
        invariantOf (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
          = invariantOf (RawTwoCellExpr.whiskerLeft oneCell cellBeta'))
    (suffixPreserves : {sourceMode middleMode targetMode : signature.graph.Mode} →
        {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode} →
        {oneCell : ModalityPath signature.graph middleMode targetMode} →
        {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG} →
        invariantOf cellAlpha = invariantOf cellAlpha' →
        invariantOf (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
          = invariantOf (RawTwoCellExpr.whiskerRight oneCell cellAlpha'))
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (conv : SaturatedConvOver signature baseRel cellAlpha cellBeta) :
    invariantOf cellAlpha = invariantOf cellBeta :=
  SaturatedConvOver.recInto
    (targetRel := fun cellLeft cellRight => invariantOf cellLeft = invariantOf cellRight)
    { ofFull := fullPreserves
      ofRelation := rowsPreserve
      vcompCongrLeft := vcompLeftPreserves
      vcompCongrRight := vcompRightPreserves
      whiskerLeftCongr := prefixPreserves
      whiskerRightCongr := suffixPreserves
      refl := fun _ => rfl
      symm := Eq.symm
      trans := Eq.trans }
    conv

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the GENERIC contextual-closure package + the invariant fold SHIP (POLY-TAB r0, T3a).**
The contextual-closure operator (`contextClosureRel`, option ii — no new inductive) with its full algebra (intro
rows / prefix / suffix / vcomp / equivalence), MONOTONICITY (`SaturatedConvOver.monotone`) and IDEMPOTENCE
(`contextClosureRel.isIdempotent`, the complete-lattice-closure fact), the generic suffix / prefix congruences
(`SaturatedConvOver.suffixCongruence` / `.prefixCongruence` — the carrier-independent dissolution of the Frobenius
row-suffix wall), and the invariant fold in both value forms (`rowConvInvariant_foldRel` relational,
`rowConvInvariant_foldEq` Eq).  Additive over the shipped `SaturatedConvOver` + `recInto`; nothing in the walker
lanes is touched.  `= true`. -/
def fxTab_hasContextClosurePackage : Bool := true

end FX1Poly.Polygraph.Amalgam
