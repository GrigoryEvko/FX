import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingSoundness
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceReconstruction

/-! # WalkingString — the COMPLETENESS direction, existence-factored, and the gated decision

Round 2 shipped the FULL two-level SOUNDNESS unconditionally (`stringSaturatedConv_matchingOf_eq_final` /
`stringSaturatedConv_colouredMatchingOf_eq_final`): saturated-convertible walking-adjoint-triple 2-cells have the
same (coloured) boundary matching.  This file carries the OTHER direction as far as it honestly goes THIS round —
the COMPLETENESS `matchingOf cellA = matchingOf cellB → StringSaturatedTwoCellConv cellA cellB` — and assembles
the DECISION modulo the single named residual.

## ★ Completeness is colour-BLIND (like soundness), NOT colour-sensitive

`StringSaturatedTwoCellConv` relates only PARALLEL cells (same `sourcePath`, same `targetPath`), and
`colouredMatchingOf sourcePath targetPath cell = { base := matchingOf cell, bottomLabels := pathLabels sourcePath,
topLabels := pathLabels targetPath }`.  For a parallel pair the `bottomLabels` / `topLabels` fields are fixed by the
shared boundary — DEFINITIONALLY identical for both cells — so

  `colouredMatchingOf .. cellA = colouredMatchingOf .. cellB  ⟺  matchingOf cellA = matchingOf cellB`.

The colours add ZERO discriminating power on the completeness direction, exactly as on soundness (r2): the shared
`G` couples the two adjunctions only at the boundary-fixed LABEL level (`pathLabels`), invisible to the
convertibility.  So `stringConvOfColouredMapEq` reduces on the nose to the base `stringConvOfMapEq`
(`congrArg ColouredDiagramType.base`).  The two per-colour reconstructions do NOT need to be "glued at `G`" —
there is nothing to glue, the matching never reads a colour.

## The route (the direct colour-blind port, one residual — NOT a shared-`G` coherence wall)

The walking ADJUNCTION's completeness `convOfMapEq` (SAT-COMPLETE, `SaturatedMatchingCanonicalization`) factors as
`convOfMapEq_ofMatchingReductsShareSpineTrace`:

  * a FREE-trace LIFT (`SaturatedTwoCellConv.ofSpineTraceEquiv`) — trace-equivalent spines lift to the saturated
    relation.  It rides the `{signature}`-GENERIC `RawTwoCellExpr.twoCellConvFull_ofSpineTraceEquiv`, so it ports
    to the three-generator seed by a one-line restatement (`StringSaturatedTwoCellConv.ofSpineTraceEquiv`, below);
  * an EXISTENCE residual (`MatchingReductsShareSpineTrace`) — matching-equal cells have saturated reducts whose
    spines are trace-equivalent — discharged in the adjunction by the ENTIRE valley-descent apparatus
    (`cellValleyTraceEquiv_holds` and the ~200 hardcoded `adjunctionModeSignature` files feeding it).

This file ports the FREE half and NAMES the residual at the string signature.  The residual
`StringMatchingReductsShareSpineTrace` is the string analog of the adjunction's `matchingReductsShareSpineTrace_holds`;
it is NOT a shared-`G` coherence obstruction (the gluing closes — see below), it is the reduct-existence descent
re-stated at three colour-blind generators, whose Lean discharge is the un-ported valley machinery (a multi-round
port, comparable in magnitude to the whole SAT-COMPLETE effort).

## ★ There is NO shared-`G` coherence gap

The union-find `matchingOf` reads only a generator's ARITY (`0 ⇒ 2` cup, `2 ⇒ 0` cap), never its `F`/`G`/`H` label
(colour-blind, r2).  The two `G`-triangles collapse to the SAME `matchingOf stringIdentityG` on the nose
(`matchingOf_stringTriangleGlo` / `matchingOf_stringTriangleGhi`, both `rfl`), so the two per-colour reconstructions
agree at the shared-`G` boundary by construction — there is no orientation/coherence obstruction to exhibit.  The
completeness residual therefore stays a PORT (`fxString_hasAdjointTripleCompleteness = false`), NOT a wall
(`fxString_hasAdjointTripleCoherenceGap = false`).

## What this file ships

  * ★ `StringSaturatedTwoCellConv.ofSpineTraceEquiv` — the free-trace lift (unconditional, ported);
  * `StringMatchingReductsShareSpineTrace` — the named completeness residual (existence-factored);
  * ★ `stringConvOfMapEq_ofReductsShareSpineTrace` — the base completeness from the residual;
  * ★ `stringConvOfColouredMapEq_ofReductsShareSpineTrace` — its two-level lift (colours collapse to the base);
  * `StringSaturatedMatchingCanonicalization` + `stringSaturatedMatchingCanonicalization_ofReducts` — the keystone
    (SOUNDNESS from r2, COMPLETENESS from the residual);
  * ★ `decidableStringSaturatedConv_ofReducts` — the FULL adjoint-triple word-problem DECISION modulo the residual
    (soundness r2 forward + completeness backward, via `ColouredDiagramType` `DecidableEq`);
  * NON-VACUITY, both UNCONDITIONAL (rides r2 soundness only, no residual): the two `G`-snakes are a genuine
    CONVERTIBLE parallel pair (`stringSnakeGlo_conv_stringSnakeGhi`, the isTrue pole), and the two unit FACES
    `η ▷ (F·G)` vs `(F·G) ◁ η` are a genuine NON-convertible parallel pair
    (`stringUnitFaces_notSaturatedConv`, the isFalse pole — distinct coloured matching, machine-refuted).

Raw Lean 4 + Init; the lift is `ofFull ∘ twoCellConvFull_ofSpineTraceEquiv`, the reduction is saturated
trans/symm glue, the refutation is `decide` on the coloured matching; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The free-trace lift into the saturated string relation (ported from the `{signature}`-generic core) -/

/-- ★ **The free-trace lift into the saturated walking-adjoint-triple relation.**  Trace-equivalent spines lift to
`StringSaturatedTwoCellConv`: run the shipped `{signature}`-GENERIC free reconstruction
`RawTwoCellExpr.twoCellConvFull_ofSpineTraceEquiv` (spines trace-equivalent ⟹ `TwoCellConvFull`), then embed via
`StringSaturatedTwoCellConv.ofFull`.  The three-generator analog of the adjunction's
`SaturatedTwoCellConv.ofSpineTraceEquiv`, and the currency-converter the completeness reduction consumes.
Unconditional. -/
theorem StringSaturatedTwoCellConv.ofSpineTraceEquiv {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (traceEquiv : SpineTraceEquiv adjointTripleModeSignature cellFirst.spine cellSecond.spine) :
    StringSaturatedTwoCellConv cellFirst cellSecond :=
  StringSaturatedTwoCellConv.ofFull
    (RawTwoCellExpr.twoCellConvFull_ofSpineTraceEquiv cellFirst cellSecond traceEquiv)

/-! ## The named completeness residual (the reduct-existence descent, owed) -/

/-- The **completeness residual, existence-factored** at the walking adjoint triple: every pair of cells with equal
boundary matchings has a pair of saturated REDUCTS (each saturated-convertible to its source cell) whose spines are
trace-equivalent.  The string analog of the adjunction's `MatchingReductsShareSpineTrace`; its Lean discharge is
the colour-blind valley-descent apparatus re-stated at the three-generator seed (the `cellValleyTraceEquiv` floor
and its dispatch), which is hardcoded to `adjunctionModeSignature` upstream and NOT yet ported — a multi-round port,
NOT an r3 residual and NOT a shared-`G` coherence obstruction. -/
def StringMatchingReductsShareSpineTrace : Prop :=
  ∀ {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath),
    matchingOf cellA = matchingOf cellB →
    ∃ reductA reductB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath,
      StringSaturatedTwoCellConv cellA reductA ∧ StringSaturatedTwoCellConv cellB reductB ∧
        SpineTraceEquiv adjointTripleModeSignature reductA.spine reductB.spine

/-! ## The completeness reduction (base + two-level lift) -/

/-- ★ **The BASE completeness from the existence residual.**  `StringMatchingReductsShareSpineTrace` yields
`stringConvOfMapEq`: the reducts' trace-equivalent spines lift to `StringSaturatedTwoCellConv`
(`ofSpineTraceEquiv`), and the glue `cellA ≈ reductA ≈ reductB ≈ cellB` closes by saturated transitivity and
symmetry.  A route to completeness that needs no canonical-cell choice — only the existence of
trace-equivalent-spined saturated reducts. -/
theorem stringConvOfMapEq_ofReductsShareSpineTrace
    (shares : StringMatchingReductsShareSpineTrace)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (matchingsEqual : matchingOf cellA = matchingOf cellB) :
    StringSaturatedTwoCellConv cellA cellB := by
  obtain ⟨reductA, reductB, convReductA, convReductB, traceEquiv⟩ :=
    shares cellA cellB matchingsEqual
  exact StringSaturatedTwoCellConv.trans convReductA
    (StringSaturatedTwoCellConv.trans
      (StringSaturatedTwoCellConv.ofSpineTraceEquiv reductA reductB traceEquiv)
      (StringSaturatedTwoCellConv.symm convReductB))

/-- ★ **The TWO-LEVEL completeness from the existence residual.**  Equal `ColouredDiagramType` of a PARALLEL pair
projects (on the nose, `congrArg ColouredDiagramType.base`) to equal base `matchingOf` — the boundary labels are
fixed by the shared source / target 1-cells and add nothing — so the two-level completeness IS the base one.  This
is the concrete meaning of "completeness is colour-blind": no shared-`G` gluing is required, the colours never
enter the reconstruction. -/
theorem stringConvOfColouredMapEq_ofReductsShareSpineTrace
    (shares : StringMatchingReductsShareSpineTrace)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (colouredMatchingsEqual :
      colouredMatchingOf sourcePath targetPath cellA = colouredMatchingOf sourcePath targetPath cellB) :
    StringSaturatedTwoCellConv cellA cellB :=
  stringConvOfMapEq_ofReductsShareSpineTrace shares cellA cellB
    (congrArg ColouredDiagramType.base colouredMatchingsEqual)

/-! ## The keystone (soundness r2 + completeness modulo the residual) + the decision -/

/-- ★ The **string saturated matching canonicalization** — the two-field keystone (soundness / completeness) for
the walking adjoint triple, the three-generator analog of the adjunction's `SaturatedMatchingCanonicalization`.
SOUNDNESS is unconditional (r2); COMPLETENESS is gated on the reduct-existence residual. -/
structure StringSaturatedMatchingCanonicalization where
  /-- SOUNDNESS: saturated-convertible cells have equal boundary matchings (the NO-direction). -/
  mapEqOfConv : {sourceMode targetMode : AdjointTripleMode} →
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode} →
    {cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath} →
    StringSaturatedTwoCellConv cellA cellB → matchingOf cellA = matchingOf cellB
  /-- COMPLETENESS: cells with equal boundary matchings are saturated-convertible (the YES-direction). -/
  convOfMapEq : {sourceMode targetMode : AdjointTripleMode} →
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode} →
    {cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath} →
    matchingOf cellA = matchingOf cellB → StringSaturatedTwoCellConv cellA cellB

/-- ★ **The whole keystone from the existence residual alone.**  SOUNDNESS is consumed from the shipped
unconditional r2 route (`stringSaturatedConv_matchingOf_eq_final`), COMPLETENESS from
`stringConvOfMapEq_ofReductsShareSpineTrace`.  The magnitude of the fib-3 keystone at the three-generator seed,
gated on exactly one named residual. -/
def stringSaturatedMatchingCanonicalization_ofReducts
    (shares : StringMatchingReductsShareSpineTrace) : StringSaturatedMatchingCanonicalization where
  mapEqOfConv := fun conv => stringSaturatedConv_matchingOf_eq_final conv
  convOfMapEq := fun matchingsEqual => stringConvOfMapEq_ofReductsShareSpineTrace shares _ _ matchingsEqual

/-- ★ **Decide saturated convertibility of the walking adjoint triple via the TWO-LEVEL matching.**  Compare the
two cells' `ColouredDiagramType` by the derived `DecidableEq` (structural over `Nat` / `List Nat` / `WireLabel` —
it COMPUTES, no `propext`): equal ⟹ `isTrue` via the two-level completeness; unequal ⟹ `isFalse`, since the
UNCONDITIONAL r2 soundness `stringSaturatedConv_colouredMatchingOf_eq_final` would force the coloured matchings
equal.  The FULL adjoint-triple word-problem decision (#2020), gated on the completeness residual; the isFalse leg
is residual-FREE (it uses only r2). -/
def decidableStringSaturatedConv_ofReducts
    (shares : StringMatchingReductsShareSpineTrace)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    Decidable (StringSaturatedTwoCellConv cellA cellB) :=
  match (inferInstance : Decidable
      (colouredMatchingOf sourcePath targetPath cellA = colouredMatchingOf sourcePath targetPath cellB)) with
  | isTrue colouredEqual =>
      isTrue (stringConvOfColouredMapEq_ofReductsShareSpineTrace shares cellA cellB colouredEqual)
  | isFalse colouredDiffer =>
      isFalse (fun conv => colouredDiffer (stringSaturatedConv_colouredMatchingOf_eq_final conv))

/-! ## ★ Non-vacuity of the decision — both poles UNCONDITIONAL (r2 soundness only, no residual) -/

/-- ★★ **The isTrue pole — a genuine CONVERTIBLE parallel pair.**  The two syntactically-distinct `G ⇒ G` snakes
`stringSnakeGlo` (colour 1) and `stringSnakeGhi` (colour 2) are `StringSaturatedTwoCellConv` (through `id_G`,
`stringSnakeGlo_conv_stringSnakeGhi`, built from the triangle constructors — no residual) and have EQUAL coloured
matching (`stringSnakeGlo_colouredMatchingOf_eq_stringSnakeGhi`, r2), so the decision returns `isTrue` on them.
The shared-`G` coherence is genuinely decided. -/
theorem decideStringSaturated_gSnakes_convertible :
    StringSaturatedTwoCellConv stringSnakeGlo stringSnakeGhi :=
  stringSnakeGlo_conv_stringSnakeGhi

/-- The left unit FACE `η ▷ (F·G) : F·G ⇒ (F·G)²` — the lower unit cup inserted at block position 0. -/
def stringUnitFaceLeft :
    RawTwoCellExpr adjointTripleModeSignature stringFG (composePath stringFG stringFG) :=
  RawTwoCellExpr.whiskerRight (signature := adjointTripleModeSignature) stringFG stringUnitLower

/-- The right unit FACE `(F·G) ◁ η : F·G ⇒ (F·G)²` — the lower unit cup inserted at block position 1.  LITERALLY
parallel to `stringUnitFaceLeft` (both `F·G ⇒ (F·G)²`, `composePath` fully reduces on the concrete `F·G`). -/
def stringUnitFaceRight :
    RawTwoCellExpr adjointTripleModeSignature stringFG (composePath stringFG stringFG) :=
  RawTwoCellExpr.whiskerLeft (signature := adjointTripleModeSignature) stringFG stringUnitLower

/-- ★ **The two unit faces are DISTINGUISHED by the two-level matching** — `δ₀ ≠ δ₁`.  The cup at the left and the
cup at the right, both `F·G ⇒ (F·G)²`, get DIFFERENT `ColouredDiagramType` (`decide` over the structural matching),
so the two-level carrier is not the trivial boundary-determined invariant: it is completeness-CAPABLE.  The
three-generator analog of the adjunction's `matchingOf_distinguishes_faces`. -/
theorem stringUnitFaces_colouredMatchingOf_ne :
    colouredMatchingOf stringFG (composePath stringFG stringFG) stringUnitFaceLeft
      ≠ colouredMatchingOf stringFG (composePath stringFG stringFG) stringUnitFaceRight := by decide

/-- ★★ **The isFalse pole — a genuine NON-convertible parallel pair.**  The two unit faces have distinct coloured
matching (`stringUnitFaces_colouredMatchingOf_ne`), so by the UNCONDITIONAL r2 soundness
`stringSaturatedConv_colouredMatchingOf_eq_final` they are NOT `StringSaturatedTwoCellConv` — the decision returns
`isFalse` on them.  This refutation rides only r2 soundness (NO completeness residual), so the decision is
non-vacuous at BOTH poles unconditionally: it separates the convertible `G`-snakes from the non-convertible unit
faces. -/
theorem stringUnitFaces_notSaturatedConv :
    ¬ StringSaturatedTwoCellConv stringUnitFaceLeft stringUnitFaceRight :=
  fun conv => stringUnitFaces_colouredMatchingOf_ne
    (stringSaturatedConv_colouredMatchingOf_eq_final conv)

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the free-trace lift + the completeness reduction + the gated decision are shipped.**  The
`{signature}`-generic free reconstruction ports to `StringSaturatedTwoCellConv.ofSpineTraceEquiv`; the existence
residual `StringMatchingReductsShareSpineTrace` reduces (base + two-level) to the completeness field
(`stringConvOfMapEq_ofReductsShareSpineTrace` / `stringConvOfColouredMapEq_ofReductsShareSpineTrace`); the keystone
`StringSaturatedMatchingCanonicalization` assembles (soundness r2 + completeness residual); and
`decidableStringSaturatedConv_ofReducts` decides EVERY parallel pair modulo the residual, non-vacuous at both poles
UNCONDITIONALLY (`decideStringSaturated_gSnakes_convertible` isTrue, `stringUnitFaces_notSaturatedConv` isFalse).
`= true`. -/
def fxString_hasSpineTraceLiftIntoStringSaturated : Bool := true

/-- **★ HONEST WALL RECORD — there is NO shared-`G` coherence gap.**  The literature (nLab adjoint+string:
the free adjoint string is the simplex category as a locally-POSETAL 2-category — at most one 2-cell per parallel
pair; nLab adjoint+triple: the two adjunctions couple at `G` by MATES, `G·F ⊣ G·H`) and the Lean substrate agree:
`matchingOf` is colour-BLIND, and the two `G`-triangles collapse to the SAME `matchingOf stringIdentityG` on the
nose (`matchingOf_stringTriangleGlo` / `matchingOf_stringTriangleGhi`, `rfl`, r2), so the two per-colour
reconstructions agree at the shared-`G` boundary by construction.  There is NO pair with equal `ColouredDiagramType`
that is provably NON-convertible for a colour reason — the only refutations (e.g. `stringUnitFaces_notSaturatedConv`)
come from DISTINCT coloured matching, never from a shared-`G` critical pair.  So NO gluing obstruction exists to
exhibit and this marker stays `false`.  `= false`. -/
def fxString_hasAdjointTripleCoherenceGap : Bool := false

/-- **OPEN — the adjoint-triple COMPLETENESS does NOT flip this round; it is an un-ported reduct-existence descent,
NOT a coherence wall.**  Completeness `matchingOf cellA = matchingOf cellB → StringSaturatedTwoCellConv cellA cellB`
is PROVED modulo exactly one named residual `StringMatchingReductsShareSpineTrace` (the free-trace lift and the
reduction are shipped here; `fxString_hasAdjointTripleCoherenceGap = false` records that no shared-`G` obstruction
blocks it).  That residual is the string analog of the adjunction's `matchingReductsShareSpineTrace_holds` — the
reduct-existence half of the SAT-COMPLETE effort — whose discharge is the colour-BLIND valley-descent apparatus
(`cellValleyTraceEquiv` + its dispatch), hardcoded to `adjunctionModeSignature` across ~200 upstream files and NOT
yet ported to the three-generator seed.  Porting it is a multi-round engineering arc (comparable in magnitude to
the whole SAT-COMPLETE completeness), not a single r3 residual — so this flip is deferred, honestly, with the exact
residual named.  `= false`. -/
def fxString_hasAdjointTripleCompleteness : Bool := false

end FX1Poly.Polygraph
