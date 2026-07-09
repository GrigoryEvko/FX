import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingCompleteness

/-! # WalkingString — the RECONSTRUCTION INTERFACE: two clean reductions of the completeness residual (FC-6, P1)

FC-6 (`#2020` / WP-STRING-3) owes exactly ONE residual for the adjoint-triple COMPLETENESS + decision:
`StringMatchingReductsShareSpineTrace` (in `StringMatchingCompleteness`) — matching-equal cells have saturated
REDUCTS whose spines are trace-equivalent.  `StringMatchingCompleteness` names it and assembles the keystone
(`stringSaturatedMatchingCanonicalization_ofReducts`) and the decision (`decidableStringSaturatedConv_ofReducts`)
modulo it.  The recon's route B (FC staircase) and the shipped valley apparatus (adjunction-hardcoded) are two
WAYS to discharge it; both bottom out in a matching-determined NORMAL FORM.

This file ships the CARRIER/BRIDGE for that discharge: TWO honest, zero-axiom REDUCTIONS of the residual to a
single named obligation each, so the remaining FC-6 work is a crisp interface inhabitation, not a re-derivation.

## Why the `SpineTraceEquiv` conjunct COLLAPSES to reflexivity

`StringMatchingReductsShareSpineTrace` asks for reducts `reductA`, `reductB` with `reductA ≈ cellA`, `reductB ≈
cellB`, and `SpineTraceEquiv reductA.spine reductB.spine`.  The valley route allows the two reducts to be
trace-equivalent-but-not-equal (whence the ~200-file spine-trace reconstruction).  BUT if both reducts are the
SAME matching-determined canonical cell — `reductA = reductB` as raw expressions — the trace conjunct is
`SpineTraceEquiv.refl` on the nose.  So the residual reduces to producing a matching-determined normal form
convertible to its source cell; nothing about spine-trace reconstruction survives.  This is the string-triple
mirror of the walking idempotent monad's `idempotentThinness_ofNormalize` (thinness from any boundary-determined
normalizer, `WalkingIdempotent/IdempotentMonadFullNormalizer`), lifted from BOUNDARY-determined to
MATCHING-determined because the walking adjoint triple is NOT thin (the two unit faces are a genuine
non-convertible parallel pair, `stringUnitFaces_notSaturatedConv`).

## The two interfaces (each names ONE obligation)

  * ★ **`StringMatchingReconstruction`** — a matching-section reconstruction: a function `reconstruct` producing a
    canonical cell at each parallel boundary FROM a `DiagramType`, together with `convToReconstruct : cell ≈
    reconstruct (matchingOf cell)`.  The residual follows because for a matching-equal pair the two reconstructions
    are literally equal (`congrArg reconstruct`), so their spines coincide and the trace conjunct is `refl`.  The
    single obligation `convToReconstruct` is the string port of the walking adjunction's arc-cell reconstruction
    (`fxMode_hasArcCellReconstruction`, the SAT-ARC-REC arc), colour-BLIND at the triple (matchingOf never reads
    `F`/`G`/`H`).
  * ★ **`StringFcNormalizer`** — the recon's route-B factoring: a normalizer `normalize` with `convToNormalize :
    cell ≈ normalize cell` and matching INJECTIVITY on its outputs (`matchingInjectiveOnNormalForms`).  The residual
    follows because soundness (`stringSaturatedConv_matchingOf_eq_final`) plus the hypothesis force
    `matchingOf (normalize cellA) = matchingOf (normalize cellB)`, whence injectivity gives `normalize cellA =
    normalize cellB` and the trace conjunct is again `refl`.  Its obligations are exactly the recon's bricks 2/3/4
    (the multi-mode staircase FOLD + its convertibility + `matchingOf` injective on FC normal forms).

Both compose with the shipped keystone/decision (`*_ofReconstruction` / `*_ofNormalizer` below), so inhabiting
EITHER interface flips `fxString_hasAdjointTripleCompleteness` with no further plumbing.  Neither is inhabited this
round (the reconstruction/normalizer is the multi-round content), so completeness stays `false`, honestly.

Raw Lean 4 + Init; each reduction is `refine ⟨reconstruct .., reconstruct .., convToX, convToX, ?_⟩` closed by a
one-line `rw` + `SpineTraceEquiv.refl`.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Interface 1 — the matching-section reconstruction -/

/-- ★ **The matching-section reconstruction interface** for the walking adjoint triple.  A `reconstruct` function
building a canonical cell at each parallel boundary from a boundary `DiagramType` matching, together with the
convertibility of every cell to the reconstruction of ITS OWN matching.  The single field `convToReconstruct` is the
string analog of the walking adjunction's arc-cell reconstruction (`fxMode_hasArcCellReconstruction`); it is
colour-BLIND (matchingOf never reads the `F`/`G`/`H` colour). -/
structure StringMatchingReconstruction where
  /-- Build a canonical cell at a parallel boundary from a `DiagramType` matching. -/
  reconstruct : {sourceMode targetMode : AdjointTripleMode} →
    (sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode) →
    DiagramType → RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath
  /-- Every cell is saturated-convertible to the reconstruction of its own boundary matching. -/
  convToReconstruct : {sourceMode targetMode : AdjointTripleMode} →
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode} →
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) →
    StringSaturatedTwoCellConv cell (reconstruct sourcePath targetPath (matchingOf cell))

/-- ★★ **The completeness residual from a matching-section reconstruction.**  Take both reducts to be
`reconstruct sourcePath targetPath (matchingOf cell·)`.  Each is convertible to its source cell by
`convToReconstruct`; and since `matchingOf cellA = matchingOf cellB` the two reconstructions are the SAME raw cell
(`congrArg`), so the required `SpineTraceEquiv reductA.spine reductB.spine` is `SpineTraceEquiv.refl` on identical
spines.  This discharges `StringMatchingReductsShareSpineTrace` — the whole valley/spine-trace apparatus collapses
to reflexivity once the reducts are matching-determined. -/
theorem stringMatchingReductsShareSpineTrace_ofReconstruction
    (recon : StringMatchingReconstruction) : StringMatchingReductsShareSpineTrace := by
  intro sourceMode targetMode sourcePath targetPath cellA cellB matchingsEqual
  refine ⟨recon.reconstruct sourcePath targetPath (matchingOf cellA),
    recon.reconstruct sourcePath targetPath (matchingOf cellB),
    recon.convToReconstruct cellA, recon.convToReconstruct cellB, ?_⟩
  rw [matchingsEqual]
  exact SpineTraceEquiv.refl _

/-- ★ **Base completeness from a reconstruction** — `matchingOf cellA = matchingOf cellB → cellA ≈ cellB`, routed
through the shipped `stringConvOfMapEq_ofReductsShareSpineTrace`. -/
theorem stringConvOfMapEq_ofReconstruction
    (recon : StringMatchingReconstruction)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (matchingsEqual : matchingOf cellA = matchingOf cellB) :
    StringSaturatedTwoCellConv cellA cellB :=
  stringConvOfMapEq_ofReductsShareSpineTrace
    (stringMatchingReductsShareSpineTrace_ofReconstruction recon) cellA cellB matchingsEqual

/-- ★ **The keystone from a reconstruction** — soundness (r2) + completeness (from the reconstruction), the two-field
`StringSaturatedMatchingCanonicalization`. -/
def stringSaturatedMatchingCanonicalization_ofReconstruction
    (recon : StringMatchingReconstruction) : StringSaturatedMatchingCanonicalization :=
  stringSaturatedMatchingCanonicalization_ofReducts
    (stringMatchingReductsShareSpineTrace_ofReconstruction recon)

/-- ★★ **The full adjoint-triple decision from a reconstruction** — `Decidable (StringSaturatedTwoCellConv ..)` on
every parallel pair via the two-level coloured matching, routed through the shipped
`decidableStringSaturatedConv_ofReducts`.  Inhabiting `StringMatchingReconstruction` inhabits the #2020 decision. -/
def decidableStringSaturatedConv_ofReconstruction
    (recon : StringMatchingReconstruction)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    Decidable (StringSaturatedTwoCellConv cellA cellB) :=
  decidableStringSaturatedConv_ofReducts
    (stringMatchingReductsShareSpineTrace_ofReconstruction recon) cellA cellB

/-! ## Interface 2 — the matching-injective normalizer (the recon's route-B factoring) -/

/-- ★ **The FC-normalizer interface** for the walking adjoint triple (the recon's route-B bricks 2/3/4).  A
`normalize` function with the convertibility of every cell to its normal form (`convToNormalize`, the multi-mode
straightening fold) and `matchingOf` INJECTIVITY on normal forms (`matchingInjectiveOnNormalForms`, the FC
identification theorem).  Together these are exactly the recon's staircase route. -/
structure StringFcNormalizer where
  /-- The FC normal form of a cell (the staircase straightening fold's output). -/
  normalize : {sourceMode targetMode : AdjointTripleMode} →
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode} →
    RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath →
    RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath
  /-- Every cell is saturated-convertible to its normal form. -/
  convToNormalize : {sourceMode targetMode : AdjointTripleMode} →
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode} →
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) →
    StringSaturatedTwoCellConv cell (normalize cell)
  /-- `matchingOf` is injective on the normal forms — the FC identification theorem. -/
  matchingInjectiveOnNormalForms : {sourceMode targetMode : AdjointTripleMode} →
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode} →
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) →
    matchingOf (normalize cellA) = matchingOf (normalize cellB) → normalize cellA = normalize cellB

/-- ★★ **The completeness residual from an FC-normalizer.**  Take both reducts to be `normalize cell·`.  Soundness
(`stringSaturatedConv_matchingOf_eq_final` applied to `convToNormalize`) gives `matchingOf cell· = matchingOf
(normalize cell·)`, so the hypothesis `matchingOf cellA = matchingOf cellB` propagates to `matchingOf (normalize
cellA) = matchingOf (normalize cellB)`; injectivity then forces `normalize cellA = normalize cellB`, so the trace
conjunct is `SpineTraceEquiv.refl` on identical spines.  Discharges `StringMatchingReductsShareSpineTrace` via the
recon's route-B bricks. -/
theorem stringMatchingReductsShareSpineTrace_ofNormalizer
    (nf : StringFcNormalizer) : StringMatchingReductsShareSpineTrace := by
  intro sourceMode targetMode sourcePath targetPath cellA cellB matchingsEqual
  refine ⟨nf.normalize cellA, nf.normalize cellB,
    nf.convToNormalize cellA, nf.convToNormalize cellB, ?_⟩
  have soundA : matchingOf cellA = matchingOf (nf.normalize cellA) :=
    stringSaturatedConv_matchingOf_eq_final (nf.convToNormalize cellA)
  have soundB : matchingOf cellB = matchingOf (nf.normalize cellB) :=
    stringSaturatedConv_matchingOf_eq_final (nf.convToNormalize cellB)
  have normalFormsMatch : matchingOf (nf.normalize cellA) = matchingOf (nf.normalize cellB) := by
    rw [← soundA, matchingsEqual]; exact soundB
  rw [nf.matchingInjectiveOnNormalForms cellA cellB normalFormsMatch]
  exact SpineTraceEquiv.refl _

/-- ★ **Base completeness from an FC-normalizer** — routed through the shipped
`stringConvOfMapEq_ofReductsShareSpineTrace`. -/
theorem stringConvOfMapEq_ofNormalizer
    (nf : StringFcNormalizer)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (matchingsEqual : matchingOf cellA = matchingOf cellB) :
    StringSaturatedTwoCellConv cellA cellB :=
  stringConvOfMapEq_ofReductsShareSpineTrace
    (stringMatchingReductsShareSpineTrace_ofNormalizer nf) cellA cellB matchingsEqual

/-- ★ **The keystone from an FC-normalizer.** -/
def stringSaturatedMatchingCanonicalization_ofNormalizer
    (nf : StringFcNormalizer) : StringSaturatedMatchingCanonicalization :=
  stringSaturatedMatchingCanonicalization_ofReducts
    (stringMatchingReductsShareSpineTrace_ofNormalizer nf)

/-- ★★ **The full adjoint-triple decision from an FC-normalizer.** -/
def decidableStringSaturatedConv_ofNormalizer
    (nf : StringFcNormalizer)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    Decidable (StringSaturatedTwoCellConv cellA cellB) :=
  decidableStringSaturatedConv_ofReducts
    (stringMatchingReductsShareSpineTrace_ofNormalizer nf) cellA cellB

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the completeness residual reduces to ONE interface obligation, TWO independent ways.**  Both
`stringMatchingReductsShareSpineTrace_ofReconstruction` (from a matching-section reconstruction
`StringMatchingReconstruction`, the arc-cell route) and `stringMatchingReductsShareSpineTrace_ofNormalizer` (from a
matching-injective FC-normalizer `StringFcNormalizer`, the recon's route-B staircase bricks) discharge
`StringMatchingReductsShareSpineTrace` UNCONDITIONALLY and zero-axiom: each collapses the `SpineTraceEquiv` conjunct
to `SpineTraceEquiv.refl` by making the two reducts the SAME matching-determined cell.  Each composes with the
shipped keystone + decision (`*_ofReconstruction` / `*_ofNormalizer`), so inhabiting EITHER interface flips
`fxString_hasAdjointTripleCompleteness` with no further plumbing.  The valley/spine-trace reconstruction is NOT on
the critical path — the residual needs only a matching-determined normal form.  `= true`. -/
def fxString_hasReconstructionInterfaceReduction : Bool := true

/-- **OPEN (honest) — neither interface is inhabited this round; completeness stays a multi-round port.**  The single
standing obligation is EITHER `StringMatchingReconstruction.convToReconstruct` (the string port of the walking
adjunction's arc-cell reconstruction `fxMode_hasArcCellReconstruction` / SAT-ARC-REC, a multi-round arc) OR the
`StringFcNormalizer` fields (`convToNormalize` = the multi-mode staircase FOLD, `fxString_hasStaircaseDriver`; plus
`matchingInjectiveOnNormalForms` = the FC identification theorem).  Both routes bottom out in a matching-determined
normal form whose construction is the genuine remaining FC-6 content; this file supplies only the CRISP interface, so
`fxString_hasAdjointTripleCompleteness` (in `StringMatchingCompleteness`) stays `false`, honestly, with the residual
now factored to a single named obligation per route.  `= false`. -/
def fxString_hasReconstructionInhabited : Bool := false

end FX1Poly.Polygraph
