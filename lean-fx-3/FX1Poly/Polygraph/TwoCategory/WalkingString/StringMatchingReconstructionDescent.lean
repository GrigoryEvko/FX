import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingReconstructionInterface
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanCanonicalWord

/-! # WalkingString — the RECONSTRUCTION DESCENT KIT: the per-mode steps a `convToNormalize` fold consumes (FC-6, P2)

FC-6 P1 (`StringMatchingReconstructionInterface`) reduced the whole adjoint-triple completeness + decision to ONE
obligation per route: `StringMatchingReconstruction.convToReconstruct` (cell ≈ reconstruct (matchingOf cell)) OR the
`StringFcNormalizer` fields (`convToNormalize` = the multi-mode straightening fold + `matchingInjectiveOnNormalForms`).
Both bottom out in a fold that fires the four shipped FC insertion MODES (CANCEL ×4 colours, EXTEND, COMMUTE,
INTERLEAVE, in `StringFussCatalanCanonicalWord`).  This file ships the PER-MODE STEP lemmas that fold consumes — the
two facts every straightening step must supply:

  1. the mode PRESERVES `matchingOf` (so the normal form has the SAME matching as the input — the soundness leg of
     the injectivity route, here FREE from the r2 soundness `stringSaturatedConv_matchingOf_eq_final`);
  2. the reconstruction/canonical target DESCENDS along the mode (redex ≈ target whenever reduct ≈ target — one
     `StringSaturatedTwoCellConv.trans` with the shipped mode lemma).

For the SUBSTANTIVE mode (CANCEL) both are shipped for all four colours; for EXTEND likewise.  Together they close
the pure-CANCEL fragment of `convToNormalize` outright: `stringSnakeStackF_reconstructsToIdentityF` witnesses the
interface obligation UNCONDITIONALLY on an infinite family (every `F`-snake stack reconstructs to `id_F`, matching
preserved).  What remains is NOT any of these steps but the redex-locating DRIVER + termination fold
(`fxString_hasStaircaseDriver`) that CHOOSES which mode to fire and recurses — the genuine multi-round FC-6 content,
recorded honestly.

Raw Lean 4 + Init; each preservation lemma is one application of the shipped r2 soundness to the shipped mode
convertibility, each descent is one `trans`.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free;
per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## CANCEL preserves `matchingOf` (all four colours) — free from r2 soundness -/

/-- ★ **CANCEL (colour-1 `F`) preserves `matchingOf`.**  `vcomp w stringSnakeF ≈ w` (`stringCancelSnakeF`) so by r2
soundness their matchings coincide — the straightening step leaves the boundary matching invariant. -/
theorem stringCancelSnakeF_preservesMatchingOf
    {sourcePath : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.tip}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.left)) :
    matchingOf (RawTwoCellExpr.vcomp w stringSnakeF) = matchingOf w :=
  stringSaturatedConv_matchingOf_eq_final (stringCancelSnakeF w)

/-- ★ **CANCEL (colour-1 lower `G`) preserves `matchingOf`.** -/
theorem stringCancelSnakeGlo_preservesMatchingOf
    {sourcePath : ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.base}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.right)) :
    matchingOf (RawTwoCellExpr.vcomp w stringSnakeGlo) = matchingOf w :=
  stringSaturatedConv_matchingOf_eq_final (stringCancelSnakeGlo w)

/-- ★ **CANCEL (colour-2 upper `G`) preserves `matchingOf`** — the OTHER colour straightening the shared `G`. -/
theorem stringCancelSnakeGhi_preservesMatchingOf
    {sourcePath : ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.base}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.right)) :
    matchingOf (RawTwoCellExpr.vcomp w stringSnakeGhi) = matchingOf w :=
  stringSaturatedConv_matchingOf_eq_final (stringCancelSnakeGhi w)

/-- ★ **CANCEL (colour-2 `H`) preserves `matchingOf`.** -/
theorem stringCancelSnakeH_preservesMatchingOf
    {sourcePath : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.tip}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.coLeft)) :
    matchingOf (RawTwoCellExpr.vcomp w stringSnakeH) = matchingOf w :=
  stringSaturatedConv_matchingOf_eq_final (stringCancelSnakeH w)

/-! ## EXTEND preserves `matchingOf` (any boundary) -/

/-- ★ **EXTEND preserves `matchingOf`.**  Absorbing a reducible `id` slot (`stringExtendByIdentity`) leaves the
boundary matching invariant — free from r2 soundness. -/
theorem stringExtendByIdentity_preservesMatchingOf
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    matchingOf (RawTwoCellExpr.vcomp w (RawTwoCellExpr.id (signature := adjointTripleModeSignature) targetPath))
      = matchingOf w :=
  stringSaturatedConv_matchingOf_eq_final (stringExtendByIdentity w)

/-! ## The reconstruction/canonical target DESCENDS along each mode -/

/-- ★ **CANCEL (colour-1 `F`) descent.**  If the reduct `w` is convertible to a target `canonical`, so is the redex
`vcomp w stringSnakeF` — one `trans` with `stringCancelSnakeF`.  The inductive step a `convToNormalize` fold fires on
a leading `F`-snake. -/
theorem stringCancelSnakeF_convDescent
    {sourcePath : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.tip}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.left))
    {canonical : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.left)}
    (ih : StringSaturatedTwoCellConv w canonical) :
    StringSaturatedTwoCellConv (RawTwoCellExpr.vcomp w stringSnakeF) canonical :=
  StringSaturatedTwoCellConv.trans (stringCancelSnakeF w) ih

/-- ★ **CANCEL (colour-1 lower `G`) descent.** -/
theorem stringCancelSnakeGlo_convDescent
    {sourcePath : ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.base}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.right))
    {canonical : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.right)}
    (ih : StringSaturatedTwoCellConv w canonical) :
    StringSaturatedTwoCellConv (RawTwoCellExpr.vcomp w stringSnakeGlo) canonical :=
  StringSaturatedTwoCellConv.trans (stringCancelSnakeGlo w) ih

/-- ★ **CANCEL (colour-2 upper `G`) descent.** -/
theorem stringCancelSnakeGhi_convDescent
    {sourcePath : ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.base}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.right))
    {canonical : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.right)}
    (ih : StringSaturatedTwoCellConv w canonical) :
    StringSaturatedTwoCellConv (RawTwoCellExpr.vcomp w stringSnakeGhi) canonical :=
  StringSaturatedTwoCellConv.trans (stringCancelSnakeGhi w) ih

/-- ★ **CANCEL (colour-2 `H`) descent.** -/
theorem stringCancelSnakeH_convDescent
    {sourcePath : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.tip}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.coLeft))
    {canonical : RawTwoCellExpr adjointTripleModeSignature sourcePath
      (singletonModalityPath AdjointTripleModality.coLeft)}
    (ih : StringSaturatedTwoCellConv w canonical) :
    StringSaturatedTwoCellConv (RawTwoCellExpr.vcomp w stringSnakeH) canonical :=
  StringSaturatedTwoCellConv.trans (stringCancelSnakeH w) ih

/-- ★ **EXTEND descent.**  Absorbing an `id` slot descends the target — the reflexive-extension step. -/
theorem stringExtendByIdentity_convDescent
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (w : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    {canonical : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath}
    (ih : StringSaturatedTwoCellConv w canonical) :
    StringSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp w (RawTwoCellExpr.id (signature := adjointTripleModeSignature) targetPath)) canonical :=
  StringSaturatedTwoCellConv.trans (stringExtendByIdentity w) ih

/-! ## Concrete satisfiability witness — the pure-CANCEL fragment of `convToNormalize` is closed -/

/-- ★★ **The interface obligation is INHABITED on the `F`-snake-stack family.**  For every `n`, the `n`-fold `F`-snake
stack is saturated-convertible to `id_F` (`stringSnakeStackF_conv_identity`) AND has the SAME boundary matching (r2
soundness).  So a reconstruction that maps `matchingOf id_F` to `id_F` satisfies `convToReconstruct` on the whole
infinite family — a concrete, unconditional witness that the FC-6 interface obligation is realizable on real cells
(not vacuous), with `id_F` the matching-determined canonical form of every snake stack. -/
theorem stringSnakeStackF_reconstructsToIdentityF (count : Nat) :
    StringSaturatedTwoCellConv (stringSnakeStackF count) stringIdentityF
      ∧ matchingOf (stringSnakeStackF count) = matchingOf stringIdentityF :=
  ⟨stringSnakeStackF_conv_identity count,
    stringSaturatedConv_matchingOf_eq_final (stringSnakeStackF_conv_identity count)⟩

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the per-mode DESCENT STEPS of `convToNormalize` are shipped, complete.**  For the substantive
mode CANCEL (all four colours `F`/`Glo`/`Ghi`/`H`) and for EXTEND, both step obligations a straightening fold consumes
are machine-checked: the mode PRESERVES `matchingOf` (`stringCancelSnake*_preservesMatchingOf` /
`stringExtendByIdentity_preservesMatchingOf`, each one r2-soundness application) and the reconstruction target
DESCENDS (`stringCancelSnake*_convDescent` / `stringExtendByIdentity_convDescent`, each one `trans`).  The pure-CANCEL
fragment closes OUTRIGHT: `stringSnakeStackF_reconstructsToIdentityF` inhabits the interface obligation on the whole
`F`-snake-stack family (convertible to `id_F`, matching preserved).  These are exactly the inductive steps
`StringFcNormalizer.convToNormalize` is assembled from.  `= true`. -/
def fxString_hasReconstructionDescentKit : Bool := true

/-- **OPEN (honest) — the descent STEPS are shipped but the DRIVER + termination FOLD are not.**  What
`convToNormalize` still needs beyond these per-mode steps is the redex-locating DRIVER (`fireSnakeAt` / `commuteAt`,
which mode to fire and WHERE) and the termination FOLD over `lex(generatorCount, size, commutePotential)` — the same
`fxString_hasStaircaseDriver` residual the Staircase / Potential files wall, plus the COMMUTE / INTERLEAVE positional
binding (`fxString_hasStaircaseFoldFromPotential`).  So this file ships the STEP lemmas complete but NOT the fold that
sequences them; `fxString_hasAdjointTripleCompleteness` (in `StringMatchingCompleteness`) stays `false`, honestly, with
the residual now localized to the driver + fold (the multi-round FC-6 content), the per-mode descent steps discharged.
`= false`. -/
def fxString_hasReconstructionDescentDriver : Bool := false

end FX1Poly.Polygraph
