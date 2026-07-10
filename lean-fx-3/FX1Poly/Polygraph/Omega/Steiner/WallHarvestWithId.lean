import FX1Poly.Polygraph.Omega.Steiner.SoundnessWithId
import FX1Poly.Polygraph.Omega.Steiner.DesignLockOmega25
import FX1Poly.Polygraph.Omega.Steiner.Reconstruct

/-! # Polygraph/Omega/Steiner/WallHarvestWithId — conservativity + whiskered completeness (OMEGA-3 r2, B3)

★ **The wall harvest.**  With the idCongr sibling (`CongruenceWithId`) and its soundness cascade
(`SoundnessWithId`) in place, three genuine harvests fall out on the crown carrier:

  * **Conservativity on atom words.**  On the whisker-free single-generator fragment, the sibling proves
    EXACTLY the old convertibilities — `SaturatedConvOverWithId ↔ SaturatedConvOver` — proved "via the
    arithmetic model as the separator" (sibling soundness gives `linearize a = linearize b`, then the
    shipped atom-word completeness reconstructs the OLD derivation; the embedding gives the converse).  So
    the sibling is a CONSERVATIVE extension there (recon §6).

  * **Whiskered completeness on the chain table (fixed whisker).**  On the genuine WHISKERED fragment
    `whiskerLeft w (atom word)` at a fixed realized whisker `w`, chain-table equality DECIDES sibling
    convertibility both ways: soundness (`→`) is `linearizeFull_eq_of_saturatedConvWithId`; completeness
    (`←`) reads the top row off the chain table (the whisker is forgotten there), reconstructs the interior
    atom-word convertibility, and re-whiskers it with the sibling's `whiskerLeftCongr`.  Both decider
    verdicts are exhibited.

## Honest scope (recon §6, executed)

Conservativity is a FRAGMENT statement, not global: the sibling is STRICTLY larger than the old congruence
overall (it proves `id a ~ id b` from `a ~ b`, which the 8-constructor relation cannot even form — see
`idCongr_word3_nonVacuous`).  The whiskered completeness here fixes the whisker (the shipped
`whiskerLeftCongr` shape); the fragment where the WHISKERING cell itself varies (composite 1-cells in
whisker position) needs the whisker-1-cell congruences AND a reconstruct that reads the whisker off the
poles — that reconstruct is the honest open work (the general bridge conv leg / OMEGA-4).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph.Steiner

/-! ## The free strict congruence over the sibling -/

/-- The **free strict congruence over the idCongr sibling** — the sibling analog of
`freeStrictCongruence`: the idCongr saturated congruence over the strict laws united with a presentation.
Additive; downstream keeps `freeStrictCongruence` (the shipped statement is untouched). -/
def freeStrictCongruenceWithId (computad : OmegaComputad) (presentationRows : CellRelOver computad) :
    CellRelOver computad :=
  fun cellAlpha cellBeta =>
    SaturatedConvOverWithId computad
      (unionCellRel computad (StrictAxiomRel computad) presentationRows) cellAlpha cellBeta

/-! ## Conservativity on the atom-word fragment (via the arithmetic separator) -/

/-- ★ **CONSERVATIVITY on atom words (the map back).**  On the whisker-free single-generator fragment, a
sibling convertibility reconstructs the OLD 8-constructor convertibility: sibling soundness gives equal
single-vector tables, and the shipped atom-word completeness (`atomWord_conv_of_linearize_eq`) rebuilds the
old derivation. -/
theorem saturatedConvOverWithId_conservative_atomWord {dim : Nat}
    {cellA cellB : CellExpr crownComputad (dim + 1)}
    (hAtomA : IsAtomWord cellA) (hAtomB : IsAtomWord cellB)
    (conv : SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad) cellA cellB) :
    SaturatedConvOver crownComputad (StrictAxiomRel crownComputad) cellA cellB :=
  atomWord_conv_of_linearize_eq hAtomA hAtomB
    (linearize_eq_of_saturatedConvWithId crownValuation conv)

/-- ★★ **THE CONSERVATIVITY EQUIVALENCE on atom words.**  On the atom-word fragment the sibling and the
shipped congruence prove EXACTLY the same convertibilities: `←` is the free embedding, `→` is the
arithmetic reconstruction.  The sibling is a conservative extension of `SaturatedConvOver` there. -/
theorem atomWord_conv_iff_withId {dim : Nat} {cellA cellB : CellExpr crownComputad (dim + 1)}
    (hAtomA : IsAtomWord cellA) (hAtomB : IsAtomWord cellB) :
    SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad) cellA cellB
      ↔ SaturatedConvOver crownComputad (StrictAxiomRel crownComputad) cellA cellB :=
  ⟨saturatedConvOverWithId_conservative_atomWord hAtomA hAtomB, embedSaturatedConvOver⟩

/-! ## Whiskered completeness on the chain table (fixed whisker) -/

/-- ★ **THE WHISKERED COMPLETENESS (`←`).**  For a fixed realized whisker `w` and atom-word interiors,
equal chain tables reconstruct sibling convertibility: the top row (which forgets `w`) gives the interior
atom-word convertibility through the shipped completeness, and `whiskerLeftCongr` re-whiskers it. -/
theorem whiskeredAtomWord_conv_of_linearizeFull_eq {dim : Nat}
    (whisker : CellExpr crownComputad (dim + 1)) {cellA cellB : CellExpr crownComputad (dim + 2)}
    (hAtomA : IsAtomWord cellA) (hAtomB : IsAtomWord cellB)
    (chainEqual : linearizeFull crownValuation (CellExpr.whiskerLeft whisker cellA)
      = linearizeFull crownValuation (CellExpr.whiskerLeft whisker cellB)) :
    SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad)
      (CellExpr.whiskerLeft whisker cellA) (CellExpr.whiskerLeft whisker cellB) := by
  -- `linearizeFull_topCoord_eq` reads the crown row off the whiskered chain equality; the whisker cell is
  -- forgotten there (`linearize (whiskerLeft w c) = linearize c` definitionally), so the interiors' tables
  -- agree.
  have topEqualWhisk : (linearize crownValuation (CellExpr.whiskerLeft whisker cellA)).coordinates
      = (linearize crownValuation (CellExpr.whiskerLeft whisker cellB)).coordinates :=
    linearizeFull_topCoord_eq crownValuation chainEqual
  have tablesEqual : linearize crownValuation cellA = linearize crownValuation cellB :=
    congrArg SteinerCell.mk topEqualWhisk
  exact SaturatedConvOverWithId.whiskerLeftCongr whisker
    (embedSaturatedConvOver (atomWord_conv_of_linearize_eq hAtomA hAtomB tablesEqual))

/-- ★★ **THE WHISKERED CROWN (fixed whisker).**  On the whiskered fragment `whiskerLeft w (atom word)`,
sibling convertibility IS chain-table equality both ways — the recon-designed whiskered fragment's
decision, at chain granularity. -/
theorem whiskeredAtomWord_conv_iff_linearizeFull_eq {dim : Nat}
    (whisker : CellExpr crownComputad (dim + 1)) {cellA cellB : CellExpr crownComputad (dim + 2)}
    (hAtomA : IsAtomWord cellA) (hAtomB : IsAtomWord cellB) :
    SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad)
        (CellExpr.whiskerLeft whisker cellA) (CellExpr.whiskerLeft whisker cellB)
      ↔ linearizeFull crownValuation (CellExpr.whiskerLeft whisker cellA)
          = linearizeFull crownValuation (CellExpr.whiskerLeft whisker cellB) :=
  ⟨fun conv => linearizeFull_eq_of_saturatedConvWithId crownValuation conv,
   whiskeredAtomWord_conv_of_linearizeFull_eq whisker hAtomA hAtomB⟩

/-! ## Non-vacuity — both whiskered verdicts over a real whisker -/

/-- A dim-2 atom word `atom . (atom . atom)` (right-nested, 3 atoms). -/
def dimTwoWordRight : CellExpr crownComputad 2 :=
  CellExpr.vcomp (crownAtom 1) (CellExpr.vcomp (crownAtom 1) (crownAtom 1))

/-- A dim-2 atom word `(atom . atom) . atom` (left-nested, 3 atoms). -/
def dimTwoWordLeft : CellExpr crownComputad 2 :=
  CellExpr.vcomp (CellExpr.vcomp (crownAtom 1) (crownAtom 1)) (crownAtom 1)

/-- A dim-2 atom word `atom . atom` (2 atoms). -/
def dimTwoWordTwo : CellExpr crownComputad 2 :=
  CellExpr.vcomp (crownAtom 1) (crownAtom 1)

theorem dimTwoWordRight_isAtomWord : IsAtomWord dimTwoWordRight :=
  IsAtomWord.vcomp IsAtomWord.atom (IsAtomWord.vcomp IsAtomWord.atom IsAtomWord.atom)

theorem dimTwoWordLeft_isAtomWord : IsAtomWord dimTwoWordLeft :=
  IsAtomWord.vcomp (IsAtomWord.vcomp IsAtomWord.atom IsAtomWord.atom) IsAtomWord.atom

theorem dimTwoWordTwo_isAtomWord : IsAtomWord dimTwoWordTwo :=
  IsAtomWord.vcomp IsAtomWord.atom IsAtomWord.atom

/-- ★ **Positive whiskered verdict.**  The two differently-associated 3-atom words, whiskered on the left by
the realized 1-cell `crownAtom 0`, are GENUINELY sibling-convertible (a real `SaturatedConvOverWithId`
derivation obtained by chain-table equality through the whiskered crown). -/
theorem whiskered_word_conv_withId :
    SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad)
      (CellExpr.whiskerLeft (crownAtom 0) dimTwoWordRight)
      (CellExpr.whiskerLeft (crownAtom 0) dimTwoWordLeft) :=
  (whiskeredAtomWord_conv_iff_linearizeFull_eq (crownAtom 0)
    dimTwoWordRight_isAtomWord dimTwoWordLeft_isAtomWord).mpr (by decide)

/-- ★ **Negative whiskered verdict.**  Whiskered words of unequal interior length (3 vs 2 atoms) are
genuinely NON-convertible under the sibling — the chain refuter carries through the whisker. -/
theorem whiskered_word_not_conv_withId :
    ¬ SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad)
        (CellExpr.whiskerLeft (crownAtom 0) dimTwoWordRight)
        (CellExpr.whiskerLeft (crownAtom 0) dimTwoWordTwo) :=
  not_conv_of_linearizeFull_ne_withId crownValuation (by decide)

/-- The whiskered chain decider computes the positive verdict (equal chain tables → `true`). -/
example : decideFullConvSound crownValuation
    (CellExpr.whiskerLeft (crownAtom 0) dimTwoWordRight)
    (CellExpr.whiskerLeft (crownAtom 0) dimTwoWordLeft) = true := by decide

/-- The whiskered chain decider computes the negative verdict (distinct chain tables → `false`). -/
example : decideFullConvSound crownValuation
    (CellExpr.whiskerLeft (crownAtom 0) dimTwoWordRight)
    (CellExpr.whiskerLeft (crownAtom 0) dimTwoWordTwo) = false := by decide

/-! ## OMEGA-3 r2 wall-harvest markers (B3 — strictly factual) -/

/-- ★ **B3 — the idCongr sibling is CONSERVATIVE on atom words.**  `atomWord_conv_iff_withId` proves
`SaturatedConvOverWithId ↔ SaturatedConvOver` on the whisker-free single-generator fragment, via the
arithmetic separator.  `= true`. -/
def fxOmega_conservativeOnAtomWordsWithIdR2 : Bool := true

/-- ★ **B3 — whiskered completeness (fixed whisker) over the chain table is SHIPPED.**  On the whiskered
fragment `whiskerLeft w (atom word)`, sibling convertibility IS chain-table equality both ways
(`whiskeredAtomWord_conv_iff_linearizeFull_eq`), both decider verdicts exhibited.  `= true`. -/
def fxOmega_whiskeredCompletenessFixedWhiskerWithIdR2 : Bool := true

/-- ★ **B3 — the GENERAL whiskered completeness (varying whisker) stays OPEN.**  `= true` records the wall
is present: the fragment where the WHISKERING cell varies (composite 1-cells in whisker position) needs a
reconstruct that reads the whisker off the poles — the honest open work (the general bridge conv leg,
OMEGA-4).  Conservativity is a FRAGMENT statement; globally the sibling is STRICTLY larger than the old
congruence (`idCongr_word3_nonVacuous` proves `id a ~ id b`, unformable in the 8-constructor relation). -/
def fxOmega_generalWhiskeredCompletenessWithIdOpenR2 : Bool := true

end FX1Poly.Polygraph.Omega
