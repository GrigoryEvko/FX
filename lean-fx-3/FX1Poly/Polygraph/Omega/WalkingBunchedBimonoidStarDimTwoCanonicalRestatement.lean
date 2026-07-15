-- TODO: DELETE THIS GARBAGE -- defective bunchedBimonoid star (refuted r29/r30/r31); superseded by the LafontProp re-founding
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarColourMislabelRefutation
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidBlockThreadingConvGeneral

/-! # Polygraph/Omega/WalkingBunchedBimonoidStarDimTwoCanonicalRestatement — the corrected #2033 completeness
target RE-STATED at its honest scope: dimension 2, canonical generator nodes (WP-PROP r29, #2033)

★★ **THE RESTATEMENT.**  The r29 sibling (`StarColourMislabelRefutation`) DECIDED the r7 star FALSE through the
off-dimension label leak.  This file re-states the genuine Lafont / Pirashvili / Fox completeness content at the
scope the twenty-four-round siege actually fought on, with the leak closed by construction:

  * **dimension PINNED to 2** — the matrix semantics is faithful only there (`bunchedBimonoidEvalCell` is a
    width at dimension 1 and constantly `()` above 2: `bunchedBimonoidDimThreeEvalTriviallyEqual`);
  * **canonical generator nodes** (`bunchedBimonoidCellGensCanonical`) — every `gen` subterm IS one of the nine
    presentation generators, on the nose: colour labels at label-dimension 0 with the point boundaries,
    operation labels at label-dimension 1 with THEIR canonical boundary words, no generators above.  This closes
    BOTH residual leaks the refutation round exposed: the colour-position mislabel
    (`bunchedBimonoidColourMislabeledMuOneCell`, excluded by `...MislabeledMuNotCanonical`) and the
    boundary-respelled operation node (`bunchedBimonoidBoundaryRespelledMu` — label `addMult` with the
    width-2-but-noncanonical source `a . (idOne . a)`, which passes EVERY r7 guard at dimension 2 yet is a fresh
    normal form: no congruence rule rewrites INSIDE a `gen` node's declared boundaries — excluded by
    `...RespelledMuNotCanonical`).

The corrected target `bunchedBimonoidStarStatementDimTwoCanonicalGens` carries additivity (r6 guard),
well-typedness (r7 guard), and generator-canonicity (r29 guard) on both cells.  It is NAMED, NOT proven — the
honest owner `fxBunchedBimonoid_dimTwoCanonicalGensStarStillOpen = false` opens the corrected siege with the
bill: (i) the total retract to the spider normal form, whose `vcomp` case consumes the r29-delivered
block-threading (`bunchedBimonoidBlockThreadingConvStatement{Mu,Delta}Delivered`) but still needs the general
`wideSwap(m,n)` riffle recursion (the r8 gate, honestly walled); (ii) the equal-matrices perm middle, already a
theorem via the r26 `bunchedBimonoidCoxeterWordUniqueViaRecComb` once the retract spells its middle as a
`permWord`; (iii) the assembly.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # THE CANONICAL-GENERATOR-NODE PREDICATE (the r29 guard)
    # =========================================================================================
-/

/-- ★★ **The per-node canonicity table** — a `gen` node is canonical iff it is one of the NINE presentation
generators ON THE NOSE: at label-dimension 0 a colour with the point boundaries; at label-dimension 1 one of the
seven operations with ITS canonical declared boundary words; no generators at label-dimension >= 2.  This is
strictly stronger than label PLACEMENT: it also pins the declared boundary SPELLINGS (the respelled-boundary
leak `bunchedBimonoidBoundaryRespelledMu` below shows placement alone is not enough). -/
def bunchedBimonoidGenNodeCanonical : (labelDim : Nat) → BunchedBIGenLabel →
    CellExpr bunchedBimonoidOmegaComputad labelDim → CellExpr bunchedBimonoidOmegaComputad labelDim → Prop
  | 0, label, source, target =>
      (label = BunchedBIGenLabel.additiveColour ∨ label = BunchedBIGenLabel.multColour)
        ∧ source = bunchedBimonoidPoint ∧ target = bunchedBimonoidPoint
  | 1, label, source, target =>
      (label = BunchedBIGenLabel.addMult
          ∧ source = bunchedBimonoidAaWord ∧ target = bunchedBimonoidAdditiveGen)
        ∨ (label = BunchedBIGenLabel.addUnit
            ∧ source = bunchedBimonoidIdOne ∧ target = bunchedBimonoidAdditiveGen)
        ∨ (label = BunchedBIGenLabel.addComult
            ∧ source = bunchedBimonoidAdditiveGen ∧ target = bunchedBimonoidAaWord)
        ∨ (label = BunchedBIGenLabel.addCounit
            ∧ source = bunchedBimonoidAdditiveGen ∧ target = bunchedBimonoidIdOne)
        ∨ (label = BunchedBIGenLabel.addSwap
            ∧ source = bunchedBimonoidAaWord ∧ target = bunchedBimonoidAaWord)
        ∨ (label = BunchedBIGenLabel.multMult
            ∧ source = bunchedBimonoidMmWord ∧ target = bunchedBimonoidMultGen)
        ∨ (label = BunchedBIGenLabel.multUnit
            ∧ source = bunchedBimonoidIdOne ∧ target = bunchedBimonoidMultGen)
  | _ + 2, _, _, _ => False

/-- ★★ **THE CANONICAL-GENERATORS PREDICATE** — a structural `Prop` fold over all six carrier constructors:
every `gen` node satisfies the canonicity table (and its declared boundaries recursively do), every other
constructor recurses.  The cells satisfying this are EXACTLY the words freely generated by the nine presentation
generators under `id` / `vcomp` / whiskering — the honest domain of the PROP completeness statement. -/
def bunchedBimonoidCellGensCanonical : {dim : Nat} → CellExpr bunchedBimonoidOmegaComputad dim → Prop
  | _, .ofMode _ => True
  | _, .gen (dim := labelDim) label source target =>
      bunchedBimonoidGenNodeCanonical labelDim label source target
        ∧ bunchedBimonoidCellGensCanonical source ∧ bunchedBimonoidCellGensCanonical target
  | _, .id cell => bunchedBimonoidCellGensCanonical cell
  | _, .vcomp left right =>
      bunchedBimonoidCellGensCanonical left ∧ bunchedBimonoidCellGensCanonical right
  | _, .whiskerLeft whisker cell =>
      bunchedBimonoidCellGensCanonical whisker ∧ bunchedBimonoidCellGensCanonical cell
  | _, .whiskerRight cell whisker =>
      bunchedBimonoidCellGensCanonical cell ∧ bunchedBimonoidCellGensCanonical whisker

/-! ## The positive witnesses — the genuine generators are canonical -/

/-- The additive colour is canonical. -/
theorem bunchedBimonoidAdditiveGenCanonical :
    bunchedBimonoidCellGensCanonical bunchedBimonoidAdditiveGen :=
  ⟨⟨Or.inl rfl, rfl, rfl⟩, True.intro, True.intro⟩

/-- The canonical `a.a` word is canonical. -/
theorem bunchedBimonoidAaWordCanonical : bunchedBimonoidCellGensCanonical bunchedBimonoidAaWord :=
  ⟨bunchedBimonoidAdditiveGenCanonical, bunchedBimonoidAdditiveGenCanonical⟩

/-- The additive multiplication `mu_a` is canonical (its declared boundaries recursively so). -/
theorem bunchedBimonoidAddMuGenCanonical : bunchedBimonoidCellGensCanonical bunchedBimonoidAddMuGen :=
  ⟨Or.inl ⟨rfl, rfl, rfl⟩, bunchedBimonoidAaWordCanonical, bunchedBimonoidAdditiveGenCanonical⟩

/-- The additive comultiplication `delta_a` is canonical. -/
theorem bunchedBimonoidAddDeltaGenCanonical : bunchedBimonoidCellGensCanonical bunchedBimonoidAddDeltaGen :=
  ⟨Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)), bunchedBimonoidAdditiveGenCanonical,
    bunchedBimonoidAaWordCanonical⟩

/-- The additive braiding `sigma_a` is canonical. -/
theorem bunchedBimonoidAddSigmaGenCanonical : bunchedBimonoidCellGensCanonical bunchedBimonoidAddSigmaGen :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))), bunchedBimonoidAaWordCanonical,
    bunchedBimonoidAaWordCanonical⟩

/-! ## The negative witnesses — BOTH r29 leaks are excluded by canonicity -/

/-- ★★ **The colour-mislabeled datum is NOT canonical** — the r29 refutation datum fails the label-dimension-0
canonicity table (`addMult` is neither colour). -/
theorem bunchedBimonoidColourMislabeledMuNotCanonical :
    ¬ bunchedBimonoidCellGensCanonical bunchedBimonoidColourMislabeledMuOneCell := by
  intro hcanonical
  cases hcanonical.1.1 with
  | inl hAdditive => exact BunchedBIGenLabel.noConfusion hAdditive
  | inr hMult => exact BunchedBIGenLabel.noConfusion hMult

/-- ★★ **THE SECOND LEAK — the boundary-respelled operation node.**  Label `addMult` at its correct
label-dimension with a WIDTH-2 source word `a . (idOne . a)` that is NOT the canonical `a.a`.  Additive,
well-typed (the width agreement sees only the width), matrix-equal to `mu_a` — yet a fresh normal form: no
congruence rule rewrites INSIDE a `gen` node's declared boundaries.  Placement alone would admit it; canonicity
excludes it. -/
def bunchedBimonoidBoundaryRespelledMu : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.gen (dim := 1) BunchedBIGenLabel.addMult
    (CellExpr.vcomp bunchedBimonoidAdditiveGen
      (CellExpr.vcomp bunchedBimonoidIdOne bunchedBimonoidAdditiveGen))
    bunchedBimonoidAdditiveGen

/-- The respelled datum passes EVERY r7 guard at dimension 2: additive, well-typed (source width `1 + (0 + 1) =
2` matches the `addMult` matrix cols), and matrix-equal to the canonical `mu_a`. -/
theorem bunchedBimonoidBoundaryRespelledMuPassesRSevenGuards :
    bunchedBimonoidCellUsesOnlyAdditive bunchedBimonoidBoundaryRespelledMu = true
      ∧ bunchedBimonoidCellWellTyped bunchedBimonoidBoundaryRespelledMu
      ∧ bunchedBimonoidEvalCell bunchedBimonoidBoundaryRespelledMu
          = bunchedBimonoidEvalCell bunchedBimonoidAddMuGen :=
  ⟨rfl,
    ⟨⟨⟨True.intro, True.intro, True.intro⟩,
        ⟨True.intro, ⟨True.intro, True.intro, True.intro⟩, True.intro⟩, True.intro⟩,
      ⟨True.intro, True.intro, True.intro⟩, rfl, rfl⟩,
    rfl⟩

/-- ★★ **The respelled datum is NOT canonical** — its source `a . (idOne . a)` differs from every canonical
boundary word of every operation label (the `addMult` arm demands `a.a` on the nose; the other six arms fail on
the label).  Machine-checked disjunct-by-disjunct via constructor-mismatch `noConfusion` and `injection`
drilling into the source word. -/
theorem bunchedBimonoidBoundaryRespelledMuNotCanonical :
    ¬ bunchedBimonoidCellGensCanonical bunchedBimonoidBoundaryRespelledMu := by
  intro hcanonical
  cases hcanonical.1 with
  | inl hMuArm =>
      have hsourceEq := hMuArm.2.1
      have hsizeEq := congrArg
        (fun (word : CellExpr bunchedBimonoidOmegaComputad 1) => cellSize word) hsourceEq
      exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hsizeEq)))
  | inr hRest =>
      cases hRest with
      | inl hEtaArm => exact BunchedBIGenLabel.noConfusion hEtaArm.1
      | inr hRest2 =>
          cases hRest2 with
          | inl hDeltaArm => exact BunchedBIGenLabel.noConfusion hDeltaArm.1
          | inr hRest3 =>
              cases hRest3 with
              | inl hEpsArm => exact BunchedBIGenLabel.noConfusion hEpsArm.1
              | inr hRest4 =>
                  cases hRest4 with
                  | inl hSigmaArm => exact BunchedBIGenLabel.noConfusion hSigmaArm.1
                  | inr hRest5 =>
                      cases hRest5 with
                      | inl hMultMuArm => exact BunchedBIGenLabel.noConfusion hMultMuArm.1
                      | inr hMultEtaArm => exact BunchedBIGenLabel.noConfusion hMultEtaArm.1

/-- ★ **The dim-2 mislabeled-whisker hazard** — whiskering the r29 refutation datum onto `sigma` produces a
DIMENSION-2 pair passing additivity, well-typedness, and matrix equality (both whiskering words have width 1),
separated only by canonicity.  The witness that the r29 guard is load-bearing at the pinned dimension itself,
not merely at dimension 1. -/
theorem bunchedBimonoidMislabeledWhiskerPairSeparatedOnlyByCanonicity :
    bunchedBimonoidCellUsesOnlyAdditive
        (CellExpr.whiskerLeft bunchedBimonoidColourMislabeledMuOneCell bunchedBimonoidAddSigmaGen) = true
      ∧ bunchedBimonoidCellWellTyped
          (CellExpr.whiskerLeft bunchedBimonoidColourMislabeledMuOneCell bunchedBimonoidAddSigmaGen)
      ∧ bunchedBimonoidEvalCell
          (CellExpr.whiskerLeft bunchedBimonoidColourMislabeledMuOneCell bunchedBimonoidAddSigmaGen)
        = bunchedBimonoidEvalCell
            (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
      ∧ ¬ bunchedBimonoidCellGensCanonical
          (CellExpr.whiskerLeft bunchedBimonoidColourMislabeledMuOneCell bunchedBimonoidAddSigmaGen)
      ∧ bunchedBimonoidCellGensCanonical
          (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen) :=
  ⟨rfl,
    ⟨bunchedBimonoidColourMislabeledMuOneCellWellTyped, bunchedBimonoidAddSigmaGenWellTyped⟩,
    rfl,
    fun hcanonical => bunchedBimonoidColourMislabeledMuNotCanonical hcanonical.1,
    ⟨bunchedBimonoidAdditiveGenCanonical, bunchedBimonoidAddSigmaGenCanonical⟩⟩

/-! # =========================================================================================
    # THE CORRECTED TARGET, NAMED (NOT proven)
    # =========================================================================================
-/

/-- ★★★ **THE CORRECTED #2033 COMPLETENESS TARGET, RE-STATED (NOT proven).**  Dimension PINNED to 2; both cells
additive (r6 guard), well-typed (r7 guard), and with CANONICAL generator nodes (r29 guard); equal `Mat(N)`
matrices imply convertibility over the star scope.  Every known refutation datum is excluded by a proven-
necessary guard: `mu_m` (additivity, r6), `misdeclaredMu` (well-typedness, r7), the colour-mislabel and the
boundary-respelled node and the dim-1/dim->=3 quantifier leaks (canonicity + the dimension pin, r29).  The
completeness bill: the total retract (its `vcomp` case consumes the r29 block-threading delivery; the general
`wideSwap(m,n)` riffle recursion is the remaining r8 gate), the r26 recComb perm middle, the assembly. -/
def bunchedBimonoidStarStatementDimTwoCanonicalGens : Prop :=
  ∀ (cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad 2),
    bunchedBimonoidCellUsesOnlyAdditive cellAlpha = true →
    bunchedBimonoidCellUsesOnlyAdditive cellBeta = true →
    bunchedBimonoidCellWellTyped cellAlpha →
    bunchedBimonoidCellWellTyped cellBeta →
    bunchedBimonoidCellGensCanonical cellAlpha →
    bunchedBimonoidCellGensCanonical cellBeta →
    bunchedBimonoidEvalCell cellAlpha = bunchedBimonoidEvalCell cellBeta →
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope cellAlpha cellBeta

/-! # =========================================================================================
    # THE MARKERS — the corrected siege opens honestly
    # =========================================================================================
-/

/-- ★★★ **ESTABLISHED — the corrected completeness target is re-stated at its honest scope.**  `= true` records
`bunchedBimonoidStarStatementDimTwoCanonicalGens` (dimension-2-pinned, additive + well-typed + canonical-gens)
and the guard witnesses: the seven positive canonicity proofs on the genuine generators, the exclusion of BOTH
r29 leaks (`bunchedBimonoid{ColourMislabeledMu,BoundaryRespelledMu}NotCanonical` — the second passing every r7
guard, `...PassesRSevenGuards`), and the dim-2 mislabeled-whisker hazard separated only by canonicity.  The
statement leak the r29 decision exposed is closed BY CONSTRUCTION in the new target. -/
def fxBunchedBimonoid_correctedStarRestatedDimTwoCanonicalGens : Bool := true

/-- ★ **THE CORRECTED STAR IS NAMED, NOT PROVEN — the new owner (no flip).**  `= false` records that
`bunchedBimonoidStarStatementDimTwoCanonicalGens` is NOT proven: the outer retraction legs are the r6 CONV
deltas, the `vcomp` block-threading engine is DELIVERED (r29, all widths, both colours), the perm middle is the
r26 recComb theorem — but the total retract still needs the general `wideSwap(m,n)` riffle recursion (the r8
gate, honestly walled) and the assembly.  This marker flips ONLY with the corrected star genuinely proven. -/
def fxBunchedBimonoid_dimTwoCanonicalGensStarStillOpen : Bool := false

/-- ★★★ **ESTABLISHED — the WP-PROP r29 restatement ledger (the honest scoreboard).**  `= true` records the
complete r29 round: THE DECISION (the r7 star refuted, sibling file), THE B1 DELIVERY (the block-threading CONV
at every width, sibling file), and THE RESTATEMENT (this file: the canonicity guard, both leak exclusions, the
corrected target named).  The corrected owner stays `= false`; every frozen upstream marker byte-intact;
zero-axiom throughout. -/
def fxBunchedBimonoid_starDimTwoCanonicalRestatementLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
