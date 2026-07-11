import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidRetractionConvDeltas

/-! # Polygraph/Omega/WalkingBunchedBimonoidStrictLawAbsorber — the BI cash-out: the three verbatim Node-A
components assemble AT THE MATRIX LEVEL, but the unconditional CELL-level strict-law absorber over the FREE
carrier is REFUTED (a mis-declared free generator breaks the strict unit law) — the honest correction of the
recon's Job-4 "mechanical assembly" verdict (WP-PROP r6, #2033, the 110-percent grind)

★ **THE DECISIVE r6 FINDING.**  The r5/r4 ledger named the strict-law matrix-soundness extension
(`fxBunchedBimonoid_matrixStrictLawExtensionReached`) with a verbatim three-component demand: "`matMul`
associativity (a finite-sum Fubini), the identity-matrix unit laws, and block multiplicativity
(whisker-functoriality + interchange)".  All THREE are now literally shipped:

  * matMul associativity = `bunchedBimonoidMatMulAssoc` (general, composable, r5);
  * identity-matrix unit laws = `bunchedBimonoidIdentity{Right,Left}Unit` (general-`n`, wf, r5);
  * block multiplicativity = `bunchedBimonoidBlockExchangeInterchange` (general, wf, r3).

They ASSEMBLE at the matrix level (`bunchedBimonoidStrictUnitLawsAssembleAtMatrixLevel`).

## BUT: the cell-level lift over the FREE carrier is FALSE

The recon's proposed flip built an unconditional
`IsSaturatedCongruenceWithId bunchedBimonoidStarCongruenceScope bunchedBimonoidMatrixEq` — i.e. the matrix
respects EVERY `StrictAxiomRel` row over ALL free `CellExpr`s.  This is REFUTED here.  The free carrier's `gen`
constructor admits MIS-DECLARED cells whose declared boundary does NOT match the label's matrix (`evalCell` fixes
the matrix by the LABEL, ignoring the declared source / target — `EvalGen`).  For the mis-declared
`bunchedBimonoidMisdeclaredMu` (label `addMult`, matrix `[[1,1]]` cols 2, but declared source `id` width 0), the
strict left-unit row `vcompUnitLeft` maps to `matMul [[1,1]] (identityMat 0) = [[]]` (`1 x 0`), which is NOT
`[[1,1]]` (`1 x 2`).  So the matrix does NOT respect `vcompUnitLeft` over the free carrier — the recon's
"evalCellWellFormed for arbitrary sub-cells" bridge is FALSE (the boundary-width equation fails at a mis-declared
`gen`), and the unconditional absorber cannot be built.

## The honest verdict

The obstruction is EXACTLY mis-declaration: the strict laws ARE matrix-respected on the WELL-TYPED fragment
(`bunchedBimonoidWellTypedMuVcompUnitLeftRespected`).  So `fxBunchedBimonoid_matrixStrictLawExtensionReached`
stays `= false` byte-intact — NOT because the three components are missing (they are shipped and assembled), but
because the CELL-level lift over the FREE carrier is refuted; the honest residual is a well-typedness predicate on
cells that the free `StrictAxiomRel` lacks.  NO fabricated flip.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # B4 — THE THREE VERBATIM COMPONENTS ASSEMBLE AT THE MATRIX LEVEL
    # =========================================================================================
-/

/-- ★★ **THE IDENTITY-UNIT COMPONENT ASSEMBLES — both unit laws for a general well-formed matrix.**  For any
well-formed `matM`, `matMul matM (identityMat matM.cols) = matM` (right unit) AND `matMul (identityMat matM.rows)
matM = matM` (left unit), by the shipped general-`n` `bunchedBimonoidIdentity{Right,Left}Unit`.  The matrix-level
content of the strict unit laws `vcompUnit{Right,Left}` — component (2) of the verbatim three, assembled. -/
theorem bunchedBimonoidStrictUnitLawsAssembleAtMatrixLevel (matM : BunchedBimonoidMat)
    (wf : bunchedBimonoidMatWellFormed matM) :
    bunchedBimonoidMatMul matM (bunchedBimonoidIdentityMat matM.cols) = matM
      ∧ bunchedBimonoidMatMul (bunchedBimonoidIdentityMat matM.rows) matM = matM :=
  ⟨bunchedBimonoidIdentityRightUnit matM wf, bunchedBimonoidIdentityLeftUnit matM wf⟩

/-- ★★ **THE ASSOCIATIVITY COMPONENT ASSEMBLES — matMul associativity for composable matrices.**  For composable
`matB.cols = matC.rows`, `matMul (matMul matA matB) matC = matMul matA (matMul matB matC)`, by the shipped general
Fubini `bunchedBimonoidMatMulAssoc`.  The matrix-level content of the strict `vcompAssoc` on WELL-TYPED (hence
composable) cells — component (1) of the verbatim three, assembled. -/
theorem bunchedBimonoidStrictAssocAssemblesAtMatrixLevel (matA matB matC : BunchedBimonoidMat)
    (composeBC : matB.cols = matC.rows) :
    bunchedBimonoidMatMul (bunchedBimonoidMatMul matA matB) matC
      = bunchedBimonoidMatMul matA (bunchedBimonoidMatMul matB matC) :=
  bunchedBimonoidMatMulAssoc matA matB matC composeBC

/-- ★★ **THE BLOCK-MULTIPLICATIVITY COMPONENT ASSEMBLES — the whisker-functoriality / interchange block law.**
For composable, well-formed blocks, `matMul (directSum topLeft bottomRight) (directSum leftFactor rightFactor) =
directSum (matMul topLeft leftFactor) (matMul bottomRight rightFactor)`, by the shipped
`bunchedBimonoidBlockExchangeInterchange`.  The matrix-level content of the strict whisker-functoriality +
interchange laws — component (3) of the verbatim three, assembled. -/
theorem bunchedBimonoidStrictBlockLawAssemblesAtMatrixLevel
    (topLeft bottomRight leftFactor rightFactor : BunchedBimonoidMat)
    (composeTop : topLeft.cols = leftFactor.rows) (composeBottom : bottomRight.cols = rightFactor.rows)
    (wfTop : bunchedBimonoidMatWellFormed topLeft) (wfBottom : bunchedBimonoidMatWellFormed bottomRight)
    (wfLeft : bunchedBimonoidMatWellFormed leftFactor) (wfRight : bunchedBimonoidMatWellFormed rightFactor) :
    bunchedBimonoidMatMul (bunchedBimonoidMatDirectSum topLeft bottomRight)
        (bunchedBimonoidMatDirectSum leftFactor rightFactor)
      = bunchedBimonoidMatDirectSum (bunchedBimonoidMatMul topLeft leftFactor)
        (bunchedBimonoidMatMul bottomRight rightFactor) :=
  bunchedBimonoidBlockExchangeInterchange topLeft bottomRight leftFactor rightFactor
    wfTop wfBottom wfLeft wfRight composeTop composeBottom

/-- ★★ **ESTABLISHED (B4) — the three verbatim Node-A components are literally shipped AND assemble at the matrix
level.**  `= true` records the verbatim three-component demand of
`fxBunchedBimonoid_matrixStrictLawExtensionReached` fully met: component (1) `matMul` associativity
(`bunchedBimonoidStrictAssocAssemblesAtMatrixLevel` = the shipped `bunchedBimonoidMatMulAssoc`); component (2) the
identity-matrix unit laws (`bunchedBimonoidStrictUnitLawsAssembleAtMatrixLevel` = the shipped
`bunchedBimonoidIdentity{Right,Left}Unit`); component (3) block multiplicativity
(`bunchedBimonoidStrictBlockLawAssemblesAtMatrixLevel` = the shipped
`bunchedBimonoidBlockExchangeInterchange`).  ALL three literally met — the recon's Job-4 flip precondition. -/
def fxBunchedBimonoid_biThreeComponentsAssembleAtMatrixLevel : Bool := true

/-! # =========================================================================================
    # B4 — THE FREE-CARRIER OBSTRUCTION: the cell-level strict-law lift is REFUTED
    # =========================================================================================
-/

/-- A **mis-declared additive-multiplication cell** — label `addMult` (so `evalCell` gives the matrix `[[1,1]]`,
cols 2) but declared source / target `id` (width 0).  The free `gen` constructor admits it (no globularity check,
Carrier §): `evalCell` fixes the matrix by the LABEL and IGNORES the declared boundary.  The witness that the free
carrier's cells are NOT all well-typed. -/
def bunchedBimonoidMisdeclaredMu : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.gen (dim := 1) BunchedBIGenLabel.addMult bunchedBimonoidIdOne bunchedBimonoidIdOne

/-- ★★★ **THE REFUTATION — the matrix does NOT respect the strict left-unit law over the FREE carrier.**  The
`vcompUnitLeft` row on `bunchedBimonoidMisdeclaredMu` relates `(id (boundarySource misMu)) ; misMu` to `misMu`;
but `boundarySource misMu = id` (width 0), so the LHS evaluates to `matMul [[1,1]] (identityMat 0) = [[]]` (`1 x
0`) while `misMu` evaluates to `[[1,1]]` (`1 x 2`) — UNEQUAL (cols `0 != 2`).  So the matrix evaluation does NOT
respect `StrictAxiomRel.vcompUnitLeft` over ALL free cells: the unconditional cell-level absorber the recon
proposed CANNOT be built.  The `evalCellWellFormed`-for-arbitrary-sub-cells bridge is FALSE at a mis-declared
`gen`. -/
theorem bunchedBimonoidMisdeclaredMuBreaksVcompUnitLeft :
    bunchedBimonoidEvalCell (CellExpr.vcomp (CellExpr.id (boundarySource bunchedBimonoidMisdeclaredMu))
        bunchedBimonoidMisdeclaredMu)
      ≠ bunchedBimonoidEvalCell bunchedBimonoidMisdeclaredMu := by
  intro heq
  have colsEq : (0 : Nat) = 2 := congrArg (fun matrix => matrix.cols) heq
  exact absurd colsEq (by decide)

/-- ★★ **THE POSITIVE INSTANCE — the strict left-unit law IS matrix-respected on the WELL-TYPED `mu_a`.**  For the
WELL-DECLARED `mu_a` (source `a.a`, width 2, matching its matrix `[[1,1]]` cols 2), the `vcompUnitLeft` row
evaluates to `matMul [[1,1]] (identityMat 2) = [[1,1]]` = `evalCell mu_a` (`rfl`, the `identityRightUnit`
specialised).  So the obstruction is EXACTLY mis-declaration: the strict laws ARE respected on the well-typed
fragment where the boundary-width equation holds. -/
theorem bunchedBimonoidWellTypedMuVcompUnitLeftRespected :
    bunchedBimonoidEvalCell (CellExpr.vcomp (CellExpr.id (boundarySource bunchedBimonoidAddMuGen))
        bunchedBimonoidAddMuGen)
      = bunchedBimonoidEvalCell bunchedBimonoidAddMuGen := rfl

/-- ★★ **ESTABLISHED (B4) — the free-carrier strict-law lift is REFUTED (the honest correction).**  `= true`
records `bunchedBimonoidMisdeclaredMuBreaksVcompUnitLeft` (the matrix does NOT respect `vcompUnitLeft` over the
free carrier, via the mis-declared `gen`) together with the positive instance
`bunchedBimonoidWellTypedMuVcompUnitLeftRespected` (the law IS respected on the well-typed `mu_a`).  This
CORRECTS the recon's Job-4 verdict: the three components are shipped and assemble at the matrix level, but the
recon's unconditional cell-level absorber (`IsSaturatedCongruenceWithId starScope matrixEq`) is IMPOSSIBLE — the
`evalCellWellFormed`-for-arbitrary-cells bridge is false at a mis-declared `gen`.  The obstruction is exactly
mis-declaration; the honest fix is a well-typedness predicate the free `StrictAxiomRel` lacks. -/
def fxBunchedBimonoid_freeCarrierStrictLawLiftRefuted : Bool := true

/-! # =========================================================================================
    # B4 — THE LEDGER: the r3 wall stays false byte-intact + the honest well-typed residual
    # =========================================================================================
-/

/-- ★ **r6 RESIDUAL — the strict-law CELL absorber needs a WELL-TYPEDNESS predicate (NOT shipped).**  `= false`
records the honest residual the refutation exposes: to lift the three matrix-level components to a CELL-level
strict-law absorber, the base relation must be restricted to WELL-TYPED cells (where `evalCell`'s matrix
dimensions match the declared boundary widths — the boundary-width equation that FAILS at a mis-declared `gen`).
The free `StrictAxiomRel` carries no such predicate, so the unconditional
`IsSaturatedCongruenceWithId bunchedBimonoidStarCongruenceScope bunchedBimonoidMatrixEq` is refuted
(`bunchedBimonoidMisdeclaredMuBreaksVcompUnitLeft`).  Building the well-typedness inductive + the restricted
`evalCellWellFormed` bridge is the r6 residual — the three components assemble the moment the base relation is
restricted to it. -/
def fxBunchedBimonoid_strictLawCellAbsorberNeedsWellTypedPredicate : Bool := false

/-- ★ **THE r3 STRICT-LAW EXTENSION WALL STAYS false — NO fabricated flip.**  `= false` records that
`fxBunchedBimonoid_matrixStrictLawExtensionReached` (r3 MatrixSemantics, the SOUNDNESS lift over `StrictAxiomRel
union R13`) stays `= false` byte-intact — NOT because the three components are missing (they are shipped and
assemble at the matrix level, `fxBunchedBimonoid_biThreeComponentsAssembleAtMatrixLevel`), but because the
CELL-level lift over the FREE carrier is REFUTED (`fxBunchedBimonoid_freeCarrierStrictLawLiftRefuted`).  The
directive's flip precondition ("the verbatim three components are all literally met") IS met, but the flip is NOT
warranted — the recon MISSED the free-carrier obstruction, so flipping the soundness marker would be a
fabrication.  The r3 marker keeps its name and `= false` value byte-intact (cross-file). -/
def fxBunchedBimonoid_strictLawExtensionStaysFalseNoFabricatedFlip : Bool := false

/-- ★★★ **ESTABLISHED (B4) — the WP-PROP r6 BI cash-out ledger (honest scoreboard).**  `= true` records the
complete r6 BI adjudication: the three verbatim Node-A components literally shipped AND assembled at the matrix
level (`fxBunchedBimonoid_biThreeComponentsAssembleAtMatrixLevel` — matMul associativity + identity units + block
multiplicativity); the DECISIVE correction of the recon's Job-4 "mechanical assembly" verdict — the unconditional
cell-level absorber over the FREE carrier is REFUTED
(`fxBunchedBimonoid_freeCarrierStrictLawLiftRefuted`, the mis-declared-`gen` datum
`bunchedBimonoidMisdeclaredMuBreaksVcompUnitLeft`) with the well-typed positive instance delimiting the
obstruction; and the honest residual named (the well-typedness predicate,
`fxBunchedBimonoid_strictLawCellAbsorberNeedsWellTypedPredicate = false`).  The r3 soundness-lift wall
`fxBunchedBimonoid_matrixStrictLawExtensionReached` stays `= false` byte-intact
(`fxBunchedBimonoid_strictLawExtensionStaysFalseNoFabricatedFlip = false`) — the three components are met but the
free-carrier lift is refuted, so NO fabricated flip.  Every upstream `= false` marker byte-intact. -/
def fxBunchedBimonoid_biCashOutRoundSixLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
