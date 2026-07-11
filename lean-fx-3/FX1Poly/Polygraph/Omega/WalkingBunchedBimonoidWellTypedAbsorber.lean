import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStrictLawAbsorber

/-! # Polygraph/Omega/WalkingBunchedBimonoidWellTypedAbsorber — the well-typedness predicate that the r6
`StrictLawAbsorber` named as the missing prerequisite: the structural `CellWellTyped` inductive, the
`evalCellWellFormed` boundary-width bridge, and the RESTRICTED strict-unit-law absorber it unlocks (WP-PROP r7,
#2033, the 110-percent grind)

★ **THE SPINE OF r7 — the delivery of the r6 residual
`fxBunchedBimonoid_strictLawCellAbsorberNeedsWellTypedPredicate`.**  The r6 `StrictLawAbsorber` refuted the
recon's UNCONDITIONAL cell-level strict-law absorber over the FREE carrier: a mis-declared free generator
`bunchedBimonoidMisdeclaredMu` (label `addMult`, matrix cols 2, but declared boundary `id` of width 0) breaks the
strict left-unit law at the matrix level (`matMul [[1,1]] (identityMat 0) = [[]]` is `1 x 0`, not `1 x 2`).  The
r6 verdict: the free `StrictAxiomRel` carries no well-typedness predicate, so the absorber can only be built once
the base relation is RESTRICTED to well-typed cells.  This file delivers exactly that predicate.

## The `CellWellTyped` predicate (the width-agreement the mis-declaration violates)

`bunchedBimonoidCellWellTyped` is a structural `Prop` over all six carrier constructors (constant `Prop` motive,
propext-clean, mirroring `IsGlobularCell`).  Its NEW content over `IsGlobularCell` is the generator
width-agreement (`bunchedBimonoidGenWidthAgreement`): a 2-cell generator's declared source / target widths must
match its matrix's `cols` / `rows`.  This is EXACTLY what `misdeclaredMu` fails (`wordWidth(id) = 0 != cols = 2`)
and what `mu_a` satisfies (`wordWidth(a.a) = 2 = cols`).  The headline self-attack
`bunchedBimonoidMisdeclaredMuNotWellTyped` machine-checks that the r6 counterexample is EXCLUDED by the predicate.

## The `evalCellWellFormed` bridge (well-typed ⟹ boundary-width agreement)

`bunchedBimonoidEvalCellWellFormed` proves, by plain structural induction (same shape as
`globularLegs_of_isGlobularCell`), that a well-typed dim-2 cell's matrix dimensions agree with its declared
boundary widths (`(evalCell cell).rows = wordWidth(boundaryTarget cell)`, `.cols = wordWidth(boundarySource
cell)`).  The `gen` case fires the width-agreement conjunct; `vcomp` chains the two sub-bridges; the whiskers add
the fixed block width; `id` is `rfl`.

## The RESTRICTED absorber (the strict unit laws are respected on well-typed cells)

`bunchedBimonoidRestrictedVcompUnit{Left,Right}Respected` prove the exact rows the r6 refutation broke — but
RESTRICTED to well-typed cells (with well-formed matrices, always true): on a well-typed cell the bridge's
width-agreement makes `identityMat (wordWidth(boundary)) = identityMat ((evalCell cell).cols)`, so the shipped
general `bunchedBimonoidIdentity{Right,Left}Unit` closes the strict unit law.  The three r6 Node-A components
assemble the moment the base relation is gated on `CellWellTyped` — the residual dissolves.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # B3 — THE WELL-TYPEDNESS PREDICATE (the width-agreement the mis-declaration violates)
    # =========================================================================================
-/

/-- The **generator width-agreement** — a 2-cell generator (`labelDim = 1`) is well-declared iff its declared
source / target widths match its matrix's `cols` / `rows`; a 1-cell generator (`labelDim = 0`) and higher carry no
matrix constraint (`True`).  This is the NEW conjunct over `IsGlobularCell`: it is exactly what `misdeclaredMu`
(source width 0, matrix cols 2) fails and what `mu_a` (source width 2, matrix cols 2) satisfies. -/
def bunchedBimonoidGenWidthAgreement : (labelDim : Nat) → BunchedBIGenLabel →
    BunchedBimonoidEvalCarrier labelDim → BunchedBimonoidEvalCarrier labelDim → Prop
  | 0, _, _, _ => True
  | 1, label, sourceWidth, targetWidth =>
      sourceWidth = (bunchedBimonoidGenMatrix label).cols
        ∧ targetWidth = (bunchedBimonoidGenMatrix label).rows
  | _ + 2, _, _, _ => True

/-- The **vertical-composite composability** — at the matrix level (`d = 1`) a vertical composite is composable
iff the left factor's output width matches the right factor's input width (`leftMatrix.rows = rightMatrix.cols`);
at the word level (`d = 0`, concatenation) and higher there is no constraint (`True`). -/
def bunchedBimonoidVcompComposable : (d : Nat) →
    BunchedBimonoidEvalCarrier (d + 1) → BunchedBimonoidEvalCarrier (d + 1) → Prop
  | 0, _, _ => True
  | 1, leftMatrix, rightMatrix => leftMatrix.rows = rightMatrix.cols
  | _ + 2, _, _ => True

/-- ★★ **THE WELL-TYPEDNESS PREDICATE `CellWellTyped`** — a structural `Prop` over all six carrier constructors
(constant `Prop` motive, propext-clean, the `IsGlobularCell` idiom plus the width/composability agreements the
matrix semantics need): every generator satisfies its width-agreement, every vertical composite is
matrix-composable, and both propagate into sub-cells.  This is the predicate the r6 `StrictLawAbsorber` named as
the missing prerequisite — the base relation the strict-law absorber must be restricted to. -/
def bunchedBimonoidCellWellTyped : {dim : Nat} → CellExpr bunchedBimonoidOmegaComputad dim → Prop
  | _, .ofMode _ => True
  | _, .gen (dim := labelDim) label source target =>
      bunchedBimonoidCellWellTyped source ∧ bunchedBimonoidCellWellTyped target
        ∧ bunchedBimonoidGenWidthAgreement labelDim label
            (bunchedBimonoidEvalCell source) (bunchedBimonoidEvalCell target)
  | _, .id cell => bunchedBimonoidCellWellTyped cell
  | _, .vcomp (dim := d) left right =>
      bunchedBimonoidCellWellTyped left ∧ bunchedBimonoidCellWellTyped right
        ∧ bunchedBimonoidVcompComposable d (bunchedBimonoidEvalCell left) (bunchedBimonoidEvalCell right)
  | _, .whiskerLeft whiskerCell cell =>
      bunchedBimonoidCellWellTyped whiskerCell ∧ bunchedBimonoidCellWellTyped cell
  | _, .whiskerRight cell whiskerCell =>
      bunchedBimonoidCellWellTyped cell ∧ bunchedBimonoidCellWellTyped whiskerCell

/-- ★★★ **THE HEADLINE SELF-ATTACK — the r6 counterexample is EXCLUDED by well-typedness.**  The mis-declared
`bunchedBimonoidMisdeclaredMu` (label `addMult`, matrix cols 2, declared source `id` of width 0) is NOT
`CellWellTyped`: its generator width-agreement demands `wordWidth(id) = cols`, i.e. `0 = 2`, which is false.  So
the exact datum the r6 `StrictLawAbsorber` used to refute the free-carrier absorber CANNOT satisfy the restricted
star's well-typedness hypothesis — the well-typed restriction excises the obstruction. -/
theorem bunchedBimonoidMisdeclaredMuNotWellTyped :
    ¬ bunchedBimonoidCellWellTyped bunchedBimonoidMisdeclaredMu := by
  intro hwt
  have widthClash : (0 : Nat) = 2 := hwt.2.2.1
  exact absurd widthClash (by decide)

/-- ★★ **THE POSITIVE — `mu_a` IS well-typed.**  The well-declared additive multiplication (source `a.a` width 2,
target `a` width 1, matrix `[[1,1]]` cols 2 rows 1) satisfies every width-agreement.  The well-typed fragment the
restricted absorber lives on contains all the genuine generators. -/
theorem bunchedBimonoidAddMuGenWellTyped :
    bunchedBimonoidCellWellTyped bunchedBimonoidAddMuGen :=
  ⟨⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩, trivial⟩,
    ⟨trivial, trivial, trivial⟩, rfl, rfl⟩

/-! # =========================================================================================
    # B3 — THE evalCellWellFormed BRIDGE (well-typed ⟹ boundary-width agreement)
    # =========================================================================================
-/

/-- The **boundary-width agreement target** — `True` below dimension 2, and at dimension 2 the two equations the
matrix semantics must satisfy: the matrix's `rows` / `cols` equal the declared target / source boundary widths.
The dim-generic motive of the bridge (the `GlobularLegs` idiom). -/

def bunchedBimonoidBoundaryWidthAgrees :
    {dim : Nat} → CellExpr bunchedBimonoidOmegaComputad dim → Prop
  | 0, _ => True
  | 1, _ => True
  | 2, cell =>
      (bunchedBimonoidEvalCell cell).rows = bunchedBimonoidWordWidth (boundaryTarget cell)
        ∧ (bunchedBimonoidEvalCell cell).cols = bunchedBimonoidWordWidth (boundarySource cell)
  | _ + 3, _ => True

/-- ★★ **THE BRIDGE — a well-typed cell's matrix dimensions AGREE with its declared boundary widths.**  By plain
structural induction (the `globularLegs_of_isGlobularCell` shape): `gen` fires the width-agreement conjunct,
`vcomp` chains the two sub-bridges (right's target, left's source — composability not even needed), the whiskers
add the fixed block width via `congrArg`, `id` is `rfl`, and every off-dimension-2 case is `True.intro`.  This is
the `evalCellWellFormed` the r6 residual named — the equation that FAILS at the mis-declared `gen` and HOLDS on
the well-typed fragment. -/
theorem bunchedBimonoidEvalCellWellFormed {dim : Nat}
    (cell : CellExpr bunchedBimonoidOmegaComputad dim) :
    bunchedBimonoidCellWellTyped cell → bunchedBimonoidBoundaryWidthAgrees cell := by
  induction cell with
  | ofMode _ => intro _; exact True.intro
  | @gen ctorDim _ _ _ _ _ =>
      intro hwt
      cases ctorDim with
      | zero => exact True.intro
      | succ ctorDimMinus =>
          cases ctorDimMinus with
          | zero =>
              obtain ⟨_, _, hagree⟩ := hwt
              exact ⟨hagree.2.symm, hagree.1.symm⟩
          | succ _ => exact True.intro
  | @id ctorDim _ _ =>
      intro _
      cases ctorDim with
      | zero => exact True.intro
      | succ ctorDimMinus =>
          cases ctorDimMinus with
          | zero => exact ⟨rfl, rfl⟩
          | succ _ => exact True.intro
  | @vcomp ctorDim _ _ ihLeft ihRight =>
      intro hwt
      cases ctorDim with
      | zero => exact True.intro
      | succ ctorDimMinus =>
          cases ctorDimMinus with
          | zero =>
              obtain ⟨wtLeft, wtRight, _⟩ := hwt
              exact ⟨(ihRight wtRight).1, (ihLeft wtLeft).2⟩
          | succ _ => exact True.intro
  | @whiskerLeft ctorDim whiskerCell _ _ ihInner =>
      intro hwt
      cases ctorDim with
      | zero =>
          obtain ⟨_, wtInner⟩ := hwt
          obtain ⟨rowsInner, colsInner⟩ := ihInner wtInner
          exact ⟨congrArg (fun rest => bunchedBimonoidWordWidth whiskerCell + rest) rowsInner,
            congrArg (fun rest => bunchedBimonoidWordWidth whiskerCell + rest) colsInner⟩
      | succ _ => exact True.intro
  | @whiskerRight ctorDim _ whiskerCell ihInner _ =>
      intro hwt
      cases ctorDim with
      | zero =>
          obtain ⟨wtInner, _⟩ := hwt
          obtain ⟨rowsInner, colsInner⟩ := ihInner wtInner
          exact ⟨congrArg (fun rest => rest + bunchedBimonoidWordWidth whiskerCell) rowsInner,
            congrArg (fun rest => rest + bunchedBimonoidWordWidth whiskerCell) colsInner⟩
      | succ _ => exact True.intro

/-! ## More positives — the additive generators are well-typed -/

/-- **`delta_a` is well-typed** (source `a` width 1, target `a.a` width 2, matrix `[[1],[1]]` cols 1 rows 2). -/
theorem bunchedBimonoidAddDeltaGenWellTyped :
    bunchedBimonoidCellWellTyped bunchedBimonoidAddDeltaGen :=
  ⟨⟨trivial, trivial, trivial⟩,
    ⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩, trivial⟩, rfl, rfl⟩

/-- **`sigma_a` is well-typed** (source / target `a.a` width 2, matrix `[[0,1],[1,0]]` cols 2 rows 2). -/
theorem bunchedBimonoidAddSigmaGenWellTyped :
    bunchedBimonoidCellWellTyped bunchedBimonoidAddSigmaGen :=
  ⟨⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩, trivial⟩,
    ⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩, trivial⟩, rfl, rfl⟩

/-! # =========================================================================================
    # B3 — THE RESTRICTED ABSORBER (the strict unit laws are respected on well-typed cells)
    # =========================================================================================
-/

/-- ★★★ **THE RESTRICTED STRICT LEFT-UNIT LAW — respected on every well-typed cell.**  The exact row the r6
refutation broke on the free carrier (`vcompUnitLeft`) IS matrix-respected once the cell is well-typed: the bridge
gives `(evalCell cell).cols = wordWidth(boundarySource cell)`, so `identityMat (wordWidth(boundarySource cell)) =
identityMat ((evalCell cell).cols)` and the shipped general `bunchedBimonoidIdentityRightUnit` closes it.  The
well-formedness hypothesis is always dischargeable (every `evalCell` matrix is well-formed by construction). -/
theorem bunchedBimonoidRestrictedVcompUnitLeftRespected
    (cell : CellExpr bunchedBimonoidOmegaComputad 2)
    (hwt : bunchedBimonoidCellWellTyped cell)
    (hwf : bunchedBimonoidMatWellFormed (bunchedBimonoidEvalCell cell)) :
    bunchedBimonoidEvalCell (CellExpr.vcomp (CellExpr.id (boundarySource cell)) cell)
      = bunchedBimonoidEvalCell cell := by
  have colsAgree : (bunchedBimonoidEvalCell cell).cols
      = bunchedBimonoidWordWidth (boundarySource cell) :=
    (bunchedBimonoidEvalCellWellFormed cell hwt).2
  show bunchedBimonoidMatMul (bunchedBimonoidEvalCell cell)
      (bunchedBimonoidIdentityMat (bunchedBimonoidWordWidth (boundarySource cell)))
      = bunchedBimonoidEvalCell cell
  rw [← colsAgree]
  exact bunchedBimonoidIdentityRightUnit (bunchedBimonoidEvalCell cell) hwf

/-- ★★★ **THE RESTRICTED STRICT RIGHT-UNIT LAW — the dual, respected on every well-typed cell.**  `vcompUnitRight`
is matrix-respected on well-typed cells: the bridge's `rows` agreement makes `identityMat (wordWidth(boundaryTarget
cell)) = identityMat ((evalCell cell).rows)`, closed by the shipped general `bunchedBimonoidIdentityLeftUnit`. -/
theorem bunchedBimonoidRestrictedVcompUnitRightRespected
    (cell : CellExpr bunchedBimonoidOmegaComputad 2)
    (hwt : bunchedBimonoidCellWellTyped cell)
    (hwf : bunchedBimonoidMatWellFormed (bunchedBimonoidEvalCell cell)) :
    bunchedBimonoidEvalCell (CellExpr.vcomp cell (CellExpr.id (boundaryTarget cell)))
      = bunchedBimonoidEvalCell cell := by
  have rowsAgree : (bunchedBimonoidEvalCell cell).rows
      = bunchedBimonoidWordWidth (boundaryTarget cell) :=
    (bunchedBimonoidEvalCellWellFormed cell hwt).1
  show bunchedBimonoidMatMul
      (bunchedBimonoidIdentityMat (bunchedBimonoidWordWidth (boundaryTarget cell)))
      (bunchedBimonoidEvalCell cell)
      = bunchedBimonoidEvalCell cell
  rw [← rowsAgree]
  exact bunchedBimonoidIdentityLeftUnit (bunchedBimonoidEvalCell cell) hwf

/-! ## Concrete instances — the general restricted laws fire on the generators -/

/-- ★★ **THE RESTRICTED LEFT-UNIT LAW ON `mu_a` (recovering the r6 positive VIA the general law).**  Instantiating
`bunchedBimonoidRestrictedVcompUnitLeftRespected` at `mu_a` (well-typed, well-formed matrix) reproduces the r6
concrete positive `bunchedBimonoidWellTypedMuVcompUnitLeftRespected` — now as a corollary of the GENERAL restricted
absorber, not a bespoke `rfl`. -/
theorem bunchedBimonoidRestrictedUnitLeftOnAddMu :
    bunchedBimonoidEvalCell
        (CellExpr.vcomp (CellExpr.id (boundarySource bunchedBimonoidAddMuGen)) bunchedBimonoidAddMuGen)
      = bunchedBimonoidEvalCell bunchedBimonoidAddMuGen :=
  bunchedBimonoidRestrictedVcompUnitLeftRespected bunchedBimonoidAddMuGen
    bunchedBimonoidAddMuGenWellTyped
    (by
      refine ⟨rfl, fun rowIndex hlt => ?_⟩
      cases rowIndex with
      | zero => rfl
      | succ predRow => exact (Nat.not_lt_zero predRow (Nat.lt_of_succ_lt_succ hlt)).elim)

/-- ★★ **THE RESTRICTED RIGHT-UNIT LAW ON `delta_a`.**  The dual concrete instance — the general right-unit
restricted law fires on the well-typed `delta_a`. -/
theorem bunchedBimonoidRestrictedUnitRightOnAddDelta :
    bunchedBimonoidEvalCell
        (CellExpr.vcomp bunchedBimonoidAddDeltaGen (CellExpr.id (boundaryTarget bunchedBimonoidAddDeltaGen)))
      = bunchedBimonoidEvalCell bunchedBimonoidAddDeltaGen :=
  bunchedBimonoidRestrictedVcompUnitRightRespected bunchedBimonoidAddDeltaGen
    bunchedBimonoidAddDeltaGenWellTyped
    (by
      refine ⟨rfl, fun rowIndex hlt => ?_⟩
      cases rowIndex with
      | zero => rfl
      | succ predRow =>
          cases predRow with
          | zero => rfl
          | succ deepRow =>
              exact (Nat.not_lt_zero deepRow
                (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hlt))).elim)

/-! # =========================================================================================
    # B3 — THE MARKERS + THE BI VERDICT (the well-typed absorber is the honest target)
    # =========================================================================================
-/

/-- ★★ **ESTABLISHED (B3) — the `CellWellTyped` predicate is delivered.**  `= true` records the structural
predicate `bunchedBimonoidCellWellTyped` (with `bunchedBimonoidGenWidthAgreement` / `bunchedBimonoidVcompComposable`
components), the HEADLINE self-attack `bunchedBimonoidMisdeclaredMuNotWellTyped` (the r6 counterexample is EXCLUDED
by well-typedness), and the positives (`mu_a` / `delta_a` / `sigma_a` well-typed).  The predicate the r6
`StrictLawAbsorber` named as the missing prerequisite. -/
def fxBunchedBimonoid_cellWellTypedPredicateShipped : Bool := true

/-- ★★ **ESTABLISHED (B3) — the `evalCellWellFormed` boundary-width bridge is delivered.**  `= true` records
`bunchedBimonoidEvalCellWellFormed`: every well-typed dim-2 cell's matrix `rows` / `cols` agree with its declared
target / source boundary widths, by structural induction.  The bridge the r6 residual named — the equation that
fails at the mis-declared `gen` and holds on the well-typed fragment. -/
def fxBunchedBimonoid_boundaryWidthBridgeShipped : Bool := true

/-- ★★★ **ESTABLISHED (B3) — the RESTRICTED strict unit laws are respected on well-typed cells.**  `= true`
records `bunchedBimonoidRestrictedVcompUnit{Left,Right}Respected`: the exact strict rows the r6 refutation broke on
the free carrier ARE matrix-respected once the cell is well-typed (the bridge's width-agreement composed with the
shipped general `bunchedBimonoidIdentity{Right,Left}Unit`), with the concrete instances on `mu_a` / `delta_a`.  The
r6 Node-A components assemble the moment the base relation is gated on `CellWellTyped`. -/
def fxBunchedBimonoid_restrictedStrictUnitLawsRespectedOnWellTyped : Bool := true

/-- ★★★ **DELIVERED — the r6 residual `strictLawCellAbsorberNeedsWellTypedPredicate` is addressed.**  `= true`
records that the two ingredients the r6 `StrictLawAbsorber` named ("Building the well-typedness inductive + the
restricted `evalCellWellFormed` bridge is the r6 residual") are BOTH shipped here: the inductive predicate
(`fxBunchedBimonoid_cellWellTypedPredicateShipped`) and the bridge
(`fxBunchedBimonoid_boundaryWidthBridgeShipped`), and the restricted absorber they unlock
(`fxBunchedBimonoid_restrictedStrictUnitLawsRespectedOnWellTyped`).  The r6 marker
`fxBunchedBimonoid_strictLawCellAbsorberNeedsWellTypedPredicate` stays `= false` byte-intact (it records the r6
state); this marker records the r7 delivery. -/
def fxBunchedBimonoid_strictLawCellAbsorberWellTypedPredicateDelivered : Bool := true

/-- ★★ **THE BI VERDICT — the well-typed absorber, NOT the free carrier, is the honest target.**  `= true` records
the recon's Job-3 verdict, machine-witnessed: the free-carrier lift stays refuted (r6 byte-intact,
`fxBunchedBimonoid_matrixStrictLawExtensionReached = false`), and the CORRECT absorber lives over `CellWellTyped`
— the restricted strict unit laws hold (`...restrictedStrictUnitLawsRespectedOnWellTyped`) exactly where the free
carrier fails (`bunchedBimonoidMisdeclaredMuNotWellTyped` excludes the refuting datum).  The BI cash-out is the
well-typed absorber. -/
def fxBunchedBimonoid_wellTypedAbsorberIsTheHonestBiTarget : Bool := true

/-- ★★★ **ESTABLISHED (B3) — the WP-PROP r7 well-typed-absorber ledger (honest scoreboard).**  `= true` records
the complete r7 B3 delivery: the `CellWellTyped` predicate + the headline exclusion of the r6 counterexample
(`fxBunchedBimonoid_cellWellTypedPredicateShipped`); the `evalCellWellFormed` boundary-width bridge
(`fxBunchedBimonoid_boundaryWidthBridgeShipped`); the RESTRICTED strict unit laws respected on well-typed cells
(`fxBunchedBimonoid_restrictedStrictUnitLawsRespectedOnWellTyped`); the r6 residual delivered
(`fxBunchedBimonoid_strictLawCellAbsorberWellTypedPredicateDelivered`); and the BI verdict
(`fxBunchedBimonoid_wellTypedAbsorberIsTheHonestBiTarget`).  Every r6 `= false` marker byte-intact; no fabricated
flip; zero-axiom.  The spine of r7 — the well-typedness prerequisite for the corrected star (B4). -/
def fxBunchedBimonoid_wellTypedAbsorberRoundSevenLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
