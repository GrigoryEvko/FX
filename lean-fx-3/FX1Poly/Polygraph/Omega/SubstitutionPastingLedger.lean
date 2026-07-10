import FX1Poly.Polygraph.Omega.PresentedKernelSeed
import FX1Poly.Polygraph.Omega.AdmissionChainSeed
import FX1Poly.Polygraph.Omega.WeakDirectedCeilingLedger

/-! # Polygraph/Omega/SubstitutionPastingLedger — the OMEGA-7 r1 ledger (B4)

★ **THE GRAND-RUNG r1 LEDGER — "substitution = pasting", the honest scoreboard.**  Mirrors
`GradedCompositionLedger` / `WeakDirectedCeilingLedger`: it gates on what compiles (it imports the Polygraph-side OMEGA-7
r1 pieces — `PresentedKernelSeed`, `AdmissionChainSeed` — plus the OMEGA-6 wall ledger it inherits; the B1
identification `SubstPasting` lives at `Tier0/Term/Subst/` because it imports the kernel substitution
engine and the layer DAG forbids Polygraph -> Tier0, so its gate is its audit twin, not this import),
records the anchored-vs-walled line as hypothesis-free `Bool` markers, names the PERMANENT walls (Makkai
general familial representability, Burroni general presented word problem) by CITATION rather than
axiomatization, states every surviving jam with its EXACT goal and NAMED blocking node, and specifies the
staircase-completion criteria that make #2237 honestly closeable at r2/r3.  Every declaration is a
hypothesis-free `Bool` def or a docstring record, so every declaration is axiom-free.  No file outside
`Omega/` is edited.

## What OMEGA-7 r1 SHIPPED (each machine-checked zero-axiom)

  * **B1 — THE IDENTIFICATION** (`SubstPasting.lean`) — THE HEADLINE.  `substCompose_assoc`: the substitution
    monoid's associativity IS the kernel `RawTerm.subst_compose` (the polynomial-monad multiplication) applied
    at `firstSubstitution position` — no re-proof, no lookalike, byte-for-byte.  The two unit laws complete
    the substitution MONOID.  `steinerPasting_isAssociativeComposition := addCoordinates_assoc` is the Steiner
    pasting shadow, byte-for-byte.  `linearize_vcomp_assoc` carries the pasting associativity through the
    shipped `linearize` homomorphism, and `substLemma_is_pastingAssoc` PAIRS the two faces: the substitution
    law and the pasting arithmetic are the same associative-composition law.  Non-vacuity on real kernel data.
  * **B2 — THE PRESENTED-KERNEL SEED** (`PresentedKernelSeed.lean`).  `PresentedKernel` is the
    `(signature, table2, table3)` tuple as a value; `demoPresentedKernel` instantiates it with `StrictAxiomRel`
    as table2 and OMEGA-4's interchange `CriticalPairRow` AS table3 (the Squier ascent made the explicit dim-3
    slot); `demoPresentedKernel_table3_threeCell` reseats `interchangeThreeCell` as the tuple's dim-3 content.
  * **B3 — THE ADMISSION CHAIN SEED** (`AdmissionChainSeed.lean`).  `AdmissionChainSeed = (dim : Nat) →
    AdmittedTableSeed` is the runged POLY-CAP kernel-as-value shape (row + decidable admissibility certificate
    per dimension); `demoAdmissionChain` admits the OMEGA-4 dim-3 slot, off-slots not admissible; MODE-ADMIT's
    `admitModeTheory` is cited as the r3 packaged-decider filler.

## The honest line (arithmetic anchor MACHINE-CHECKED, the model homomorphism WALLED)

The recon picked r1 Form B (the arithmetic shadow) over Form A (a total `termToCell` model homomorphism).
Form A is the Makkai wall: arbitrary lambda-terms are NOT strong-Steiner (they carry binders / relations →
Burroni-undecidable in general), so a total `termToCell` homomorphism into the integer-arithmetic fragment
cannot exist in general.  r1 ships the arithmetic anchor (the substitution law IS the pasting arithmetic on
the strong-Steiner fragment, relative to a valuation) and names the wall; the wall is NOT axiomatized (it is
a `= false` marker inheriting the OMEGA-6 citations).

Raw Lean 4 + Init; a docstring record plus hypothesis-free `Bool` markers, so every declaration is axiom-free.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The r1 shipped-piece markers (each cites machine-checked code) -/

/-- ★ **B1 — the substitution = pasting arithmetic ANCHOR is SHIPPED.**  `= true`: `substCompose_assoc` (the
substitution monoid associativity = kernel `RawTerm.subst_compose`, byte-for-byte) +
`steinerPasting_isAssociativeComposition` (`:= addCoordinates_assoc`, the pasting shadow) + `linearize_vcomp_assoc`
(the shadow carried through the `linearize` homomorphism) + `substLemma_is_pastingAssoc` (the paired anchor). -/
def fxOmega7_substCompositionAnchored : Bool := true

/-- ★ **B1 — the pasting arithmetic is SHIPPED** (recall of OMEGA-2).  `= true`: the Steiner pasting side is
the already-shipped abelian-group kit (`addCoordinates_assoc` / `_comm` / `_zeroVector_left/right`) plus the
`linearize` composition homomorphism (its `.vcomp` arm literally `addCoordinates`).  r1 supplies the term-side
monoid and the identification; the arithmetic side was OMEGA-2. -/
def fxOmega7_pastingArithmeticShipped : Bool := true

/-- ★ **B2 — the presented-kernel (signature, table2, table3) tuple is SEEDED.**  `= true`: `PresentedKernel`
+ `demoPresentedKernel` (StrictAxiomRel as table2, the OMEGA-4 interchange `CriticalPairRow` as table3) +
`demoPresentedKernel_table3_threeCell` (a genuine dim-3 3-cell in the tuple's table3 slot). -/
def fxOmega7_presentedKernelTupleSeeded : Bool := true

/-- ★ **B3 — the per-dimension admission chain is SEEDED.**  `= true`: `AdmissionChainSeed = (dim : Nat) →
AdmittedTableSeed` (the kernel-as-value shape) + `presentedKernelAdmissionChain` + `demoAdmissionChain`
(admissible through the OMEGA-4 dim-3 slot, off-slots not admissible). -/
def fxOmega7_admissionChainSeeded : Bool := true

/-! ## The r1 completion marker (the anchor SCOPE is done) -/

/-- ★ **The OMEGA-7 r1 anchor round is COMPLETE.**  `= true`: B1 (the identification) + B2 (the tuple seed) +
B3 (the admission chain seed) + B4 (this ledger) shipped, machine-checked zero-axiom.  This gates the r1
SCOPE (the arithmetic anchor + the tuple/admission SHAPES), NOT the deeper theorems — those are the jam
markers below (all `false`). -/
def fxOmega7_r1AnchorRoundComplete : Bool := true

/-! ## The surviving-jam markers (each `= false` — NOT reached; the exact goal + NAMED node below)

  * **JAM — the total `termToCell` model homomorphism (Form A).**  Goal: a TOTAL `termToCell : RawTerm →
    SteinerCell` with `termToCell (t.subst σ) = pasteAlong (contextToScheme σ) (termToCell t)` on the GENERAL
    computad.  NAMED node: general familial representability (Weber / Makkai strength) — `pasteAlong`
    well-defined + associative on the general computad needs the general presented word problem
    (`fxOmega6_generalPresentedWordProblemDecidable = false`, Burroni TCS 1993) and its weak-ω analog
    (`fxOmega6_weakOmegaCoherenceEqualityDecidable = false`, Makkai / SN-638).  Arbitrary lambda-terms are not
    strong-Steiner, so no total homomorphism into the ℤ-arithmetic fragment exists in general — memo pin
    OMEGA-7(c).  `fxOmega7_totalTermToCellModelReached = false`.

  * **JAM — the fragment-level `substCell = pasteAlong` as a genuine map (r2).**  Goal: `substCell =
    pasteAlong` on the STRONG-STEINER fragment as a genuine map (not only the arithmetic shadow), with the
    substitution lemma discharged VIA `addCoordinates_assoc`.  NAMED node: `pasteAlong` on the `CellExpr`
    carrier aligned with `boundarySource` / `boundaryTarget` (the pasting engine on the fragment); r1 did the
    arithmetic shadow (`linearize_vcomp_assoc`).  `fxOmega7_fragmentSubstCellEqPasteAlongReached = false`.

  * **JAM — the kernel-as-value tuple with genuine per-dimension admission (r3).**  Goal: the tuple
    `(signature, table2, table3, …)` as `Kernel := (n : Nat) → AdmittedTable n` with per-dimension admission
    lifted from `admitModeTheory` (the packaged decider, not a `Bool` flag).  NAMED node: MODE-ADMIT's
    `admitModeTheory` (`Amalgam/ModeAdmit.lean`) lifted to a per-dimension family, which needs the OMEGA-7
    pasting engine to TYPE the rows' boundaries (the typed telescope + substitution, `fxOmega6_psContextTypedTelescope
    = false`).  r1 SEEDED the SHAPE (`PresentedKernel`, `AdmissionChainSeed` with a `Bool` certificate).
    `fxOmega7_kernelAsValueTuple = false`. -/

/-- ★ **The total `termToCell` model homomorphism is NOT reached (Form A).**  `= false` — the general
familial representability wall: `pasteAlong` on the general computad needs the general presented / weak-ω word
problem, both undecidable (Burroni / Makkai), and arbitrary lambda-terms are not strong-Steiner (memo
OMEGA-7(c)). -/
def fxOmega7_totalTermToCellModelReached : Bool := false

/-- ★ **The fragment-level `substCell = pasteAlong` genuine map is NOT reached (r2).**  `= false` — needs
`pasteAlong` on the `CellExpr` carrier aligned with the shipped boundaries; r1 did the arithmetic shadow
(`linearize_vcomp_assoc` = `addCoordinates_assoc` under `linearize`). -/
def fxOmega7_fragmentSubstCellEqPasteAlongReached : Bool := false

/-- ★ **The kernel-as-value tuple with genuine per-dimension admission is NOT reached (r3).**  `= false` —
`Kernel := (n : Nat) → AdmittedTable n` with `admitModeTheory`-packaged deciders needs the OMEGA-7 pasting
engine to type the rows' boundaries; r1 seeded the SHAPE with a `Bool` admissibility certificate. -/
def fxOmega7_kernelAsValueTuple : Bool := false

/-! ## The permanent walls (cited, NEVER axiomatized — inherit the OMEGA-6 ledger) -/

/-- ★ **WALL (permanent, cited) — general familial representability is NOT decidable.**  `= false`: Weber's
familial-representability theorem is pen-and-paper; the general `pasteAlong` (Form A) needs the general
presented word problem, already walled by `fxOmega6_generalPresentedWordProblemDecidable = false` (Burroni)
and `fxOmega6_weakOmegaCoherenceEqualityDecidable = false` (Makkai).  Cited, NOT axiomatized. -/
def fxOmega7_generalFamilialityDecidable : Bool := false

/-- ★ **The staircase-closure criteria for #2237 are RECORDED.**  `= true`: #2237 closes when (r1) the
substitution ≡ pasting ARITHMETIC anchor is machine-checked [DONE, `fxOmega7_substCompositionAnchored`], (r2)
the fragment-level `substCell = pasteAlong` is proven as a genuine map [`fxOmega7_fragmentSubstCellEqPasteAlongReached`],
and (r3) the kernel tuple `(signature, table2, table3, …)` is assembled with per-dimension admission
[`fxOmega7_kernelAsValueTuple`] OR the general familiality is honestly walled by citation with the fragment
identification banked as the prize.  Decided-or-walled: r2/r3 are closeable because both endpoints are
shipped (the subst lemma is `subst_compose`, the pasting law is `addCoordinates_assoc`); the wall is a real
result (Burroni / Makkai), not a punt. -/
def fxOmega7_staircaseClosureCriteriaRecorded : Bool := true

end FX1Poly.Polygraph.Omega
