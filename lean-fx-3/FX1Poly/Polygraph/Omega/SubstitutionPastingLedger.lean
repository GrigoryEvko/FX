import FX1Poly.Polygraph.Omega.PresentedKernelSeed
import FX1Poly.Polygraph.Omega.AdmissionChainSeed
import FX1Poly.Polygraph.Omega.WeakDirectedCeilingLedger
import FX1Poly.Polygraph.Omega.TypedKernelTuple

/-! # Polygraph/Omega/SubstitutionPastingLedger — the OMEGA-7 r1+r2 ledger (B4)

★ **THE GRAND-RUNG r1 LEDGER — "substitution = pasting", the honest scoreboard.**  Mirrors
`GradedCompositionLedger` / `WeakDirectedCeilingLedger`: it gates on what compiles (it imports the Polygraph-side OMEGA-7
r1 pieces — `PresentedKernelSeed`, `AdmissionChainSeed` — plus the OMEGA-6 wall ledger it inherits; the B1
identification `SubstPasting` lives at `Axis/Term/Subst/` because it imports the kernel substitution
engine and the layer DAG forbids Polygraph -> Axis, so its gate is its audit twin, not this import),
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

/-! ## The r2 shipped-piece markers (the fragment cell leg — COMPOSITION = pasting at chain granularity)

★ **HONESTY CORRECTION (the r2 adversarial verification).**  r2 originally shipped under the headline
"substitution = pasting at cell level"; the verifier REFUTED that framing — the composite (`composeLinearized`,
originally misnamed `substCell`) never routes through `RawTermSubst`, and the paired statement is a
variable-disjoint CONJUNCTION, not an identification.  What r2 genuinely lifts is r1's single-vector
arithmetic shadow to the boundary-faithful CHAIN map: **composition = pasting**.  The genuine
"substitution = pasting" glue is the NEW named node `fxOmega7_fragmentTermToCellActionReached` below.
The pieces live at `Axis/Term/Subst/PastingCompositeLinearization.lean` (they sit BESIDE the kernel
term-side law `substCompose_assoc`; Polygraph may not import Axis, so these `Bool` markers gate against
the audit twin `PastingCompositeLinearizationAudit.lean`, not this import).  Each is machine-checked
zero-axiom (independent `#print axioms`: "does not depend on any axioms"). -/

/-- ★ **r2 — the fragment pasting composite is DEFINED and boundary-aligned.**  `= true`: `pasteAlong` on the
`CellExpr` carrier (the free vertical composite `vcomp`) + `boundarySource_pasteAlong` / `boundaryTarget_pasteAlong`
(both `rfl`: source-from-left, target-from-right, aligned with the shipped total boundaries). -/
def fxOmega7_fragmentPasteAlongDefined : Bool := true

/-- ★ **r2 — the chain composite of the linearizations is REALIZED.**  `= true`: `composeLinearized`
= `composeAtFull (linearizeFull left) (linearizeFull right)`, the boundary-faithful chain composite that
RETAINS the boundary poles the single-vector shadow drops (the r2 upgrade over r1's `linearize`).
HONESTY: it performs NO substitution — pure chain composition (the verifier-refuted `substCell` misnomer
is corrected; the marker name keeps its shipped spelling for stability, its content is as stated here). -/
def fxOmega7_fragmentSubstCellRealized : Bool := true

/-- ★ **r2 — the pasting associativity is discharged VIA `addCoordinates_assoc`.**  `= true`: `linearizeFull_pasteAlong_assoc`
re-brackets a triple pasting composite invisibly to `linearizeFull` — the boundary POLES agree by `rfl`, the
TOP row by `addCoordinates_assoc` (the jam's literal demand), the chain-level upgrade of r1's
`linearize_vcomp_assoc`. -/
def fxOmega7_fragmentSubstCellAssocViaAddCoordinates : Bool := true

/-- **r2 — the two faces stated SIDE BY SIDE.**  `= true`: `substComposeAssoc_and_pastingAssoc` states the
kernel term-side law (`substCompose_assoc`, = `RawTerm.subst_compose`) AND the chain-level pasting
associativity in one theorem.  HONESTY (the r2 verifier's refutation): this is a variable-disjoint
CONJUNCTION of two independently-true facts, NOT an identification — no map or shared variable links the
substitution side to the pasting side.  The genuine glue is `fxOmega7_fragmentTermToCellActionReached`
below (`= false`, the named node). -/
def fxOmega7_fragmentSubstPairedAnchor : Bool := true

/-- ★ **The OMEGA-7 r2 fragment round is COMPLETE.**  `= true`: the fragment `composeLinearized = pasteAlong` genuine
map (`fxOmega7_fragmentPastingCompositeLinearized`), its associativity via `addCoordinates_assoc`, the paired
kernel anchor, and the two concrete dim-3 non-vacuity witnesses (identical concrete chains) all shipped,
machine-checked zero-axiom, RELATIVE to a `ComputadValuation` on the STRONG-STEINER fragment (Makkai wall
scope preserved, NEVER widened).  This gates the r2 SCOPE (the boundary-faithful map identification); the r3
kernel-as-value tuple is the surviving jam below. -/
def fxOmega7_r2FragmentRoundComplete : Bool := true

/-! ## The r2-SHIPPED fragment leg + the surviving-jam markers (the exact goal + NAMED node below)

  * **SHIPPED (r2) — the fragment-level `composeLinearized = pasteAlong` as a genuine map.**  `composeLinearized = pasteAlong`
    on the STRONG-STEINER fragment as a GENUINE MAP (not only the arithmetic shadow), with the substitution
    lemma discharged VIA `addCoordinates_assoc`.  `pasteAlong` on the `CellExpr` carrier aligned with
    `boundarySource` / `boundaryTarget` (the pasting engine on the fragment); r1 did only the arithmetic shadow
    (`linearize_vcomp_assoc`).  DONE at `Axis/Term/Subst/PastingCompositeLinearization.lean`, machine-checked zero-axiom.
    `fxOmega7_fragmentPastingCompositeLinearized = true`.

  * **JAM — the total `termToCell` model homomorphism (Form A).**  Goal: a TOTAL `termToCell : RawTerm →
    SteinerCell` with `termToCell (t.subst σ) = pasteAlong (contextToScheme σ) (termToCell t)` on the GENERAL
    computad.  NAMED node: general familial representability (Weber / Makkai strength) — `pasteAlong`
    well-defined + associative on the general computad needs the general presented word problem
    (`fxOmega6_generalPresentedWordProblemDecidable = false`, Burroni TCS 1993) and its weak-ω analog
    (`fxOmega6_weakOmegaCoherenceEqualityDecidable = false`, Makkai / SN-638).  Arbitrary lambda-terms are not
    strong-Steiner, so no total homomorphism into the ℤ-arithmetic fragment exists in general — memo pin
    OMEGA-7(c).  `fxOmega7_totalTermToCellModelReached = false`.

  * **SHIPPED (r3) — the kernel-as-value tuple with genuine TYPED per-dimension admission.**  The tuple
    `(signature, table2, table3, …)` as `TypedKernel := (n : Nat) → AdmittedTable n` with per-dimension admission
    carried as a genuine `cohFullnessCheck` decision over the r2 typed telescope (NOT r1's `Bool` flag).  r2 shipped
    the exact gap the r1 jam named — TYPING the rows' boundaries (`psTypedCheck` / `telescopeWellFormed` + the
    fullness decision `cohFullnessCheck`) — so r3 consumes it: `AdmittedTable` seats a row on a `TeleType` boundary
    at its dimension over a checked well-formed ps-context with a `cohFullnessCheck` admissibility proof;
    `demoTypedKernel` instantiates the tuple over the real kernel rows.  MODE-ADMIT's `admitModeTheory`
    (`Amalgam/ModeAdmit.lean`) is the packaged ω-word-problem decider the `AdmissionInheritanceShape` slot enables
    one dimension up — cited by name, NOT imported (the layer rule + cross-lane discipline).  DONE at
    `TypedKernelTuple.lean`, machine-checked zero-axiom.  `fxOmega7_kernelAsValueTuple = true`.  Residual (NOT
    required by the criteria, r4): the type-respecting VALUATION seating each row on its own reconstructed pasting
    boundary — the fragment term→cell action (`fxOmega7_fragmentTermToCellActionReached = false`, below). -/

/-- ★ **The total `termToCell` model homomorphism is NOT reached (Form A).**  `= false` — the general
familial representability wall: `pasteAlong` on the general computad needs the general presented / weak-ω word
problem, both undecidable (Burroni / Makkai), and arbitrary lambda-terms are not strong-Steiner (memo
OMEGA-7(c)). -/
def fxOmega7_totalTermToCellModelReached : Bool := false

/-- ★ **The fragment-level `composeLinearized = pasteAlong` genuine map is REACHED (r2).**  `= true` — SHIPPED at
`Axis/Term/Subst/PastingCompositeLinearization.lean`: `pasteAlong` on the `CellExpr` carrier (boundary-aligned with the
shipped `boundarySource`/`boundaryTarget`), `composeLinearized` its boundary-faithful chain realization
(`composeAtFull` on `linearizeFull`), and `linearizeFull_pasteAlong_eq_composeLinearized` the GENUINE MAP equality (whole chain,
boundary poles included, the rfl-anchor `linearizeFull_vcomp_composeAtFull`) with `linearizeFull_pasteAlong_assoc` discharged
VIA `addCoordinates_assoc` (poles by `rfl`) — the boundary-faithful upgrade over r1's single-vector shadow
(`linearize_vcomp_assoc`).  Machine-checked zero-axiom (independent `#print axioms`), gated by the audit twin
`PastingCompositeLinearizationAudit.lean` (this ledger cannot import Axis).  Scope: RELATIVE to a `ComputadValuation` on
the STRONG-STEINER fragment (Makkai wall NEVER widened). -/
def fxOmega7_fragmentPastingCompositeLinearized : Bool := true

/-- ★ **The kernel-as-value tuple with genuine per-dimension admission is REACHED (r3).**  `= true` — SHIPPED at
`TypedKernelTuple.lean`: `AdmittedTable computad n` seats a `row` on a `TeleType` boundary AT its dimension
(`boundaryDim : teleTypeDim boundary = n`) over a `psTypedCheck`-checked, `telescopeWellFormed` ps-context,
with admissibility DECIDED by `cohFullnessCheck` over the r2 typed telescope (`fullnessOverPs = true`, a genuine
decision-procedure proof — NOT r1's naked `AdmittedTableSeed.isAdmissible : Bool`).  `TypedKernel := (n : Nat) →
AdmittedTable n` is the tuple; `demoTypedKernel` instantiates it over the real kernel rows
(`StrictAxiomRel` table2 at dim 2, the OMEGA-4 interchange `criticalPairRel` table3 at dim 3) at every
dimension, `n` flowing uniformly into `starTower n` (no dependent match — propext trap dodged).  Non-vacuity:
`demoTypedKernel_dim3_rowFires` (the interchange 3-cell fires through the tuple's dim-3 slot),
`demoDim3AdmittedTableFull` (the real row over its GENUINE 9-entry full context, the middle object covered), and
the LOAD-BEARING `interchangeMissingMiddle_notAdmitted` (the gate REJECTS the missing-middle boundary,
`cohFullnessCheck = false`).  `typedKernelForget` maps back to the r1 `AdmissionChainSeed` shape, identified
through the shared `row`.  Machine-checked zero-axiom (audit twin `TypedKernelTupleAudit.lean` + independent
`#print axioms`).  HONESTY (never widen): `cohFullnessCheck` is the typed fullness gate (support coverage over
the telescope), honestly slightly MORE permissive than strict CaTT type reconstruction; the tuple seats each
real row on the CANONICAL dimension-`n` boundary, NOT the row's reconstructed pasting boundary — that
type-respecting VALUATION is the fragment term→cell action, now REACHED (r4,
`fxOmega7_fragmentTermToCellActionReached = true`, below): `ActionAdmittedRow` seats each fragment row on its
action-reconstructed pasting boundary at SteinerChainCell granularity (`FragmentTermCellAction.lean`, the
seating genuinely varies per row), the `AdmittedTable` `TeleType` bridge (cell → de-Bruijn typed boundary)
the documented Makkai-adjacent residual of the SAME wall.  What is genuine: every slot carries a REAL
generator row AND a seated typed decision, no Bool flag. -/
def fxOmega7_kernelAsValueTuple : Bool := true

/-- ★ **The fragment term-to-cell ACTION is REACHED (r4) — the genuine "substitution = pasting" glue (the
r2 verifier's named node), machine-checked zero-axiom.**  `= true` — SHIPPED at
`Axis/Term/Subst/FragmentTermCellAction.lean`.  On the strong-Steiner successor-tower fragment
(`omegaSuccTower`, the `gen_natSucc` tower over one `gen_var`, closed under the tower substitutions
`towerSubst`), relative to `towerValuation`, the action equation

    linearizeFull (fragmentTermToCell (t.subst sigma)) = linearizeFull (pasteAlong (cellOf sigma) (fragmentTermToCell t))

holds with the SHARED `(t, sigma)` linking the two sides (`fragmentTermToCell_subst_eq_pasteAlong`) — exactly
the glue the r2 conjunction `substComposeAssoc_and_pastingAssoc` lacks: the kernel `RawTerm.subst`
(`subst_omegaSuccTower` = `subst (towerSubst m) (tower k) = tower (m + k)`, the genuine polynomial-monad
substitution) is CARRIED to `pasteAlong`.  `fragmentTermToCell` / `cellOf` genuinely consume `RawTerm` /
`RawTermSubst` (the mutual `fold` / `foldChildren` idiom); the map lands through the SHIPPED Steiner valuation
machinery (`pasteAlong` = `CellExpr.vcomp`, `linearizeFull`), no lookalikes.  NON-DEGENERATE (the truth probe,
`rfl`): at `(m = 1, k = 2)` both sides compute to the same non-trivial chain `⟨[([0],[0])], [3]⟩` — the term
side genuinely rewrites (`subst -> tower 3`, top `[3]`, strictly beyond the input top `[2]`), the cell side
genuinely composes a `[1]`-cell with a `[2]`-cell.  The proof: the subst leg reduces the LHS, then
`linearizeFull_eq_of` closes it (poles `[([0],[0])]` both sides by the boundary lemmas, tops add via
`addCoordinates_assoc` / `_comm`).  Machine-checked zero-axiom (audit twin `FragmentTermCellActionAudit.lean` +
independent `#print axioms`: "does not depend on any axioms"), gated by that twin (this ledger cannot import
Axis).  Scope: RELATIVE to `towerValuation` on the strong-Steiner fragment — arbitrary lambda-terms with
binders stay Makkai / Form-A-walled (`fxOmega7_totalTermToCellModelReached = false`, NEVER widened). -/
def fxOmega7_fragmentTermToCellActionReached : Bool := true

/-! ## The permanent walls (cited, NEVER axiomatized — inherit the OMEGA-6 ledger) -/

/-- ★ **WALL (permanent, cited) — general familial representability is NOT decidable.**  `= false`: Weber's
familial-representability theorem is pen-and-paper; the general `pasteAlong` (Form A) needs the general
presented word problem, already walled by `fxOmega6_generalPresentedWordProblemDecidable = false` (Burroni)
and `fxOmega6_weakOmegaCoherenceEqualityDecidable = false` (Makkai).  Cited, NOT axiomatized. -/
def fxOmega7_generalFamilialityDecidable : Bool := false

/-- ★ **The staircase-closure criteria for #2237 are RECORDED.**  `= true`: #2237 closes when (r1) the
substitution ≡ pasting ARITHMETIC anchor is machine-checked [DONE, `fxOmega7_substCompositionAnchored`], (r2)
the fragment-level `composeLinearized = pasteAlong` is proven as a genuine map [DONE,
`fxOmega7_fragmentPastingCompositeLinearized`], and (r3) the kernel tuple `(signature, table2, table3, …)`
is assembled with per-dimension admission [`fxOmega7_kernelAsValueTuple`] OR the general familiality is
honestly walled by citation with the fragment identification banked as the prize.  Decided-or-walled: r3 is
closeable because both endpoints are shipped (the subst lemma is `subst_compose`, the pasting map is now the
genuine `composeLinearized = pasteAlong`); the wall is a real result (Burroni / Makkai), not a punt. -/
def fxOmega7_staircaseClosureCriteriaRecorded : Bool := true

/-! ## The r3 section — the kernel-as-value tuple SHIPPED, the staircase CLOSED (B4)

★ **What OMEGA-7 r3 SHIPPED (machine-checked zero-axiom, `TypedKernelTuple.lean`).**  The r3 disjunct of the
staircase criteria is closed via its FIRST branch: the kernel tuple is genuinely assembled.  `AdmittedTable`
upgrades r1's `AdmittedTableSeed.isAdmissible : Bool` to a seated `cohFullnessCheck` decision over the r2 typed
telescope; `TypedKernel := (n) → AdmittedTable n` is the tuple; `demoTypedKernel` seats the real kernel rows at
every dimension; the load-bearing `interchangeMissingMiddle_notAdmitted` witnesses the gate is non-vacuous.
This consumes exactly the r2 typing deliverable (`fxOmega6_psContextTypedTelescopeTypingShipped`,
`fxOmega6_cohFullnessCheckedTyped`).

The fragment term→cell ACTION (`fxOmega7_fragmentTermToCellActionReached`) is NOT part of the recorded criteria,
but r4 REACHED it anyway — reversing the r3 "left open" disposition with a genuine, machine-checked,
NON-DEGENERATE action (NOT the near-vacuous flip r3 warned against).  The r3 forecast was exactly right: a
non-vacuous action needs the richer strong-Steiner fragment, and r4 supplies precisely that — the
`omegaSuccTower` successor tower, on which the shared-variable action equation is a genuine `pasteAlong`
composite (witness `(m=1,k=2)` computes both sides to `⟨[([0],[0])],[3]⟩` by `rfl`; the term side genuinely
rewrites, the cell side genuinely composes two non-identity cells).  See `FragmentTermCellAction.lean` and the
flip below; the r4 round-complete marker `fxOmega7_r4FragmentActionRoundComplete` records the SHIPPED pieces. -/

/-- ★ **The OMEGA-7 r3 kernel-tuple round is COMPLETE.**  `= true`: `AdmittedTable` (the typed admission row),
`TypedKernel` (the kernel-as-value tuple), `demoTypedKernel` (the tuple over the real kernel rows with seated
`cohFullnessCheck` deciders), the dim-3 firing + admissibility witnesses, the non-degenerate
`demoDim3AdmittedTableFull`, the load-bearing `interchangeMissingMiddle_notAdmitted`, and the forgetful map
`typedKernelForget` all shipped, machine-checked zero-axiom.  Gates the r3 SCOPE (the tuple assembled with typed
per-dimension admission); the deeper term→cell action stays the walled node below. -/
def fxOmega7_r3KernelTupleRoundComplete : Bool := true

/-- ★ **The substitution=pasting STAIRCASE (#2237) is CLOSED.**  `= true` — decided via the FIRST disjunct of
`fxOmega7_staircaseClosureCriteriaRecorded`: (r1) the substitution ≡ pasting arithmetic anchor
[`fxOmega7_substCompositionAnchored`], (r2) the fragment-level `composeLinearized = pasteAlong` genuine map
[`fxOmega7_fragmentPastingCompositeLinearized`], and (r3) the kernel tuple assembled with typed per-dimension
admission [`fxOmega7_kernelAsValueTuple`, now `true`] are ALL shipped machine-checked zero-axiom.  (The SECOND
disjunct — walled-with-prize — was already independently satisfiable, `fxOmega7_generalFamilialityDecidable =
false` cited + the fragment prize banked; the tuple flip upgrades the close to the maximal FIRST disjunct.)

WHAT STAYS OPEN after r4 (the ONLY residual — a permanent, cited wall, never fabricated closed):
  * the total `termToCell` model homomorphism (Form A) — the Makkai / Burroni general-familiality WALL,
    `fxOmega7_totalTermToCellModelReached = false`, `fxOmega7_generalFamilialityDecidable = false` (cited).
    The fragment term→cell ACTION (`fxOmega7_fragmentTermToCellActionReached`) is now REACHED (r4), so the
    shared-variable "substitution = pasting" glue the r2 verifier named is BANKED; its `AdmittedTable`
    `TeleType`-bridge reseat (cell → de-Bruijn typed boundary) is the documented Makkai-adjacent SUB-residual
    of the same wall (arbitrary binder-terms are not strong-Steiner) — NEVER widened. -/
def fxOmega7_substitutionPastingStaircaseClosed : Bool := true

/-! ## The r4 section — the fragment term→cell ACTION SHIPPED (the r3 residual CLOSED)

★ **What OMEGA-7 r4 SHIPPED (machine-checked zero-axiom, `Axis/Term/Subst/FragmentTermCellAction.lean`).**
The r2 verifier's named node — the shared-variable "substitution = pasting" glue — is now inhabited on a
genuine, non-degenerate fragment:

  * **THE FRAGMENT** — `omegaSuccTower` (the `gen_natSucc` successor tower over one `gen_var`), closed under
    the tower substitutions `towerSubst` (`subst_omegaSuccTower` = the kernel `RawTerm.subst`), strong-Steiner
    realizable through the SHIPPED `linearize` / `linearizeFull` / `composeAtFull`.
  * **THE MAPS** — `fragmentTermToCell` / `cellOf` genuinely consuming `RawTerm` / `RawTermSubst` (the mutual
    `fold` / `foldChildren` idiom, propext-clean; no wildcard-over-generators, no partial dependent match).
  * **THE ACTION EQUATION** — `fragmentTermToCell_subst_eq_pasteAlong`, kernel substitution genuinely CARRIED
    to `pasteAlong` with the SHARED `(t, sigma)`, at `linearizeFull` granularity (the r1/r2 scoping); the
    non-degeneracy witness `(m=1,k=2)` computes both sides to `⟨[([0],[0])],[3]⟩` by `rfl` BEFORE any theorem
    (the truth probe — LHS ≠ the input image, RHS a genuine composite of a `[1]`-cell and a `[2]`-cell).
  * **THE TUPLE RE-SEAT** — `ActionAdmittedRow` seats each fragment row on its ACTION-RECONSTRUCTED pasting
    boundary (SteinerChainCell granularity, the seating genuinely varies per row), the admissibility
    certificate being the action equation itself; the r3 disclosed uniform-singleton seating weakness is
    de-degenerated.  The `AdmittedTable` `TeleType` bridge stays the documented residual (below).

Gated by the audit twin `FragmentTermCellActionAudit.lean` (this ledger cannot import Axis).  Scope RELATIVE
to `towerValuation` on the strong-Steiner fragment — the Makkai / Form-A wall is NEVER widened. -/

/-- ★ **The OMEGA-7 r4 fragment-action round is COMPLETE.**  `= true`: the fragment (`omegaSuccTower` closed
under `towerSubst`, `subst_omegaSuccTower`), the maps genuinely consuming `RawTerm` / `RawTermSubst`
(`fragmentTermToCell` / `cellOf`), the shared-variable action equation
(`fragmentTermToCell_subst_eq_pasteAlong`) with its `rfl` non-degeneracy witness, and the de-degenerated tuple
re-seat (`ActionAdmittedRow` / `actionAdmittedTable` at SteinerChainCell granularity) all shipped,
machine-checked zero-axiom (`#assert_no_axioms` + independent `#print axioms`).  Gates the r4 SCOPE (the
fragment term→cell ACTION reached, `fxOmega7_fragmentTermToCellActionReached = true`); the ONLY residual is
the permanent Makkai / Burroni wall (the total Form A + its `TeleType`-bridge sub-residual), cited never
axiomatized. -/
def fxOmega7_r4FragmentActionRoundComplete : Bool := true

end FX1Poly.Polygraph.Omega
