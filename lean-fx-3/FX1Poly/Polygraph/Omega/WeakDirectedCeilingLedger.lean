import FX1Poly.Polygraph.Omega.PsContext
import FX1Poly.Polygraph.Omega.CohSeed
import FX1Poly.Polygraph.Omega.InvertibilitySeed
import FX1Poly.Polygraph.Omega.PsContextTyped
import FX1Poly.Polygraph.Omega.CohGateTyped
import FX1Poly.Polygraph.Omega.InvertibilityReverseSeed

/-! # Polygraph/Omega/WeakDirectedCeilingLedger — the OMEGA-6 ceiling ledger + the OMEGA-7 handoff (B4)

The honest r1 ledger for the weak/directed rung, mirroring `CertificateFunctorLedger.lean`.  It gates on what
compiles (it imports every OMEGA-6 r1 piece — `PsContext`, `CohSeed`, `InvertibilitySeed`), records the
checking-vs-deciding line as hypothesis-free `Bool` markers, names the two PERMANENT walls (Makkai weak-ω
coherence equality, Burroni general presented word problem) by CITATION rather than axiomatization, marks the
OMEGA-7 deferrals, and specifies the OMEGA-7 ("substitution = pasting") handoff.  Every declaration is a
hypothesis-free `Bool` def or a docstring record, so every declaration is axiom-free.  No file outside `Omega/`
is edited.

## What OMEGA-6 r1 SHIPPED (each machine-checked zero-axiom)

  * **B1 — the CaTT ps-context layer** (`PsContext.lean`).  `PsContextRow` (the Finster–Mimram pss/pse/psd/ps
    move sequence, a FLAT inductive) + `psContextCheck` (the decidable ps-judgment as a focus-dimension stack
    walk) + non-vacuity: the single-2-cell disk and the horizontal-composite pasting scheme CHECK `true`, a
    dangling context and an underflowing context CHECK `false`.
  * **B2 — the CaTT coherence-rule seed** (`CohSeed.lean`).  `CohRow` (a checked ps-context + a parallel
    boundary, cloning `CriticalPairRow`) + `cohGenerator` (the fire, `CellExpr.gen`) + the row-generation seed
    (`cohGenerator_fills`) + globularity-for-free (`cohGenerator_isGlobularCell`) + two REAL coherence
    generators (the disk 2-cell coherence and the interchange coherence — a CaTT `coh` cell filling the
    Godement critical pair, boundaries structurally distinct).
  * **B3 — the invertibility duality seed** (`InvertibilitySeed.lean`).  `omegaCellStructure` (HL23
    `CellStructure` on the ω-cells, identity Skolem placeholder) + the hypothesis-free one-way inclusion
    `omegaSnInvertible_subset_folkInvertible` (least ⊆ greatest) + the conditional collapse recall
    `omegaFixpointsAgree_of_wellFounded` (HL23 Cor 4.35) + the honest placeholder-gap witness
    `placeholderGap_folkStrictlyBiggerThanSn` (HL23 Prop 4.31).

## The honest line (checking DECIDED, two walls NAMED)

CaTT **type-checking** — the ps-judgment (B1), coherence-admission (checked ps + decidable parallelism, B2),
and raw-term structural equality (`cellBeq`, OMEGA-1) — is DECIDABLE and ships as `Bool` checkers.  What is NOT
decidable is (a) the general PRESENTED STRICT word problem (Burroni TCS 1993, already walled by
`CeilingLift.lean`), and (b) WEAK-ω COHERENCE EQUALITY (Makkai — the weak-ω analog of the strict word problem,
aligned with the `makkaiWordEquality` / §3.9 ledger).  r1 ships the checking and names both walls; neither is
axiomatized (both are `= false` markers with citations).

Raw Lean 4 + Init; a docstring record plus hypothesis-free `Bool` markers, so every declaration is axiom-free.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The checking-vs-deciding markers (the ceiling ledger) -/

/-- ★ **The ps-judgment is a DECIDABLE syntactic check.**  `= true`: `psContextCheck : PsContextRow → Bool`
computes the Finster–Mimram ps-judgment structurally (a focus-dimension stack walk), propext-clean.  CaTT
ps-context membership is decided by computation (Finster–Mimram, LICS 2017). -/
def fxOmega6_psContextCheckDecidable : Bool := true

/-- ★ **Coherence-cell admission is DECIDABLE / checkable.**  `= true`: a `CohRow` fires its `cohGenerator`
once the ps-context CHECKS (`psContextChecks`) and the boundary is a parallel pair (`boundaryParallel`) — both
a `Bool` gate and a decidable-parallelism gate at the `IsParallelPair` level (NOT requiring `Prop`-valued
`DecidableEq (CellExpr)`; that Bool→Prop residual stays off the critical path). -/
def fxOmega6_cohCellCheckable : Bool := true

/-- ★ **The FREE-strict word problem is DECIDABLE** (recall, not re-proved).  `= true` via the OMEGA-2 Steiner
crown on the strong-Steiner fragment (`decideFreeConvSound` + `isStrongSteiner`, `Steiner/`).  The decidable
floor the weak/directed rung sits above. -/
def fxOmega6_freeStrictWordProblemDecidable : Bool := true

/-- ★ **WALL (permanent, cited) — WEAK-ω coherence equality is NOT decidable in general.**  `= false`:
deciding equality of parallel coherence cells UP TO the weak-ω structure is the weak-ω analog of the strict
word problem — Makkai strength.  Cited, NOT axiomatized; aligned with the `makkaiWordEquality` / §3.9 ledger
(`SN-638`).  Set `true` only if a general weak-ω decision procedure existed — it does not. -/
def fxOmega6_weakOmegaCoherenceEqualityDecidable : Bool := false

/-- ★ **WALL (permanent, cited) — the GENERAL presented (strict) word problem is NOT decidable.**  `= false`:
already carried by `CeilingLift.lean` (`fxOmega_ceilingLiftUndecidableInstanceMechanized`,
`semiThue_iff_encodedTwoCellSuspended`) — Post 1947 / Markov 1947 / Burroni TCS 1993.  Referenced here, NOT
duplicated. -/
def fxOmega6_generalPresentedWordProblemDecidable : Bool := false

/-- ★ **The full weak-ω MODEL (contractible globular-operad algebra) is NOT shipped.**  `= false`: the
Batanin–Leinster weak-ω via a contractible globular operad algebra is deferred (`GlobularSet.lean`
`fxMode_hasInitialContractibleOperadAlgebras := false`).  The B2 `CohSeed` is the ps-GATED fragment of
Leinster's `GlobularContraction`, not the full operad-algebra model. -/
def fxOmega6_weakOmegaModelAsOperadAlgebra : Bool := false

/-! ## The deferred-item markers (OMEGA-7 and the placeholder honesty) -/

/-- ★ **The CaTT FULLNESS side-condition is NOT enforced in r1.**  `= false`: `CohRow` carries the ps-check
and the parallelism, but NOT "every variable of `Γ` occurs in the boundary type", and NOT the typed link that
`source` / `target` live OVER `psContext`.  Both need the typed telescope + substitution — the OMEGA-7 pasting
engine. -/
def fxOmega6_cohFullnessChecked : Bool := false

/-- ★ **No typed telescope / variables / substitution in r1.**  `= false`: the ps-context ships as flat DATA +
a `Bool` checker (B1), deliberately NOT a typed telescope (a typed telescope drags weakening / substitution =
OMEGA-7, "substitution = pasting"). -/
def fxOmega6_psContextTypedTelescope : Bool := false

/-- ★ **The GENUINE ω reverse / unit / counit is NOT modelled in r1.**  `= false`: `omegaCellStructure` uses
the identity Skolem placeholder (InvertibilitySet's own caveat); a meaningful invertibility predicate needs the
genuine ω-categorical inverses + coherence witnesses + the identity base, DEFERRED to the Mode / OmegaCategory
substrate. -/
def fxOmega6_genuineOmegaReverseModelled : Bool := false

/-- ★ **The SN-invertible ⊆ folk-invertible inclusion IS shipped (hypothesis-free).**  `= true`:
`omegaSnInvertible_subset_folkInvertible` (least ⊆ greatest at the ω-carrier); the always-true half of the
HL23 duality, with the honest placeholder gap witnessed alongside. -/
def fxOmega6_snInvertibleSubsetFolkShipped : Bool := true

/-! ## The completion marker -/

/-- ★ **OMEGA-6 r1 = CHECKING SHIPPED / TWO WALLS NAMED.**  `= true` (recording the r1 scope is met): the ps
+ coherence checking layer + the invertibility one-way seed all type-check zero-axiom, with the two permanent
walls (Makkai / Burroni) named and the OMEGA-7 deferrals recorded.  This is NOT a claim that the weak-ω MODEL
is complete (`fxOmega6_weakOmegaModelAsOperadAlgebra = false`) — it records that the r1 CHECKING deliverable +
seeds shipped. -/
def fxOmega6_r1CheckingShipped : Bool := true

/-! ## The OMEGA-7 handoff spec

OMEGA-7 ("substitution = pasting", #2237) is the ONE engine that turns the flat ps-context DATA into a typed
pasting / substitution operation.  It CONSUMES, from r1:

  * `PsContextRow` + `psContextCheck` (B1) — the checked pasting-scheme shapes;
  * `CohRow` + `cohGenerator` (B2) — the coherence generators whose boundaries the pasting must type;
  * `boundarySource` / `boundaryTarget` (OMEGA-1) — the carrier boundaries the typed link runs over.

and PRODUCES: the `psContextRealize` pasting map (a checked ps-context → a composite carrier cell), the typed
link (`CohRow.source` / `.target` live over `.psContext`), the CaTT fullness gate, and the coh IOTA (the
coherence cell's computation / substitution rule).  `OmegaSevenPastingShape` records the core signature. -/

/-- The OMEGA-7 **pasting-engine core signature** — realize a (checked) ps-context as a composite cell over the
carrier.  Ships here as the handoff contract; OMEGA-7 additionally supplies the typed link, the fullness gate,
and the coh iota (see the section docstring). -/
def OmegaSevenPastingShape (computad : OmegaComputad) : Type :=
  PsContextRow → OmegaCell computad

/-- ★ **The OMEGA-7 handoff is RECORDED** (the consumed interface — `PsContextRow`, `CohRow`, the carrier
boundaries — and the produced `OmegaSevenPastingShape` pasting core, typed link, fullness gate, and coh iota).
`= true`. -/
def fxOmega6_omegaSevenHandoffRecorded : Bool := true

/-! ## The r2 section — the TYPED TELESCOPE + the FULLNESS gate + the REVERSE duality (this file imports every
r2 piece: `PsContextTyped`, `CohGateTyped`, `InvertibilityReverseSeed`)

★ **What OMEGA-6 r2 SHIPPED (each machine-checked zero-axiom).**

  * **B1 — the TYPED ps-telescope on de Bruijn LEVELS** (`PsContextTyped.lean`).  `TeleType` (`star |
    arrow base sLevel tLevel` with `Nat` level endpoints) + `elaboratePsContext` (the r1 focus walk refined
    into `(telescope, level, type)`) + `psTypedCheck` + `telescopeWellFormed` (endpoints carry their base
    type) + THE ERASURE COMMUTING LEMMA `psTypedCheck_implies_psContextCheck` (via
    `elaborate_focusDim_eq_psFocus`: `teleTypeDim` of the focus type IS r1 `psFocus`) with the honest converse
    `psContextCheck_implies_psTypedCheck` (equivalent on the bare spine).  Levels — not indices — make
    weakening a free list extension; substitution is NOT introduced (it stays OMEGA-7).
  * **B2 — the TYPED coherence FULLNESS gate** (`CohGateTyped.lean`).  `cohFullnessCheck` decides the CaTT
    fullness side-condition over the r2 telescope; `CohRowTyped` enriches an r1 `CohRow` and `cohRowTypedForget`
    is the genuine forgetful MAP (identification through the shared row, not a disjoint conjunction);
    `interchangeMissingMiddleCoh` is the LOAD-BEARING rejection (r1 admits, typing rejects by `rfl`-false).
  * **B3 — the REVERSE invertibility duality, classified** (`InvertibilityReverseSeed.lean`).
    `reverseDuality_unconditional_false` machine-checks that the guard-free reverse is FALSE; the conditional
    reverse is recalled by name (`omegaFixpointsAgree_of_wellFounded`, r1); the genuine ω reverse is walled.

## The honesty discipline on the r1 marker (conjunction-vs-identification, applied to the MARKER)

r1's `fxOmega6_psContextTypedTelescope` (`= false`) BUNDLES the typed telescope WITH substitution
("substitution = pasting", OMEGA-7); `SubstitutionPastingLedger.lean` cites it `= false`.  r2 ships the TYPING
half but NOT substitution, so flipping the bundled r1 marker to bare `true` would OVER-CLAIM substitution and
stale that citation.  So the r1 marker STAYS `false` (append-only: no r1 marker flipped), and r2 records the
precise sub-claim in `fxOmega6_psContextTypedTelescopeTypingShipped` below.  Fabricating a flip of the bundled
marker is exactly the trap this discipline forbids. -/

/-- ★ **The TYPING half of the typed telescope is SHIPPED (B1+B2).**  `= true`: `TeleType` + `teleTypeDim` +
`PsTelescope` + `psTypedCheck` + `telescopeWellFormed` (the typed context object with well-scoped, endpoint
-typed entries) + `cohFullnessCheck` (the typed-parallelism / fullness decision) shipped zero-axiom.  This does
NOT include substitution / realization — those stay OMEGA-7 ("substitution = pasting"); the bundled r1 marker
`fxOmega6_psContextTypedTelescope` therefore STAYS `false` (its docstring bundles substitution).  This is the
OMEGA-7 r3 typed-boundary INTERFACE: r3 seats `AdmittedTable n` on `TeleType` (`teleTypeDim boundary = n`) and
types a row's boundary OVER a `psTypedCheck`-checked context, `cohFullnessCheck` deciding admissibility. -/
def fxOmega6_psContextTypedTelescopeTypingShipped : Bool := true

/-- ★ **The CaTT FULLNESS side-condition is now DECIDED, typed over the telescope (B2).**  `= true`:
`cohFullnessCheck` decides "every variable of the ps-context occurs in the boundary" over the r2 telescope
(`CohGateTyped.lean`), and `CohRowTyped` / `cohRowTypedForget` link a typed row to its r1 `CohRow` by a genuine
map.  Complements r1's `fxOmega6_cohFullnessChecked = false` (which stays `false`: r1's `CohRow` fields were
independent; the DECISION lands here, over the typed telescope).  NON-VACUITY: `interchangeMissingMiddleCoh`
is admitted by r1 but rejected by this gate. -/
def fxOmega6_cohFullnessCheckedTyped : Bool := true

/-- ★ **The UNCONDITIONAL reverse duality is FALSE (B3) — cited, not axiomatized.**  `= false`: the guard-free
"folk-invertible ⇒ SN-invertible" is refuted machine-checked by `reverseDuality_unconditional_false` (HL23
Prop 4.31 at the identity-Skolem placeholder).  A GENUINE reverse needs either the well-founded guard (r1
`omegaFixpointsAgree_of_wellFounded`, globally false at the raw ω-layer) or the genuine ω inverses — the
Makkai wall, aligned with `fxOmega6_genuineOmegaReverseModelled = false` and
`fxOmega6_weakOmegaCoherenceEqualityDecidable = false` (Makkai / SN-638).  NEVER axiomatized. -/
def fxOmega6_reverseDualityUnconditional : Bool := false

/-- ★ **OMEGA-6 r2 = TYPED TELESCOPE + FULLNESS GATE + REVERSE CLASSIFIED, SHIPPED.**  `= true` (recording the
r2 scope is met): the typed telescope + erasure commuting lemma (B1), the typed fullness gate + load-bearing
rejection (B2), and the reverse-duality refutation + walls (B3) all type-check zero-axiom.  This is NOT a
claim that substitution / realization is shipped (`fxOmega6_psContextTypedTelescope` STAYS `false`) — it
records that the r2 TYPING deliverable + the OMEGA-7 r3 typed-boundary interface shipped.  The residual r3 gap
the telescope does NOT close is the type-respecting VALUATION `TeleVar(level) → CellExpr` (the shared-variable
term→cell action, `SubstitutionPastingLedger.fxOmega7_fragmentTermToCellActionReached = false`). -/
def fxOmega6_r2TypedTelescopeShipped : Bool := true

end FX1Poly.Polygraph.Omega
