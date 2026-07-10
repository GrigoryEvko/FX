import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentLawRelation
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedNormalizer
import FX1Poly.Polygraph.TwoCategory.Amalgam.ComposableFragmentDispatch

/-! # Polygraph/TwoCategory/Amalgam/SaturatedRelationFamily — the parametric relation-family library
(RELFAM r1, #2213)

The generic saturated interface (`SaturatedOver.lean`) shipped the carrier `SaturatedConvOver signature baseRel`,
its decision interface `DecidableSaturatedConvForRel signature baseRel`, and its universal property
`SaturatedConvOver.recInto`.  Two shipped deciders already inhabit that interface over NON-TRIVIAL walkers by the
SAME four-line move: run a bespoke walker decision, then transport its verdict along the walker's iff bridge to
the generic carrier.  `monadWalkerSaturatedDecider` (`ComposableFragmentDispatch.lean`) does it for the walking
monad; `decideSaturatedConvOverIdempotent` (`SaturatedComponentDecider.lean`) does it for the walking idempotent
monad.  Both bodies are IDENTICAL up to the walker decision and the bridge — the transport is copy-pasted.

This file abstracts that ONE transport into a `SaturatedRelationFamily` record and derives the generic-interface
decider `SaturatedRelationFamily.decider` from it ONCE.  Every shipped walker becomes an instance whose `.decider`
reduces DEFINITIONALLY to the already-shipped bespoke wrapper (three `rfl` regressions).  RELFAM r1 is therefore
the BEST CASE: PACKAGING + REGRESSION — the two hard deciders were already wrapped at the generic interface, so
nothing new needs proving; the family just names the shared last mile.

## The `_ofSeed` genericity route taken (honest)

`decideSaturatedTwoCellConv_ofSeed` (`WalkingAdjunction/SaturatedMatchingDecisionAssembly.lean`) is NOT the
transport this library abstracts.  It is adjunction-HARDCODED: it decides the BESPOKE `SaturatedTwoCellConv` over
`adjunctionModeSignature` by the Schanuel-Street monotone-map canonicalization (`convOfMapEq` / `mapEqOfConv`),
NOT the generic `SaturatedConvOver`, and carries no signature/relation parameter.  Its `_ofSeed` suffix does NOT
denote a bounded seed-enumeration (there is none).  So it is neither reused nor generalized here — the family
transport is the iff-wrap, which already exists TWICE as the two shipped wrappers and is abstracted once as
`SaturatedRelationFamily.decider`.

## The shape (NOT a rows-list + fuel + completeness certificate)

The recon's hypothesized T1 shape — a `List RelationRow` + a bounded-saturation fuel + an enumeration-closure
certificate — DOES NOT EXIST in the substrate.  The real deciders each carry their own model: the monad a Delta
monotone-map arity fold, the idempotent monad a boundary-length normalization + local posetality, the involution
plain thinness.  What a family member supplies is exactly `(signature, baseRel, walkerConv, iff-bridge,
walker-decider)`; the family-generic content is the iff-transport, not a saturation loop.

## What ships here (each piece zero-axiom, structural, ASCII-only)

  * **`SaturatedRelationFamily`** — the record: a presentation `signature`, a law relation `baseRel`, a walker
    convertibility `walkerConv`, the bridge `walkerIffGeneric : walkerConv <-> SaturatedConvOver signature
    baseRel`, and a `walkerDecider : Decidable (walkerConv ..)`.
  * **`SaturatedRelationFamily.decider`** — the ONE family-generic transport: `Decidable (walkerConv ..)` +
    `walkerConv <-> SaturatedConvOver ..` ==> `DecidableSaturatedConvForRel signature baseRel`.  Verbatim the two
    shipped wrappers, proved once.
  * **`monadRelationFamily` / `idempotentRelationFamily` / `involutionRelationFamily`** — the three instances, at
    the two named regression targets (idempotent, involution) plus the monad (the member that separates).
  * **`*_decider_eq_*`** — the three `rfl` regressions: each family `.decider` IS the shipped bespoke decider
    (full-hom-set DEFINITIONAL equality, the strongest agreement form — not merely equal on named pairs).
  * non-vacuity `#eval`s: monad separates (isTrue on assoc, isFalse on the two faces); idempotent and involution
    decide isTrue (both TOTAL deciders — see the divergence note).

## The tier ladder + the divergence (the markers stay honest)

`fxRelFam_hasParametricFamilyLibrary` flips `true`: the family + transport + three regressions are hypothesis-free.
The two deeper tiers stay `false`.  `fxRelFam_hasInvariantTierFamilyDecision = false`: there is NO family-generic
boundary-INVARIANT decision — each walker's `walkerDecider` carries its own bespoke invariant (Delta / boundary
length / thinness), abstracted nowhere.  `fxRelFam_hasNormalFormTierFamilyDecision = false`: there is NO
family-generic NORMAL FORM either.  The library abstracts only the LAST mile (verdict transport), not the decision
mechanism.

DIVERGENCE (precise, reshapes #2214): the two named regression targets are BOTH total always-`isTrue` deciders —
the idempotent monad is locally posetal (Lack), the involution is thin (no 2-generators) — so NEITHER can exhibit
an `isFalse`.  The family's separating power is witnessed by the MONAD member (Delta monotone-map), included here
for that reason.  A relation family is thus NOT guaranteed to separate; separation is a per-walker property, not a
family-generic one.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## P1 — the relation-family record -/

/-- ★ **A saturated relation family** — the packaging of one decided walker at the generic saturated interface.
A family bundles a presentation `signature`, its law relation `baseRel` (the doctrine's generating equations), the
walker's own convertibility `walkerConv` (a `CellRel`), the bridge `walkerIffGeneric` identifying `walkerConv`
with the generic `SaturatedConvOver signature baseRel`, and a `walkerDecider` deciding `walkerConv`.  From these
five fields `SaturatedRelationFamily.decider` derives the generic-interface `DecidableSaturatedConvForRel` with no
further work.  This is the MODE-ADMIT (#2214) consumption interface: a mode theory that supplies these fields
INHERITS its word-problem decidability at the composable interface, zero new proofs. -/
structure SaturatedRelationFamily where
  /-- The presentation the walker lives over. -/
  signature : ModeSignature
  /-- The doctrine's law relation — the generating equations `SaturatedConvOver` closes into a congruence. -/
  baseRel : CellRel signature
  /-- The walker's own saturated convertibility (a `CellRel`), e.g. `MonadSaturatedTwoCellConv`. -/
  walkerConv : CellRel signature
  /-- The bridge: the walker's convertibility IS the generic saturated conv at `baseRel` — the `mp`/`mpr` are the
  two structural inductions each shipped walker already proves (`monadSaturated_iff_generic` pattern). -/
  walkerIffGeneric :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    (cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath) →
      (walkerConv cellAlpha cellBeta ↔ SaturatedConvOver signature baseRel cellAlpha cellBeta)
  /-- The walker's own decision of its convertibility — its bespoke model (Delta / boundary length / thinness). -/
  walkerDecider :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    (cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath) →
      Decidable (walkerConv cellAlpha cellBeta)

/-! ## P2 — the family-generic transport (ONE proof, verbatim the two shipped wrappers) -/

/-- ★★ **The family-generic saturated decider** — the ONE transport RELFAM abstracts.  Given a family, run its
`walkerDecider` and carry the verdict across `walkerIffGeneric` to the generic carrier: `isTrue` via `.mp`,
`isFalse` by the contrapositive via `.mpr`.  This is the four-line move duplicated in `monadWalkerSaturatedDecider`
and `decideSaturatedConvOverIdempotent`, now proved once.  Full enumeration of `Decidable` (no wildcard), so
propext-free — exactly the shipped wrappers' zero-axiom pattern. -/
def SaturatedRelationFamily.decider (fam : SaturatedRelationFamily) :
    DecidableSaturatedConvForRel fam.signature fam.baseRel :=
  fun cellAlpha cellBeta =>
    match fam.walkerDecider cellAlpha cellBeta with
    | isTrue conv => isTrue ((fam.walkerIffGeneric cellAlpha cellBeta).mp conv)
    | isFalse notConv =>
        isFalse (fun generic => notConv ((fam.walkerIffGeneric cellAlpha cellBeta).mpr generic))

/-! ## P3 — regression instance ONE: the walking idempotent monad (named target) -/

/-- The **walking-idempotent-monad relation family** — BORN GENERIC (POLY-TAB r5): the four idempotent laws
(`IdempotentLawRel`), the walker conv IS the generic carrier `SaturatedConvOver monadModeSignature IdempotentLawRel`
itself (so the bridge is `Iff.rfl`), and its decider is the BESPOKE-FREE native
`decideSaturatedConvOverIdempotentNative` (local posetality proved directly over the generic carrier).  The bespoke
`IdempotentMonadSaturatedTwoCellConv` lane is RETIRED; this member now has the involution's identity-migration shape,
a genuine NON-EMPTY-relation family member decided natively. -/
def idempotentRelationFamily : SaturatedRelationFamily where
  signature := monadModeSignature
  baseRel := IdempotentLawRel
  walkerConv := fun cellAlpha cellBeta =>
    SaturatedConvOver monadModeSignature IdempotentLawRel cellAlpha cellBeta
  walkerIffGeneric := fun _ _ => Iff.rfl
  walkerDecider := decideSaturatedConvOverIdempotentNative

/-- ★ **Regression ONE (full-hom definitional agreement).**  On EVERY parallel pair the idempotent family's
derived decider IS the BESPOKE-FREE native `decideSaturatedConvOverIdempotentNative` — the born-generic family's
`walkerDecider` field, carried across the `Iff.rfl` bridge to identity.  Universally quantified over the whole hom
set, so this is full-hom agreement (not merely per named pair).  Post-retirement (POLY-TAB r5) the library
reproduces the SHIPPED native decider exactly (the old bespoke-riding `decideSaturatedConvOverIdempotent` was
retired; its decision content is preserved natively). -/
theorem idempotentRelationFamily_decider_eq_shipped
    {sourceMode targetMode : monadModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadModeSignature.graph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    idempotentRelationFamily.decider cellAlpha cellBeta
      = decideSaturatedConvOverIdempotentNative cellAlpha cellBeta :=
  rfl

/-! ## P4 — regression instance TWO: the walking involution (named target) -/

/-- The **walking-involution relation family** — the thin (no-2-generator) member.  Its law relation is EMPTY
(`emptyCellRel`), its walker conv IS the generic carrier itself, so the bridge is `Iff.rfl`, and its decider is
the shipped thin decision (`involutionSaturatedThinDecider`).  The degenerate but genuine end of the family. -/
def involutionRelationFamily : SaturatedRelationFamily where
  signature := involutionComputad.toModeSignature
  baseRel := emptyCellRel involutionComputad.toModeSignature
  walkerConv := fun cellAlpha cellBeta =>
    SaturatedConvOver involutionComputad.toModeSignature
      (emptyCellRel involutionComputad.toModeSignature) cellAlpha cellBeta
  walkerIffGeneric := fun _ _ => Iff.rfl
  walkerDecider := involutionSaturatedThinDecider

/-- ★ **Regression TWO (full-hom definitional agreement).**  On EVERY parallel pair the involution family's
derived decider IS the shipped thin decider `involutionSaturatedThinDecider`: the bridge is `Iff.rfl` (the walker
conv already IS the generic carrier) and the thin decider is always `isTrue`, so the transport collapses to
identity. -/
theorem involutionRelationFamily_decider_eq_thin
    {sourceMode targetMode : involutionComputad.toModeSignature.graph.Mode}
    {sourcePath targetPath :
      ModalityPath involutionComputad.toModeSignature.graph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr involutionComputad.toModeSignature sourcePath targetPath) :
    involutionRelationFamily.decider cellAlpha cellBeta
      = involutionSaturatedThinDecider cellAlpha cellBeta :=
  rfl

/-! ## The separating member: the walking monad (Delta monotone-map, exhibits isFalse) -/

/-- The **walking-monad relation family** — the three monad laws (`MonadLawRel`), the walker conv
(`MonadSaturatedTwoCellConv`), its bridge (`monadSaturated_iff_generic`), and the Delta monotone-map decision
(`monadSaturatedTwoCellDecision`).  Included because it is the member whose decider genuinely SEPARATES parallel
pairs (isFalse capable) — the two named targets cannot (both total). -/
def monadRelationFamily : SaturatedRelationFamily where
  signature := monadModeSignature
  baseRel := MonadLawRel
  walkerConv := fun cellAlpha cellBeta => MonadSaturatedTwoCellConv cellAlpha cellBeta
  walkerIffGeneric := monadSaturated_iff_generic
  walkerDecider := monadSaturatedTwoCellDecision

/-- ★ **Regression THREE (full-hom definitional agreement).**  On EVERY parallel pair the monad family's derived
decider IS the shipped `monadWalkerSaturatedDecider` (`ComposableFragmentDispatch.lean`) — verbatim the same
body. -/
theorem monadRelationFamily_decider_eq_walker
    {sourceMode targetMode : monadModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadModeSignature.graph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    monadRelationFamily.decider cellAlpha cellBeta = monadWalkerSaturatedDecider cellAlpha cellBeta := by
  dsimp only [SaturatedRelationFamily.decider, monadWalkerSaturatedDecider, monadRelationFamily]
  cases monadSaturatedTwoCellDecision cellAlpha cellBeta with
  | isTrue conv => rfl
  | isFalse notConv => rfl

/-! ## P6 — non-vacuity: the family deciders RUN, agreeing with the bespoke deciders

The two named targets (idempotent, involution) are TOTAL always-`isTrue` deciders (local posetality / thinness),
so isFalse can only come from the monad member (Delta monotone-map).  Each smoke reuses a shipped pair. -/

/-- The idempotent family decider on the shipped size-4 pair `mu . (eta |> t)` vs `mu . (t <| eta)` — expect
`true` (idempotent hom is posetal, always convertible).  Agrees with `idempotentNativeDecidesTrue_smoke`. -/
def idempotentFamilyDecidesTrue_smoke : Bool :=
  match idempotentRelationFamily.decider (RawTwoCellExpr.vcomp monadMulTwoCell monadEtaTCell)
      (RawTwoCellExpr.vcomp monadMulTwoCell monadTEtaCell) with
  | isTrue _ => true
  | isFalse _ => false

/-- Smoke value: the idempotent family decider returns `true` on the shipped size-4 pair (by `rfl`). -/
theorem idempotentFamilyDecidesTrue_smoke_holds : idempotentFamilyDecidesTrue_smoke = true := rfl

/-- A pure-involution 2-cell: the identity 2-cell on the empty modality path at the involution's unique mode
(`modeCount = 1`).  A genuine cell over `involutionComputad.toModeSignature`, so the involution smoke is not
vacuous. -/
def involutionIdentityCell :
    RawTwoCellExpr involutionComputad.toModeSignature
      (ModalityPath.nil (graph := involutionComputad.toModeSignature.graph) ⟨0, by decide⟩)
      (ModalityPath.nil (graph := involutionComputad.toModeSignature.graph) ⟨0, by decide⟩) :=
  RawTwoCellExpr.id (ModalityPath.nil (graph := involutionComputad.toModeSignature.graph) ⟨0, by decide⟩)

/-- The involution family decider on the reflexive identity pair — expect `true` (thin: every parallel pair
convertible).  Agrees with `involutionSaturatedThinDecider`. -/
def involutionFamilyDecidesTrue_smoke : Bool :=
  match involutionRelationFamily.decider involutionIdentityCell involutionIdentityCell with
  | isTrue _ => true
  | isFalse _ => false

/-- Smoke value: the involution family decider returns `true` on the reflexive identity pair (by `rfl`). -/
theorem involutionFamilyDecidesTrue_smoke_holds : involutionFamilyDecidesTrue_smoke = true := rfl

/-- The monad family decider on the associativity foldings `mu . (mu |> t)` vs `mu . (t <| mu)` — expect `true`
(both fold to the width-3 degeneracy, convertible through completeness).  Agrees with `monadWalkerAssocVerdict`. -/
def monadFamilyAssocVerdict : Bool :=
  match monadRelationFamily.decider monadAssocLeftCell monadAssocRightCell with
  | isTrue _ => true
  | isFalse _ => false

/-- The monad family decider on the two unit faces `t <| eta` (`whiskerRight t eta`) vs `eta |> t`
(`whiskerLeft t eta`) — expect `false` (distinct monotone maps `[1]` vs `[0]`, separated by soundness).  The
family's separating verdict; agrees with `monadWalkerFacesVerdict`. -/
def monadFamilyFacesVerdict : Bool :=
  match monadRelationFamily.decider
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell) with
  | isTrue _ => true
  | isFalse _ => false

-- The idempotent family decider on the size-4 pair: expect `true`.
#eval idempotentFamilyDecidesTrue_smoke
-- The involution family decider on the reflexive identity pair: expect `true`.
#eval involutionFamilyDecidesTrue_smoke
-- The monad family decider on the associativity foldings: expect `true`.
#eval monadFamilyAssocVerdict
-- The monad family decider on the two unit faces (the family's separating verdict): expect `false`.
#eval monadFamilyFacesVerdict

/-! ## P5 — honesty markers -/

/-- ★★ **Honesty marker — the PARAMETRIC saturated relation-family library SHIPS (RELFAM r1).**  The record
`SaturatedRelationFamily` (presentation + law relation + walker conv + bridge + walker decider), the ONE
family-generic transport `SaturatedRelationFamily.decider` (verbatim the two shipped wrappers, proved once), and
three hypothesis-free instances whose derived decider each equals the shipped bespoke decider DEFINITIONALLY
(`idempotentRelationFamily_decider_eq_shipped`, `involutionRelationFamily_decider_eq_thin`,
`monadRelationFamily_decider_eq_walker` — full-hom-set agreement by `rfl`, not per-named-pair).  Non-vacuous: the
monad member separates (isFalse on the unit faces, isTrue on associativity), idempotent and involution decide
isTrue.  PACKAGING + REGRESSION only — nothing new proved; the `_ofSeed` decision is adjunction-hardcoded and NOT
the transport (the transport is the iff-wrap).  `= true`. -/
def fxRelFam_hasParametricFamilyLibrary : Bool := true

/-- ★ **Tier marker (honest, `false`) — NO family-generic boundary-INVARIANT decision.**  The library abstracts
only the verdict transport; each family member's `walkerDecider` still carries its OWN bespoke boundary invariant
(the walking monad a Delta monotone-map arity fold, the idempotent monad a boundary-length normalization + local
posetality, the involution plain thinness).  There is no ONE invariant-computing decision the family shares — the
recon's hypothesized rows-list + fuel + enumeration-closure shape does not exist in the substrate.  `= false`. -/
def fxRelFam_hasInvariantTierFamilyDecision : Bool := false

/-- ★ **Tier marker (honest, `false`) — NO family-generic NORMAL FORM.**  Likewise there is no shared normal form
across the family: the monad reifies to a monotone map, the idempotent monad to a boundary-length representative,
the involution to nothing (thin).  A family-generic NF would need the walkers to share a reification target; they
do not.  `= false`. -/
def fxRelFam_hasNormalFormTierFamilyDecision : Bool := false

end FX1Poly.Polygraph.Amalgam
