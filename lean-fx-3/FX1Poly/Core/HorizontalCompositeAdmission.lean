import FX1Poly.Core.CertifyRawCellExactCompHRejects
import FX1Poly.Core.CertifiedRawCell
/-! # FX1Poly/Core/HorizontalCompositeAdmission — the compH admission boundary

The raw layer represents horizontal composition
(`RawCell.horizontalComposite`) but the certifier rejects it
unconditionally (`certifyRawCellExact?_compH_rejects`,
`.unsupportedCompH`), pending the Axis 6 Gray-tensor semantics.
This file ships the precise ADMISSION BOUNDARY for that rejection:

1. `HorizontallyDimComposable` — the decidable DIMENSIONAL half of
   the horizontal-composability obligation (both operands positive-
   dimensional, equal dimension), separate from raw representability.
   NECESSARY only: the full Gray boundary condition additionally
   needs codimension-1 endpoint matching, which the raw layer cannot
   express (composite cells carry no endpoint accessors) — that
   judgment is a FIELD of the admission record below, supplied by a
   future Axis 6 module, not a computable predicate here.

2. `GrayInterchangeShape` — ★ THE BLOCKER, stated, never assumed:
   the interchange law `(a ∘v b) ∘h (c ∘v d) ~ (a ∘h c) ∘v (b ∘h d)`
   over an arbitrary cell equivalence.  At raw syntactic equality the
   two sides are distinct trees, so any admission must supply the
   equivalence AND the law.  No instance is constructed anywhere.

3. `HorizontalCompositeAdmission profile` — what a profile must
   supply to certify compH: an endpoint judgment refining the
   dimensional predicate, a CERTIFIED composable witness pair (the
   non-degeneracy guard against `False`-judgment fake admissions),
   the certificate builder for composites, and the interchange law.

4. ★ The COMPLETENESS theorems: `PolyCell` deliberately has no
   horizontalComposite constructor, so the certified layer cannot
   represent a compH-indexed certificate AT ALL
   (`PolyCell.horizontalComposite_empty`,
   `CertifiedRawCell.horizontalComposite_empty`) — and therefore
   `HorizontalCompositeAdmission.unrealizable`: NO profile can
   inhabit the admission record today.  This upgrades the existing
   behavioral rejection ("the current certifier returns
   `.unsupportedCompH`") to a structural one ("any certifier into the
   current certified layer MUST reject").  Admitting compH requires
   extending `PolyCell` itself with Gray boundary semantics — the
   Axis 6 design decision, exactly as polycell.md §4 stages it.

## Why no certifier branch is added

The task discipline: a certifier branch may exist ONLY after the
semantic admission predicate can discharge the boundary obligations.
`HorizontalCompositeAdmission.unrealizable` proves no such discharge
exists against the current `PolyCell`, so the branch would be dead
code guarded by an uninhabited hypothesis — the honest state is the
unconditional rejection plus this record of what unlocking it costs.

## The reducibility-coverage story (SN-080)

`horizontalComposite` is a CELL-layer constructor, not one of the
203 dim-0 `Generator`s: the `SupportedGenerator` / `semanticTier`
classifiers and the `RawTerm` reducibility/SN coverage do not range
over it BY KIND (a `RawTerm` contains no cells, so no `Step` rule,
no reducibility candidate, and no SN obligation can mention it).
Its only possible semantic story is cell-level — precisely what the
emptiness theorems pin as absent.  `horizontalCompositeStatus =
.stagingOnly` is the honest ledger marker; a vacuous "SN arm" for it
would be a fake claim.

Zero-axiom; gated in `FX1PolyAudit/AuditCoreSubstrateEta.lean`.
-/

namespace FX1Poly.Core

/-- The DIMENSIONAL half of horizontal composability: both operands
positive-dimensional and at the same dimension.  Decidable, and
necessary for any genuine Gray-boundary judgment — but NOT
sufficient (endpoint matching is not expressible at the raw layer). -/
def HorizontallyDimComposable {scope : Nat}
    (left right : RawCell scope) : Prop :=
  0 < left.dim ∧ left.dim = right.dim

instance {scope : Nat} (left right : RawCell scope) :
    Decidable (HorizontallyDimComposable left right) :=
  inferInstanceAs (Decidable (0 < left.dim ∧ left.dim = right.dim))

/-- Positive smoke: two identity cells over term bases are
dimensionally composable (both at dim 1). -/
theorem identityPair_horizontallyDimComposable {scope : Nat}
    (leftBase rightBase : RawTerm scope) :
    HorizontallyDimComposable
      (.identityCell (.termBase leftBase))
      (.identityCell (.termBase rightBase)) :=
  ⟨Nat.zero_lt_one, rfl⟩

/-- Negative smoke: term bases (dim 0) are never horizontally
composable — there is no dim-(-1) boundary to glue along. -/
theorem termBasePair_not_horizontallyDimComposable {scope : Nat}
    (leftTerm rightTerm : RawTerm scope) :
    ¬ HorizontallyDimComposable (.termBase leftTerm) (.termBase rightTerm) :=
  fun composable => Nat.lt_irrefl 0 composable.1

/-- ★ THE BLOCKER, stated as a law shape and never assumed: the Gray
interchange — composing vertically then horizontally agrees with
composing horizontally then vertically, up to the supplied cell
equivalence, on boundary-compatible quadruples.  At raw syntactic
equality the two sides are DISTINCT trees, so any future Axis 6
admission must supply a genuine cell equivalence together with this
law.  polycell.md §4 stages this as the Axis 6 obligation. -/
def GrayInterchangeShape
    (cellEquiv : {scope : Nat} → RawCell scope → RawCell scope → Prop)
    (boundaryJudgment : {scope : Nat} → RawCell scope → RawCell scope → Prop) :
    Prop :=
  ∀ {scope : Nat}
    (upperLeft lowerLeft upperRight lowerRight : RawCell scope),
    boundaryJudgment upperLeft upperRight →
    boundaryJudgment lowerLeft lowerRight →
    cellEquiv
      (.horizontalComposite (.verticalComposite upperLeft lowerLeft)
        (.verticalComposite upperRight lowerRight))
      (.verticalComposite (.horizontalComposite upperLeft upperRight)
        (.horizontalComposite lowerLeft lowerRight))

/-- What a profile must supply for the certifier to ADMIT horizontal
composition.  The witness fields are the non-degeneracy guard: a
`False` boundary judgment cannot fake-satisfy this record, because a
concrete CERTIFIED composable pair must be exhibited.

No instance of this structure exists in the tree, and
`HorizontalCompositeAdmission.unrealizable` below PROVES none can
exist against the current `PolyCell` — the record is the honest
price list for the Axis 6 unlock, not a claim. -/
structure HorizontalCompositeAdmission (profile : PolyProfile) where
  /-- The full Gray boundary judgment (endpoint matching included),
  supplied by the future Axis 6 module. -/
  boundaryJudgment :
    {scope : Nat} → RawCell scope → RawCell scope → Prop
  /-- The judgment refines the decidable dimensional predicate. -/
  boundaryRequiresDimComposable :
    ∀ {scope : Nat} {left right : RawCell scope},
      boundaryJudgment left right → HorizontallyDimComposable left right
  /-- The cell equivalence the interchange law is stated over. -/
  cellEquiv : {scope : Nat} → RawCell scope → RawCell scope → Prop
  /-- ★ The interchange law — the Axis 6 blocker, demanded, never
  assumed. -/
  interchange : GrayInterchangeShape cellEquiv boundaryJudgment
  /-- Non-degeneracy witness scope. -/
  witnessScope : Nat
  /-- Non-degeneracy witness: left operand. -/
  witnessLeft : RawCell witnessScope
  /-- Non-degeneracy witness: right operand. -/
  witnessRight : RawCell witnessScope
  /-- The witnesses are composable under the supplied judgment. -/
  witnessComposable : boundaryJudgment witnessLeft witnessRight
  /-- The left witness certifies. -/
  witnessLeftCertified : CertifiedRawCell profile witnessScope witnessLeft
  /-- The right witness certifies. -/
  witnessRightCertified : CertifiedRawCell profile witnessScope witnessRight
  /-- The certificate builder: composable certified operands yield a
  certificate FOR THE COMPOSITE — the field the certifier branch
  would consume. -/
  buildComposite :
    ∀ {scope : Nat} (left right : RawCell scope),
      boundaryJudgment left right →
      CertifiedRawCell profile scope left →
      CertifiedRawCell profile scope right →
      CertifiedRawCell profile scope (.horizontalComposite left right)

/-- ★ The certified layer cannot represent horizontal composition:
`PolyCell` has no constructor whose rawCell index is a
`.horizontalComposite` (the constructor is deliberately absent
pending Axis 6), so the type is empty at that index. -/
theorem PolyCell.horizontalComposite_empty {profile : PolyProfile}
    {sort : CellSort} {dim scope : Nat}
    {boundary : CellBoundary profile sort dim scope}
    {left right : RawCell scope}
    (cell : PolyCell profile sort dim scope boundary
      (.horizontalComposite left right)) :
    False :=
  nomatch cell

/-- A compH-indexed certificate cannot exist: its `certifiedCell`
field would inhabit the empty `PolyCell` index. -/
theorem CertifiedRawCell.horizontalComposite_empty {profile : PolyProfile}
    {scope : Nat} {left right : RawCell scope}
    (certified :
      CertifiedRawCell profile scope (.horizontalComposite left right)) :
    False :=
  PolyCell.horizontalComposite_empty certified.certifiedCell

/-- ★★ No profile can admit horizontal composition against the
current certified layer: any admission record would build a
compH-indexed certificate from its own witnesses, contradicting the
emptiness.  The behavioral rejection
(`certifyRawCellExact?_compH_rejects`) is therefore COMPLETE — every
certifier into this `PolyCell` must reject compH, and unlocking it
requires extending `PolyCell` with Gray boundary semantics (Axis 6),
not editing the certifier. -/
theorem HorizontalCompositeAdmission.unrealizable {profile : PolyProfile}
    (admission : HorizontalCompositeAdmission profile) : False :=
  CertifiedRawCell.horizontalComposite_empty
    (admission.buildComposite admission.witnessLeft admission.witnessRight
      admission.witnessComposable
      admission.witnessLeftCertified admission.witnessRightCertified)

/-- Cell-layer semantic admission status for composite constructors. -/
inductive CellCompositeStatus where
  /-- Admitted by the certifier with full boundary obligations. -/
  | certified
  /-- Representable at the raw layer only; the certifier rejects and
  the certified layer has no constructor for it. -/
  | stagingOnly
  deriving DecidableEq, Repr

/-- Vertical composition is CERTIFIED: the certifier admits it under
the equal-positive-dimension boundary discipline. -/
def verticalCompositeStatus : CellCompositeStatus := .certified

/-- Horizontal composition is STAGING-ONLY: representable raw, never
certified (see the emptiness + unrealizability theorems above).
This is the SN-080 honesty marker — compH is a cell-layer ctor
outside the Generator-based reducibility coverage BY KIND, and its
cell-level semantic story is provably absent today. -/
def horizontalCompositeStatus : CellCompositeStatus := .stagingOnly

theorem horizontalCompositeStatus_eq_stagingOnly :
    horizontalCompositeStatus = .stagingOnly := rfl

end FX1Poly.Core
