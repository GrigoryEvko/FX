import FX1Poly.Polygraph.Omega.WalkingEquivalencePromotionParityObstruction
import FX1Poly.Polygraph.Omega.EckmannHiltonWithId

/-! # Polygraph/Omega/WalkingEquivalencePromotionUnitorScope — the promotion DELIVERED over the
whisker-unitor-augmented relation (WP-EQUIV #2068 r4)

★★ **THE HONEST SUCCESSOR NODE IS CLOSED POSITIVELY — the classical promotion DERIVES.**  The r3
adjudication (`WalkingEquivalencePromotionParityObstruction.lean`) machine-refuted the promotion over the
bare relation — even with the left triangle adjoined as a row, the flagged-generator-parity invariant blocks
the idempotency — and located the obstruction exactly at the missing whisker-by-identity-1-cell unitors,
naming the successor node `fxEquiv_promotionOverWhiskerUnitorScopeOpen := false` ("the promotion re-founded
over `unionCellRel _ walkingEquivBaseRel (whiskerUnitRel _)`").  The r3 handoff suspected the successor
would ALSO be a refutation ("one triangle does not force the other is genuine content").  That suspicion is
WRONG for this scope, and this file proves it by DERIVATION:

  1. **The middle collapses** (`walkingEquivScopeMiddleCollapses`): from the left triangle `phi_f ~ id f`,
     the contract-order middle `(eps |> g) . (g <| eta) ~ id (g . u_A)` — the exact two-Godement-firing
     interchange bracketing the r2 recon named, compiled move-for-move once the unitor rows exist.
  2. **The idempotency** (`walkingEquivScopeIdempotencyFromLeftTriangle`): `psi_g . psi_g ~ psi_g` from the
     left triangle — the EXACT statement the original B3 wall guarded, now over the unitor scope.
  3. **The right triangle** (`walkingEquivScopeRightTriangleFromLeftTriangle`): `psi_g ~ id g` — the full
     promotion, via the shipped abstract invertible-idempotent engine + the shipped defect inverse
     (transported by the new relation-monotonicity fold `saturatedConvOverWithIdMono`).
  4. **Non-vacuously instantiated**: over `walkingEquivUnitorLeftTriangleRel` (unitor scope + the left
     triangle adjoined AS A ROW — the same test bench as the r3 refutation), the hypothesis is INHABITED
     (`walkingEquivLeftTriangle_derivableOverUnitorTriangleRel`) and both the idempotency AND the right
     triangle are DERIVED (`walkingEquiv*_derivableOverUnitorTriangleRel`).  Contrast r3: the SAME
     adjunction over the unitor-FREE relation is machine-refuted.  The wall is localized on both sides.
  5. **The scope does not collapse** (the guard): over the unitor scope WITHOUT the triangle row, the left
     triangle and the right triangle are still UNDERIVABLE (`walkingEquiv*_notDerivableOverUnitorScopeRel`)
     — by the FLAG-FREE eta-family parity (eta-occurrence count mod 2), which the unitor rows conserve (they
     only flip whisker-ancestry flags, and the flag-free table cannot see flags).  So the unitor rows supply
     exactly the classical bookkeeping, NOT a collapse: the triangle row stays load-bearing content.

## Why the classical argument compiles here (the r2 recon recipe, executed)

The Cat-proof of "one triangle + invertible unit/counit forces the other" uses naturality of `eta` / `eps`
only against WHISKERED `eta` / `eps` cells — and naturality against a whiskered cell IS the Godement
interchange row.  Concretely: interchange on the self-pairs gives the slide laws
`etaInv |> u_A ~ u_A <| etaInv` and `eps |> u_B ~ u_B <| eps` (after the unitor rows clean the
whisker-by-identity residues — this is where `whiskerUnitRel` is spent); the left triangle whiskered by `g`
gives `f <| (eps |> g) ~ etaInv |> u_A`; and ONE interchange firing on `(eps |> g, eta)` re-brackets the
middle `(eps |> g) . (g <| eta)` into whiskered factors that the slide laws convert into the adjacent pair
`((g . u_A) <| eta) . ((g . u_A) <| etaInv)`, which the E1a cancellation annihilates.  Every move is a
shipped row; the unitor rows are load-bearing in exactly two places (the interchange-residue cleanups).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` + independent
`#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The relation-monotonicity fold (generic infrastructure) -/

/-- The **monotonicity absorber**: `SaturatedConvOverWithId relWide` is itself a saturated-with-id
congruence over any subrelation `relNarrow` — each of the eleven fields is the namesake constructor, with
`ofRelation` routed through the row inclusion. -/
def saturatedConvOverWithIdMonoAbsorber (computad : OmegaComputad)
    (relNarrow relWide : CellRelOver computad)
    (hRowIncluded : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim},
      relNarrow cellAlpha cellBeta → relWide cellAlpha cellBeta) :
    IsSaturatedCongruenceWithId computad relNarrow
      (fun {_dim : Nat} cellAlpha cellBeta =>
        SaturatedConvOverWithId computad relWide cellAlpha cellBeta) where
  ofRelation := by
    intro _dim _cellAlpha _cellBeta row
    exact SaturatedConvOverWithId.ofRelation (hRowIncluded row)
  vcompCongrLeft := by
    intro _dim _cellAlpha _cellAlpha' cellBeta ihConv
    exact SaturatedConvOverWithId.vcompCongrLeft cellBeta ihConv
  vcompCongrRight := by
    intro _dim cellAlpha _cellBeta _cellBeta' ihConv
    exact SaturatedConvOverWithId.vcompCongrRight cellAlpha ihConv
  whiskerLeftCongr := by
    intro _dim whiskeringCell _cellBeta _cellBeta' ihConv
    exact SaturatedConvOverWithId.whiskerLeftCongr whiskeringCell ihConv
  whiskerRightCongr := by
    intro _dim _cellAlpha _cellAlpha' whiskeringCell ihConv
    exact SaturatedConvOverWithId.whiskerRightCongr whiskeringCell ihConv
  idCongr := by
    intro _dim _cellAlpha _cellBeta ihConv
    exact SaturatedConvOverWithId.idCongr ihConv
  whiskerLeftWhiskerCongr := by
    intro _dim _whiskerAlpha _whiskerAlpha' innerCell ihConv
    exact SaturatedConvOverWithId.whiskerLeftWhiskerCongr innerCell ihConv
  whiskerRightWhiskerCongr := by
    intro _dim innerCell _whiskerAlpha _whiskerAlpha' ihConv
    exact SaturatedConvOverWithId.whiskerRightWhiskerCongr innerCell ihConv
  refl := by
    intro _dim cell
    exact SaturatedConvOverWithId.refl cell
  symm := by
    intro _dim _cellAlpha _cellBeta ihConv
    exact SaturatedConvOverWithId.symm ihConv
  trans := by
    intro _dim _cellAlpha _cellBeta _cellGamma ihLeft ihRight
    exact SaturatedConvOverWithId.trans ihLeft ihRight

/-- ★ **Relation monotonicity for the sibling congruence** — every derivation over a subrelation transports
to any relation including its rows.  The missing generic fold the promotion transport needs (the shipped
defect-inverse chains live over `walkingEquivBaseRel`; the unitor scope includes it). -/
theorem saturatedConvOverWithIdMono {computad : OmegaComputad}
    {relNarrow relWide : CellRelOver computad}
    (hRowIncluded : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim},
      relNarrow cellAlpha cellBeta → relWide cellAlpha cellBeta)
    {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim}
    (conv : SaturatedConvOverWithId computad relNarrow cellAlpha cellBeta) :
    SaturatedConvOverWithId computad relWide cellAlpha cellBeta :=
  SaturatedConvOverWithId.recInto
    (saturatedConvOverWithIdMonoAbsorber computad relNarrow relWide hRowIncluded) conv

/-! ## The unitor-augmented scope (the r3-named successor relation) -/

/-- ★ The **unitor-augmented walking-equivalence relation** — the bare cancellation congruence
`walkingEquivBaseRel` (strict omega rows + the four iso-cancellations) united with the
whisker-by-identity-1-cell unit rows `whiskerUnitRel` (EckmannHiltonWithId's additive pattern).  This is
EXACTLY the relation the r3 successor node named. -/
def walkingEquivUnitorScopeRel : CellRelOver walkingEquivComputad :=
  unionCellRel walkingEquivComputad walkingEquivBaseRel (whiskerUnitRel walkingEquivComputad)

/-- The unitor scope with the left triangle ADJOINED AS A ROW — the non-vacuous test bench, mirroring the
r3 refutation bench `walkingEquivLeftTriangleAdjoinedRel` exactly (same single triangle row, unitor rows
added).  Over THIS relation the r3 refutation is answered by a derivation. -/
def walkingEquivUnitorLeftTriangleRel : CellRelOver walkingEquivComputad :=
  unionCellRel walkingEquivComputad walkingEquivUnitorScopeRel WalkingEquivLeftTriangleOnlyRow

/-! ## The scope-generic helpers

Every theorem below is generic in a relation `scopeRel` absorbing the bare rows (`hAbsorbBase`) and the
unitor rows (`hAbsorbUnitor`), so ONE proof serves both the conditional form (over
`walkingEquivUnitorScopeRel`) and the non-vacuous row-adjoined form (over
`walkingEquivUnitorLeftTriangleRel`). -/

/-- **Absorb a trailing identity across a boundary conversion**: `W . id U ~ W` once `U` converts to `W`'s
target boundary — the `idCongr` + right-unit composite the boundary bookkeeping repeatedly needs. -/
theorem walkingEquivScopeAbsorbTrailingId {scopeRel : CellRelOver walkingEquivComputad}
    (hAbsorbBase : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim},
      walkingEquivBaseRel cellAlpha cellBeta → scopeRel cellAlpha cellBeta)
    {dim : Nat} (cellW : CellExpr walkingEquivComputad (dim + 1))
    {unitCarrier : CellExpr walkingEquivComputad dim}
    (hCarrierToTarget : SaturatedConvOverWithId walkingEquivComputad scopeRel
      unitCarrier (boundaryTarget cellW)) :
    SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp cellW (CellExpr.id unitCarrier)) cellW :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrRight cellW
      (SaturatedConvOverWithId.idCongr hCarrierToTarget))
    (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl (StrictAxiomRel.vcompUnitRight cellW))))

/-- **Cancel a common invertible right factor**: from `X . Z ~ Y . Z` and the cancellation
`Z . ZInv ~ id U`, conclude `X ~ Y` (given the two trailing-identity absorptions).  The peeling engine for
the interchange-residue slide laws. -/
theorem walkingEquivScopeCancelRightFactor {scopeRel : CellRelOver walkingEquivComputad}
    (hAbsorbBase : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim},
      walkingEquivBaseRel cellAlpha cellBeta → scopeRel cellAlpha cellBeta)
    {dim : Nat} {cellX cellY cellZ cellZInv : CellExpr walkingEquivComputad (dim + 1)}
    {unitCarrier : CellExpr walkingEquivComputad dim}
    (hComposedEqual : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp cellX cellZ) (CellExpr.vcomp cellY cellZ))
    (hCancelPair : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp cellZ cellZInv) (CellExpr.id unitCarrier))
    (hAbsorbX : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp cellX (CellExpr.id unitCarrier)) cellX)
    (hAbsorbY : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp cellY (CellExpr.id unitCarrier)) cellY) :
    SaturatedConvOverWithId walkingEquivComputad scopeRel cellX cellY :=
  SaturatedConvOverWithId.trans (SaturatedConvOverWithId.symm hAbsorbX)
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.vcompCongrRight cellX (SaturatedConvOverWithId.symm hCancelPair))
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
          (hAbsorbBase (Or.inl (StrictAxiomRel.vcompAssoc cellX cellZ cellZInv)))))
        (SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.vcompCongrLeft cellZInv hComposedEqual)
          (SaturatedConvOverWithId.trans
            (SaturatedConvOverWithId.ofRelation
              (hAbsorbBase (Or.inl (StrictAxiomRel.vcompAssoc cellY cellZ cellZInv))))
            (SaturatedConvOverWithId.trans
              (SaturatedConvOverWithId.vcompCongrRight cellY hCancelPair)
              hAbsorbY)))))

/-! ## The two slide laws (interchange on the self-pairs + unitor cleanup + cancellation peel) -/

/-- ★ **The etaInv slide law** `etaInv |> u_A ~ u_A <| etaInv` — Godement interchange on the self-pair
`(etaInv, etaInv)`, the two whisker-by-identity residues cleaned by the UNITOR rows, then the common right
factor `etaInv` peeled via the E1b cancellation.  (In Cat terms: naturality of `eta^{-1}` at its own
component.) -/
theorem walkingEquivScopeEtaInvSlidesAcrossUnitA {scopeRel : CellRelOver walkingEquivComputad}
    (hAbsorbBase : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim},
      walkingEquivBaseRel cellAlpha cellBeta → scopeRel cellAlpha cellBeta)
    (hAbsorbUnitor : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim},
      whiskerUnitRel walkingEquivComputad cellAlpha cellBeta → scopeRel cellAlpha cellBeta) :
    SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA)
      (CellExpr.whiskerLeft walkingEquivUnitA walkingEquivEtaInvGen) := by
  have fireInterchange : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA)
        (CellExpr.whiskerLeft walkingEquivIdA walkingEquivEtaInvGen))
      (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivUnitA walkingEquivEtaInvGen)
        (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivIdA)) :=
    SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
      (StrictAxiomRel.interchange walkingEquivEtaInvGen walkingEquivEtaInvGen)))
  have leftResidueClean : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA)
        (CellExpr.whiskerLeft walkingEquivIdA walkingEquivEtaInvGen))
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA)
        walkingEquivEtaInvGen) :=
    SaturatedConvOverWithId.vcompCongrRight
      (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA)
      (SaturatedConvOverWithId.ofRelation (hAbsorbUnitor
        (whiskerUnitRel.whiskerLeftIdCellUnit walkingEquivObjectA walkingEquivEtaInvGen)))
  have rightResidueClean : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivUnitA walkingEquivEtaInvGen)
        (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivIdA))
      (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivUnitA walkingEquivEtaInvGen)
        walkingEquivEtaInvGen) :=
    SaturatedConvOverWithId.vcompCongrRight
      (CellExpr.whiskerLeft walkingEquivUnitA walkingEquivEtaInvGen)
      (SaturatedConvOverWithId.ofRelation (hAbsorbUnitor
        (whiskerUnitRel.whiskerRightIdCellUnit walkingEquivEtaInvGen walkingEquivObjectA)))
  have composedEqual : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA)
        walkingEquivEtaInvGen)
      (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivUnitA walkingEquivEtaInvGen)
        walkingEquivEtaInvGen) :=
    SaturatedConvOverWithId.trans (SaturatedConvOverWithId.symm leftResidueClean)
      (SaturatedConvOverWithId.trans fireInterchange rightResidueClean)
  exact walkingEquivScopeCancelRightFactor hAbsorbBase composedEqual
    (SaturatedConvOverWithId.ofRelation
      (hAbsorbBase (Or.inr WalkingEquivCancellationRow.unitCancelBackward)))
    (walkingEquivScopeAbsorbTrailingId hAbsorbBase
      (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA)
      (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
        (hAbsorbBase (Or.inl (StrictAxiomRel.vcompUnitLeft walkingEquivUnitA))))))
    (walkingEquivScopeAbsorbTrailingId hAbsorbBase
      (CellExpr.whiskerLeft walkingEquivUnitA walkingEquivEtaInvGen)
      (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
        (hAbsorbBase (Or.inl (StrictAxiomRel.vcompUnitRight walkingEquivUnitA))))))

/-- ★ **The eps slide law** `eps |> u_B ~ u_B <| eps` — the mirror: interchange on `(eps, eps)`, unitor
cleanup at `B`, and the E2a cancellation peel. -/
theorem walkingEquivScopeEpsSlidesAcrossUnitB {scopeRel : CellRelOver walkingEquivComputad}
    (hAbsorbBase : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim},
      walkingEquivBaseRel cellAlpha cellBeta → scopeRel cellAlpha cellBeta)
    (hAbsorbUnitor : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim},
      whiskerUnitRel walkingEquivComputad cellAlpha cellBeta → scopeRel cellAlpha cellBeta) :
    SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivUnitB)
      (CellExpr.whiskerLeft walkingEquivUnitB walkingEquivEpsGen) := by
  have fireInterchange : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivUnitB)
        (CellExpr.whiskerLeft walkingEquivIdB walkingEquivEpsGen))
      (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivUnitB walkingEquivEpsGen)
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivIdB)) :=
    SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
      (StrictAxiomRel.interchange walkingEquivEpsGen walkingEquivEpsGen)))
  have leftResidueClean : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivUnitB)
        (CellExpr.whiskerLeft walkingEquivIdB walkingEquivEpsGen))
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivUnitB)
        walkingEquivEpsGen) :=
    SaturatedConvOverWithId.vcompCongrRight
      (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivUnitB)
      (SaturatedConvOverWithId.ofRelation (hAbsorbUnitor
        (whiskerUnitRel.whiskerLeftIdCellUnit walkingEquivObjectB walkingEquivEpsGen)))
  have rightResidueClean : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivUnitB walkingEquivEpsGen)
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivIdB))
      (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivUnitB walkingEquivEpsGen)
        walkingEquivEpsGen) :=
    SaturatedConvOverWithId.vcompCongrRight
      (CellExpr.whiskerLeft walkingEquivUnitB walkingEquivEpsGen)
      (SaturatedConvOverWithId.ofRelation (hAbsorbUnitor
        (whiskerUnitRel.whiskerRightIdCellUnit walkingEquivEpsGen walkingEquivObjectB)))
  have composedEqual : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivUnitB)
        walkingEquivEpsGen)
      (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivUnitB walkingEquivEpsGen)
        walkingEquivEpsGen) :=
    SaturatedConvOverWithId.trans (SaturatedConvOverWithId.symm leftResidueClean)
      (SaturatedConvOverWithId.trans fireInterchange rightResidueClean)
  exact walkingEquivScopeCancelRightFactor hAbsorbBase composedEqual
    (SaturatedConvOverWithId.ofRelation
      (hAbsorbBase (Or.inr WalkingEquivCancellationRow.counitCancelForward)))
    (walkingEquivScopeAbsorbTrailingId hAbsorbBase
      (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivUnitB)
      (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
        (hAbsorbBase (Or.inl (StrictAxiomRel.vcompUnitLeft walkingEquivUnitB))))))
    (walkingEquivScopeAbsorbTrailingId hAbsorbBase
      (CellExpr.whiskerLeft walkingEquivUnitB walkingEquivEpsGen)
      (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
        (hAbsorbBase (Or.inl (StrictAxiomRel.vcompUnitRight walkingEquivUnitB))))))

/-! ## The left triangle spent: the whiskered-triangle normal form and its two consequences -/

/-- ★ **The right-whiskered left triangle, normalized**: from `phi_f ~ id f`,
`(eta |> u_A) . (f <| (eps |> g)) ~ id u_A` — whisker the hypothesis by `g`, split by functoriality, and
re-bracket by the sesqui rows.  (The Cat-proof's "apply `G` to the triangle".) -/
theorem walkingEquivScopeTriangleWhiskeredNormalized {scopeRel : CellRelOver walkingEquivComputad}
    (hAbsorbBase : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim},
      walkingEquivBaseRel cellAlpha cellBeta → scopeRel cellAlpha cellBeta)
    (hLeftTriangle : SaturatedConvOverWithId walkingEquivComputad scopeRel
      walkingEquivLeftTriangleLeg walkingEquivIdF) :
    SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEtaGen walkingEquivUnitA)
        (CellExpr.whiskerLeft walkingEquivFGen
          (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)))
      (CellExpr.id walkingEquivUnitA) := by
  have whiskeredTriangle : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.whiskerRight walkingEquivLeftTriangleLeg walkingEquivGGen)
      (CellExpr.whiskerRight walkingEquivIdF walkingEquivGGen) :=
    SaturatedConvOverWithId.whiskerRightCongr walkingEquivGGen hLeftTriangle
  have rhsCollapse : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.whiskerRight walkingEquivIdF walkingEquivGGen)
      (CellExpr.id walkingEquivUnitA) :=
    SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
      (StrictAxiomRel.whiskerRightUnit walkingEquivFGen walkingEquivGGen)))
  have lhsSplit : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.whiskerRight walkingEquivLeftTriangleLeg walkingEquivGGen)
      (CellExpr.vcomp
        (CellExpr.whiskerRight (CellExpr.whiskerRight walkingEquivEtaGen walkingEquivFGen)
          walkingEquivGGen)
        (CellExpr.whiskerRight (CellExpr.whiskerLeft walkingEquivFGen walkingEquivEpsGen)
          walkingEquivGGen)) :=
    SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
      (StrictAxiomRel.whiskerRightFunctorial
        (CellExpr.whiskerRight walkingEquivEtaGen walkingEquivFGen)
        (CellExpr.whiskerLeft walkingEquivFGen walkingEquivEpsGen) walkingEquivGGen)))
  have firstFactorFused : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.whiskerRight walkingEquivEtaGen walkingEquivUnitA)
      (CellExpr.whiskerRight (CellExpr.whiskerRight walkingEquivEtaGen walkingEquivFGen)
        walkingEquivGGen) :=
    SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
      (StrictAxiomRel.whiskerAssocRight walkingEquivEtaGen walkingEquivFGen walkingEquivGGen)))
  have secondFactorCommuted : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.whiskerRight (CellExpr.whiskerLeft walkingEquivFGen walkingEquivEpsGen)
        walkingEquivGGen)
      (CellExpr.whiskerLeft walkingEquivFGen
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)) :=
    SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
      (StrictAxiomRel.whiskerLeftRightCommute walkingEquivFGen walkingEquivEpsGen
        walkingEquivGGen)))
  exact SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrLeft
      (CellExpr.whiskerLeft walkingEquivFGen
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen))
      firstFactorFused)
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.vcompCongrRight
        (CellExpr.whiskerRight (CellExpr.whiskerRight walkingEquivEtaGen walkingEquivFGen)
          walkingEquivGGen)
        (SaturatedConvOverWithId.symm secondFactorCommuted))
      (SaturatedConvOverWithId.trans (SaturatedConvOverWithId.symm lhsSplit)
        (SaturatedConvOverWithId.trans whiskeredTriangle rhsCollapse)))

/-- ★ **The slid counit IS the slid inverse unit**: from the left triangle,
`f <| (eps |> g) ~ etaInv |> u_A` — peel the invertible `eta |> u_A` off the normalized whiskered
triangle.  (The Cat-proof's `GF(eta_{Gx})^{-1} = G(eps_{FGx})` step.) -/
theorem walkingEquivScopeSlidEpsIsSlidEtaInv {scopeRel : CellRelOver walkingEquivComputad}
    (hAbsorbBase : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim},
      walkingEquivBaseRel cellAlpha cellBeta → scopeRel cellAlpha cellBeta)
    (hLeftTriangle : SaturatedConvOverWithId walkingEquivComputad scopeRel
      walkingEquivLeftTriangleLeg walkingEquivIdF) :
    SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.whiskerLeft walkingEquivFGen
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen))
      (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA) := by
  have inversePairCollapse : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA)
        (CellExpr.whiskerRight walkingEquivEtaGen walkingEquivUnitA))
      (CellExpr.id (CellExpr.vcomp walkingEquivUnitA walkingEquivUnitA)) :=
    SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
        (StrictAxiomRel.whiskerRightFunctorial walkingEquivEtaInvGen walkingEquivEtaGen
          walkingEquivUnitA)))))
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.whiskerRightCongr walkingEquivUnitA
          (SaturatedConvOverWithId.ofRelation
            (hAbsorbBase (Or.inr WalkingEquivCancellationRow.unitCancelBackward))))
        (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
          (StrictAxiomRel.whiskerRightUnit walkingEquivUnitA walkingEquivUnitA)))))
  have sourceWordConv : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp walkingEquivFGen (CellExpr.vcomp walkingEquivUnitB walkingEquivGGen))
      (CellExpr.vcomp walkingEquivUnitA walkingEquivUnitA) :=
    SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.vcompCongrRight walkingEquivFGen
        (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
          (StrictAxiomRel.vcompAssoc walkingEquivGGen walkingEquivFGen walkingEquivGGen)))))
      (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
        (StrictAxiomRel.vcompAssoc walkingEquivFGen walkingEquivGGen walkingEquivUnitA)))))
  have insertUnit : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.whiskerLeft walkingEquivFGen
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen))
      (CellExpr.vcomp
        (CellExpr.id (CellExpr.vcomp walkingEquivFGen
          (CellExpr.vcomp walkingEquivUnitB walkingEquivGGen)))
        (CellExpr.whiskerLeft walkingEquivFGen
          (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen))) :=
    SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
      (StrictAxiomRel.vcompUnitLeft (CellExpr.whiskerLeft walkingEquivFGen
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen))))))
  have unitToInversePair : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp
        (CellExpr.id (CellExpr.vcomp walkingEquivFGen
          (CellExpr.vcomp walkingEquivUnitB walkingEquivGGen)))
        (CellExpr.whiskerLeft walkingEquivFGen
          (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)))
      (CellExpr.vcomp
        (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA)
          (CellExpr.whiskerRight walkingEquivEtaGen walkingEquivUnitA))
        (CellExpr.whiskerLeft walkingEquivFGen
          (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen))) :=
    SaturatedConvOverWithId.vcompCongrLeft
      (CellExpr.whiskerLeft walkingEquivFGen
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen))
      (SaturatedConvOverWithId.trans (SaturatedConvOverWithId.idCongr sourceWordConv)
        (SaturatedConvOverWithId.symm inversePairCollapse))
  have reassoc : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp
        (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA)
          (CellExpr.whiskerRight walkingEquivEtaGen walkingEquivUnitA))
        (CellExpr.whiskerLeft walkingEquivFGen
          (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)))
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA)
        (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEtaGen walkingEquivUnitA)
          (CellExpr.whiskerLeft walkingEquivFGen
            (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)))) :=
    SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
      (StrictAxiomRel.vcompAssoc (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA)
        (CellExpr.whiskerRight walkingEquivEtaGen walkingEquivUnitA)
        (CellExpr.whiskerLeft walkingEquivFGen
          (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)))))
  have applyTriangle : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA)
        (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEtaGen walkingEquivUnitA)
          (CellExpr.whiskerLeft walkingEquivFGen
            (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen))))
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA)
        (CellExpr.id walkingEquivUnitA)) :=
    SaturatedConvOverWithId.vcompCongrRight
      (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA)
      (walkingEquivScopeTriangleWhiskeredNormalized hAbsorbBase hLeftTriangle)
  have dropUnit : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA)
        (CellExpr.id walkingEquivUnitA))
      (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA) :=
    walkingEquivScopeAbsorbTrailingId hAbsorbBase
      (CellExpr.whiskerRight walkingEquivEtaInvGen walkingEquivUnitA)
      (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
        (hAbsorbBase (Or.inl (StrictAxiomRel.vcompUnitLeft walkingEquivUnitA)))))
  exact SaturatedConvOverWithId.trans insertUnit
    (SaturatedConvOverWithId.trans unitToInversePair
      (SaturatedConvOverWithId.trans reassoc
        (SaturatedConvOverWithId.trans applyTriangle dropUnit)))

/-- ★ **The `u_B`-slid counit**: from the left triangle,
`u_B <| (eps |> g) ~ (g <| etaInv) |> u_A` — whisker the previous consequence by `g` on the left and
re-bracket. -/
theorem walkingEquivScopeUnitBSlidEps {scopeRel : CellRelOver walkingEquivComputad}
    (hAbsorbBase : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim},
      walkingEquivBaseRel cellAlpha cellBeta → scopeRel cellAlpha cellBeta)
    (hLeftTriangle : SaturatedConvOverWithId walkingEquivComputad scopeRel
      walkingEquivLeftTriangleLeg walkingEquivIdF) :
    SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.whiskerLeft walkingEquivUnitB
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen))
      (CellExpr.whiskerRight (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen)
        walkingEquivUnitA) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
      (StrictAxiomRel.whiskerAssocLeft walkingEquivGGen walkingEquivFGen
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)))))
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.whiskerLeftCongr walkingEquivGGen
        (walkingEquivScopeSlidEpsIsSlidEtaInv hAbsorbBase hLeftTriangle))
      (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
        (StrictAxiomRel.whiskerLeftRightCommute walkingEquivGGen walkingEquivEtaInvGen
          walkingEquivUnitA))))))

/-! ## The middle collapse — the interchange bracketing, executed -/

/-- ★★ **THE MIDDLE COLLAPSES** — from the left triangle, the contract-order middle of `psi_g . psi_g`
straightens: `(eps |> g) . (g <| eta) ~ id (g . u_A)`.  ONE Godement interchange firing on
`(eps |> g, eta)` re-brackets the middle into whiskered factors; the unitor rows clean the two
whisker-by-identity residues; the slide laws + the `g`-whiskered triangle convert the second factor into
`(g . u_A) <| etaInv` adjacent to `(g . u_A) <| eta`; functoriality fuses the pair and the E1a
cancellation annihilates it.  This is EXACTLY the interchange bracketing the r2 wall named — executable
once (and only once) the whisker-unitor rows exist. -/
theorem walkingEquivScopeMiddleCollapses {scopeRel : CellRelOver walkingEquivComputad}
    (hAbsorbBase : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim},
      walkingEquivBaseRel cellAlpha cellBeta → scopeRel cellAlpha cellBeta)
    (hAbsorbUnitor : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim},
      whiskerUnitRel walkingEquivComputad cellAlpha cellBeta → scopeRel cellAlpha cellBeta)
    (hLeftTriangle : SaturatedConvOverWithId walkingEquivComputad scopeRel
      walkingEquivLeftTriangleLeg walkingEquivIdF) :
    SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
        (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen))
      (CellExpr.id (CellExpr.vcomp walkingEquivGGen walkingEquivUnitA)) := by
  have fireInterchange : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp
        (CellExpr.whiskerRight (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
          walkingEquivIdA)
        (CellExpr.whiskerLeft (CellExpr.vcomp walkingEquivIdB walkingEquivGGen)
          walkingEquivEtaGen))
      (CellExpr.vcomp
        (CellExpr.whiskerLeft (CellExpr.vcomp walkingEquivUnitB walkingEquivGGen)
          walkingEquivEtaGen)
        (CellExpr.whiskerRight (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
          walkingEquivUnitA)) :=
    SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
      (StrictAxiomRel.interchange
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen) walkingEquivEtaGen)))
  have leftSideClean : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp
        (CellExpr.whiskerRight (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
          walkingEquivIdA)
        (CellExpr.whiskerLeft (CellExpr.vcomp walkingEquivIdB walkingEquivGGen)
          walkingEquivEtaGen))
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
        (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen)) :=
    SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.vcompCongrLeft
        (CellExpr.whiskerLeft (CellExpr.vcomp walkingEquivIdB walkingEquivGGen)
          walkingEquivEtaGen)
        (SaturatedConvOverWithId.ofRelation (hAbsorbUnitor
          (whiskerUnitRel.whiskerRightIdCellUnit
            (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
            walkingEquivObjectA))))
      (SaturatedConvOverWithId.vcompCongrRight
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
        (SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
            (StrictAxiomRel.whiskerAssocLeft walkingEquivIdB walkingEquivGGen
              walkingEquivEtaGen))))
          (SaturatedConvOverWithId.ofRelation (hAbsorbUnitor
            (whiskerUnitRel.whiskerLeftIdCellUnit walkingEquivObjectB
              (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen))))))
  have middleViaInterchange : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
        (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen))
      (CellExpr.vcomp
        (CellExpr.whiskerLeft (CellExpr.vcomp walkingEquivUnitB walkingEquivGGen)
          walkingEquivEtaGen)
        (CellExpr.whiskerRight (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
          walkingEquivUnitA)) :=
    SaturatedConvOverWithId.trans (SaturatedConvOverWithId.symm leftSideClean) fireInterchange
  have oneCellAssocConv : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp walkingEquivUnitB walkingEquivGGen)
      (CellExpr.vcomp walkingEquivGGen walkingEquivUnitA) :=
    SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
      (StrictAxiomRel.vcompAssoc walkingEquivGGen walkingEquivFGen walkingEquivGGen)))
  have firstFactorReassoc : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.whiskerLeft (CellExpr.vcomp walkingEquivUnitB walkingEquivGGen)
        walkingEquivEtaGen)
      (CellExpr.whiskerLeft (CellExpr.vcomp walkingEquivGGen walkingEquivUnitA)
        walkingEquivEtaGen) :=
    SaturatedConvOverWithId.whiskerLeftWhiskerCongr walkingEquivEtaGen oneCellAssocConv
  have secondFactorChain : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.whiskerRight (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
        walkingEquivUnitA)
      (CellExpr.whiskerLeft (CellExpr.vcomp walkingEquivGGen walkingEquivUnitA)
        walkingEquivEtaInvGen) :=
    SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
        (StrictAxiomRel.whiskerAssocRight walkingEquivEpsGen walkingEquivGGen
          walkingEquivUnitA)))))
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.whiskerRightWhiskerCongr walkingEquivEpsGen
          (SaturatedConvOverWithId.symm oneCellAssocConv))
        (SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
            (StrictAxiomRel.whiskerAssocRight walkingEquivEpsGen walkingEquivUnitB
              walkingEquivGGen))))
          (SaturatedConvOverWithId.trans
            (SaturatedConvOverWithId.whiskerRightCongr walkingEquivGGen
              (walkingEquivScopeEpsSlidesAcrossUnitB hAbsorbBase hAbsorbUnitor))
            (SaturatedConvOverWithId.trans
              (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
                (StrictAxiomRel.whiskerLeftRightCommute walkingEquivUnitB walkingEquivEpsGen
                  walkingEquivGGen))))
              (SaturatedConvOverWithId.trans
                (walkingEquivScopeUnitBSlidEps hAbsorbBase hLeftTriangle)
                (SaturatedConvOverWithId.trans
                  (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
                    (StrictAxiomRel.whiskerLeftRightCommute walkingEquivGGen
                      walkingEquivEtaInvGen walkingEquivUnitA))))
                  (SaturatedConvOverWithId.trans
                    (SaturatedConvOverWithId.whiskerLeftCongr walkingEquivGGen
                      (walkingEquivScopeEtaInvSlidesAcrossUnitA hAbsorbBase hAbsorbUnitor))
                    (SaturatedConvOverWithId.symm
                      (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
                        (StrictAxiomRel.whiskerAssocLeft walkingEquivGGen walkingEquivUnitA
                          walkingEquivEtaInvGen))))))))))))
  have etaPairCollapse : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp
        (CellExpr.whiskerLeft (CellExpr.vcomp walkingEquivGGen walkingEquivUnitA)
          walkingEquivEtaGen)
        (CellExpr.whiskerLeft (CellExpr.vcomp walkingEquivGGen walkingEquivUnitA)
          walkingEquivEtaInvGen))
      (CellExpr.id (CellExpr.vcomp walkingEquivGGen walkingEquivUnitA)) :=
    SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
        (StrictAxiomRel.whiskerLeftFunctorial
          (CellExpr.vcomp walkingEquivGGen walkingEquivUnitA)
          walkingEquivEtaGen walkingEquivEtaInvGen)))))
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.whiskerLeftCongr
          (CellExpr.vcomp walkingEquivGGen walkingEquivUnitA)
          (SaturatedConvOverWithId.ofRelation
            (hAbsorbBase (Or.inr WalkingEquivCancellationRow.unitCancelForward))))
        (SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
            (StrictAxiomRel.whiskerLeftUnit
              (CellExpr.vcomp walkingEquivGGen walkingEquivUnitA) walkingEquivIdA))))
          (SaturatedConvOverWithId.idCongr
            (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
              (StrictAxiomRel.vcompUnitRight
                (CellExpr.vcomp walkingEquivGGen walkingEquivUnitA))))))))
  exact SaturatedConvOverWithId.trans middleViaInterchange
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.vcompCongrLeft
        (CellExpr.whiskerRight (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
          walkingEquivUnitA)
        firstFactorReassoc)
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrRight
          (CellExpr.whiskerLeft (CellExpr.vcomp walkingEquivGGen walkingEquivUnitA)
            walkingEquivEtaGen)
          secondFactorChain)
        etaPairCollapse))

/-! ## The idempotency and the right triangle — the promotion, delivered -/

/-- ★★★ **THE IDEMPOTENCY FROM THE LEFT TRIANGLE — the exact walled statement, DERIVED over the unitor
scope.**  `psi_g . psi_g ~ psi_g` from `phi_f ~ id f`: re-bracket the doubled leg around the contract-order
middle, collapse the middle (`walkingEquivScopeMiddleCollapses`), and absorb the identity across the
associator.  The statement the r2 wall `fxEquiv_promotionIdempotencyFromLeftTriangleWalled` guarded and the
r3 parity invariant refuted over the unitor-free rows — now a theorem over the r3-named successor scope. -/
theorem walkingEquivScopeIdempotencyFromLeftTriangle {scopeRel : CellRelOver walkingEquivComputad}
    (hAbsorbBase : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim},
      walkingEquivBaseRel cellAlpha cellBeta → scopeRel cellAlpha cellBeta)
    (hAbsorbUnitor : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim},
      whiskerUnitRel walkingEquivComputad cellAlpha cellBeta → scopeRel cellAlpha cellBeta)
    (hLeftTriangle : SaturatedConvOverWithId walkingEquivComputad scopeRel
      walkingEquivLeftTriangleLeg walkingEquivIdF) :
    SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp walkingEquivRightTriangleLeg walkingEquivRightTriangleLeg)
      walkingEquivRightTriangleLeg := by
  have expand : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp walkingEquivRightTriangleLeg walkingEquivRightTriangleLeg)
      (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen)
        (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
          walkingEquivRightTriangleLeg)) :=
    SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
      (StrictAxiomRel.vcompAssoc (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen)
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
        walkingEquivRightTriangleLeg)))
  have innerReassoc : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
        walkingEquivRightTriangleLeg)
      (CellExpr.vcomp
        (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
          (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen))
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)) :=
    SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
      (StrictAxiomRel.vcompAssoc (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
        (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen)
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)))))
  have innerCollapse : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp
        (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
          (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen))
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen))
      (CellExpr.vcomp (CellExpr.id (CellExpr.vcomp walkingEquivGGen walkingEquivUnitA))
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)) :=
    SaturatedConvOverWithId.vcompCongrLeft
      (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
      (walkingEquivScopeMiddleCollapses hAbsorbBase hAbsorbUnitor hLeftTriangle)
  have idShift : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp (CellExpr.id (CellExpr.vcomp walkingEquivGGen walkingEquivUnitA))
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen))
      (CellExpr.vcomp (CellExpr.id (CellExpr.vcomp walkingEquivUnitB walkingEquivGGen))
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)) :=
    SaturatedConvOverWithId.vcompCongrLeft
      (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
      (SaturatedConvOverWithId.idCongr (SaturatedConvOverWithId.symm
        (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
          (StrictAxiomRel.vcompAssoc walkingEquivGGen walkingEquivFGen walkingEquivGGen))))))
  have unitDrop : SaturatedConvOverWithId walkingEquivComputad scopeRel
      (CellExpr.vcomp (CellExpr.id (CellExpr.vcomp walkingEquivUnitB walkingEquivGGen))
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen))
      (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen) :=
    SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
      (StrictAxiomRel.vcompUnitLeft
        (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen))))
  exact SaturatedConvOverWithId.trans expand
    (SaturatedConvOverWithId.vcompCongrRight
      (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen)
      (SaturatedConvOverWithId.trans innerReassoc
        (SaturatedConvOverWithId.trans innerCollapse
          (SaturatedConvOverWithId.trans idShift unitDrop))))

/-- ★★★ **THE RIGHT TRIANGLE FROM THE LEFT TRIANGLE — the full promotion, DERIVED over the unitor
scope.**  `psi_g ~ id g` from `phi_f ~ id f`: the derived idempotency feeds the shipped abstract
invertible-idempotent engine, with the shipped defect left inverse transported into the scope by
relation-monotonicity.  The classical "an equivalence with one triangle identity is an adjoint
equivalence", machine-checked. -/
theorem walkingEquivScopeRightTriangleFromLeftTriangle {scopeRel : CellRelOver walkingEquivComputad}
    (hAbsorbBase : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim},
      walkingEquivBaseRel cellAlpha cellBeta → scopeRel cellAlpha cellBeta)
    (hAbsorbUnitor : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim},
      whiskerUnitRel walkingEquivComputad cellAlpha cellBeta → scopeRel cellAlpha cellBeta)
    (hLeftTriangle : SaturatedConvOverWithId walkingEquivComputad scopeRel
      walkingEquivLeftTriangleLeg walkingEquivIdF) :
    SaturatedConvOverWithId walkingEquivComputad scopeRel
      walkingEquivRightTriangleLeg walkingEquivIdG :=
  SaturatedConvOverWithId.trans
    (convEndoInvertibleIdempotent_isIdentity
      (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
        (StrictAxiomRel.vcompUnitLeft walkingEquivRightTriangleLeg))))
      (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
        (StrictAxiomRel.vcompAssoc walkingEquivRightDefectInverse
          walkingEquivRightTriangleLeg walkingEquivRightTriangleLeg))))
      (saturatedConvOverWithIdMono hAbsorbBase walkingEquivRightDefect_leftInverse)
      (walkingEquivScopeIdempotencyFromLeftTriangle hAbsorbBase hAbsorbUnitor hLeftTriangle))
    (SaturatedConvOverWithId.idCongr
      (SaturatedConvOverWithId.ofRelation (hAbsorbBase (Or.inl
        (StrictAxiomRel.vcompUnitRight walkingEquivGGen)))))

/-! ## The concrete instantiations — conditional over the unitor scope, non-vacuous over the adjoined bench -/

/-- ★ **The conditional promotion over the unitor scope** — the r2 walled statement verbatim, with
`walkingEquivBaseRel` upgraded to `walkingEquivUnitorScopeRel`: from the left triangle, the idempotency. -/
theorem walkingEquivIdempotencyFromLeftTriangleOverUnitorScope
    (hLeftTriangle : SaturatedConvOverWithId walkingEquivComputad walkingEquivUnitorScopeRel
      walkingEquivLeftTriangleLeg walkingEquivIdF) :
    SaturatedConvOverWithId walkingEquivComputad walkingEquivUnitorScopeRel
      (CellExpr.vcomp walkingEquivRightTriangleLeg walkingEquivRightTriangleLeg)
      walkingEquivRightTriangleLeg :=
  walkingEquivScopeIdempotencyFromLeftTriangle
    (fun row => Or.inl row) (fun row => Or.inr row) hLeftTriangle

/-- ★ **The conditional right triangle over the unitor scope** — the full conditional promotion. -/
theorem walkingEquivRightTriangleFromLeftTriangleOverUnitorScope
    (hLeftTriangle : SaturatedConvOverWithId walkingEquivComputad walkingEquivUnitorScopeRel
      walkingEquivLeftTriangleLeg walkingEquivIdF) :
    SaturatedConvOverWithId walkingEquivComputad walkingEquivUnitorScopeRel
      walkingEquivRightTriangleLeg walkingEquivIdG :=
  walkingEquivScopeRightTriangleFromLeftTriangle
    (fun row => Or.inl row) (fun row => Or.inr row) hLeftTriangle

/-- **Positive control**: over the triangle-adjoined unitor bench the left triangle IS derivable (fire the
row) — so the two derivations below are NOT vacuous. -/
theorem walkingEquivLeftTriangle_derivableOverUnitorTriangleRel :
    SaturatedConvOverWithId walkingEquivComputad walkingEquivUnitorLeftTriangleRel
      walkingEquivLeftTriangleLeg walkingEquivIdF :=
  SaturatedConvOverWithId.ofRelation (Or.inr WalkingEquivLeftTriangleOnlyRow.leftTriangle)

/-- ★★ **THE r3 REFUTATION, ANSWERED**: over the unitor-augmented bench with the left triangle adjoined —
the hypothesis genuinely inhabited — the idempotency `psi_g . psi_g ~ psi_g` IS derivable.  Contrast
`walkingEquivIdempotency_notDerivableEvenWithLeftTriangleRow` (r3): the SAME adjunction over the
unitor-FREE rows is machine-refuted.  The unitor rows are exactly the load-bearing gap. -/
theorem walkingEquivIdempotency_derivableOverUnitorTriangleRel :
    SaturatedConvOverWithId walkingEquivComputad walkingEquivUnitorLeftTriangleRel
      (CellExpr.vcomp walkingEquivRightTriangleLeg walkingEquivRightTriangleLeg)
      walkingEquivRightTriangleLeg :=
  walkingEquivScopeIdempotencyFromLeftTriangle
    (fun row => Or.inl (Or.inl row)) (fun row => Or.inl (Or.inr row))
    walkingEquivLeftTriangle_derivableOverUnitorTriangleRel

/-- ★★★ **THE PROMOTION HEADLINE — the right triangle derives on the inhabited bench.**  Over
`walkingEquivUnitorLeftTriangleRel` (strict rows + four iso-cancellations + whisker-unitors + the LEFT
triangle row), the RIGHT triangle `psi_g ~ id g` is DERIVED — the walking equivalence with one triangle
identity promotes to the walking adjoint equivalence, machine-checked, zero-axiom.  (r3's
`walkingEquivRightTriangle_notDerivableEvenWithLeftTriangleRow` refutes the same statement without the
unitor rows.) -/
theorem walkingEquivRightTriangle_derivableOverUnitorTriangleRel :
    SaturatedConvOverWithId walkingEquivComputad walkingEquivUnitorLeftTriangleRel
      walkingEquivRightTriangleLeg walkingEquivIdG :=
  walkingEquivScopeRightTriangleFromLeftTriangle
    (fun row => Or.inl (Or.inl row)) (fun row => Or.inl (Or.inr row))
    walkingEquivLeftTriangle_derivableOverUnitorTriangleRel

/-! ## The guard — the unitor scope does NOT collapse the triangle content

The flag-free eta-family parity (the number of `eta`/`etaInv` occurrences mod 2, IGNORING whisker-ancestry
flags) is conserved by every row of the unitor scope: the strict rows and cancellations by the r3 generic
dischargers, the unitor rows because they only flip flags the table cannot see.  It separates `phi_f` from
`id f` and `psi_g` from `id g` — so WITHOUT the triangle row, neither triangle is derivable over the unitor
scope.  The unitor rows are bookkeeping, not content; the triangle row stays load-bearing. -/

/-- The **flag-free eta-family contribution table** — counts `eta` / `etaInv` occurrences regardless of
whisker-ancestry flags (the flags the unitor rows flip are invisible to it). -/
def walkingEquivEtaFamilyFlagFreeContribution
    (_hasLeftAncestor _hasRightAncestor : Bool) (label : WalkingEquivGenLabel) : Bool :=
  walkingEquivIsEtaFamilyLabel label

/-- The flag-free table pairs the unit with its inverse (both eta-family). -/
theorem walkingEquivEtaFamilyFlagFree_pairsEta :
    ∀ (hasLeft hasRight : Bool),
      walkingEquivEtaFamilyFlagFreeContribution hasLeft hasRight WalkingEquivGenLabel.etaUnit
        = walkingEquivEtaFamilyFlagFreeContribution hasLeft hasRight WalkingEquivGenLabel.etaInv :=
  fun _ _ => rfl

/-- The flag-free table pairs the counit with its inverse (both outside the eta family). -/
theorem walkingEquivEtaFamilyFlagFree_pairsEps :
    ∀ (hasLeft hasRight : Bool),
      walkingEquivEtaFamilyFlagFreeContribution hasLeft hasRight WalkingEquivGenLabel.epsCounit
        = walkingEquivEtaFamilyFlagFreeContribution hasLeft hasRight WalkingEquivGenLabel.epsInv :=
  fun _ _ => rfl

/-- ★ **The flag-free fold is flag-independent** — the parity of a flag-free table does not depend on the
ancestry flags (structural induction; the whisker arms shift flags, which the table ignores).  This is
exactly why the unitor rows conserve it. -/
theorem walkingEquivEtaFamilyParity_flagIndependent :
    {dim : Nat} → (cell : CellExpr walkingEquivComputad dim) →
    (hasLeftFirst hasRightFirst hasLeftSecond hasRightSecond : Bool) →
    walkingEquivFlaggedGenParity walkingEquivEtaFamilyFlagFreeContribution
        hasLeftFirst hasRightFirst cell
      = walkingEquivFlaggedGenParity walkingEquivEtaFamilyFlagFreeContribution
        hasLeftSecond hasRightSecond cell
  | _, .ofMode _, _, _, _, _ => rfl
  | _, .gen _ _ _, _, _, _, _ => rfl
  | _, .id _, _, _, _, _ => rfl
  | _, .vcomp leftCell rightCell, hasLeftFirst, hasRightFirst, hasLeftSecond, hasRightSecond =>
      show walkingEquivParityAdd
          (walkingEquivFlaggedGenParity walkingEquivEtaFamilyFlagFreeContribution
            hasLeftFirst hasRightFirst leftCell)
          (walkingEquivFlaggedGenParity walkingEquivEtaFamilyFlagFreeContribution
            hasLeftFirst hasRightFirst rightCell)
        = walkingEquivParityAdd
          (walkingEquivFlaggedGenParity walkingEquivEtaFamilyFlagFreeContribution
            hasLeftSecond hasRightSecond leftCell)
          (walkingEquivFlaggedGenParity walkingEquivEtaFamilyFlagFreeContribution
            hasLeftSecond hasRightSecond rightCell) from
      congr
        (congrArg walkingEquivParityAdd
          (walkingEquivEtaFamilyParity_flagIndependent leftCell
            hasLeftFirst hasRightFirst hasLeftSecond hasRightSecond))
        (walkingEquivEtaFamilyParity_flagIndependent rightCell
          hasLeftFirst hasRightFirst hasLeftSecond hasRightSecond)
  | _, .whiskerLeft _ innerCell, _, hasRightFirst, _, hasRightSecond =>
      walkingEquivEtaFamilyParity_flagIndependent innerCell
        true hasRightFirst true hasRightSecond
  | _, .whiskerRight innerCell _, hasLeftFirst, _, hasLeftSecond, _ =>
      walkingEquivEtaFamilyParity_flagIndependent innerCell
        hasLeftFirst true hasLeftSecond true

/-- ★ **Every unitor-scope row conserves the flag-free eta parity** — base rows by the r3 generic
dischargers, unitor rows by flag-independence. -/
theorem walkingEquivEtaFamilyParity_ofUnitorScopeRow
    {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim}
    (row : walkingEquivUnitorScopeRel cellAlpha cellBeta)
    (hasLeftAncestor hasRightAncestor : Bool) :
    walkingEquivFlaggedGenParity walkingEquivEtaFamilyFlagFreeContribution
        hasLeftAncestor hasRightAncestor cellAlpha
      = walkingEquivFlaggedGenParity walkingEquivEtaFamilyFlagFreeContribution
        hasLeftAncestor hasRightAncestor cellBeta := by
  cases row with
  | inl baseRow =>
      exact walkingEquivFlaggedGenParity_ofBaseRel walkingEquivEtaFamilyFlagFreeContribution
        walkingEquivEtaFamilyFlagFree_pairsEta walkingEquivEtaFamilyFlagFree_pairsEps
        baseRow hasLeftAncestor hasRightAncestor
  | inr unitorRow =>
      cases unitorRow with
      | whiskerLeftIdCellUnit lower cell =>
          exact walkingEquivEtaFamilyParity_flagIndependent cell
            true hasRightAncestor hasLeftAncestor hasRightAncestor
      | whiskerRightIdCellUnit cell lower =>
          exact walkingEquivEtaFamilyParity_flagIndependent cell
            hasLeftAncestor true hasLeftAncestor hasRightAncestor

/-- ★ **THE GUARD (left)**: the left triangle stays UNDERIVABLE over the unitor scope without the triangle
row — the unitor rows do not smuggle the triangle in.  Any derivation folds through the flag-free
eta-parity absorber to `true = false`. -/
theorem walkingEquivLeftTriangle_notDerivableOverUnitorScopeRel
    (hLeftTriangle : SaturatedConvOverWithId walkingEquivComputad walkingEquivUnitorScopeRel
      walkingEquivLeftTriangleLeg walkingEquivIdF) : False :=
  Bool.noConfusion
    (SaturatedConvOverWithId.recInto
      (walkingEquivFlaggedGenParityAbsorbs walkingEquivEtaFamilyFlagFreeContribution
        walkingEquivEtaFamilyParity_ofUnitorScopeRow)
      hLeftTriangle false false)

/-- ★ **THE GUARD (right)**: the right triangle stays UNDERIVABLE over the unitor scope without the
triangle row — the promotion theorems above are genuinely conditional on triangle content, not a collapse
artifact of the unitor rows. -/
theorem walkingEquivRightTriangle_notDerivableOverUnitorScopeRel
    (hRightTriangle : SaturatedConvOverWithId walkingEquivComputad walkingEquivUnitorScopeRel
      walkingEquivRightTriangleLeg walkingEquivIdG) : False :=
  Bool.noConfusion
    (SaturatedConvOverWithId.recInto
      (walkingEquivFlaggedGenParityAbsorbs walkingEquivEtaFamilyFlagFreeContribution
        walkingEquivEtaFamilyParity_ofUnitorScopeRow)
      hRightTriangle false false)

/-! ## The kernel-computed parity pins (each `rfl`) -/

/-- `phi_f` folds to `true` at the flag-free eta parity (one eta occurrence). -/
theorem walkingEquivLeftTriangleLeg_etaFamilyParityPin :
    walkingEquivFlaggedGenParity walkingEquivEtaFamilyFlagFreeContribution false false
      walkingEquivLeftTriangleLeg = true := rfl

/-- `id f` folds to `false` — SEPARATED from `phi_f`. -/
theorem walkingEquivIdF_etaFamilyParityPin :
    walkingEquivFlaggedGenParity walkingEquivEtaFamilyFlagFreeContribution false false
      walkingEquivIdF = false := rfl

/-- `psi_g` folds to `true` at the flag-free eta parity (one eta occurrence). -/
theorem walkingEquivRightTriangleLeg_etaFamilyParityPin :
    walkingEquivFlaggedGenParity walkingEquivEtaFamilyFlagFreeContribution false false
      walkingEquivRightTriangleLeg = true := rfl

/-- `id g` folds to `false` — SEPARATED from `psi_g`. -/
theorem walkingEquivIdG_etaFamilyParityPin :
    walkingEquivFlaggedGenParity walkingEquivEtaFamilyFlagFreeContribution false false
      walkingEquivIdG = false := rfl

/-- The doubled right leg is structurally DISTINCT from the single leg — the derived idempotency relates
genuinely different words (non-vacuity of the positive theorems). -/
theorem walkingEquivDoubledRightTriangleLeg_distinctFromSingle :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq
      (CellExpr.vcomp walkingEquivRightTriangleLeg walkingEquivRightTriangleLeg)
      walkingEquivRightTriangleLeg = false := rfl

/-! ## Non-vacuity probes -/

#eval walkingEquivFlaggedGenParity walkingEquivEtaFamilyFlagFreeContribution false false
  walkingEquivLeftTriangleLeg
#eval walkingEquivFlaggedGenParity walkingEquivEtaFamilyFlagFreeContribution false false
  walkingEquivRightTriangleLeg
#eval walkingEquivFlaggedGenParity walkingEquivEtaFamilyFlagFreeContribution false false
  walkingEquivIdG
#eval cellBeq walkingEquivModeBeq walkingEquivGenBeq
  (CellExpr.vcomp walkingEquivRightTriangleLeg walkingEquivRightTriangleLeg)
  walkingEquivRightTriangleLeg

/-! ## Honesty markers — the r4 delivery -/

/-- ★★★ **THE r3 SUCCESSOR NODE IS DELIVERED (r4).**  `= true` records that the walking-equivalence
promotion IS mechanized over the unitor-augmented relation the r3 adjudication named
(`walkingEquivUnitorScopeRel = unionCellRel _ walkingEquivBaseRel (whiskerUnitRel _)`): the conditional
idempotency and right triangle (`walkingEquiv*FromLeftTriangleOverUnitorScope`), and — non-vacuously, on
the triangle-adjoined bench with the hypothesis INHABITED — the derived idempotency and right triangle
(`walkingEquiv*_derivableOverUnitorTriangleRel`).  The r3 owner
`fxEquiv_promotionOverWhiskerUnitorScopeOpen` stays byte-intact `false`; THIS marker supersedes it by
content.  The r3 handoff's suspicion that the successor is also a refutation is REFUTED by derivation: the
interchange bracketing compiles once the whisker-unitors exist. -/
def fxEquiv_promotionOverWhiskerUnitorScopeMechanized : Bool := true

/-- ★★ **THE WALL IS LOCALIZED ON BOTH SIDES (r4).**  `= true` records the exact two-sided localization of
the promotion obstruction: (i) WITHOUT the unitor rows, the idempotency and right triangle are
machine-REFUTED even with the left triangle adjoined (r3, flagged parity); (ii) WITH the unitor rows they
are machine-DERIVED (this file); (iii) WITH the unitor rows but WITHOUT the triangle row, both triangles
stay machine-refuted (`walkingEquiv*_notDerivableOverUnitorScopeRel`, flag-free eta parity).  The
whisker-by-identity-1-cell unitors are exactly the classical bookkeeping the promotion spends, and the
triangle is exactly the content it consumes — nothing more on either side. -/
def fxEquiv_promotionUnitorWallLocalizedBothSides : Bool := true

end FX1Poly.Polygraph.Omega
