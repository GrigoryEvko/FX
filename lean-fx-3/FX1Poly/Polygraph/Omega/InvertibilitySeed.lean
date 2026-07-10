import FX1Poly.Polygraph.Invertibility.WitnessClosure
import FX1Poly.Polygraph.Invertibility.InvertibilitySet
import FX1Poly.Polygraph.Invertibility.FiniteNoGap
import FX1Poly.Polygraph.Omega.NonVacuity

/-! # Polygraph/Omega/InvertibilitySeed — the coinductive-invertibility = SN-duality seed at the ω-carrier
    (OMEGA-6 r1, B3)

★ **The abstract Henry–Loubaton invertibility duality, connected to the Omega ω-cell carrier.**  The
substrate-agnostic engine (`Polygraph/Invertibility/`) already proves the duality:

  * `inductiveClosure` = the LEAST fixpoint of a monotone witness operator ("SN / reducibility-invertible");
  * `coinductiveClosure` = the GREATEST fixpoint ("folk / coinductively invertible", HL23 Def 4.15 `eq 𝒟`);
  * ★ `inductiveClosure_subset_coinductiveClosure` — least ⊆ greatest, hypothesis-free ("SN-invertible ⊆
    folk-invertible");
  * ★ `fixpoints_agree_of_wellFounded` — HL23 Cor 4.35, "no coinductive gap" under a well-founded guard.

This file INSTANTIATES that engine at the ω-cell carrier: `omegaCellStructure` puts an HL23 `CellStructure` on
`Σ dim, CellExpr computad dim`, and the seed lands the one-way inclusion + the conditional collapse over it.

## The honest placeholder (r1 caveat, baked in)

The genuine ω-categorical `reverse` / `unitWitness` / `counitWitness` (real inverses + coherence witnesses) are
NOT modelled — they belong to the Mode / OmegaCategory substrate.  r1 uses the **identity** Skolemization
(`reverse = unitWitness = counitWitness = fun cell => cell`), the honest "clearly-a-placeholder" choice
(InvertibilitySet's own caveat).  Two consequences, stated openly:

  * the maximal (folk) set is EVERYTHING (every family is post-fixed under the identity operator);
  * the inductive (SN) set is EMPTY — the pure invertibility operator has NO identity base case (real
    invertibility would seed the identities), so its least fixpoint is empty regardless of the Skolemization.

So at the placeholder the two fixpoints DISAGREE, and the seed also witnesses the gap CONCRETELY
(`placeholderGap_folkStrictlyBiggerThanSn`) — a genuine instance of HL23 Prop 4.31 ("coinductive is strictly
bigger without finiteness").  The SEED is the machinery connection + the always-true inclusion + the honest
gap; a meaningful invertibility PREDICATE needs the genuine reverse/witnesses + the identity base, DEFERRED.

## What the conditional collapse needs (matches the Core caveat)

`omegaFixpointsAgree_of_wellFounded` recalls HL23 Cor 4.35 over the ω-carrier CONDITIONALLY: it takes a guard,
an `applyFromGuard` bridge, and a `WellFounded guard` premise.  At the RAW ω-layer `WellFounded` on the
cell-reduction guard is globally FALSE (the F1 memo pin; the Core instantiation lives with
`StrongNormalizationBridge.lean`), so the collapse is stated as a hypothesis-taking theorem, not discharged
here.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph.Invertibility

/-! ## The ω-cell structure -/

/-- The **carrier of ω-cells** of a computad — a `dim`-indexed cell packed with its dimension.  The `Cell` type
the HL23 invertibility statement runs over. -/
def OmegaCell (computad : OmegaComputad) : Type := Sigma (fun dim : Nat => CellExpr computad dim)

/-- The **ω-cell structure** — an HL23 `CellStructure` on the ω-cells.  r1 Skolemizes the reverse / unit / counit
as the IDENTITY (the honest placeholder; the genuine ω-categorical inverses are deferred to the
Mode / OmegaCategory substrate). -/
def omegaCellStructure (computad : OmegaComputad) : CellStructure where
  Cell := OmegaCell computad
  reverse := fun cell => cell
  unitWitness := fun cell => cell
  counitWitness := fun cell => cell

/-- The **ω invertibility operator** — the HL23 witness operator of `omegaCellStructure` (a family applies to a
cell exactly when the cell's reverse / unit / counit are already members). -/
def omegaInvertibilityOperator (computad : OmegaComputad) :
    WitnessOperator (omegaCellStructure computad).Cell :=
  invertibilityWitnessOperator (omegaCellStructure computad)

/-- The **SN / reducibility-invertible** ω-cells — the inductive (least) fixpoint. -/
def omegaSnInvertible (computad : OmegaComputad) : OmegaCell computad → Prop :=
  inductiveClosure (omegaInvertibilityOperator computad)

/-- The **folk / coinductively-invertible** ω-cells — the maximal invertibility set (HL23 `eq 𝒟`, the greatest
fixpoint). -/
def omegaFolkInvertible (computad : OmegaComputad) : OmegaCell computad → Prop :=
  maximalInvertibilitySet (omegaCellStructure computad)

/-! ## The provable one-way seed (hypothesis-free) + the conditional collapse (recalled) -/

/-- ★ **SN-invertible ⊆ folk-invertible** at the ω-carrier — the hypothesis-free r1 seed, the instantiated
`inductiveClosure_subset_coinductiveClosure` (the direction that is ALWAYS true: the least fixpoint lies in the
greatest). -/
theorem omegaSnInvertible_subset_folkInvertible (computad : OmegaComputad) {cell : OmegaCell computad}
    (member : omegaSnInvertible computad cell) : omegaFolkInvertible computad cell :=
  inductiveClosure_subset_coinductiveClosure (omegaInvertibilityOperator computad) member

/-- ★ **The finite collapse (recalled, conditional).**  HL23 Cor 4.35 at the ω-carrier: under a well-founded
guard bridging into the invertibility operator, the folk and SN sets AGREE ("no coinductive gap").  The
well-founded premise is NOT available at the raw ω-layer (globally false — the Core `StrongNormalizationBridge`
caveat), so this is a hypothesis-taking recall, not a discharge. -/
theorem omegaFixpointsAgree_of_wellFounded (computad : OmegaComputad)
    (guard : OmegaCell computad → OmegaCell computad → Prop)
    (applyFromGuard : ∀ (family : OmegaCell computad → Prop) (element : OmegaCell computad),
      (∀ predecessor, guard predecessor element → family predecessor) →
        (omegaInvertibilityOperator computad).apply family element)
    (guardWellFounded : WellFounded guard) (cell : OmegaCell computad) :
    omegaFolkInvertible computad cell ↔ omegaSnInvertible computad cell :=
  fixpoints_agree_of_wellFounded (omegaInvertibilityOperator computad) guard applyFromGuard guardWellFounded
    cell

/-! ## Non-vacuity — the placeholder gap is real (HL23 Prop 4.31) -/

/-- Under the identity placeholder, EVERY ω-cell is folk-invertible: the total family `fun _ => True` is
post-fixed, so the coinductive closure is everything.  (Honest degeneracy witness — the placeholder makes folk
invertibility trivial; a meaningful predicate needs the genuine reverse/witnesses.) -/
theorem cell_folkInvertible (computad : OmegaComputad) (cell : OmegaCell computad) :
    omegaFolkInvertible computad cell :=
  (show IsPostFixed (omegaInvertibilityOperator computad) (fun _ => True) from
    fun _ _ => ⟨trivial, trivial, trivial⟩).subset_coinductiveClosure trivial

/-- The object cell is folk-invertible (non-vacuity of the coinductive side). -/
theorem objectCell_folkInvertible : omegaFolkInvertible demoComputad ⟨0, objectCell⟩ :=
  cell_folkInvertible demoComputad ⟨0, objectCell⟩

/-- The object cell is NOT SN-invertible: the pure invertibility operator has no identity base, so its least
fixpoint is empty (instantiate the inductive-closure universal at the empty family `fun _ => False`). -/
theorem objectCell_not_snInvertible : ¬ omegaSnInvertible demoComputad ⟨0, objectCell⟩ := by
  intro member
  exact member (fun _ => False) (fun _ hApplied => hApplied.1)

/-- ★ **The placeholder gap is real**: the object cell is folk-invertible but NOT SN-invertible — folk
invertibility is STRICTLY bigger than SN invertibility at this instance.  A concrete witness of HL23 Prop 4.31
("coinductive is strictly bigger without finiteness"), the honest counterpart to the always-true inclusion
`omegaSnInvertible_subset_folkInvertible`. -/
theorem placeholderGap_folkStrictlyBiggerThanSn :
    omegaFolkInvertible demoComputad ⟨0, objectCell⟩ ∧
    ¬ omegaSnInvertible demoComputad ⟨0, objectCell⟩ :=
  ⟨objectCell_folkInvertible, objectCell_not_snInvertible⟩

end FX1Poly.Polygraph.Omega
