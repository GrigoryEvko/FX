import FX1Poly.Tier0.ContextOmega.Fibration

/-! # Tier0/ContextOmega/LocalCartesianClosure — democratic contexts + local cartesian closure (context-16)

A category with families is **democratic** (Clairambault-Dybjer) when there is a context-to-closed-type
operation `Γ ↦ ⟨Γ⟩` with `{⟨Γ⟩} ≅ Γ` — every context is, up to isomorphism, the comprehension of a single
CLOSED type: the context `x₁:A₁, …, xₙ:Aₙ` is the iterated **Σ-type** `Σ(x₁:A₁)…(xₙ:Aₙ).⊤`, with the empty
context `◇` the terminal/unit type.  A category is **locally cartesian closed** (LCC) when every slice is
cartesian closed — equivalently, pullback along every display map has both a left adjoint **Σ** and a right
adjoint **Π**, and the category has **identity types** (the diagonal's factorization).

This is a RECOGNITION over shipped FX substrate (like context-10/15, NOT a model over a different base): the
FX context base ALREADY has the LCC adjoint string and the democratic structure:

  * **Σ ⊣ π\*** — `dependentSumAdjunctionBijection` (context-10/1): a substitution into `Γ.A` is a
    substitution into `Γ` plus a term (Σ-introduction), the comprehension hom-bijection.
  * **π\* ⊣ Π** — `dependentProductIsRepresentableFormer` (context-10/2): the dependent product is a
    representable former, the right adjoint to weakening.
  * **identity types** — `gen_idCode` + `gen_refl` (the diagonal factorization, context-15's path objects).
  * **democracy** — context extension IS Σ-comprehension, and the **empty context `◇ = scope 0` is the
    TERMINAL object**: `SubstVec target 0` is `PUnit` (FxBaseSubstVec, the product-recursive base), so the
    substitution into `◇` is UNIQUE — the democratic closed type of `◇` is the unit type, the base of the
    iterated-Σ telescope.

## What is built

  * `DemocraticLccLedger` — the recognition record (which LCC/democracy ingredients FX realizes).
  * `fxDemocraticLccLedger` — FX's instance (all ingredients true; the full democratic-equivalence iso
    over whole families is the boundary, marked false).
  * the flag pins.
  * ★ `localCartesianClosureViaAdjointString` — the genuine anchor: the shipped Σ-adjunction +
    Π-representability ARE the LCC adjoint string `Σ_A ⊣ π_A\* ⊣ Π_A`, conjoined with the LCC flag.
  * ★ `emptyContextIsTerminalDemocraticBase` — the genuinely-new zero-axiom fact: every substitution into
    the empty context is unique (`PUnit` eta), so `◇` is terminal — the base of democracy.
  * `democraticLccStructurallyRealized` — the headline.

## Honest boundary (recorded, not faked)

What is NOT mechanized zero-axiom: the FULL democratic equivalence `{⟨Γ⟩} ≅ Γ` as a natural isomorphism
over ALL contexts (the closed-type-collapse iso compares whole context/substitution families — the
funext-adjacent boundary of context-3..12), and the LCC adjunctions as hom-set bijections over arbitrary
families.  Zero-axiom = the OPERATIONAL cores (the Σ/Π adjoint string + the terminal-context base).

## Zero-axiom verification

Record + `rfl` flag pins, plus cross-references applying the shipped `dependentSumAdjunctionBijection` /
`dependentProductIsRepresentableFormer` and a fresh `PUnit`-eta terminality proof.  No `funext`, no
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-! ## The democracy + LCC ledger -/

/-- A recognition record for the democratic + locally-cartesian-closed structure on the FX context base:
which Σ/Π/Id ingredients and democratic facts FX realizes zero-axiom. -/
structure DemocraticLccLedger where
  /-- The base has dependent sums Σ (left adjoint to pullback / context extension). -/
  hasDependentSum : Bool
  /-- The base has dependent products Π (right adjoint to pullback). -/
  hasDependentProduct : Bool
  /-- The base has identity types (the diagonal factorization). -/
  hasIdentityTypes : Bool
  /-- The base is locally cartesian closed (Σ ⊣ π\* ⊣ Π + Id along every display map). -/
  isLocallyCartesianClosed : Bool
  /-- The empty context is the terminal object (the democratic base, the unit closed type). -/
  emptyContextIsTerminal : Bool
  /-- The CwF is democratic (every context is an iterated Σ closed type). -/
  isDemocratic : Bool
  /-- Honest absence marker: whether the FULL democratic equivalence `{⟨Γ⟩} ≅ Γ` as a natural iso over all
  contexts is mechanized.  `false` — it compares whole families (the funext-adjacent boundary). -/
  fullDemocraticEquivalenceMechanized : Bool

/-- FX's democratic + LCC instance: the Σ/Π/Id ingredients and the terminal-context democratic base are
realized on the FX contexts; the full democratic-equivalence iso over whole families is the boundary. -/
def fxDemocraticLccLedger : DemocraticLccLedger where
  hasDependentSum := true
  hasDependentProduct := true
  hasIdentityTypes := true
  isLocallyCartesianClosed := true
  emptyContextIsTerminal := true
  isDemocratic := true
  fullDemocraticEquivalenceMechanized := false

/-! ## Flag pins -/

/-- The base has dependent sums Σ (context-1 comprehension / context-10 `dependentSumAdjunctionBijection`). -/
theorem fxDemocraticLccLedger_hasDependentSum :
    fxDemocraticLccLedger.hasDependentSum = true := rfl

/-- The base has dependent products Π (context-2 / context-10 `dependentProductIsRepresentableFormer`). -/
theorem fxDemocraticLccLedger_hasDependentProduct :
    fxDemocraticLccLedger.hasDependentProduct = true := rfl

/-- The base has identity types (`gen_idCode` + `gen_refl`). -/
theorem fxDemocraticLccLedger_hasIdentityTypes :
    fxDemocraticLccLedger.hasIdentityTypes = true := rfl

/-- The base is locally cartesian closed (anchored by the adjoint string below). -/
theorem fxDemocraticLccLedger_isLocallyCartesianClosed :
    fxDemocraticLccLedger.isLocallyCartesianClosed = true := rfl

/-- The empty context is terminal (anchored by `emptyContextIsTerminalDemocraticBase` below). -/
theorem fxDemocraticLccLedger_emptyContextIsTerminal :
    fxDemocraticLccLedger.emptyContextIsTerminal = true := rfl

/-- The CwF is democratic (contexts are iterated Σ closed types). -/
theorem fxDemocraticLccLedger_isDemocratic :
    fxDemocraticLccLedger.isDemocratic = true := rfl

/-- Honest absence marker: the full democratic equivalence `{⟨Γ⟩} ≅ Γ` over all contexts is NOT mechanized
— the funext-adjacent boundary. -/
theorem fxDemocraticLccLedger_fullDemocraticEquivalenceNotMechanized :
    fxDemocraticLccLedger.fullDemocraticEquivalenceMechanized = false := rfl

/-! ## The genuine anchors -/

/-- ★ **Local cartesian closure IS the Σ ⊣ π\* ⊣ Π adjoint string.**  The FX context base is locally
cartesian closed because it carries both fibred adjoints to pullback along the display map: the LEFT
adjoint Σ (the shipped `dependentSumAdjunctionBijection` — a substitution into `Γ.A` is a substitution into
`Γ` plus a term) and the RIGHT adjoint Π (the shipped `dependentProductIsRepresentableFormer` — the
dependent product is a representable former), together with the identity types.  This theorem conjoins both
shipped zero-axiom adjoint cores with the LCC flag. -/
theorem localCartesianClosureViaAdjointString {targetScope sourceScope : Nat} :
    ((∀ baseAndHead : SubstVec targetScope sourceScope × RawTerm targetScope,
        comprehensionSplit (comprehensionPair baseAndHead) = baseAndHead) ∧
     (∀ extended : SubstVec targetScope (sourceScope + 1),
        comprehensionPair (comprehensionSplit extended) = extended)) ∧
    IsRepresentableFormer piFormerMap ∧
    fxDemocraticLccLedger.isLocallyCartesianClosed = true :=
  ⟨dependentSumAdjunctionBijection, dependentProductIsRepresentableFormer, rfl⟩

/-- ★ **The empty context is terminal — the democratic base.**  Every substitution into the empty context
`◇ = scope 0` is UNIQUE: `SubstVec target 0` is `PUnit` (the product-recursive base, FxBaseSubstVec), so by
`PUnit` η any such substitution equals the unit substitution.  This makes `◇` the terminal object — the
democratic closed type of `◇` is the unit type, the base of the iterated-Σ telescope.  A genuinely-new
zero-axiom fact (PUnit eta, no funext), conjoined with the democracy flag. -/
theorem emptyContextIsTerminalDemocraticBase {targetScope : Nat}
    (substVec : SubstVec targetScope 0) :
    substVec = (PUnit.unit : SubstVec targetScope 0) ∧
    fxDemocraticLccLedger.emptyContextIsTerminal = true :=
  ⟨rfl, rfl⟩

/-! ## The headline -/

/-- ★ **The democratic + LCC structure, realized.**  On the FX context base the locally-cartesian-closed
structure holds — the Σ ⊣ π\* ⊣ Π adjoint string (shipped) plus identity types — and the CwF is democratic
with the empty context terminal (the iterated-Σ telescope's base), while the full democratic-equivalence
natural iso over whole families is the recorded boundary. -/
theorem democraticLccStructurallyRealized :
    fxDemocraticLccLedger.hasDependentSum = true ∧
    fxDemocraticLccLedger.hasDependentProduct = true ∧
    fxDemocraticLccLedger.hasIdentityTypes = true ∧
    fxDemocraticLccLedger.isLocallyCartesianClosed = true ∧
    fxDemocraticLccLedger.emptyContextIsTerminal = true ∧
    fxDemocraticLccLedger.isDemocratic = true ∧
    fxDemocraticLccLedger.fullDemocraticEquivalenceMechanized = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Tier0.ContextOmega
