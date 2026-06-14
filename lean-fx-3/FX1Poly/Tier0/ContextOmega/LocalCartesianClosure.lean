import FX1Poly.Tier0.ContextOmega.Fibration

/-! # Tier0/ContextOmega/LocalCartesianClosure — democratic contexts + local cartesian closure (context-16)

A category with families is **democratic** (Clairambault-Dybjer) when there is a context-to-closed-type
operation `Γ ↦ ⟨Γ⟩` with `{⟨Γ⟩} ≅ Γ` — every context is, up to isomorphism, the comprehension of a single
CLOSED type: the context `x₁:A₁, …, xₙ:Aₙ` is the iterated **Σ-type** `Σ(x₁:A₁)…(xₙ:Aₙ).⊤`, with the empty
context `◇` the terminal/unit type.  A category is **locally cartesian closed** (LCC) when every slice is
cartesian closed — equivalently, pullback along every display map has both a left adjoint **Σ** and a right
adjoint **Π**, and the category has **identity types** (the diagonal's factorization).

This module ships the two genuine anchors the LCC/democracy structure reduces to on the FX context base:

  * ★ `localCartesianClosureViaAdjointString` — the FX context base carries the LCC adjoint string
    `Σ_A ⊣ π_A* ⊣ Π_A`: the LEFT adjoint Σ (the shipped `dependentSumAdjunctionBijection`) and the RIGHT
    adjoint Π (the shipped `dependentProductIsRepresentableFormer`).
  * ★ `emptyContextIsTerminalDemocraticBase` — the genuinely-new zero-axiom fact: every substitution into
    the empty context `◇ = scope 0` is unique (`PUnit` eta, no funext), so `◇` is the terminal object —
    the democratic closed type of `◇` is the unit type, the base of the iterated-Σ telescope.

## Honest boundary (recorded, not faked)

What is NOT mechanized zero-axiom: the FULL democratic equivalence `{⟨Γ⟩} ≅ Γ` as a natural isomorphism
over ALL contexts (the closed-type-collapse iso compares whole context/substitution families — the
funext-adjacent boundary of context-3..12), and the LCC adjunctions as hom-set bijections over arbitrary
families.  Zero-axiom = the OPERATIONAL cores (the Σ/Π adjoint string + the terminal-context base).

Cross-references apply the shipped `dependentSumAdjunctionBijection` / `dependentProductIsRepresentableFormer`
and a fresh `PUnit`-eta terminality proof.  No `funext`, no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-- ★ **Local cartesian closure IS the Σ ⊣ π* ⊣ Π adjoint string.**  The FX context base is locally
cartesian closed because it carries both fibred adjoints to pullback along the display map: the LEFT
adjoint Σ (the shipped `dependentSumAdjunctionBijection` — a substitution into `Γ.A` is a substitution into
`Γ` plus a term) and the RIGHT adjoint Π (the shipped `dependentProductIsRepresentableFormer` — the
dependent product is a representable former).  This bundles both shipped zero-axiom adjoint cores. -/
theorem localCartesianClosureViaAdjointString {targetScope sourceScope : Nat} :
    ((∀ baseAndHead : SubstVec targetScope sourceScope × RawTerm targetScope,
        comprehensionSplit (comprehensionPair baseAndHead) = baseAndHead) ∧
     (∀ extended : SubstVec targetScope (sourceScope + 1),
        comprehensionPair (comprehensionSplit extended) = extended)) ∧
    IsRepresentableFormer piFormerMap :=
  ⟨dependentSumAdjunctionBijection, dependentProductIsRepresentableFormer⟩

/-- ★ **The empty context is terminal — the democratic base.**  Every substitution into the empty context
`◇ = scope 0` is UNIQUE: `SubstVec target 0` is `PUnit` (the product-recursive base, FxBaseSubstVec), so by
`PUnit` η any such substitution equals the unit substitution.  This makes `◇` the terminal object — the
democratic closed type of `◇` is the unit type, the base of the iterated-Σ telescope.  A genuinely-new
zero-axiom fact (PUnit eta, no funext). -/
theorem emptyContextIsTerminalDemocraticBase {targetScope : Nat}
    (substVec : SubstVec targetScope 0) :
    substVec = (PUnit.unit : SubstVec targetScope 0) :=
  rfl

end FX1Poly.Tier0.ContextOmega
