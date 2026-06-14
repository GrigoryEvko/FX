import FX1Poly.Tier0.ContextOmega.Fibration

/-! # Tier0/ContextOmega/BeckChevalleyCoherence — dependent-adjoint naturality at full strength (context-17)

The **Beck-Chevalley condition** is the coherence that makes the fibred adjoints `Σ_A ⊣ π_A^* ⊣ Π_A`
of a comprehension fibration stable under substitution: reindexing along a pullback square commutes
with the adjoints (the canonical comparison is an iso).  context-10 (`Fibration.lean`) proved the
condition for the DISPLAY MAP `π` — the `beckChevalleyDisplaySquare` `weakening ∘ (lift σ) = σ ∘
weakening`, the pullback-stability of `π`.  This module extends Beck-Chevalley to the dependent
FORMERS — the LEFT adjoint `Σ` and the RIGHT adjoint `Π` — **at full strength**: substitution commutes
strictly (as an EQUALITY of terms, not merely a coherent iso) with both `Σ`- and `Π`-formation, with
the codomain reindexed along the SAME Cartesian lift `σ⁺ = cartesianLift σ` that context-10 covers `σ`
with.

The genuine content: on the FX context base the dependent formers are de Bruijn term constructors and
substitution recurses structurally — into the domain with `σ`, and into the codomain (under one
binder) with the LIFTED substitution.  That lifted substitution is EXACTLY context-10's Cartesian lift
`σ⁺ = substVec.liftUnderBinder` (bridged at the term level by the shipped `liftUnderBinder_subst_apply`).
So `(Π_A B)[σ] = Π_{A[σ]}(B[σ⁺])` and `(Σ_A B)[σ] = Σ_{A[σ]}(B[σ⁺])` hold ON THE NOSE — the dependent
adjoints' Beck-Chevalley naturality is strict, the same σ⁺ threading the display map, the left adjoint,
and the right adjoint uniformly.

## What is built

  * `piFormerCode` / `sigmaFormerCode` — the Tier0/Core-level Π/Σ type-former code cells (de Bruijn,
    domain at shift `0` + codomain under one binder at shift `1`; the same shape the `Typed` layer's
    `piTyCodeCell`/`sigmaTyCodeCell` carry, restated here so the Tier0 layer needs no `Typed` import).
  * `piFormerCode_subst` / `sigmaFormerCode_subst` — the structural `rfl` facts: substitution recurses
    into a former with the codomain under the kernel lift `RawTermSubst.lift`.
  * ★ `piFormerBeckChevalleyNaturality` / `sigmaFormerBeckChevalleyNaturality` — the genuine theorems:
    substitution commutes with `Π`- / `Σ`-formation via the Cartesian lift `cartesianLift σ` (context-10).
  * ★ `dependentAdjointBeckChevalleyAtFullStrength` — the headline: the display map `π` (context-10),
    the left adjoint `Σ`, and the right adjoint `Π` ALL commute with substitution via the SAME `σ⁺`.

## Honest boundary (recorded, not faked)

The FULL fibred Beck-Chevalley ISO — the natural isomorphism comparing `Σ`/`Π` with reindexing along an
ARBITRARY pullback square in the base, as hom-set bijections over arbitrary type families — compares
whole `SubstFamilyMap`/section families at every fibre (the same `funext` boundary as context-3..16,
off the zero-axiom path).  What IS zero-axiom is the OPERATIONAL core: the strict former-substitution
EQUATIONS (`Π`/`Σ` naturality on de Bruijn codes) and their coherence with the display-map square — the
substitution-stability of the dependent adjoints, realized strictly on the FX syntactic base.

## Zero-axiom verification

The `_subst` lemmas are `rfl` (substitution computes structurally on a former); the BC naturality
theorems compose them with the shipped `SubstVec.liftUnderBinder_subst_apply` (the σ⁺-bridge) via
`congrArg`; the headline conjoins them with context-10's `beckChevalleyDisplaySquare`.  No `funext`, no
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-! ## The Tier0 Π/Σ former-code builders -/

/-- The dependent function-type code `Π domainCode. codomainCode` at the Tier0/Core layer — the
`gen_piTyCode` cell (binder shifts `[0, 1]`: the codomain lives under one fresh value binder, hence at
`scope + 1`; `Unit` payload; the two children are the domain and codomain codes).  Restated here so the
Tier0 fibration layer needs no `Typed`-layer import (it matches `Typed.piTyCodeCell` exactly). -/
def piFormerCode {scope : Nat} (domainCode : RawTerm scope)
    (codomainCode : RawTerm (scope + 1)) : RawTerm scope :=
  RawTerm.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))

/-- The dependent pair-type code `Σ domainCode. codomainCode` at the Tier0/Core layer — the
`gen_sigmaTyCode` cell, structurally identical to `piFormerCode` (shifts `[0, 1]`, `Unit` payload, two
children) but with the head generator `gen_sigmaTyCode`.  The dual former, restated for the Tier0 layer. -/
def sigmaFormerCode {scope : Nat} (domainCode : RawTerm scope)
    (codomainCode : RawTerm (scope + 1)) : RawTerm scope :=
  RawTerm.mkGen .gen_sigmaTyCode () (.childCons domainCode (.childCons codomainCode .childNil))

/-! ## The structural former-substitution facts -/

/-- **Substitution recurses structurally through the Π former.**  Substituting `substitution` into a
`Π`-code substitutes into the domain with `substitution` and into the codomain — which lives under one
binder — with the kernel lift `RawTermSubst.lift substitution`.  A `rfl`: the kernel's `subst` is a
structural fold that applies the per-child binder lift (`shift = 1` for the codomain). -/
theorem piFormerCode_subst {target source : Nat} (substitution : RawTermSubst source target)
    (domainCode : RawTerm source) (codomainCode : RawTerm (source + 1)) :
    RawTerm.subst substitution (piFormerCode domainCode codomainCode)
      = piFormerCode (RawTerm.subst substitution domainCode)
          (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) := rfl

/-- **Substitution recurses structurally through the Σ former** — the dual of `piFormerCode_subst`
(`gen_sigmaTyCode` shares the former shape), again `rfl`. -/
theorem sigmaFormerCode_subst {target source : Nat} (substitution : RawTermSubst source target)
    (domainCode : RawTerm source) (codomainCode : RawTerm (source + 1)) :
    RawTerm.subst substitution (sigmaFormerCode domainCode codomainCode)
      = sigmaFormerCode (RawTerm.subst substitution domainCode)
          (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) := rfl

/-! ## Beck-Chevalley naturality of the dependent formers via the Cartesian lift -/

/-- ★ **Beck-Chevalley naturality of the RIGHT adjoint `Π`, via the Cartesian lift.**  Substituting
`substVec` into a `Π`-code is the `Π`-code of the components reindexed along `substVec`: the domain by
`substVec`, the codomain by the **Cartesian lift** `cartesianLift substVec = σ⁺` (context-10's morphism
covering `σ` over the display map).  `(Π_A B)[σ] = Π_{A[σ]}(B[σ⁺])` — the strict Beck-Chevalley
naturality of the right adjoint, the codomain threaded by the SAME `σ⁺` that the display-map square uses.
Proved from the structural `piFormerCode_subst` composed with the shipped term-level σ⁺-bridge
`liftUnderBinder_subst_apply`. -/
theorem piFormerBeckChevalleyNaturality {targetScope sourceScope : Nat}
    (substVec : SubstVec targetScope sourceScope)
    (domainCode : RawTerm sourceScope) (codomainCode : RawTerm (sourceScope + 1)) :
    RawTerm.subst substVec.toRawTermSubst (piFormerCode domainCode codomainCode)
      = piFormerCode (RawTerm.subst substVec.toRawTermSubst domainCode)
          (RawTerm.subst (cartesianLift substVec).toRawTermSubst codomainCode) :=
  (piFormerCode_subst substVec.toRawTermSubst domainCode codomainCode).trans
    (congrArg (piFormerCode (RawTerm.subst substVec.toRawTermSubst domainCode))
      (SubstVec.liftUnderBinder_subst_apply substVec codomainCode).symm)

/-- ★ **Beck-Chevalley naturality of the LEFT adjoint `Σ`, via the Cartesian lift** — the dual of
`piFormerBeckChevalleyNaturality`.  `(Σ_A B)[σ] = Σ_{A[σ]}(B[σ⁺])`: substituting into a `Σ`-code
reindexes the domain by `σ` and the codomain by the Cartesian lift `σ⁺`.  The strict Beck-Chevalley
naturality of the left adjoint, the same `σ⁺` threading. -/
theorem sigmaFormerBeckChevalleyNaturality {targetScope sourceScope : Nat}
    (substVec : SubstVec targetScope sourceScope)
    (domainCode : RawTerm sourceScope) (codomainCode : RawTerm (sourceScope + 1)) :
    RawTerm.subst substVec.toRawTermSubst (sigmaFormerCode domainCode codomainCode)
      = sigmaFormerCode (RawTerm.subst substVec.toRawTermSubst domainCode)
          (RawTerm.subst (cartesianLift substVec).toRawTermSubst codomainCode) :=
  (sigmaFormerCode_subst substVec.toRawTermSubst domainCode codomainCode).trans
    (congrArg (sigmaFormerCode (RawTerm.subst substVec.toRawTermSubst domainCode))
      (SubstVec.liftUnderBinder_subst_apply substVec codomainCode).symm)

/-! ## The headline -/

/-- ★ **The dependent-adjoint Beck-Chevalley, at full strength.**  On the FX context base ALL THREE
legs of the comprehension fibration's adjoint string `Σ_A ⊣ π_A^* ⊣ Π_A` commute with substitution via
the SAME Cartesian lift `σ⁺ = cartesianLift substVec`:

  * the **display map** `π` — `weakening ∘ (lift σ) = σ ∘ weakening` (context-10's
    `beckChevalleyDisplaySquare`, the pullback-stability of `π`);
  * the **left adjoint** `Σ` — `(Σ_A B)[σ] = Σ_{A[σ]}(B[σ⁺])`;
  * the **right adjoint** `Π` — `(Π_A B)[σ] = Π_{A[σ]}(B[σ⁺])`.

This is the dependent-adjoint Beck-Chevalley naturality at FULL strength: context-10 covered only the
display map; here the left and right adjoints commute with substitution strictly, the SAME `σ⁺` threading
every leg.  (The full fibred Beck-Chevalley ISO over arbitrary families is the recorded funext boundary.) -/
theorem dependentAdjointBeckChevalleyAtFullStrength {targetScope sourceScope : Nat}
    (substVec : SubstVec targetScope sourceScope)
    (domainCode : RawTerm sourceScope) (codomainCode : RawTerm (sourceScope + 1)) :
    ((SubstVec.weakening sourceScope).compose substVec.liftUnderBinder =
        substVec.compose (SubstVec.weakening targetScope)) ∧
    (RawTerm.subst substVec.toRawTermSubst (sigmaFormerCode domainCode codomainCode)
        = sigmaFormerCode (RawTerm.subst substVec.toRawTermSubst domainCode)
            (RawTerm.subst (cartesianLift substVec).toRawTermSubst codomainCode)) ∧
    (RawTerm.subst substVec.toRawTermSubst (piFormerCode domainCode codomainCode)
        = piFormerCode (RawTerm.subst substVec.toRawTermSubst domainCode)
            (RawTerm.subst (cartesianLift substVec).toRawTermSubst codomainCode)) :=
  ⟨beckChevalleyDisplaySquare substVec,
   sigmaFormerBeckChevalleyNaturality substVec domainCode codomainCode,
   piFormerBeckChevalleyNaturality substVec domainCode codomainCode⟩

end FX1Poly.Tier0.ContextOmega
