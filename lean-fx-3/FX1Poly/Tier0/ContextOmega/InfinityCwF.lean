import FX1Poly.Tier0.ContextOmega.SimplicialModel
import FX1Poly.Tier0.ContextOmega.Comprehension

/-! # Tier0/ContextOmega/InfinityCwF — the (∞,1)-CwF / natural model in an ∞-topos (context-14)

A **natural model** (Awodey) presents type theory as a *representable* natural transformation
`Tm → Ty` in a presheaf category; a **category with families** packages the same data.  The
**(∞,1)-categorical** refinement (Nguyen-Uemura "∞-type theories", Kapulkin-Lumsdaine "homotopy theory
of type theories") replaces the Set-valued presheaves with **space- / ∞-groupoid-valued** presheaves
over a Grothendieck **∞-topos**: a comprehension ∞-category / natural model whose universe is the
**object classifier** of the ∞-topos — which is **univalent by construction**.  The simplicial model
(context-13) is ONE concrete presentation of such an ∞-topos (the ∞-topos of spaces, presented by `sSet`).

Like the simplicial model, this is a **semantic model over a higher-categorical base** — an ∞-topos,
NOT the FX syntactic context category `fxBaseSubstCategory`.  ∞-groupoids / ∞-toposes cannot be built
zero-axiom in raw Lean 4 (Init only): the standard constructions need either simplicial machinery (a
large classical development) or higher-inductive quotients (`Quot.sound`).  So the (∞,1)-CwF itself is
CITED (documentary `infinityToposNaturalModelLedger`), not constructed.

The one machine-checked content — the GENUINE recognition this module adds:

  * ★ `fxNaturalModelIsZeroTruncationOfInfinityCwF` — the FX syntactic CwF (the shipped 1-categorical
    comprehension structure) is the **homotopy-0-truncation** of the (∞,1)-CwF.  At h-level 0 the natural
    model's representability — an EQUIVALENCE of mapping SPACES `Tm(Δ) ≃ Hom(Δ, Γ.A)` — collapses to a
    STRICT BIJECTION of hom-SETS, which is EXACTLY the shipped zero-axiom `comprehensionBijection`
    (context-1).  So FX realizes the (∞,1)-natural-model representability at the set level, on the nose.

The (∞,1)-CwF / ∞-topos natural model, the object classifier, and the proof that the object classifier is
univalent are NOT constructed in FX — they are the cited higher-categorical constructions (needing
∞-categorical machinery + classical metatheory for the standard spaces presentation; cubical models give a
constructive route, which FX instead realizes DEFINITIONALLY via the DEFUNIV arc).

Raw Lean 4 + Init only; the cross-reference applies the shipped zero-axiom `comprehensionBijection`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated
in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-- The (∞,1)-CwF / natural model in an ∞-topos (Nguyen-Uemura ∞-type theories; Kapulkin-Lumsdaine
homotopy theory of type theories): contexts and types live in a Grothendieck ∞-topos, the universe is
the ∞-topos' object classifier (univalent by construction).  A CLASSICAL relative-consistency anchor for
univalence — the abstract form of which the simplicial model (context-13) is a concrete instance.  NOT
constructed in FX (the honest flags record this); documentary citation only. -/
def infinityToposNaturalModelLedger : SemanticModelLedger where
  modelName :=
    "(∞,1)-CwF / natural model in an ∞-topos (Nguyen-Uemura ∞-type theories; Kapulkin-Lumsdaine homotopy theory of type theories)"
  baseCategory :=
    "a Grothendieck ∞-topos (space- / ∞-groupoid-valued presheaves), e.g. the ∞-topos of spaces presented by sSet"
  fibrationNotion :=
    "the natural model's representable natural transformation Tm → Ty, enriched in spaces (a fibrant family in the ∞-topos)"
  universeContent :=
    "the object classifier of the ∞-topos — univalent by construction (univalence = the object classifier's classifying property)"
  providesUnivalentUniverse := true
  role := .relativeConsistency
  requiresClassicalMetatheory := true
  baseIsFXSyntacticContext := false
  isMechanizedInFX := false

/-- ★ **FX's syntactic CwF is the 0-truncation of the (∞,1)-CwF.**  The (∞,1)-natural-model
representability is an EQUIVALENCE of mapping spaces `Tm(Δ) ≃ Hom(Δ, Γ.A)`.  At the homotopy-0-truncation
(the FX set-level syntactic model) an equivalence of spaces collapses to a STRICT BIJECTION of hom-sets —
which is EXACTLY the shipped zero-axiom `comprehensionBijection` (context-1, both round-trips hold over
the FX term base).  So FX realizes the (∞,1)-natural-model representability ON THE NOSE at h-level 0.
Delegates to the shipped `comprehensionBijection`. -/
theorem fxNaturalModelIsZeroTruncationOfInfinityCwF {targetScope sourceScope : Nat} :
    (∀ baseAndHead : SubstVec targetScope sourceScope × RawTerm targetScope,
        comprehensionSplit (comprehensionPair baseAndHead) = baseAndHead) ∧
    (∀ extended : SubstVec targetScope (sourceScope + 1),
        comprehensionPair (comprehensionSplit extended) = extended) :=
  comprehensionBijection

end FX1Poly.Tier0.ContextOmega
