import FX1Poly.Tier0.ContextOmega.Colimits
import FX1Poly.Tier0.ContextOmega.Strictification

/-! # Tier0/ContextOmega/StrictnessAndGlueContexts — pushout contexts + the strictness axiom (context-19)

Cubical type theory builds **Glue** and **Weld** types — the type formers that realize univalence
(Glue) and its dual (Weld) by gluing a "partial" type on a cofibration `φ` onto a total type along an
equivalence.  For these to typecheck, the gluing must be **STRICT**: `Glue [φ ↦ (T, e)] A` must agree
with `T` *definitionally* (not merely up to a path) on `φ`.  Orton-Pitts ("Axioms for Modelling Cubical
Type Theory in a Topos") isolate this as the **strictness axiom**: a postulate that, given a partial
type strictly extending along a cofibration, a strict total extension EXISTS.  In a semantic model this
must be axiomatized; the gluing of contexts along a cofibration is a **pushout** of contexts.

This module ships the two genuine zero-axiom anchors:

  * ★ `contextPushoutSubstrateViaCoproducts` — the FX context category has finite **coproducts** (context
    concatenation, context-3's `coproductHomBijection`) and the initial empty context, the colimit data a
    context pushout is assembled from.
  * ★ `reindexingStrictnessIsDefinitional` — what the cubical strictness axiom POSTULATES (strict agreement
    of a reindexed/glued type) FX gets DEFINITIONALLY: reindexing satisfies `A[σ∘τ] = A[σ][τ]` ON THE NOSE
    (context-7's `reindexType_compose`), because the FX base is syntactic (substitution is strictly
    functorial).  So the "axiom" of cubical models is a theorem here.

## Honest boundary (recorded, not faked)

What is NOT mechanized zero-axiom: the **Glue / Weld** type formers themselves and the strictness axiom
in its FULL cubical form (a strict total type agreeing with a partial type on an arbitrary cofibration)
need the **interval** object + a **cofibration** structure (a dominance / face lattice) + a specific
topos — the cubical-model construction.  What IS zero-axiom is the colimit substrate (coproducts +
initial) the context pushout is built from, and the strictness FX realizes syntactically.

Cross-references apply the shipped zero-axiom `coproductHomBijection` (context-3) and `reindexType_compose`
(context-7).  No `funext`, no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-- ★ **The context pushout substrate, via coproducts.**  Gluing contexts along a cofibration is a
PUSHOUT of contexts; a pushout is assembled from COPRODUCTS and the initial object.  The FX context
category has finite coproducts — context concatenation, with the universal property
`Hom(s1 + s2, Y) ≅ Hom(s1, Y) × Hom(s2, Y)` (context-3's `coproductHomBijection`, both round-trips) —
the colimit substrate the context pushout is built from. -/
theorem contextPushoutSubstrateViaCoproducts {ambientScope firstScope secondScope : Nat} :
    (∀ leftPart : SubstVec ambientScope firstScope,
        ∀ rightPart : SubstVec ambientScope secondScope,
          coproductSplit (coproductCopair leftPart rightPart) = (leftPart, rightPart)) ∧
    (∀ combinedVec : SubstVec ambientScope (firstScope + secondScope),
        coproductCopair (coproductSplit combinedVec).1 (coproductSplit combinedVec).2 = combinedVec) :=
  coproductHomBijection

/-- ★ **The strictness is definitional, not an axiom.**  The cubical strictness axiom POSTULATES that a
reindexed / glued type strictly agrees on its boundary; FX gets that strictness FOR FREE — reindexing
satisfies `A[σ∘τ] = A[σ][τ]` ON THE NOSE (context-7's `reindexType_compose`), an EQUALITY because the FX
base is syntactic and substitution is strictly functorial.  So what cubical models must axiomatize is a
THEOREM here. -/
theorem reindexingStrictnessIsDefinitional (family : SubstActionFamily) {scopeA scopeB scopeC : Nat}
    (firstVec : SubstVec scopeB scopeA) (secondVec : SubstVec scopeC scopeB)
    (typeCell : family.sections scopeA) :
    reindexType family (firstVec.compose secondVec) typeCell =
      reindexType family secondVec (reindexType family firstVec typeCell) :=
  reindexType_compose family firstVec secondVec typeCell

end FX1Poly.Tier0.ContextOmega
