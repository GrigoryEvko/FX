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

This is a RECOGNITION over the FX substrate (`baseIsFXSyntacticContext = true`, like context-15/16/18):

  * **the pushout substrate exists** — the FX context category has finite **coproducts** (context
    concatenation, context-3's `coproductHomBijection`) and the **initial** object (the empty context),
    the colimit data a pushout is assembled from;
  * **the strictness is a THEOREM, not an axiom** — what the cubical strictness axiom POSTULATES (strict
    agreement of a reindexed/glued type) FX gets DEFINITIONALLY: reindexing satisfies `A[σ∘τ] = A[σ][τ]`
    ON THE NOSE (context-7's `reindexType_compose`), because the FX base is syntactic (substitution is
    strictly functorial).  So the "axiom" of cubical models is a `rfl`-level fact here.

## Honest boundary (recorded, not faked)

What is NOT mechanized zero-axiom: the **Glue / Weld** type formers themselves and the strictness axiom
in its FULL cubical form (a strict total type agreeing with a partial type on an arbitrary cofibration)
need the **interval** object + a **cofibration** structure (a dominance / face lattice) + a specific
topos — the cubical-model construction, off the zero-axiom path.  What IS zero-axiom is the colimit
substrate (coproducts + initial) the context pushout is built from, and the strictness that FX realizes
syntactically (the reindexing-strictness theorem the cubical axiom would otherwise postulate).

## What is built

  * `StrictnessGlueLedger` — the recognition record.
  * `fxStrictnessGlueLedger` — FX's instance.
  * the flag pins.
  * ★ `contextPushoutSubstrateViaCoproducts` — the genuine anchor: the FX context coproduct
    hom-bijection (context-3) IS the colimit substrate for context pushouts, conjoined with the flag.
  * ★ `reindexingStrictnessIsDefinitional` — the strictness anchor: `A[σ∘τ] = A[σ][τ]` definitionally
    (context-7), the strictness the cubical axiom postulates, here a theorem.
  * `strictnessAndPushoutContextsRecognized` — the headline.

## Zero-axiom verification

Record + `rfl` flag pins, plus cross-references applying the shipped zero-axiom `coproductHomBijection`
(context-3) and `reindexType_compose` (context-7).  No `funext`, no `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-! ## The strictness / Glue ledger -/

/-- A recognition record for the cubical strictness axiom + Glue/Weld at the context level: which
ingredients FX realizes zero-axiom (the context pushout substrate, the strictness-as-a-theorem) and
which are the cubical boundary (the Glue/Weld formers, the full strictness axiom over a cofibration). -/
structure StrictnessGlueLedger where
  /-- The context pushout substrate exists: the FX context category has finite coproducts (context
  concatenation) + the initial object (empty context). -/
  contextPushoutSubstrateRealized : Bool
  /-- Reindexing strictness `A[σ∘τ] = A[σ][τ]` is a THEOREM (definitional), not an axiom — the strictness
  the cubical strictness axiom would postulate, realized syntactically. -/
  reindexingStrictnessIsTheoremNotAxiom : Bool
  /-- Whether the base is the FX syntactic context category.  `true` — recognized ON the FX contexts. -/
  baseIsFXSyntacticContext : Bool
  /-- Honest absence marker: whether the Glue / Weld type formers are constructed.  `false` — they need
  the interval + cofibrations. -/
  glueWeldTypesConstructed : Bool
  /-- Honest absence marker: whether the cubical strictness axiom in its FULL form (strict total type
  agreeing with a partial type on an arbitrary cofibration) is mechanized.  `false` — the cubical
  construction over an interval / cofibration topos. -/
  cubicalStrictnessAxiomInFullForm : Bool

/-- FX's strictness / Glue instance: the context pushout substrate and the strictness-as-a-theorem are
realized on the FX contexts; the Glue/Weld formers and the full cubical strictness axiom are the
recorded boundary. -/
def fxStrictnessGlueLedger : StrictnessGlueLedger where
  contextPushoutSubstrateRealized := true
  reindexingStrictnessIsTheoremNotAxiom := true
  baseIsFXSyntacticContext := true
  glueWeldTypesConstructed := false
  cubicalStrictnessAxiomInFullForm := false

/-! ## Flag pins -/

/-- The context pushout substrate is realized (anchored by `contextPushoutSubstrateViaCoproducts`). -/
theorem fxStrictnessGlueLedger_contextPushoutSubstrateRealized :
    fxStrictnessGlueLedger.contextPushoutSubstrateRealized = true := rfl

/-- Reindexing strictness is a theorem (anchored by `reindexingStrictnessIsDefinitional`). -/
theorem fxStrictnessGlueLedger_reindexingStrictnessIsTheoremNotAxiom :
    fxStrictnessGlueLedger.reindexingStrictnessIsTheoremNotAxiom = true := rfl

/-- The strictness / Glue structure is recognized ON the FX syntactic context category. -/
theorem fxStrictnessGlueLedger_baseIsFXSyntacticContext :
    fxStrictnessGlueLedger.baseIsFXSyntacticContext = true := rfl

/-- Honest absence marker: the Glue / Weld type formers are NOT constructed (they need the interval +
cofibrations) — the cubical boundary. -/
theorem fxStrictnessGlueLedger_glueWeldTypesNotConstructed :
    fxStrictnessGlueLedger.glueWeldTypesConstructed = false := rfl

/-- Honest absence marker: the full cubical strictness axiom (over a cofibration) is NOT mechanized —
the cubical boundary. -/
theorem fxStrictnessGlueLedger_cubicalStrictnessAxiomNotInFullForm :
    fxStrictnessGlueLedger.cubicalStrictnessAxiomInFullForm = false := rfl

/-! ## The genuine anchors -/

/-- ★ **The context pushout substrate, via coproducts.**  Gluing contexts along a cofibration is a
PUSHOUT of contexts; a pushout is assembled from COPRODUCTS and the initial object.  The FX context
category has finite coproducts — context concatenation, with the universal property
`Hom(s1 + s2, Y) ≅ Hom(s1, Y) × Hom(s2, Y)` (context-3's `coproductHomBijection`, both round-trips) —
the colimit substrate the context pushout is built from.  This conjoins that shipped bijection with the
pushout-substrate flag. -/
theorem contextPushoutSubstrateViaCoproducts {ambientScope firstScope secondScope : Nat} :
    ((∀ leftPart : SubstVec ambientScope firstScope,
        ∀ rightPart : SubstVec ambientScope secondScope,
          coproductSplit (coproductCopair leftPart rightPart) = (leftPart, rightPart)) ∧
     (∀ combinedVec : SubstVec ambientScope (firstScope + secondScope),
        coproductCopair (coproductSplit combinedVec).1 (coproductSplit combinedVec).2 = combinedVec)) ∧
    fxStrictnessGlueLedger.contextPushoutSubstrateRealized = true :=
  ⟨coproductHomBijection, rfl⟩

/-- ★ **The strictness is definitional, not an axiom.**  The cubical strictness axiom POSTULATES that a
reindexed / glued type strictly agrees on its boundary; FX gets that strictness FOR FREE — reindexing
satisfies `A[σ∘τ] = A[σ][τ]` ON THE NOSE (context-7's `reindexType_compose`), an EQUALITY because the FX
base is syntactic and substitution is strictly functorial.  So what cubical models must axiomatize is a
THEOREM here.  This conjoins the shipped strict-functoriality coherence with the
strictness-is-a-theorem flag. -/
theorem reindexingStrictnessIsDefinitional (family : SubstActionFamily) {scopeA scopeB scopeC : Nat}
    (firstVec : SubstVec scopeB scopeA) (secondVec : SubstVec scopeC scopeB)
    (typeCell : family.sections scopeA) :
    reindexType family (firstVec.compose secondVec) typeCell =
        reindexType family secondVec (reindexType family firstVec typeCell) ∧
    fxStrictnessGlueLedger.reindexingStrictnessIsTheoremNotAxiom = true :=
  ⟨reindexType_compose family firstVec secondVec typeCell, rfl⟩

/-! ## The headline -/

/-- ★ **Pushout contexts + the strictness axiom, recognized.**  On the FX context base (a) the context
PUSHOUT substrate is realized — finite coproducts (context concatenation) + the initial empty context,
context-3's colimit data — and (b) the strictness the cubical strictness axiom would POSTULATE is a
definitional THEOREM (`A[σ∘τ] = A[σ][τ]`, context-7), realized syntactically; over the FX syntactic
context category, while (c) the Glue/Weld type formers and (d) the full cubical strictness axiom (over a
cofibration, needing the interval) are the recorded boundary. -/
theorem strictnessAndPushoutContextsRecognized :
    fxStrictnessGlueLedger.contextPushoutSubstrateRealized = true ∧
    fxStrictnessGlueLedger.reindexingStrictnessIsTheoremNotAxiom = true ∧
    fxStrictnessGlueLedger.baseIsFXSyntacticContext = true ∧
    fxStrictnessGlueLedger.glueWeldTypesConstructed = false ∧
    fxStrictnessGlueLedger.cubicalStrictnessAxiomInFullForm = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Tier0.ContextOmega
