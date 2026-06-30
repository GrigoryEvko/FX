import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.ContextPolygraphPresentation

/-! # FX1PolyAudit/.../ContextPolygraphPresentation — zero-axiom gate for context-40

Per-declaration zero-axiom gate for `context-40`'s deliverable
(`FX1Poly/Tier0/Context/ContextPolygraphPresentation.lean`): the context category as a FINITELY-PRESENTED
(∞,ω)-polygraph with a DECIDABLE admissible-extension predicate.  The generating context formers
(`empty`/`cons`/`lockCons` — the kernel `TypingContext` constructors, modeled over the scope substrate),
their finite COMPLETE generating set, the free context words, the self-contained structural `natEq`, the
decidable admissible-extension check with its propext-free structural `Decidable` instance, the grounding in
real construction, the packaged presentation, and the `context-36` 0-skeleton bridge.  The FULL (∞,ω)
polygraph — the generating HIGHER CELLS and the ω-coherence quotient (needs `Quot.sound`) — is the honest
`false` marker; the Core table-native row is the honest cross-axis `×type` sibling (`= false`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The generators — the context formers
#assert_no_axioms FX1Poly.Tier0.ContextFormer
#assert_no_axioms FX1Poly.Tier0.ContextFormer.arity
#assert_no_axioms FX1Poly.Tier0.ContextFormer.scopeShift
#assert_no_axioms FX1Poly.Tier0.contextFormers
#assert_no_axioms FX1Poly.Tier0.contextFormers_length
#assert_no_axioms FX1Poly.Tier0.contextFormers_complete
#assert_no_axioms FX1Poly.Tier0.contextFormers_exhaustive

-- The free words over the generators
#assert_no_axioms FX1Poly.Tier0.ContextExpr
#assert_no_axioms FX1Poly.Tier0.ContextExpr.scope

-- The self-contained structural Nat-equality
#assert_no_axioms FX1Poly.Tier0.natEq
#assert_no_axioms FX1Poly.Tier0.natEq_refl

-- The decidable admissible-extension predicate
#assert_no_axioms FX1Poly.Tier0.isAdmissibleExtension
#assert_no_axioms FX1Poly.Tier0.isAdmissibleExtension_empty
#assert_no_axioms FX1Poly.Tier0.isAdmissibleExtension_cons
#assert_no_axioms FX1Poly.Tier0.isAdmissibleExtension_lockCons
#assert_no_axioms FX1Poly.Tier0.isAdmissibleExtension_empty_overNonemptyBase
#assert_no_axioms FX1Poly.Tier0.IsAdmissibleExtension
#assert_no_axioms FX1Poly.Tier0.instDecidableIsAdmissibleExtension
#assert_no_axioms FX1Poly.Tier0.contextPolygraph_admissibleExtension_decidable

-- Admissibility grounded in real construction
#assert_no_axioms FX1Poly.Tier0.cons_extension_admissible
#assert_no_axioms FX1Poly.Tier0.lockCons_extension_admissible
#assert_no_axioms FX1Poly.Tier0.empty_extension_admissible

-- The packaged finite presentation
#assert_no_axioms FX1Poly.Tier0.ContextPolygraphPresentation
#assert_no_axioms FX1Poly.Tier0.contextPolygraph

-- The context-36 0-skeleton bridge + scope-increasing generators
#assert_no_axioms FX1Poly.Tier0.natSuccNeSelf
#assert_no_axioms FX1Poly.Tier0.contextPolygraphZeroSkeleton
#assert_no_axioms FX1Poly.Tier0.consGenerator_scopeStrictlyIncreases
#assert_no_axioms FX1Poly.Tier0.lockConsGenerator_scopeStrictlyIncreases

-- Honesty markers + smokes
#assert_no_axioms FX1Poly.Tier0.fxContextPolygraph_hasFinitePresentation
#assert_no_axioms FX1Poly.Tier0.fxContextPolygraph_hasDecidableAdmissibleExtension
#assert_no_axioms FX1Poly.Tier0.fxContextPolygraph_hasFullInfinityOmegaPolygraph
#assert_no_axioms FX1Poly.Tier0.fxContextPolygraph_isOverCoreIotaTable
#assert_no_axioms FX1Poly.Tier0.contextPolygraph_cons_admissible_smoke
#assert_no_axioms FX1Poly.Tier0.contextPolygraph_lockCons_admissible_smoke
#assert_no_axioms FX1Poly.Tier0.contextPolygraph_empty_rejected_smoke

end FX1PolyAudit
