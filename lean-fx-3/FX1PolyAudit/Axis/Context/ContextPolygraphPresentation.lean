import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.ContextPolygraphPresentation

/-! # FX1PolyAudit/.../ContextPolygraphPresentation — zero-axiom gate for context-40

Per-declaration zero-axiom gate for `context-40`'s deliverable
(`FX1Poly/Axis/Context/ContextPolygraphPresentation.lean`): the context category as a FINITELY-PRESENTED
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
#assert_no_axioms FX1Poly.Axis.ContextFormer
#assert_no_axioms FX1Poly.Axis.ContextFormer.arity
#assert_no_axioms FX1Poly.Axis.ContextFormer.scopeShift
#assert_no_axioms FX1Poly.Axis.contextFormers
#assert_no_axioms FX1Poly.Axis.contextFormers_length
#assert_no_axioms FX1Poly.Axis.contextFormers_complete
#assert_no_axioms FX1Poly.Axis.contextFormers_exhaustive

-- The free words over the generators
#assert_no_axioms FX1Poly.Axis.ContextExpr
#assert_no_axioms FX1Poly.Axis.ContextExpr.scope

-- The self-contained structural Nat-equality
#assert_no_axioms FX1Poly.Axis.natEq
#assert_no_axioms FX1Poly.Axis.natEq_refl

-- The decidable admissible-extension predicate
#assert_no_axioms FX1Poly.Axis.isAdmissibleExtension
#assert_no_axioms FX1Poly.Axis.isAdmissibleExtension_empty
#assert_no_axioms FX1Poly.Axis.isAdmissibleExtension_cons
#assert_no_axioms FX1Poly.Axis.isAdmissibleExtension_lockCons
#assert_no_axioms FX1Poly.Axis.isAdmissibleExtension_empty_overNonemptyBase
#assert_no_axioms FX1Poly.Axis.IsAdmissibleExtension
#assert_no_axioms FX1Poly.Axis.instDecidableIsAdmissibleExtension
#assert_no_axioms FX1Poly.Axis.contextPolygraph_admissibleExtension_decidable

-- Admissibility grounded in real construction
#assert_no_axioms FX1Poly.Axis.cons_extension_admissible
#assert_no_axioms FX1Poly.Axis.lockCons_extension_admissible
#assert_no_axioms FX1Poly.Axis.empty_extension_admissible

-- The packaged finite presentation
#assert_no_axioms FX1Poly.Axis.ContextPolygraphPresentation
#assert_no_axioms FX1Poly.Axis.contextPolygraph

-- The context-36 0-skeleton bridge + scope-increasing generators
#assert_no_axioms FX1Poly.Axis.natSuccNeSelf
#assert_no_axioms FX1Poly.Axis.contextPolygraphZeroSkeleton
#assert_no_axioms FX1Poly.Axis.consGenerator_scopeStrictlyIncreases
#assert_no_axioms FX1Poly.Axis.lockConsGenerator_scopeStrictlyIncreases

-- Honesty markers + smokes
#assert_no_axioms FX1Poly.Axis.fxContextPolygraph_hasFinitePresentation
#assert_no_axioms FX1Poly.Axis.fxContextPolygraph_hasDecidableAdmissibleExtension
#assert_no_axioms FX1Poly.Axis.fxContextPolygraph_hasFullInfinityOmegaPolygraph
#assert_no_axioms FX1Poly.Axis.fxContextPolygraph_isOverCoreIotaTable
#assert_no_axioms FX1Poly.Axis.contextPolygraph_cons_admissible_smoke
#assert_no_axioms FX1Poly.Axis.contextPolygraph_lockCons_admissible_smoke
#assert_no_axioms FX1Poly.Axis.contextPolygraph_empty_rejected_smoke

end FX1PolyAudit
