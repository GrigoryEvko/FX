import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.Biequivalence

/-! # FX1PolyAudit/AuditTier0ContextBiequivalence — zero-axiom gate for context-6's shared-base residue

Per-declaration zero-axiom gate for `context-6`'s strictly context-side deliverable
(`FX1Poly/Tier0/Context/Biequivalence.lean`): the contextual-category (Cartmell) / C-system (Voevodsky)
OBJECT-LEVEL structure that is the shared context base of the model biequivalence (CwF ≃ natural model ≃
RMC ≃ CwA ≃ contextual category).

  * `ContextualBaseStructure` — the object-level C-system interface (length grading + root + father +
    extend, with the grading/father laws and structural induction);
  * `length_fatherContext_extendContext` / `extendContext_injective` / `extendContext_length_ne_zero` —
    generic consequences: the father decreases length, extension is injective (NO-CONFUSION), and
    extensions are never the root;
  * `fxBaseScope_isRootOrExtension` — the structural-induction helper on scopes;
  * `fxBaseSubstContextualStructure` — the syntactic context category as a contextual category
    (length = id, root = 0, father = Nat.pred, extend = Nat.succ);
  * the cross-rung bridges — length = `context-5` realization, extend = `context-5` algebra extension,
    father inverts the algebra extension, root = `context-5` empty (= `context-3` initial object).

The type/term presheaves (CwF / natural model / CwA), the representable display map + comprehension
pullback, and the five-way comparison functors realizing the biequivalence are the cross-axis core,
honestly deferred to `fib-8`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The object-level contextual-category interface + its generic no-confusion / grading consequences
#assert_no_axioms FX1Poly.Tier0.ContextualBaseStructure
#assert_no_axioms FX1Poly.Tier0.ContextualBaseStructure.length_fatherContext_extendContext
#assert_no_axioms FX1Poly.Tier0.ContextualBaseStructure.extendContext_injective
#assert_no_axioms FX1Poly.Tier0.ContextualBaseStructure.extendContext_length_ne_zero

-- The syntactic context category as a contextual category (object-level C-system)
#assert_no_axioms FX1Poly.Tier0.fxBaseScope_isRootOrExtension
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstCategory_object_eq_nat
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstContextualStructure

-- The cross-rung bridges: grading = context-5 realization, father/extend/root tie to context-5/3
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstContextualStructure_length_eq_realizeScope
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstContextualStructure_extendContext_eq_algebra
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstContextualStructure_fatherContext_algebra_extendContext
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstContextualStructure_rootContext_eq_empty

end FX1PolyAudit
