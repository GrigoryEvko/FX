import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.Biequivalence

/-! # FX1PolyAudit/AuditAxisContextBiequivalence — zero-axiom gate for context-6's shared-base residue

Per-declaration zero-axiom gate for `context-6`'s strictly context-side deliverable
(`FX1Poly/Axis/Context/Biequivalence.lean`): the contextual-category (Cartmell) / C-system (Voevodsky)
OBJECT-LEVEL structure that is the shared context base of the model biequivalence (CwF ≃ natural model ≃
RMC ≃ CwA ≃ contextual category).

  * `ContextualBaseStructure` — the object-level C-system interface (length grading + root + father +
    extend, with the grading/father laws and structural induction);
  * `length_fatherContext_extendContext` (+ strict `_lt`: the WELL-FOUNDED grading measure) /
    `extendContext_injective` / `extendContext_length_ne_zero` — generic consequences: the father
    decreases length (strictly), extension is injective (NO-CONFUSION), extensions are never the root;
  * `length_eq_zero_isRoot` (the UNIQUE root) / `length_fatherContext_of_length_succ` (the
    canonical-projection grading law) / `fatherTower` + `fatherTower_length_eq_root` (the C-system
    `ft`-TOWER: every context descends to the root in exactly `length` father-steps) — the defining
    C-system object axioms, the destructor-side dual of `context-5`'s `realizeScope` build-up;
  * `fxBaseScope_isRootOrExtension` — the structural case-analysis helper on scopes;
  * `fxBaseSubstContextualStructure` — the syntactic context category as a contextual category
    (length = id, root = 0, father = Nat.pred, extend = Nat.succ);
  * `fxBaseSubstContextualInduction` — the C-system INDUCTION PRINCIPLE (the elimination-side dual of
    `context-5`'s `realizeScope` construction), with `_recovers_realizeScope_id` witnessing adequacy;
  * the cross-rung bridges — length = `context-5` realization, extend = `context-5` algebra extension,
    father inverts the algebra extension, root = `context-5` empty (= `context-3` initial object).

The type/term presheaves (CwF / natural model / CwA), the representable display map + comprehension
pullback, and the five-way comparison functors realizing the biequivalence are the cross-axis core,
honestly deferred to `fib-8`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The object-level contextual-category interface + its generic no-confusion / grading consequences
#assert_no_axioms FX1Poly.Axis.ContextualBaseStructure
#assert_no_axioms FX1Poly.Axis.ContextualBaseStructure.length_fatherContext_extendContext
#assert_no_axioms FX1Poly.Axis.ContextualBaseStructure.length_fatherContext_extendContext_lt
#assert_no_axioms FX1Poly.Axis.ContextualBaseStructure.extendContext_injective
#assert_no_axioms FX1Poly.Axis.ContextualBaseStructure.extendContext_length_ne_zero

-- The C-system object axioms: unique root + projection-grading law + the ft-tower reaching the root
#assert_no_axioms FX1Poly.Axis.ContextualBaseStructure.length_eq_zero_isRoot
#assert_no_axioms FX1Poly.Axis.ContextualBaseStructure.length_fatherContext_of_length_succ
#assert_no_axioms FX1Poly.Axis.ContextualBaseStructure.fatherTower
#assert_no_axioms FX1Poly.Axis.ContextualBaseStructure.fatherTower_eq_root_of_length
#assert_no_axioms FX1Poly.Axis.ContextualBaseStructure.fatherTower_length_eq_root

-- The syntactic context category as a contextual category (object-level C-system) + its eliminator
#assert_no_axioms FX1Poly.Axis.fxBaseScope_isRootOrExtension
#assert_no_axioms FX1Poly.Axis.fxBaseSubstCategory_object_eq_nat
#assert_no_axioms FX1Poly.Axis.fxBaseSubstContextualStructure
#assert_no_axioms FX1Poly.Axis.fxBaseSubstContextualInduction
#assert_no_axioms FX1Poly.Axis.fxBaseSubstContextualInduction_recovers_realizeScope_id
#assert_no_axioms FX1Poly.Axis.fxBaseSubstContextualStructure_fatherTower_eq_root

-- The cross-rung bridges: grading = context-5 realization, father/extend/root tie to context-5/3
#assert_no_axioms FX1Poly.Axis.fxBaseSubstContextualStructure_length_eq_realizeScope
#assert_no_axioms FX1Poly.Axis.fxBaseSubstContextualStructure_extendContext_eq_algebra
#assert_no_axioms FX1Poly.Axis.fxBaseSubstContextualStructure_fatherContext_algebra_extendContext
#assert_no_axioms FX1Poly.Axis.fxBaseSubstContextualStructure_rootContext_eq_empty

end FX1PolyAudit
