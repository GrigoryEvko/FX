import FX1Poly.Axis.Context.Initiality

/-! # context-6 — the shared context base of the model biequivalence (contextual-category residue)

`context-6` is the BIEQUIVALENCE rung: the many notions of a model of dependent type theory —
category with families (CwF), natural model (Awodey), representable map category (Uemura, RMC), category
with attributes (Cartmell, CwA), and contextual category / C-system (Cartmell / Voevodsky) — are all
BIEQUIVALENT (Ahrens–Lumsdaine–North, Newstead).  The full biequivalence is `×type+term`: each of the
five notions packages the TYPES and TERMS fibred over the context base, and the equivalences are the
type/term comparison functors plus their coherences (an honest construction needs the comprehension
universal property and a substitution-coherence quotient).  That core defers to `fib-8`.

This file ships the strictly CONTEXT-SIDE residue — the one fragment of the five notions that lives
purely on the BASE of contexts, with the type/term presheaves abstracted away:

  the CONTEXTUAL-CATEGORY object structure (Cartmell's "contextual category" / Voevodsky's C-system,
  restricted to its action on context OBJECTS): a LENGTH grading, a unique ROOT (empty) context, and a
  FATHER operation that drops the last binding.

This is exactly the part of "contextual category" (one of the five biequivalent notions) that does not
mention types — and it is what the biequivalence's SHARED context base amounts to.  The pieces:

  * `ContextualBaseStructure` — the object-level C-system interface over the context-object type:
    `length`, `rootContext`, `fatherContext`, `extendContext`, with the three grading/father laws and
    the structural induction `isRootOrExtension` (every context is the root or an extension of its
    father).  The morphism-level DISPLAY MAP `p : Γ.A → Γ` and the comprehension PULLBACK (where
    types/terms enter) are the `×type+term` core deferred to `fib-8`.
  * `extendContext_injective` / `extendContext_length_ne_zero` — the abstract axioms already force
    NO-CONFUSION of contexts (father is a retraction of extend) and that extensions are never the root.
  * `fxBaseSubstContextualStructure` — the SYNTACTIC context structure as a contextual category over the
    context category's objects (`fxBaseSubstCategory.Object = Nat`, `fxBaseSubstCategory_object_eq_nat`):
    `length = id`, `rootContext = 0`, `fatherContext = Nat.pred`, `extendContext = Nat.succ`.
  * the cross-rung BRIDGES — `length = realizeScope` (the grading IS `context-5`'s realization),
    `fatherContext` inverts `context-5`'s algebra extension (father is the destructor dual to
    `context-5`'s constructor), and `rootContext = emptyContext` (= `context-3`'s initial object).

So `fxBaseSubstCategory` carries all of: `context-0`'s representable-map-category base, `context-5`'s
initial context-extension algebra (constructor side), and `context-6`'s contextual-category grading
(destructor side) — ONE shared context base, exactly as the biequivalence requires.

DEFERRED to `fib-8` (`×type+term`, honestly NOT shipped here): the type/term presheaves of CwF / natural
model / CwA, the representable display map and the comprehension pullback, and the comparison functors
realizing the five-way biequivalence with their coherences.  `context-6` is the prerequisite of
`context-5` (#1539) and only the shared-context-base residue is unconditional and lands now. -/

namespace FX1Poly.Axis

universe u

/-- The OBJECT-LEVEL structure of a contextual category (Cartmell) / C-system (Voevodsky) over the type
of context objects: a `length` grading into `Nat`, a `rootContext` (the empty context, length 0), a
`fatherContext` operation (drop the last binding), and the `extendContext` operation it inverts.  The
laws are the grading laws plus `isRootOrExtension` (every context is the root or its father extended) —
the structural-induction / no-confusion content.  The morphism-level display map and comprehension
pullback (where TYPES enter) are abstracted away: that is the `×type+term` content of `fib-8`. -/
structure ContextualBaseStructure (ContextObject : Type u) where
  /-- The length grading: how many bindings a context carries. -/
  length : ContextObject → Nat
  /-- The root: the empty / terminal context, the unique length-0 object. -/
  rootContext : ContextObject
  /-- The father: drop the last binding (the canonical projection's codomain). -/
  fatherContext : ContextObject → ContextObject
  /-- Context extension: add one binding (the object-action of comprehension). -/
  extendContext : ContextObject → ContextObject
  /-- The root has length 0. -/
  length_root : length rootContext = 0
  /-- Extension increments the length. -/
  length_extend : ∀ object, length (extendContext object) = length object + 1
  /-- The father inverts extension (father is the destructor dual to the extension constructor). -/
  father_extend : ∀ object, fatherContext (extendContext object) = object
  /-- Structural induction: every context is the root or its father extended (no third shape). -/
  isRootOrExtension :
    ∀ object, object = rootContext ∨ object = extendContext (fatherContext object)

/-- The father decreases the length of an extension back to the predecessor's (a derived grading law,
generic over any contextual base). -/
theorem ContextualBaseStructure.length_fatherContext_extendContext
    {ContextObject : Type u} (contextualBase : ContextualBaseStructure ContextObject)
    (object : ContextObject) :
    contextualBase.length (contextualBase.fatherContext (contextualBase.extendContext object))
      = contextualBase.length object :=
  congrArg contextualBase.length (contextualBase.father_extend object)

/-- **The grading is a well-founded measure**: stepping to the father of an extension strictly
decreases the length.  This is the data that contexts are built bottom-up from the root by finitely
many extensions — the well-foundedness that justifies induction over contexts.  Generic over any
contextual base, zero-axiom (no `WellFounded.fix`). -/
theorem ContextualBaseStructure.length_fatherContext_extendContext_lt
    {ContextObject : Type u} (contextualBase : ContextualBaseStructure ContextObject)
    (object : ContextObject) :
    contextualBase.length (contextualBase.fatherContext (contextualBase.extendContext object))
      < contextualBase.length (contextualBase.extendContext object) := by
  rw [contextualBase.length_fatherContext_extendContext, contextualBase.length_extend]
  exact Nat.le.refl

/-- **No-confusion of contexts**: the contextual axioms alone force context extension to be INJECTIVE
— two contexts with the same one-binding extension are equal, because the father is a retraction of
extend.  Generic over any contextual base. -/
theorem ContextualBaseStructure.extendContext_injective
    {ContextObject : Type u} (contextualBase : ContextualBaseStructure ContextObject)
    {firstObject secondObject : ContextObject}
    (extensionsAgree :
      contextualBase.extendContext firstObject = contextualBase.extendContext secondObject) :
    firstObject = secondObject :=
  (contextualBase.father_extend firstObject).symm.trans
    ((congrArg contextualBase.fatherContext extensionsAgree).trans
      (contextualBase.father_extend secondObject))

/-- An extension is never the root: its length is a successor, hence nonzero.  Generic over any
contextual base. -/
theorem ContextualBaseStructure.extendContext_length_ne_zero
    {ContextObject : Type u} (contextualBase : ContextualBaseStructure ContextObject)
    (object : ContextObject)
    (lengthIsZero : contextualBase.length (contextualBase.extendContext object) = 0) : False :=
  Nat.noConfusion ((contextualBase.length_extend object).symm.trans lengthIsZero)

/-- **The root is the UNIQUE length-0 object**: any context of length 0 IS the root.  Together with
`length_root` (the root has length 0) this is the defining C-system axiom that `rootContext` is the
sole length-0 object.  Generic over any contextual base, zero-axiom. -/
theorem ContextualBaseStructure.length_eq_zero_isRoot
    {ContextObject : Type u} (contextualBase : ContextualBaseStructure ContextObject)
    {object : ContextObject} (lengthIsZero : contextualBase.length object = 0) :
    object = contextualBase.rootContext := by
  rcases contextualBase.isRootOrExtension object with isRoot | isExtension
  · exact isRoot
  · exfalso
    apply contextualBase.extendContext_length_ne_zero (contextualBase.fatherContext object)
    rw [← isExtension]
    exact lengthIsZero

/-- **The canonical projection drops the length by one**: on a non-root object (length a successor),
the father has the predecessor's length.  This is the grading law of the C-system's display map
`p : Γ.A → Γ` (each projection peels one binding).  Generic over any contextual base, zero-axiom. -/
theorem ContextualBaseStructure.length_fatherContext_of_length_succ
    {ContextObject : Type u} (contextualBase : ContextualBaseStructure ContextObject)
    {object : ContextObject} {predecessorLength : Nat}
    (lengthIsSucc : contextualBase.length object = predecessorLength + 1) :
    contextualBase.length (contextualBase.fatherContext object) = predecessorLength := by
  rcases contextualBase.isRootOrExtension object with isRoot | isExtension
  · rw [isRoot, contextualBase.length_root] at lengthIsSucc
    exact Nat.noConfusion lengthIsSucc
  · have lengthIsExtendSucc : contextualBase.length object
        = contextualBase.length (contextualBase.fatherContext object) + 1 :=
      (congrArg contextualBase.length isExtension).trans
        (contextualBase.length_extend (contextualBase.fatherContext object))
    rw [lengthIsExtendSucc] at lengthIsSucc
    exact Nat.succ.inj lengthIsSucc

/-- Iterating the father `steps` times.  Specialized to `steps = length object` (see
`fatherTower_length_eq_root`) this is Voevodsky's C-system `ft`-tower: the canonical-projection chain
descending a context to the root. -/
def ContextualBaseStructure.fatherTower {ContextObject : Type u}
    (contextualBase : ContextualBaseStructure ContextObject) :
    Nat → ContextObject → ContextObject
  | 0, object => object
  | steps + 1, object => contextualBase.fatherTower steps (contextualBase.fatherContext object)

/-- The length-indexed `ft`-tower lands on the root: iterating the father `length object` times (here
parameterized by a matching `steps`) reaches `rootContext`.  Structural recursion on `steps`,
zero-axiom. -/
theorem ContextualBaseStructure.fatherTower_eq_root_of_length
    {ContextObject : Type u} (contextualBase : ContextualBaseStructure ContextObject) :
    ∀ (steps : Nat) (object : ContextObject), contextualBase.length object = steps →
      contextualBase.fatherTower steps object = contextualBase.rootContext
  | 0, _object, lengthEq => contextualBase.length_eq_zero_isRoot lengthEq
  | steps + 1, object, lengthEq =>
      contextualBase.fatherTower_eq_root_of_length steps (contextualBase.fatherContext object)
        (contextualBase.length_fatherContext_of_length_succ lengthEq)

/-- **The `ft`-tower reaches the root**: every context descends to the root in exactly `length object`
father-steps.  This is the C-system's defining structural axiom — contexts are finite towers of
bindings over the unique root — and the destructor-side dual of `context-5`'s `realizeScope`
build-up.  Generic over any contextual base, zero-axiom. -/
theorem ContextualBaseStructure.fatherTower_length_eq_root
    {ContextObject : Type u} (contextualBase : ContextualBaseStructure ContextObject)
    (object : ContextObject) :
    contextualBase.fatherTower (contextualBase.length object) object = contextualBase.rootContext :=
  contextualBase.fatherTower_eq_root_of_length (contextualBase.length object) object rfl

/-- Every syntactic scope is the root (`0`) or the successor of its predecessor — the structural
induction principle the contextual category needs.  Total 2-case analysis on `Nat`, zero-axiom. -/
theorem fxBaseScope_isRootOrExtension :
    ∀ scope : Nat, scope = 0 ∨ scope = Nat.succ (Nat.pred scope)
  | 0 => Or.inl rfl
  | _scope + 1 => Or.inr rfl

/-- The context category's objects are the scopes (`Nat`) — the anchor tying the contextual structure
below back to `fxBaseSubstCategory` (the morphism-level display map over this category is deferred). -/
theorem fxBaseSubstCategory_object_eq_nat : fxBaseSubstCategory.Object = Nat := rfl

/-- The SYNTACTIC context structure as a CONTEXTUAL CATEGORY (object-level C-system) over the context
category's objects (`Nat`, by `fxBaseSubstCategory_object_eq_nat`): the length grading is the identity
(scope `n` has length `n`), the root is the empty context (scope `0`), the father drops the last binding
(`Nat.pred`), and extension adds one (`Nat.succ`).  Every law holds by computation, zero-axiom. -/
def fxBaseSubstContextualStructure : ContextualBaseStructure Nat where
  length := fun object => object
  rootContext := 0
  fatherContext := Nat.pred
  extendContext := Nat.succ
  length_root := rfl
  length_extend := fun _object => rfl
  father_extend := fun _object => rfl
  isRootOrExtension := fxBaseScope_isRootOrExtension

/-- **The contextual-category INDUCTION PRINCIPLE** for the syntactic structure: to prove a property of
every context it suffices to prove it for the root and to propagate it across one extension.  This is
the C-system's defining elimination principle — the dual of `context-5`'s `realizeScope` CONSTRUCTION
(both over the same `Nat` of scopes): `realizeScope` folds a model UP from the generators, this folds a
proof DOWN over them.  Computed as structural recursion (`Nat.rec`), zero-axiom. -/
theorem fxBaseSubstContextualInduction (motive : Nat → Prop)
    (atRoot : motive fxBaseSubstContextualStructure.rootContext)
    (atExtend :
      ∀ context, motive context → motive (fxBaseSubstContextualStructure.extendContext context)) :
    ∀ context, motive context
  | 0 => atRoot
  | context + 1 => atExtend context (fxBaseSubstContextualInduction motive atRoot atExtend context)

/-- **Cross-rung bridge**: the contextual category's length grading IS `context-5`'s realization — the
length of a context is its realization into the syntactic algebra (which is the scope itself).  Ties
the destructor-side grading to the constructor-side recursion. -/
theorem fxBaseSubstContextualStructure_length_eq_realizeScope (object : Nat) :
    fxBaseSubstContextualStructure.length object
      = fxBaseSubstContextAlgebra.realizeScope object :=
  (fxBaseSubstContextAlgebra_realizeScope_id object).symm

/-- **Cross-rung bridge**: the contextual category's extension is `context-5`'s algebra extension (both
are `Nat.succ`).  The two rungs describe ONE extension structure — `context-5` from the constructor
side, `context-6` from the destructor side. -/
theorem fxBaseSubstContextualStructure_extendContext_eq_algebra (object : Nat) :
    fxBaseSubstContextualStructure.extendContext object
      = fxBaseSubstContextAlgebra.extendContext object :=
  rfl

/-- **Cross-rung bridge**: the contextual father is the genuine LEFT INVERSE of `context-5`'s algebra
extension — father is the destructor dual to the extension constructor of the initial algebra. -/
theorem fxBaseSubstContextualStructure_fatherContext_algebra_extendContext (object : Nat) :
    fxBaseSubstContextualStructure.fatherContext (fxBaseSubstContextAlgebra.extendContext object)
      = object :=
  rfl

/-- **Cross-rung bridge**: the contextual category's root is `context-5`'s empty context, which is in
turn `context-3`'s initial object (`fxBaseSubstInitial`).  All notions agree on the empty context. -/
theorem fxBaseSubstContextualStructure_rootContext_eq_empty :
    fxBaseSubstContextualStructure.rootContext = fxBaseSubstContextAlgebra.emptyContext :=
  rfl

/-- **The contextual eliminator is adequate**: the `context-6` induction principle reproves `context-5`'s
realization identity (`realizeScope c = c`) — anything `context-5` established by raw `Nat.rec` over the
scopes is reachable by the `context-6` contextual induction.  A non-vacuous witness that the elimination
principle fires (root arm = `realizeScope_zero`, extension arm consumes the inductive hypothesis through
`realizeScope_succ`). -/
theorem fxBaseSubstContextualInduction_recovers_realizeScope_id :
    ∀ context, fxBaseSubstContextAlgebra.realizeScope context = context :=
  fxBaseSubstContextualInduction
    (fun context => fxBaseSubstContextAlgebra.realizeScope context = context)
    fxBaseSubstContextAlgebra.realizeScope_zero
    (fun context inductiveHypothesis => by
      show fxBaseSubstContextAlgebra.realizeScope (context + 1)
        = fxBaseSubstContextAlgebra.extendContext context
      rw [fxBaseSubstContextAlgebra.realizeScope_succ, inductiveHypothesis])

/-- **The syntactic `ft`-tower computes**: iterating the father (`Nat.pred`) `scope`-many times from a
scope of length `scope` reaches the empty context (`0`).  The concrete C-system spine for the syntactic
context category — every scope is a finite tower of bindings over the root. -/
theorem fxBaseSubstContextualStructure_fatherTower_eq_root (scope : Nat) :
    fxBaseSubstContextualStructure.fatherTower scope scope
      = fxBaseSubstContextualStructure.rootContext :=
  fxBaseSubstContextualStructure.fatherTower_length_eq_root scope

end FX1Poly.Axis
