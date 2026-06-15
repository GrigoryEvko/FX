import FX1Poly.Tier0.Context.Initiality

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

namespace FX1Poly.Tier0

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

end FX1Poly.Tier0
