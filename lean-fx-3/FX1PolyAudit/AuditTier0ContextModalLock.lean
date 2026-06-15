import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.ModalLock

/-! # FX1PolyAudit/AuditTier0ContextModalLock — zero-axiom gate for context-4's lock leg

Per-declaration zero-axiom gate for `context-4`'s strictly context-side deliverable
(`FX1Poly/Tier0/Context/ModalLock.lean`): the modal lock `◐_μ` carrier structure — `RawEndofunctor`
COMPOSITION (the operation `context-0` left open next to `RawEndofunctor.identity`), the three STRICT
monoid laws (`LOCK` 2-functoriality's strict target `End(𝒞)`), and the generic natural transformation
between locks (the **keys**) with its vertical 2-cell structure.

  * `RawEndofunctor.compose` — composition of locks (`◐_(ν∘μ) = ◐_μ ∘ ◐_ν`), both functor laws proved;
  * `RawEndofunctor.identity_compose` / `compose_identity` / `compose_assoc` — the strict monoid laws,
    so the locks on the context category form a genuine monoid (the one-object strict 2-category);
  * `RawEndofunctorTransformation` — the generic endofunctor nat-trans (the keys), with `identity`,
    vertical composition `vcomp`, and the componentwise unit laws, every naturality square proved.
  * `RawEndofunctorTransformation.whiskerOuter` / `whiskerInner` / `hcomp` + `interchange_component` —
    the full strict 2-category `End(𝒞)`: the two whiskerings, horizontal (Godement) composition of
    keys, and the INTERCHANGE law (the literal target structure of `LOCK` 2-functoriality).

The dependent right adjoint `⟨μ|−⟩` (`IsEndoAdjunction` + its identity/compose/unit/counit + the two
triangle identities certifying `η`/`ε` form a genuine adjunction), the **modal monad**
`T = ⟨μ|◐_μ−⟩` it generates (`modalMultiplication` + the three monad laws), the **modal comonad**
`D = ◐_μ⟨μ|−⟩` (the `□`-necessity; `modalComultiplication` + the three comonad laws, dual to the
monad's), and **RAPL** (the lock preserves the `context-3` initial object + binary coproduct via
`mapInitialObject` / `mapBinaryCoproduct`), the bundled `ContextLock`, and the concrete locks on
`fxBaseSubstCategory`
(`fxIdentityLock` wired to the `context-0` slot via `fxContextAxis_lockOn_eq_identityLock`, plus the
non-trivial `fxWeakeningLock`) are gated below.  The `×mode` family `μ ↦ ◐_μ` indexed by a mode
2-category and the type-indexed DRA over `Core/` are the cross-axis deliverable, deferred to `fib-3`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Composition of locks + the three strict monoid laws (the End(𝒞) monoid)
#assert_no_axioms FX1Poly.Tier0.RawEndofunctor.compose
#assert_no_axioms FX1Poly.Tier0.RawEndofunctor.identity_compose
#assert_no_axioms FX1Poly.Tier0.RawEndofunctor.compose_identity
#assert_no_axioms FX1Poly.Tier0.RawEndofunctor.compose_assoc

-- The keys: the generic natural transformation between locks
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation.identity
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation.vcomp
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation.identity_component
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation.vcomp_component
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation.identity_vcomp_component
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation.vcomp_identity_component

-- The strict 2-category End(𝒞): whiskering, horizontal composition, and the interchange law
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation.whiskerOuter
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation.whiskerInner
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation.hcomp
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation.whiskerOuter_component
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation.whiskerInner_component
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation.hcomp_component
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation.interchange_component

-- The residual strict-2-category coherence: vertical + horizontal associativity, Godement decomp, unit
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation.vcomp_assoc_component
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation.hcomp_assoc_component
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation.hcomp_eq_vcompWhiskers_component
#assert_no_axioms FX1Poly.Tier0.RawEndofunctorTransformation.hcomp_identity_component

-- The dependent right adjoint: the lock-DRA adjunction (hom-bijection form) + its 2-functoriality
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.identity
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.compose

-- The modal unit and counit (η / ε) recovered from the transpose
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.unit
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.counit

-- The inverse-transpose naturalities + the two triangle identities (η/ε form a genuine adjunction)
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.transposeLeft_natural_left
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.transposeLeft_natural_right
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.unit_counit_left_triangle
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.unit_counit_right_triangle

-- The modal monad T = ⟨μ|◐_μ −⟩ generated by the adjunction: multiplication + the three monad laws
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.modalMultiplication
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.modalMonad_leftUnit
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.modalMonad_rightUnit
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.modalMonad_assoc

-- The modal comonad D = ◐_μ⟨μ|−⟩ (the □-necessity): comultiplication + the three comonad laws
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.modalComultiplication
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.modalComonad_counitLeft
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.modalComonad_counitRight
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.modalComonad_coassoc

-- RAPL: the lock (left adjoint) preserves the context-3 colimits (initial object + binary coproduct)
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.mapInitialObject
#assert_no_axioms FX1Poly.Tier0.IsEndoAdjunction.mapBinaryCoproduct

-- The bundled modal lock with its dependent right adjoint + identity lock + lock composition
#assert_no_axioms FX1Poly.Tier0.ContextLock
#assert_no_axioms FX1Poly.Tier0.ContextLock.identity
#assert_no_axioms FX1Poly.Tier0.ContextLock.compose

-- The concrete locks on the FX substitution category + the wiring theorem to context-0's slot
#assert_no_axioms FX1Poly.Tier0.fxIdentityLock
#assert_no_axioms FX1Poly.Tier0.fxContextAxis_lockOn_eq_identityLock
#assert_no_axioms FX1Poly.Tier0.fxWeakeningLock

end FX1PolyAudit
