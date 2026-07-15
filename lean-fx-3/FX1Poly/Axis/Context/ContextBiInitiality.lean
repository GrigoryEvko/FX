import FX1Poly.Axis.Context.Initiality

/-! # context-39 — the context category is BI-INITIAL in the (∞,ω)-category of models (strict residue)

`context-39` (★, on the fib-* arc, →fib-5) asks: is the context category BI-INITIAL in the (∞,ω)-category of
models — for every model, a morphism unique up to coherent equivalence (the recursion / interpretation
principle of the doctrine)?  The FULL theorem is `×type+term`: it threads every former's
substitution-coherence through an intrinsic QIIT presentation whose quotient needs `Quot.sound`, and the
(∞,ω) up-to-coherent-equivalence uniqueness adds higher cells whose naturality needs `funext` — both
off-limits under the zero-axiom discipline (the same boundary as `fib-5c`/`fib-5d`).

This file ships the GENUINELY-REACHABLE residue — the STRICT / OBJECT-LEVEL bi-initiality — by REUSING the
shipped syntactic-model construction (`context-5` `Initiality.lean`: the syntactic context structure
`fxBaseSubstContextAlgebra` is the INITIAL context-extension algebra), re-presented as the bi-initiality
universal property of the context category.  NO new quotient, NO funext.

  * **`context-5`** proved `syntacticRealizationMorphism` is the interpretation morphism OUT of the syntactic
    context structure into ANY model, and `syntacticRealizationMorphism_unique` proves it is the ONLY one
    (existence + uniqueness, the recursor on scopes, zero-axiom; the type/term content abstracted away = the
    `×type+term` deferral).  This is the same syntactic-model shape `fib-5b` (`Core/Fib/BiInitiality.lean`)
    wraps at the assembled kernel; here it is the standalone context-axis universal property.

## What lands here (all zero-axiom)

  * **`ContextModel`** — the structure a model carries (the strict 1-truncation: `context-5`'s object-level
    `ContextExtensionAlgebra` — a carrier of semantic contexts with empty + extend; the (∞,ω) model's higher
    cells abstracted away).
  * **`syntacticContextInitialMorphism`** — ★ the unique STRICT interpreting morphism from the context
    category into any model (`context-5`'s `syntacticRealizationMorphism`, re-presented).
  * **`syntacticContextInitialMorphism_unique`** + **`syntacticContext_interpretation_unique_pointwise`** —
    strict uniqueness (structure-eta on the syntactic generators): every interpreting morphism agrees
    pointwise with it, so any two agree — the strict 1-truncation of the bi-initial "unique up to coherent
    equivalence" (here, up to EQUALITY).
  * **`SyntacticContextBiInitiality`** + **`syntacticContextBiInitiality`** — ★ the packaged STRICT
    BI-INITIALITY datum (existence + pointwise-uniqueness) and its zero-axiom witness.
  * **`syntacticContextInitialMorphism_faithful`** — non-vacuity: the interpreting morphism embeds the
    syntactic scopes FAITHFULLY into a non-trivial model (telescopes), so bi-initiality does not collapse the
    structure.

## What is deferred (the honest wall)

  * The WEAK (∞,ω) BI-INITIALITY — the interpreting morphism's action on substitutions (`×term`), the
    type/term presheaf uniqueness (`×type`), the intrinsic QIIT substitution-coherence quotient
    (`Quot.sound`), and the up-to-coherent-equivalence uniqueness with its higher naturality (`funext`) — is
    NOT shipped (`fxContextBiInitiality_hasWeakInfinityOmegaBiInitiality = false`).  Same boundary as
    `fib-5c`/`fib-5d`.
  * The bi-initiality here is the SELF-CONTAINED Axis residue, NOT a Core `StepOverTable` iota row
    (`fxContextBiInitiality_isOverCoreIotaTable = false`).

Imports only `Initiality` (its `context-5` sibling).  A Axis design-lock must not import up into `Core/` /
`Typed/`.  Zero external dependencies — raw Lean 4 + Init only.

Reference: Brunerie–de Boer–Lumsdaine–Mörtberg, "Initiality for Martin-Löf type theory"; Riehl & Verity,
"Elements of ∞-Category Theory", CUP 2022 (bi-initiality in an ∞-cosmos); the `context-5` initiality
(`Initiality.lean`); the `fib-5b` assembled-kernel form (`Core/Fib/BiInitiality.lean`).
-/

namespace FX1Poly.Axis

/-! ## Models and the interpreting morphism -/

/-- A **model** of the context doctrine — the structure a model carries, at the STRICT / object level: the
data an interpreting morphism is evaluated into, namely `context-5`'s object-level `ContextExtensionAlgebra`
(a carrier of semantic contexts with a chosen empty context and a unary context-extension).  The FULL (∞,ω)
model would add the higher cells / coherences; this is the strict 1-truncation (the `×type+term` content
abstracted away). -/
abbrev ContextModel := ContextExtensionAlgebra.{0}

/-- A **strict interpreting morphism** from the context category into a model — a context-extension
homomorphism out of the syntactic context structure.  (At the (∞,ω) level this would be an (∞,ω)-functor;
the strict 1-truncation is exactly such a homomorphism.) -/
abbrev SyntacticContextMorphismInto (model : ContextModel) :=
  ContextExtensionAlgebraMorphism fxBaseSubstContextAlgebra model

/-- ★ **The unique STRICT interpreting morphism** from the context category into any model — `context-5`'s
`syntacticRealizationMorphism`, re-presented as the bi-initiality structure map.  Existence half: the
recursor on scopes (zero-axiom). -/
def syntacticContextInitialMorphism (model : ContextModel) :
    SyntacticContextMorphismInto model :=
  syntacticRealizationMorphism model

/-- ★ **Strict uniqueness** (the bi-initiality theorem proper, object level): every interpreting morphism out
of the context category into a model agrees pointwise with `syntacticContextInitialMorphism` — there is
exactly one.  `context-5`'s `syntacticRealizationMorphism_unique`, by structure-eta on the syntactic
generators. -/
theorem syntacticContextInitialMorphism_unique (model : ContextModel)
    (other : SyntacticContextMorphismInto model) (scope : Nat) :
    other.mapCarrier scope = (syntacticContextInitialMorphism model).mapCarrier scope :=
  syntacticRealizationMorphism_unique model other scope

/-- The strict 1-truncation of the bi-initial "unique up to coherent equivalence": ANY TWO interpreting
morphisms into a model agree pointwise (up to EQUALITY, the strict form of equivalence).  Both factor through
the unique `syntacticContextInitialMorphism`. -/
theorem syntacticContext_interpretation_unique_pointwise (model : ContextModel)
    (firstMorphism secondMorphism : SyntacticContextMorphismInto model) (scope : Nat) :
    firstMorphism.mapCarrier scope = secondMorphism.mapCarrier scope :=
  (syntacticContextInitialMorphism_unique model firstMorphism scope).trans
    (syntacticContextInitialMorphism_unique model secondMorphism scope).symm

/-! ## The packaged strict bi-initiality datum -/

/-- The **strict bi-initiality datum** of the syntactic context structure in the (∞,ω)-category of models: for
every model an interpreting morphism EXISTS, and it is pointwise-UNIQUE on the syntactic scopes.  The
object-level / strict 1-truncation of the bi-initial universal property; the higher (∞,ω) coherence is
walled. -/
structure SyntacticContextBiInitiality where
  /-- Existence: an interpreting morphism into each model. -/
  interpret : (model : ContextModel) →
    ContextExtensionAlgebraMorphism fxBaseSubstContextAlgebra model
  /-- Uniqueness: every interpreting morphism agrees pointwise with `interpret`. -/
  interpretUnique : (model : ContextModel) →
    (other : ContextExtensionAlgebraMorphism fxBaseSubstContextAlgebra model) →
    (scope : Nat) → other.mapCarrier scope = (interpret model).mapCarrier scope

/-- ★ **The context category is strictly bi-initial.**  The zero-axiom witness assembling the existence
(`syntacticContextInitialMorphism`) and uniqueness (`syntacticContextInitialMorphism_unique`) of the
interpreting morphism — the object-level / strict residue of (∞,ω) bi-initiality, no `Quot.sound`, no
`funext`. -/
def syntacticContextBiInitiality : SyntacticContextBiInitiality where
  interpret := syntacticContextInitialMorphism
  interpretUnique := syntacticContextInitialMorphism_unique

/-! ## Non-vacuity -/

/-- The strict bi-initiality is NON-VACUOUS: the interpreting morphism embeds the syntactic scopes FAITHFULLY
into a non-trivial model (`unaryListAlgebra`, contexts as telescopes of unit-bindings) — distinct scopes have
distinct realizations.  So bi-initiality does not collapse the syntactic context structure. -/
theorem syntacticContextInitialMorphism_faithful {firstScope secondScope : Nat}
    (realizationsAgree :
      (syntacticContextInitialMorphism unaryListAlgebra).mapCarrier firstScope
        = (syntacticContextInitialMorphism unaryListAlgebra).mapCarrier secondScope) :
    firstScope = secondScope :=
  realizeScope_unaryList_injective realizationsAgree

/-! ## Honesty markers -/

/-- **Honesty marker.**  The STRICT / OBJECT-LEVEL bi-initiality of the context category is shipped: for every
model a unique interpreting morphism (existence + pointwise-uniqueness, `syntacticContextBiInitiality`),
reusing `context-5`'s initial syntactic context structure.  `= true`. -/
def fxContextBiInitiality_hasStrictBiInitiality : Bool := true

/-- **Honesty marker.**  The WEAK (∞,ω) BI-INITIALITY — the interpreting morphism's action on substitutions
(`×term`), the type/term presheaf uniqueness (`×type`), the intrinsic QIIT substitution-coherence quotient
(needs `Quot.sound`), and the up-to-coherent-equivalence uniqueness with its higher naturality (needs
`funext`) — is NOT shipped.  Both axioms are off-limits zero-axiom: the same boundary as `fib-5c`/`fib-5d`.
`= false`. -/
def fxContextBiInitiality_hasWeakInfinityOmegaBiInitiality : Bool := false

/-- **Honesty marker.**  This is the SELF-CONTAINED Axis residue of bi-initiality, re-presenting `context-5`'s
object-level initiality; it is NOT a Core table-native row, and gluing it to the assembled kernel (`fib-5b`)
is cross-axis `×type+term`.  `= false`. -/
def fxContextBiInitiality_isOverCoreIotaTable : Bool := false

/-! ## Smoke -/

/-- Smoke: the bi-initiality datum's interpretation of the SYNTACTIC structure into ITSELF is the identity on
scopes — bi-initiality reflexively (the initial object has only the identity endomorphism), surfaced through
the packaged `SyntacticContextBiInitiality`. -/
theorem syntacticContextBiInitiality_interpret_self_identity_smoke (scope : Nat) :
    (syntacticContextBiInitiality.interpret fxBaseSubstContextAlgebra).mapCarrier scope = scope :=
  fxBaseSubstContextAlgebra_realizeScope_id scope

/-- Smoke: any two interpreting morphisms into the telescope model agree at every scope — the strict
up-to-equivalence uniqueness, concrete. -/
theorem syntacticContext_unique_pointwise_smoke
    (firstMorphism secondMorphism : SyntacticContextMorphismInto unaryListAlgebra) (scope : Nat) :
    firstMorphism.mapCarrier scope = secondMorphism.mapCarrier scope :=
  syntacticContext_interpretation_unique_pointwise unaryListAlgebra firstMorphism secondMorphism scope

end FX1Poly.Axis
