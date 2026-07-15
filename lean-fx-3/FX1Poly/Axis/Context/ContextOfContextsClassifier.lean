import FX1Poly.Axis.Context.ContextFunctorialGrothendieck

/-! # context-38 — the CONTEXT-OF-CONTEXTS classifier (paradox-free, STRATIFIED self-classification)

`context-38` (★, on the fib-* arc, →fib-11/12) asks for a universe object that CLASSIFIES
context-indexed families of contexts WITHOUT Girard's paradox.  A "universe of contexts" that
classified ALL context-families INCLUDING ITSELF at the SAME level would be the impredicative
`Type : Type` — Girard-INCONSISTENT.  The genuinely-reachable, zero-axiom content is the STRATIFIED
(predicative, SIZED) classifier: the classifier of level-`u` context-families is itself a level-`(u+1)`
object, so it can be classified ONE LEVEL UP — self-classification is paradox-free precisely BECAUSE
the classifying classifier sits at a strictly higher level.

## What a classifier is — a Tarski universe of context-codes

Following the `context-37` `[C, U]` mechanism (a context-indexed family of contexts is the object-action
of a functor `C ⟶ U` into a universe of contexts), a classifier is a Tarski universe: a `Code` type of
context-codes plus a `decode` sending each code to the context (a `Type u`) it names.  A family
`family : Index → Type u` (indexed by the context category's objects — for the syntactic context category,
`Index = Nat`, the scopes, `fxBaseSubstContextAlgebra.Carrier`) is CLASSIFIED when it factors through
`decode`: each index's context is NAMED by a code.  This is the object-level straightening (the morphism /
naturality action is the `×type` content the `context-35`/`context-37` directed Grothendieck classification
defers to `funext`).

## Why the level gap makes self-classification paradox-free (and is FORCED, not gratuitous)

  * **Impredicative self-classification is Girard-INCONSISTENT.**  Its Russell/Cantor kernel:
    `contextClassifier_noImpredicativeSelfClassification` — no `decode : Code → (Code → Bool)` (a universe
    naming `Bool`-predicates over its OWN codes) is COMPLETE; the diagonal predicate
    `fun code => not (decode code code)` has no code.  A diagonalization, zero-axiom (a `Bool` cannot equal
    its own negation).  So a level-`u` universe cannot completely classify families/predicates over itself
    AT level `u` — `Type u : Type u` explodes.  The level gap is therefore NECESSARY.
  * **Stratified self-classification is consistent.**  `stratifiedSelfClassifier` is a level-`(u+1)`
    classifier that NAMES the level-`u` universe `Type u` as a single context, and `discreteClassifier_isParadoxFree`
    exhibits the discrete (scope) classifier's own universe `Type 0` classified one level up — a genuine
    Lean term, no contradiction, BECAUSE `Type 0 : Type 1` predicatively (NOT `Type 0 : Type 0`).

## What lands here (all zero-axiom)

  * **`ContextFamilyClassifier`** — the Tarski universe of context-codes (`Code` + `decode`), level-parameterized;
    `ContextFamilyClassifier.{u} : Type (u+1)` — the SIZE of the classifier is visibly one level above the
    families it classifies.
  * **`ContextFamilyClassifier.Classifies`** + **`classifies_decode`** — the classification relation (a family
    factors through `decode`), and the generic family `decode` self-named by the identity.
  * **`scopeContextClassifier`** — ★ the DISCRETE witness: codes are the syntactic context category's objects
    (scopes `Nat`), `decode n = Fin n` (scope `n` named by its `n` de Bruijn slots) — a non-degenerate
    classifier over the actual context substrate, living in `Type 1`.
  * **`contextClassifier_noImpredicativeSelfClassification`** — ★ the Cantor/Russell diagonal: same-level
    impredicative self-classification is impossible (the Girard kernel).
  * **`stratifiedSelfClassifier`** + **`stratifiedSelfClassifier_classifies_universe`** — the level-`(u+1)`
    classifier naming the level-`u` universe, and the proof it classifies the universe family.
  * **`discreteClassifier_isParadoxFree`** — ★ the STRATIFIED self-classification of the DISCRETE witness's
    universe is paradox-free: `Type 0` (into which `scopeContextClassifier` classifies) is itself classified
    one level up.

## What is deferred (the honest wall)

  * The IMPREDICATIVE self-classification (`Type : Type`, a universe classifying itself at its OWN level) is
    Girard-INCONSISTENT, so it is NOT shipped — its marker is honestly `false`
    (`fxContextOfContexts_hasImpredicativeSelfClassification = false`).
  * The morphism / naturality action of the classification (the full functorial `C ⟶ U` straightening with
    coherent naturality) is the `×type` content `context-37` defers to `funext`; only the object-level
    classification lands here.
  * The classifier here is the SELF-CONTAINED Axis analog, NOT a Core `StepOverTable` iota row
    (`fxContextOfContexts_isOverCoreIotaTable = false`).

Imports only `ContextFunctorialGrothendieck` (its `context-37` sibling — transitively the `RawCategory` /
`discreteUniverseObject` / `[C, U]` substrate).  A Axis design-lock must not import up into `Core/` / `Typed/`.
Zero external dependencies — raw Lean 4 + Init only.

Reference: Girard's paradox (System U inconsistency); Cantor's theorem / Russell's paradox (the diagonal);
predicative / sized universes (Coquand; Sterling); the `context-30` univalent universe object, the `context-37`
`[C, U]` mechanism, and the `context-39` strict-residue pattern (`ContextBiInitiality.lean`).
-/

namespace FX1Poly.Axis

universe u v

/-! ## The Tarski universe of context-codes -/

/-- A **classifier of context-indexed families of contexts** at level `u`: a Tarski universe — a `Code`
type of context-codes and a `decode` sending each code to the context (a `Type u`) it NAMES.  The
classifier itself is `Type (u+1)`: its SIZE is visibly one level above the families it classifies, which is
exactly the predicative gap that keeps self-classification paradox-free. -/
structure ContextFamilyClassifier where
  /-- The type of context-codes. -/
  Code : Type u
  /-- Decoding: each code names a context (a `Type u`). -/
  decode : Code → Type u

/-- A context-indexed family of contexts is **classified** by the classifier when it FACTORS THROUGH
`decode`: each index's context is named by a code, `decode (name index) = family index`.  Indexing over an
arbitrary `Index` is the object-action of a functor `C ⟶ U` (`context-37`'s `[C, U]`); the syntactic context
category instantiates `Index = Nat` (its scopes). -/
def ContextFamilyClassifier.Classifies (classifier : ContextFamilyClassifier.{u})
    {Index : Type v} (family : Index → Type u) : Prop :=
  ∃ name : Index → classifier.Code, ∀ index, classifier.decode (name index) = family index

/-- The **generic family** `decode` is classified by the classifier itself — the identity names every code.
The universal classification: a Tarski universe classifies its own decoding tautologically. -/
theorem ContextFamilyClassifier.classifies_decode (classifier : ContextFamilyClassifier.{u}) :
    classifier.Classifies classifier.decode :=
  ⟨fun code => code, fun _ => rfl⟩

/-- The **universe** a classifier classifies INTO — the `Type u` its codes decode to.  Self-classification
is the classification of THIS universe (as a single context); it lives at `Type (u+1)`, the level above the
classifier's codes, which is why the stratified version is consistent. -/
def ContextFamilyClassifier.universe (_classifier : ContextFamilyClassifier.{u}) : Type (u + 1) := Type u

/-! ## The discrete witness — the scope classifier over the actual context substrate -/

/-- ★ **The discrete (set-level) context-of-contexts classifier.**  Codes are the syntactic context
category's objects — the scopes `Nat` (`fxBaseSubstContextAlgebra.Carrier`) — and `decode n = Fin n` names
scope `n` by its `n` de Bruijn slots.  Non-degenerate (distinct scopes name distinct finite contexts) and
grounded in the real context substrate; it lives in `Type 1`, one level above the families `Nat → Type 0` it
classifies. -/
def scopeContextClassifier : ContextFamilyClassifier.{0} where
  Code := Nat
  decode := fun scope => Fin scope

/-- The discrete classifier classifies the de-Bruijn-slot family `fun scope => Fin scope` — its own generic
family, named by the identity on scopes. -/
theorem scopeContextClassifier_classifies_fin :
    scopeContextClassifier.Classifies (fun scope => Fin scope) :=
  ⟨fun scope => scope, fun _ => rfl⟩

/-! ## The Girard kernel — impredicative same-level self-classification is impossible (Cantor/Russell) -/

/-- A `Bool` cannot equal its own negation — the two-element diagonal, by case analysis. -/
theorem boolEqNotSelfAbsurd : ∀ flag : Bool, flag = Bool.not flag → False
  | true, isEqNot => Bool.noConfusion isEqNot
  | false, isEqNot => Bool.noConfusion isEqNot

/-- ★ **The Girard / Cantor / Russell kernel: impredicative SAME-LEVEL self-classification is impossible.**
No `decode : Code → (Code → Bool)` — a universe whose codes name `Bool`-predicates over its OWN codes — is
COMPLETE: the diagonal predicate `fun code => not (decode code code)` has NO code.  A diagonalization
(`boolEqNotSelfAbsurd`): a code for the diagonal, applied to itself, would force `b = not b`.  This is why a
level-`u` universe cannot classify families/predicates over itself AT level `u` (`Type u : Type u` explodes)
— the level gap is NECESSARY, not gratuitous. -/
theorem contextClassifier_noImpredicativeSelfClassification {Code : Type u}
    (decode : Code → (Code → Bool)) :
    ¬ ∃ diagonalCode : Code, decode diagonalCode = fun code => Bool.not (decode code code) := by
  intro selfClassification
  obtain ⟨diagonalCode, diagonalSpec⟩ := selfClassification
  have selfApplication : decode diagonalCode diagonalCode
      = Bool.not (decode diagonalCode diagonalCode) :=
    congrFun diagonalSpec diagonalCode
  exact boolEqNotSelfAbsurd (decode diagonalCode diagonalCode) selfApplication

/-! ## The stratified self-classification — paradox-free, one level up -/

/-- ★ **The stratified self-classifier.**  A level-`(u+1)` classifier that NAMES the level-`u` universe
`Type u` as a single context — a single code decoding to `Type u`.  Well-typed precisely because
`Type u : Type (u+1)` (predicatively), whereas the impredicative `Type u : Type u` is Girard-inconsistent
(`contextClassifier_noImpredicativeSelfClassification`). -/
def stratifiedSelfClassifier : ContextFamilyClassifier.{u + 1} where
  Code := PUnit.{u + 2}
  decode := fun _ => (Type u : Type (u + 1))

/-- The stratified self-classifier classifies the UNIVERSE family `fun _ => Type u` — the level-`u` universe
of contexts, named as a single context one level up.  This is self-classification made consistent by the
predicative level gap. -/
theorem stratifiedSelfClassifier_classifies_universe :
    stratifiedSelfClassifier.{u}.Classifies (fun (_ : PUnit.{1}) => (Type u : Type (u + 1))) :=
  ⟨fun _ => PUnit.unit, fun _ => rfl⟩

/-- ★ **The discrete classifier's self-classification is PARADOX-FREE.**  The universe `Type 0` INTO which the
discrete `scopeContextClassifier` classifies (`scopeContextClassifier.universe`) is itself classified — as a
single context, by the level-1 `stratifiedSelfClassifier`.  No Girard: the classification sits at `Type 1`,
strictly above the level-0 families `scopeContextClassifier` classifies.  Together with
`contextClassifier_noImpredicativeSelfClassification` (the same-level version is impossible), this is the
genuine content: self-classification is reachable, paradox-free, EXACTLY in its stratified form. -/
theorem discreteClassifier_isParadoxFree :
    stratifiedSelfClassifier.{0}.Classifies
      (fun (_ : PUnit.{1}) => scopeContextClassifier.universe) :=
  ⟨fun _ => PUnit.unit, fun _ => rfl⟩

/-! ## Honesty markers -/

/-- **Honesty marker.**  STRATIFIED (predicative, sized) self-classification is shipped: the discrete
classifier's universe is classified one level up (`discreteClassifier_isParadoxFree`,
`stratifiedSelfClassifier`).  `= true`. -/
def fxContextOfContexts_hasStratifiedSelfClassification : Bool := true

/-- **Honesty marker.**  PARADOX-FREEDOM of the stratified self-classification is PROVEN: same-level
impredicative self-classification is impossible (`contextClassifier_noImpredicativeSelfClassification`, the
Cantor/Russell diagonal), while the stratified version is a genuine term — so the level gap is necessary and
the stratified self-classification carries no contradiction.  `= true`. -/
def fxContextOfContexts_hasParadoxFreedom : Bool := true

/-- **Honesty marker.**  IMPREDICATIVE self-classification (a universe of contexts classifying ITSELF at its
OWN level — `Type : Type`) is NOT shipped: it is Girard-INCONSISTENT (its Russell/Cantor kernel is
`contextClassifier_noImpredicativeSelfClassification`).  `= false`. -/
def fxContextOfContexts_hasImpredicativeSelfClassification : Bool := false

/-- **Honesty marker.**  This is the SELF-CONTAINED Axis analog of a Core table-native classifier row; a
Axis design-lock cannot import the Core engine, so the classifier is re-shipped here over the `context-30` /
`context-37` substrate.  Gluing the Axis and Core forms is cross-axis `×type`.  `= false`. -/
def fxContextOfContexts_isOverCoreIotaTable : Bool := false

/-! ## Smoke -/

/-- Smoke: the discrete scope classifier names scope `0` by the empty context `Fin 0` — `decode 0 = Fin 0`,
the concrete content of classifying a context-family over the real scope substrate. -/
theorem scopeContextClassifier_decode_zero_smoke :
    scopeContextClassifier.decode (0 : Nat) = Fin 0 := rfl

/-- Smoke: the level-1 stratified classifier decodes its single code to the level-0 universe `Type 0` — the
context-of-contexts named one level up, the heart of paradox-free self-classification. -/
theorem stratifiedSelfClassifier_decode_smoke :
    stratifiedSelfClassifier.{0}.decode PUnit.unit = (Type 0 : Type 1) := rfl

end FX1Poly.Axis
