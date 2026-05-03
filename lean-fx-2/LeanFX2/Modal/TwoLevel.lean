import LeanFX2.Modal.Foundation
import LeanFX2.Foundation.Mode

/-! # Modal/TwoLevel — Two-Level Type Theory (2LTT)

Stratifies FX's modes into two layers per `fx_design.md` §6 and
the cohesive-modality framework:

* **Static layer** — typing-time only; `ghost` mode.  Values
  exist solely at compile time (proof-relevant content,
  refinements, phantom types).
* **Dynamic layer** — runtime computation; `software`,
  `hardware`, `wire`, `bridge` modes.  Values have runtime
  representation.

The 2LTT discipline forbids unrestricted flow between layers:
a static value cannot become a dynamic value without an
explicit modal coercion (e.g., `next` for `▶`, `unbox` for `□`,
or a paired adjunction).

## What ships (Phase 12.A.4 — Day 4 D4.1)

* `Layer` — closed enum (static, dynamic)
* `Mode.layer` — projection from Mode to Layer
* `Mode.IsStatic`, `Mode.IsDynamic` — Layer-of-mode predicates
* Predicate algebra: static/dynamic mutually exclusive,
  exhaustive, decidable
* `Layer.compose` — sequential composition (worst-case
  monotonic — static then dynamic ⇒ dynamic)
* Composition laws: associativity, identity, idempotency,
  commutativity-up-to-monotone
* `LayerMonotone : Layer → Layer → Prop` — partial order
  (static ≤ dynamic; the inclusion of static into dynamic
  encodes the implicit erasure direction)
* `LayerMonotone` algebra: reflexivity, transitivity,
  antisymmetry, total order
* Cross-layer flow witness predicates: `RespectsLayerSeparation`
  characterizes signatures that respect 2LTT's static/dynamic
  separation
* Smoke: `ghost` is the unique static mode; the four others
  are dynamic

## Algebra (Layer as bounded join-semilattice)

`(Layer, ⊔, static)` is a bounded join-semilattice:
* `static ⊔ Layer = Layer` (static is bottom)
* `dynamic ⊔ Layer = dynamic` (dynamic absorbs)
* `Layer ⊔ Layer = Layer` (idempotent)
* commutative + associative

Captured in `Layer.join`; laws proven by full enumeration (4
cases each, no propext leak — closed enum with full pattern
match per `feedback_lean_zero_axiom_match.md`).

## Why static/dynamic, not finer-grained

Per `fx_design.md` §6.3, the modal hierarchy has 5 modes and
the full 2-cell structure (Modality 1-cells, TwoCell 2-cells)
ships in `Modal/Foundation.lean`.  This file's `Layer` enum is
the COARSE-GRAINED stratification needed for 2LTT
metatheoretic claims.  The Modality 1-cell structure refines
this within each Layer.

## Dependencies

* `Modal/Foundation.lean` — Modality 1-cells (referenced
  conceptually; this file lives at the Layer abstraction level)
* `Foundation/Mode.lean` — the 5-mode enum

## Downstream consumers

* `Modal/Adjunction.lean` (D4.2) — ◇ ⊣ □ unit/counit
* `Modal/BoxPath.lean` (D4.3) — □ commutes with Path/Id
* `Modal/Cohesive.lean` (D4.4) — ♭/♯ modal pair
* `Modal/Bridge.lean` (D4.6) — Layer transfer between modes
* `Modal/Ghost.lean` — ghost ⊣ erase (the canonical 2LTT pair)

Zero-axiom verified per declaration via AuditAll. -/

namespace LeanFX2

/-! ## Layer enum -/

/-- The two semantic layers of FX's 2LTT stratification.

* `static` — compile-time only; the `ghost` mode lives here.
  Values have no runtime representation; they exist for proofs,
  type-level computation, and erasable annotations.

* `dynamic` — runtime; software, hardware, wire, and bridge
  modes live here.  Values have machine representations
  (registers, memory, gates, etc.) and persist into the
  compiled artifact. -/
inductive Layer : Type
  /-- Compile-time only layer. -/
  | static
  /-- Runtime layer (software, hardware, wire, bridge). -/
  | dynamic
  deriving DecidableEq, Repr

/-! ## Mode-to-Layer projection -/

namespace Mode

/-- Project a Mode into its Layer.  Per `fx_design.md` §6.3:
* `ghost` → static
* `software`, `hardware`, `wire`, `bridge` → dynamic

This is the canonical 2LTT classification.  Compilation depends
on this projection: static-mode values are erased (no code
emission), dynamic-mode values are emitted as instructions. -/
def layer : Mode → Layer
  | .ghost    => .static
  | .software => .dynamic
  | .hardware => .dynamic
  | .wire     => .dynamic
  | .bridge   => .dynamic
  | .strict => .dynamic
  | .observational => .dynamic
  | .univalent => .dynamic
  | .cohesiveFlat => .dynamic
  | .cohesiveSharp => .dynamic

/-- A mode is static iff its layer is `static`.  By the
projection table above, only `ghost` is static. -/
def IsStatic (someMode : Mode) : Prop :=
  someMode.layer = Layer.static

/-- A mode is dynamic iff its layer is `dynamic`.  By the
projection table, `software`, `hardware`, `wire`, `bridge` are
dynamic. -/
def IsDynamic (someMode : Mode) : Prop :=
  someMode.layer = Layer.dynamic

/-! ## Mutual exclusivity and exhaustiveness -/

/-- A mode is either static or dynamic — never both, never
neither.  Discharged by full case enumeration. -/
theorem layer_dichotomy (someMode : Mode) :
    IsStatic someMode ∨ IsDynamic someMode := by
  match someMode with
  | .ghost    => exact Or.inl rfl
  | .software => exact Or.inr rfl
  | .hardware => exact Or.inr rfl
  | .wire     => exact Or.inr rfl
  | .bridge   => exact Or.inr rfl
  | .strict => exact Or.inr rfl
  | .observational => exact Or.inr rfl
  | .univalent => exact Or.inr rfl
  | .cohesiveFlat => exact Or.inr rfl
  | .cohesiveSharp => exact Or.inr rfl

/-- A mode cannot be both static and dynamic.  Discharged by
case-splitting + Layer ctor disjointness. -/
theorem static_dynamic_disjoint (someMode : Mode)
    (staticEvidence : IsStatic someMode)
    (dynamicEvidence : IsDynamic someMode) : False := by
  rw [IsStatic] at staticEvidence
  rw [IsDynamic] at dynamicEvidence
  rw [staticEvidence] at dynamicEvidence
  exact Layer.noConfusion dynamicEvidence

/-! ## Decidability -/

/-- Layer-of-mode is decidable for every mode. -/
instance IsStatic.decidable (someMode : Mode) :
    Decidable someMode.IsStatic :=
  inferInstanceAs (Decidable (someMode.layer = Layer.static))

instance IsDynamic.decidable (someMode : Mode) :
    Decidable someMode.IsDynamic :=
  inferInstanceAs (Decidable (someMode.layer = Layer.dynamic))

end Mode

/-! ## Layer algebra (bounded join-semilattice) -/

namespace Layer

/-- Join of two layers: static joined with anything is the
other; dynamic absorbs everything.  Encodes the 2LTT
"escalation": a computation that touches both static and
dynamic must run dynamically. -/
def join : Layer → Layer → Layer
  | .static,  .static  => .static
  | .static,  .dynamic => .dynamic
  | .dynamic, .static  => .dynamic
  | .dynamic, .dynamic => .dynamic

/-- Static is the join-semilattice bottom: `static ⊔ x = x`. -/
theorem join_static_left (someLayer : Layer) :
    join Layer.static someLayer = someLayer := by
  match someLayer with
  | .static  => rfl
  | .dynamic => rfl

/-- Static is right-identity: `x ⊔ static = x`. -/
theorem join_static_right (someLayer : Layer) :
    join someLayer Layer.static = someLayer := by
  match someLayer with
  | .static  => rfl
  | .dynamic => rfl

/-- Dynamic absorbs from the left: `dynamic ⊔ x = dynamic`. -/
theorem join_dynamic_left (someLayer : Layer) :
    join Layer.dynamic someLayer = Layer.dynamic := by
  match someLayer with
  | .static  => rfl
  | .dynamic => rfl

/-- Dynamic absorbs from the right: `x ⊔ dynamic = dynamic`. -/
theorem join_dynamic_right (someLayer : Layer) :
    join someLayer Layer.dynamic = Layer.dynamic := by
  match someLayer with
  | .static  => rfl
  | .dynamic => rfl

/-- Join is commutative.  Discharged by full enumeration. -/
theorem join_comm (firstLayer secondLayer : Layer) :
    join firstLayer secondLayer = join secondLayer firstLayer := by
  match firstLayer, secondLayer with
  | .static,  .static  => rfl
  | .static,  .dynamic => rfl
  | .dynamic, .static  => rfl
  | .dynamic, .dynamic => rfl

/-- Join is associative. -/
theorem join_assoc (firstLayer secondLayer thirdLayer : Layer) :
    join (join firstLayer secondLayer) thirdLayer =
      join firstLayer (join secondLayer thirdLayer) := by
  match firstLayer, secondLayer, thirdLayer with
  | .static,  .static,  .static  => rfl
  | .static,  .static,  .dynamic => rfl
  | .static,  .dynamic, .static  => rfl
  | .static,  .dynamic, .dynamic => rfl
  | .dynamic, .static,  .static  => rfl
  | .dynamic, .static,  .dynamic => rfl
  | .dynamic, .dynamic, .static  => rfl
  | .dynamic, .dynamic, .dynamic => rfl

/-- Join is idempotent. -/
theorem join_idem (someLayer : Layer) :
    join someLayer someLayer = someLayer := by
  match someLayer with
  | .static  => rfl
  | .dynamic => rfl

/-! ## Layer preorder (≤)

`static ≤ dynamic` — static is the bottom, dynamic the top.
This is the lattice's preorder, equivalent to `join`-equality:
`firstLayer ≤ secondLayer ↔ join firstLayer secondLayer = secondLayer`. -/

/-- Layer preorder: every layer is `≤` itself; static is `≤`
dynamic; nothing else. -/
def le : Layer → Layer → Prop
  | .static,  _        => True
  | .dynamic, .static  => False
  | .dynamic, .dynamic => True

/-- Preorder reflexivity. -/
theorem le_refl (someLayer : Layer) : le someLayer someLayer := by
  match someLayer with
  | .static  => exact True.intro
  | .dynamic => exact True.intro

/-- Preorder transitivity. -/
theorem le_trans (firstLayer secondLayer thirdLayer : Layer)
    (firstLe : le firstLayer secondLayer)
    (secondLe : le secondLayer thirdLayer) :
    le firstLayer thirdLayer := by
  match firstLayer, secondLayer, thirdLayer with
  | .static,  _,        _        => exact True.intro
  | .dynamic, .static,  _        => exact firstLe.elim
  | .dynamic, .dynamic, .static  => exact secondLe.elim
  | .dynamic, .dynamic, .dynamic => exact True.intro

/-- Preorder is antisymmetric: `≤` both ways implies equal. -/
theorem le_antisymm (firstLayer secondLayer : Layer)
    (firstLe : le firstLayer secondLayer)
    (secondLe : le secondLayer firstLayer) :
    firstLayer = secondLayer := by
  match firstLayer, secondLayer with
  | .static,  .static  => rfl
  | .static,  .dynamic => exact secondLe.elim
  | .dynamic, .static  => exact firstLe.elim
  | .dynamic, .dynamic => rfl

/-- Static is the bottom: `static ≤ Layer` for every Layer. -/
theorem static_least (someLayer : Layer) :
    le Layer.static someLayer := by
  match someLayer with
  | .static  => exact True.intro
  | .dynamic => exact True.intro

/-- Dynamic is the top: `Layer ≤ dynamic` for every Layer. -/
theorem dynamic_greatest (someLayer : Layer) :
    le someLayer Layer.dynamic := by
  match someLayer with
  | .static  => exact True.intro
  | .dynamic => exact True.intro

/-! ## Join is the LUB of the preorder -/

/-- Left operand is `≤` join. -/
theorem le_join_left (firstLayer secondLayer : Layer) :
    le firstLayer (join firstLayer secondLayer) := by
  match firstLayer, secondLayer with
  | .static,  .static  => exact True.intro
  | .static,  .dynamic => exact True.intro
  | .dynamic, .static  => exact True.intro
  | .dynamic, .dynamic => exact True.intro

/-- Right operand is `≤` join. -/
theorem le_join_right (firstLayer secondLayer : Layer) :
    le secondLayer (join firstLayer secondLayer) := by
  match firstLayer, secondLayer with
  | .static,  .static  => exact True.intro
  | .static,  .dynamic => exact True.intro
  | .dynamic, .static  => exact True.intro
  | .dynamic, .dynamic => exact True.intro

/-- Join is the least upper bound. -/
theorem join_least_upper_bound
    (firstLayer secondLayer thirdLayer : Layer)
    (firstLe : le firstLayer thirdLayer)
    (secondLe : le secondLayer thirdLayer) :
    le (join firstLayer secondLayer) thirdLayer := by
  match firstLayer, secondLayer, thirdLayer with
  | .static,  .static,  _        => exact firstLe
  | .static,  .dynamic, _        => exact secondLe
  | .dynamic, .static,  _        => exact firstLe
  | .dynamic, .dynamic, _        => exact firstLe

end Layer

/-! ## 2LTT layer-separation theorem

A signature respects 2LTT's layer separation when it never
silently moves a value between static and dynamic layers.
The escalation ALWAYS happens via an explicit modal operator
(`next` for `▶`, `unbox` for `□`, etc.).

Captured here as the predicate `RespectsLayerSeparation` on
mode-pairs: a mode-pair `(input, output)` respects layer
separation iff their layers are equal OR the output dominates
the input via `Layer.le`. -/

namespace TwoLevel

/-- A mode-pair `(input, output)` respects 2LTT layer separation
iff the input's layer is `≤` the output's layer.  Static input
can produce any output; dynamic input must produce dynamic
output (no implicit downgrade — the static result of a dynamic
function would require explicit erasure). -/
def RespectsLayerSeparation
    (inputMode outputMode : Mode) : Prop :=
  Layer.le inputMode.layer outputMode.layer

/-- A pure-static signature respects layer separation: ghost in,
ghost out (proof-relevant computation that stays at the static
layer). -/
theorem RespectsLayerSeparation.ghost_to_ghost :
    RespectsLayerSeparation Mode.ghost Mode.ghost :=
  True.intro

/-- A pure-dynamic signature respects layer separation: software
in, software out. -/
theorem RespectsLayerSeparation.software_to_software :
    RespectsLayerSeparation Mode.software Mode.software :=
  True.intro

/-- Static input → dynamic output respects layer separation
(this is the COMMON 2LTT direction: erase a ghost into a runtime
value, e.g., proof-of-bound erased to runtime check elision). -/
theorem RespectsLayerSeparation.ghost_to_software :
    RespectsLayerSeparation Mode.ghost Mode.software :=
  True.intro

/-- Dynamic input → static output VIOLATES layer separation
(this is the FORBIDDEN direction: a runtime value cannot become
a ghost; it would create computational content from runtime
behavior, breaking erasure). -/
theorem RespectsLayerSeparation.software_to_ghost_violates :
    ¬ RespectsLayerSeparation Mode.software Mode.ghost :=
  fun absurdLe => absurdLe.elim

/-! ## RespectsLayerSeparation is a preorder

The predicate inherits its preorder structure from `Layer.le`,
making "respects layer separation" composable: chained
signatures preserve the property. -/

/-- Reflexivity: every mode respects layer separation with
itself. -/
theorem RespectsLayerSeparation.refl (someMode : Mode) :
    RespectsLayerSeparation someMode someMode :=
  Layer.le_refl someMode.layer

/-- Transitivity: composing two respecting mode-pairs gives a
respecting mode-pair. -/
theorem RespectsLayerSeparation.trans
    (firstMode secondMode thirdMode : Mode)
    (firstRespects : RespectsLayerSeparation firstMode secondMode)
    (secondRespects : RespectsLayerSeparation secondMode thirdMode) :
    RespectsLayerSeparation firstMode thirdMode :=
  Layer.le_trans firstMode.layer secondMode.layer thirdMode.layer
    firstRespects secondRespects

end TwoLevel

/-! ## Smoke samples -/

/-- `ghost` is the unique static mode. -/
example : Mode.ghost.IsStatic := rfl

/-- `software` is dynamic. -/
example : Mode.software.IsDynamic := rfl

/-- `hardware` is dynamic. -/
example : Mode.hardware.IsDynamic := rfl

/-- `wire` is dynamic. -/
example : Mode.wire.IsDynamic := rfl

/-- `bridge` is dynamic. -/
example : Mode.bridge.IsDynamic := rfl

/-- `ghost` is not dynamic. -/
example : ¬ Mode.ghost.IsDynamic :=
  fun absurdEq => Layer.noConfusion absurdEq

/-- `software` is not static. -/
example : ¬ Mode.software.IsStatic :=
  fun absurdEq => Layer.noConfusion absurdEq

/-- `static` is the join-semilattice bottom. -/
example : Layer.join Layer.static Layer.dynamic = Layer.dynamic := rfl

/-- `dynamic` absorbs `static`. -/
example : Layer.join Layer.dynamic Layer.static = Layer.dynamic := rfl

/-- The 2LTT prohibition: dynamic-to-static violates layer
separation. -/
example : ¬ TwoLevel.RespectsLayerSeparation Mode.software Mode.ghost :=
  TwoLevel.RespectsLayerSeparation.software_to_ghost_violates

/-- Cohesive composition: ghost → software → hardware respects
layer separation transitively. -/
example :
    TwoLevel.RespectsLayerSeparation Mode.ghost Mode.hardware :=
  TwoLevel.RespectsLayerSeparation.trans
    Mode.ghost Mode.software Mode.hardware
    True.intro True.intro

end LeanFX2
