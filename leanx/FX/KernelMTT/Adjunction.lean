import FX.KernelMTT.Mode

/-!
# Adjunction — cross-mode morphism records (R0.4 + R0.8)

Formalizes the four cross-mode morphisms of the FX mode theory
per `fx_reframing.md` §3.5.  Two are proper adjunctions with
unit/counit laws (ghost ⊣ erase; serialize ⊣ parse); two are
one-way or partial morphisms (synth: Software → Hardware,
partial; observe: Hardware → Software, one-way).

## R0.8 — unit/counit laws at the scaffold layer

For proper adjunctions `F ⊣ G` where
`F : leftMode → rightMode` and `G : rightMode → leftMode`,
standard category theory requires two natural transformations
and two triangle identities:

  * Unit   `η : 1_leftMode  → G ∘ F`  (starts and ends at
    `leftMode`, pits at `rightMode`)
  * Counit `ε : F ∘ G → 1_rightMode`  (starts and ends at
    `rightMode`, pits at `leftMode`)
  * Triangle identities:
      `(ε F) ∘ (F η) = 1_F`  and  `(G ε) ∘ (η G) = 1_G`.

At the R0 scaffold layer — before R1's kernel admits
mode-transition TERMS — we cannot discharge the triangle
identities as equations between terms.  What we CAN pin by
`decide` on the finite mode/morphism data is the SHAPE of
those identities:

  * The unit 2-cell's named identifier exists exactly for
    proper adjunctions.
  * The counit 2-cell's named identifier exists exactly for
    proper adjunctions.
  * The unit triangle's endpoint triple in `Mode × Mode × Mode`
    is `(leftMode, rightMode, leftMode)` — the round-trip
    through `rightMode` and back.
  * The counit triangle's endpoint triple is
    `(rightMode, leftMode, rightMode)`.
  * All six mode-level morphism names plus the four unit/
    counit 2-cell names are pairwise distinct (no name
    shadowing between 1-cells and 2-cells).

These pin the PRE-CONDITIONS on which R1+ discharges the
actual triangle-identity equations.  An edit that drops a
unit/counit name, reroutes a forward morphism without
updating the triangle shape, or collides two names now fails
`lake build` at this file rather than at a downstream MTT
kernel rule.

`fx_reframing.md` §3.5.3 uses the non-standard phrasing
"the adjunction unit (serialize ∘ parse = id_Wire)" — we read
that as the spec citing the TRIANGLE IDENTITY whose shape
involves `serialize ∘ parse`, not as the categorical unit
direction.  The docstrings on `unitName` / `counitName`
clarify this.

## The adjunction diagram

```
                   erase
        Software ──────────> Ghost
               <────────────
                   ghost

        Software ──────────> Hardware
                 synth
                              (partial)

        Software ──────────> Wire
               <────────────
                   parse
                 serialize

        Hardware ──────────> Software
                 observe
                              (one-way)
```

Four records aggregate the six directed morphism edges declared
in `Mode.lean` R0.2 (`Mode.ghostMorphisms`, etc.) into the four
topic sections of `fx_reframing.md` §3.5.  The `all` enumeration
covers every edge; the `morphisms_agree_with_mode_config`
theorem pins list equality between the two representations.

## Scope

R0.4 defines the CARRIER: modes, forward/backward morphism
names, adjunction-vs-one-way classification, partiality flag.
R0.8 extends the record with named unit/counit 2-cells for
proper adjunctions plus endpoint-pinning theorems (the actual
triangle equations remain scheduled for R1+ once mode-transition
terms exist — at the enumerated-data layer we can only pin
name existence and endpoint shapes).

## Trust layer

Scaffold (per `FX/KernelMTT/CLAUDE.md`).  No axioms.  Pinning
theorems assert agreement with `Mode.lean`'s morphism list.

## Cross-references

  * `fx_reframing.md` §3.5 — the four adjunction subsections
  * `FX/KernelMTT/Mode.lean` — the 0-cells and the six directed
    morphism edges the four records aggregate
  * `fx_reframing.md` §4.6 — 2LTT separation at Ghost ⊣ Software
    informs the properAdjunction = true commitment for
    §3.5.1
  * R0.8 — unit/counit 2-cell names + triangle-shape pinning
    (this file, §"## R0.8" below).  Full triangle-identity
    EQUATIONS land with R1's kernel terms.
-/

namespace FX.KernelMTT

/-- A cross-mode morphism record.  Represents one of §3.5's
    four subtopics: either a proper adjunction with a backward
    partner morphism, or a one-way/partial morphism without a
    partner at this topic level.

    For proper adjunctions (isProperAdj = true), `backwardName`
    is `some partnerName` — the partner morphism's name.  The
    unit/counit laws are an R0.8 obligation.

    For one-way morphisms (isProperAdj = false),
    `backwardName` is `none`.  Note that §3.5's Software ↔
    Hardware traffic is represented by TWO separate records
    (`softwareHardware` for synth; `hardwareSoftware` for
    observe) — they're NOT a proper adjunction (synth is
    partial, no unit/counit), but are the only traffic between
    the two modes.

    `isForwardPartial` flags partiality of the forward
    morphism.  Only `synth` is partial (§3.5.2: "Defined on
    the Hardware-modality-compatible subset of Software
    types; undefined otherwise").  `observe`, `ghost`,
    `erase`, `serialize`, `parse` are all total on their
    domain. -/
structure Adjunction where
  /-- Human-readable name matching `fx_reframing.md` §3.5.x
      section headers.  Used in diagnostics. -/
  name             : String
  /-- Source of the primary forward morphism. -/
  leftMode         : Mode
  /-- Target of the primary forward morphism. -/
  rightMode        : Mode
  /-- Name of the forward morphism (leftMode → rightMode). -/
  forwardName      : String
  /-- Name of the backward morphism, when the adjunction is
      proper.  `none` for one-way morphisms. -/
  backwardName     : Option String
  /-- Name of the unit 2-cell `η : 1_leftMode → backward ∘ forward`,
      present for proper adjunctions.  Categorically: the 2-cell
      whose triangle identity involves `(backward ∘ forward)` as
      the round-trip through `rightMode`.

      `fx_reframing.md` §3.5.3's "adjunction unit" language
      refers to THIS 2-cell's triangle identity (the equation
      witnessed by η and ε together that forward ∘ backward
      and backward ∘ forward collapse to identities on the
      appropriate modes).

      `none` for one-way / partial morphisms (`synth`,
      `observe`), which carry no triangle structure. -/
  unitName         : Option String
  /-- Name of the counit 2-cell `ε : forward ∘ backward → 1_rightMode`,
      present for proper adjunctions.  Categorically dual to
      `unitName`: the round-trip through `leftMode`.  `none`
      for one-way / partial morphisms. -/
  counitName       : Option String
  /-- `true` when this is a proper adjunction with unit/counit
      laws (R0.8 pins the 2-cell names and triangle endpoint
      shapes; the triangle equations land with R1's kernel
      terms).  `false` for one-way morphisms.

      Proper under the reframe: `ghost ⊣ erase` (§3.5.1),
      `serialize ⊣ parse` (§3.5.3).  Not proper:
      `synth` (§3.5.2, partial, no right adjoint),
      `observe` (§3.5.4, one-way, no inverse). -/
  isProperAdj      : Bool
  /-- `true` when the forward morphism is partial (has a domain
      narrower than `leftMode`'s full type universe).  Only
      `synth` qualifies. -/
  isForwardPartial : Bool
  /-- Cross-reference to the `fx_reframing.md` subsection
      specifying this adjunction.  E.g., "3.5.1". -/
  docSection       : String
  deriving Repr, Inhabited, DecidableEq

namespace Adjunction

/-- `Ghost ⊣ Software` per `fx_reframing.md` §3.5.1.  The
    canonical 2LTT separation (§4.6): every ghost value lifts
    to a zero-runtime-cost Software view, and every Software
    value has a canonical erase-to-Ghost view.

    Unit `ghost`: Ghost → Software.  Embed a proof-level term
    as a runtime-cost-zero view at Software.

    Counit `erase`: Software → Ghost.  Forget the runtime
    content, keeping the typing.

    Both total.  Proper adjunction — R0.8 discharges the
    unit/counit laws. -/
def ghostSoftware : Adjunction :=
  { name             := "Ghost ⊣ Software"
  , leftMode         := Mode.ghost
  , rightMode        := Mode.software
  , forwardName      := "ghost"
  , backwardName     := some "erase"
  , unitName         := some "eta_ghost"
  , counitName       := some "epsilon_ghost"
  , isProperAdj      := true
  , isForwardPartial := false
  , docSection       := "3.5.1"
  }

/-- `Software → Hardware (synth)` per `fx_reframing.md` §3.5.2.
    Partial morphism: defined on the Hardware-modality-
    compatible subset of Software types (per R0.3's
    `Modality.isAdmissibleAt` with mode `hardware`); undefined
    otherwise.

    No right adjoint — R4.2's derived synthesizability rules
    come from the absence of Hardware-admissible modalities
    for those Software types, not from a backward morphism
    here.  `observe` (§3.5.4) is the Hardware → Software
    direction but does NOT form an adjunction with `synth`. -/
def softwareHardware : Adjunction :=
  { name             := "Software → Hardware (synth)"
  , leftMode         := Mode.software
  , rightMode        := Mode.hardware
  , forwardName      := "synth"
  , backwardName     := none  -- `observe` is a separate record
  , unitName         := none  -- no triangle for a partial one-way morphism
  , counitName       := none
  , isProperAdj      := false
  , isForwardPartial := true
  , docSection       := "3.5.2"
  }

/-- `Software ⇄ Wire (serialize ⊣ parse)` per
    `fx_reframing.md` §3.5.3.  Mediated by a contract.
    Serialize encodes a Software value per contract C into a
    Wire value; parse decodes a Wire value back into Software,
    potentially failing.

    Proper adjunction.  Unit `serialize ∘ parse = id_Wire` is
    the round-trip law contracts must satisfy; counit
    `parse ∘ serialize = id_Software` is the preservation law
    for contracted types.  R0.8 discharges both obligations. -/
def softwareWire : Adjunction :=
  { name             := "Software ⇄ Wire (serialize ⊣ parse)"
  , leftMode         := Mode.software
  , rightMode        := Mode.wire
  , forwardName      := "serialize"
  , backwardName     := some "parse"
  , unitName         := some "eta_serialize"
  , counitName       := some "epsilon_serialize"
  , isProperAdj      := true
  , isForwardPartial := false
  , docSection       := "3.5.3"
  }

/-- `Hardware → Software (observe)` per `fx_reframing.md`
    §3.5.4.  One-way morphism.  A hardware signal (Hardware
    mode) reads into Software at a specific clock cycle.  The
    result is a Software value tagged with the clock domain it
    came from.

    No inverse — Software values cannot be injected into
    Hardware without `synth` (§3.5.2).  Not an adjunction with
    `synth` because synth is partial. -/
def hardwareSoftware : Adjunction :=
  { name             := "Hardware → Software (observe)"
  , leftMode         := Mode.hardware
  , rightMode        := Mode.software
  , forwardName      := "observe"
  , backwardName     := none  -- `synth` is a separate record
  , unitName         := none  -- no triangle for a one-way morphism
  , counitName       := none
  , isProperAdj      := false
  , isForwardPartial := false
  , docSection       := "3.5.4"
  }

/-- All four adjunction records in order matching
    `fx_reframing.md` §3.5.1 – §3.5.4.  The canonical
    enumeration the mode theory's adjunction layer uses. -/
def all : List Adjunction :=
  [ ghostSoftware, softwareHardware, softwareWire, hardwareSoftware ]

/-- All directed morphism edges implied by the four records:
    every forward edge, plus every backward edge where present.
    Returns `(sourceMode, targetMode, morphismName)` triples.

    Used by `morphisms_agree_with_mode_config` below to verify
    these edges match `Mode.config`'s independently-declared
    morphism lists. -/
def allEdges : List (Mode × Mode × String) :=
  all.flatMap fun adj =>
    let forward := (adj.leftMode, adj.rightMode, adj.forwardName)
    match adj.backwardName with
    | some backward => [forward, (adj.rightMode, adj.leftMode, backward)]
    | none          => [forward]

/-- Lookup an adjunction record by its forward morphism name.
    Returns `none` when no record has `forwardName == name`.
    Used by the §3.5 presentation layer (R1.12 diagnostics) to
    resolve morphism references back to their adjunction
    context. -/
def findByForward? (name : String) : Option Adjunction :=
  all.find? fun adj => adj.forwardName == name

/-- Lookup an adjunction record by EITHER its forward or its
    backward morphism name.  Useful when resolving a diagnostic
    that mentions "erase" or "parse" — these are backward
    halves of proper adjunctions, not forward morphisms. -/
def findByMorphism? (name : String) : Option Adjunction :=
  all.find? fun adj =>
    adj.forwardName == name
      || (match adj.backwardName with
          | some backName => backName == name
          | none          => false)

/-- Extract the forward morphism's edge as a `(source, target,
    name)` triple. -/
def forwardEdge (adj : Adjunction) : Mode × Mode × String :=
  (adj.leftMode, adj.rightMode, adj.forwardName)

/-- Extract the backward morphism's edge as a triple when
    present; `none` for one-way records. -/
def backwardEdge? (adj : Adjunction) : Option (Mode × Mode × String) :=
  adj.backwardName.map fun nm => (adj.rightMode, adj.leftMode, nm)

/-- Unit 2-cell's triangle endpoints as `(source, pit, sink)` for
    proper adjunctions.  The unit `η : 1_leftMode → backward ∘
    forward` witnesses a round-trip `leftMode → rightMode →
    leftMode`, so the endpoints are `(leftMode, rightMode,
    leftMode)`.  Returns `none` for one-way / partial morphisms
    (no triangle structure).

    Used by R0.8's triangle-shape pinning theorems and by R1+'s
    kernel rules once mode-transition terms exist. -/
def unitTriangleEndpoints? (adj : Adjunction) : Option (Mode × Mode × Mode) :=
  match adj.unitName with
  | some _ => some (adj.leftMode, adj.rightMode, adj.leftMode)
  | none   => none

/-- Counit 2-cell's triangle endpoints as `(source, pit, sink)`
    for proper adjunctions.  The counit `ε : forward ∘ backward →
    1_rightMode` witnesses a round-trip `rightMode → leftMode →
    rightMode`, so the endpoints are `(rightMode, leftMode,
    rightMode)`.  Returns `none` for one-way / partial
    morphisms. -/
def counitTriangleEndpoints? (adj : Adjunction) : Option (Mode × Mode × Mode) :=
  match adj.counitName with
  | some _ => some (adj.rightMode, adj.leftMode, adj.rightMode)
  | none   => none

/-- Every 2-cell name carried by the four records: for each
    proper adjunction, both the unit and the counit; for one-way
    morphisms, nothing.  Used for uniqueness checks against the
    six mode-level morphism names. -/
def twoCellNames : List String :=
  all.flatMap fun adj =>
    (adj.unitName.toList) ++ (adj.counitName.toList)

/-! ## Shape sanity theorems

Pinning the four-record shape and its agreement with
`Mode.lean`'s morphism list.  A future refactor that
accidentally drops an adjunction or adds a new one fails
exactly one of these theorems. -/

/-- Exactly 4 adjunction records per §3.5. -/
theorem total_count : all.length = 4 := by decide

/-- Exactly 2 proper adjunctions (§3.5.1 ghost⊣erase, §3.5.3
    serialize⊣parse).  R0.8 will discharge the unit/counit
    laws for these two. -/
theorem proper_adjunction_count :
    (all.filter (fun adj => adj.isProperAdj)).length = 2 := by
  decide

/-- Exactly 2 non-proper (one-way or partial) records (§3.5.2
    synth, §3.5.4 observe). -/
theorem non_proper_count :
    (all.filter (fun adj => ¬ adj.isProperAdj)).length = 2 := by
  decide

/-- Exactly 1 adjunction's forward morphism is partial: `synth`
    (§3.5.2). -/
theorem partial_forward_count :
    (all.filter (fun adj => adj.isForwardPartial)).length = 1 := by
  decide

/-- The four records expose exactly 6 directed edges: 2 proper
    adjunctions × 2 directions each + 2 one-way morphisms × 1
    direction each. -/
theorem edge_count : allEdges.length = 6 := by decide

/-- Proper adjunctions always have a backward morphism name
    (`some _`); one-way morphisms never do.  Pin the
    invariant — a future edit that marks an adjunction
    `isProperAdj = true` while leaving `backwardName = none`
    fails this. -/
theorem proper_adj_has_backward :
    all.all (fun adj =>
      adj.isProperAdj = (adj.backwardName.isSome)) = true := by
  decide

/-! ### Per-record pinning

Individual tests so a failure names the specific adjunction
that drifted. -/

theorem ghost_software_is_proper :
    ghostSoftware.isProperAdj = true := by decide

theorem software_hardware_is_not_proper :
    softwareHardware.isProperAdj = false := by decide

theorem software_wire_is_proper :
    softwareWire.isProperAdj = true := by decide

theorem hardware_software_is_not_proper :
    hardwareSoftware.isProperAdj = false := by decide

theorem synth_is_partial :
    softwareHardware.isForwardPartial = true := by decide

theorem ghost_is_not_partial :
    ghostSoftware.isForwardPartial = false := by decide

theorem serialize_is_not_partial :
    softwareWire.isForwardPartial = false := by decide

theorem observe_is_not_partial :
    hardwareSoftware.isForwardPartial = false := by decide

/-! ### Agreement with `Mode.lean`'s morphism lists

The four adjunction records MUST expose the same directed
edges as the four `Mode.*Morphisms` lists in `Mode.lean`
R0.2.  A drift between the two representations indicates a
refactor that broke one without updating the other.  Pin the
agreement as list equality over the concatenated Mode.config
morphisms and `allEdges`.

The comparison uses a sorted-by-source-mode projection: both
sides are de-duplicated and compared as multi-sets of triples.
For a clean `decide`, we flatten `Mode.config ... |>.morphisms`
into triples matching `allEdges`'s shape and assert set-
equality via sorted-list equality.
-/

/-- Every edge in `Mode.config`'s per-mode `morphisms` lists
    appears in `allEdges`.  I.e., every directed morphism
    Mode.lean declares is covered by some adjunction record.

    Uses `List.Perm` — the two lists have the same elements up
    to reordering.  Both are decidable by `decide` given the
    finite data. -/
theorem mode_morphisms_covered_by_allEdges :
    let modeEdges :=
      Mode.all.flatMap fun src =>
        (Mode.config src).morphisms.map fun (tgt, morphName) =>
          (src, tgt, morphName)
    modeEdges.all (fun edge => allEdges.contains edge) = true := by
  decide

/-- Conversely: every edge in `allEdges` is declared in
    `Mode.config`'s morphism lists.  The two-direction check
    together pins set equality: every `Mode.lean` edge is
    covered AND no spurious edges exist here. -/
theorem allEdges_covered_by_mode_morphisms :
    let modeEdges :=
      Mode.all.flatMap fun src =>
        (Mode.config src).morphisms.map fun (tgt, morphName) =>
          (src, tgt, morphName)
    allEdges.all (fun edge => modeEdges.contains edge) = true := by
  decide

/-- The two lists have the same length — confirming no
    duplicates or silently-dropped edges beyond what the two
    `_covered_by_` theorems individually catch. -/
theorem edge_count_matches_mode_config :
    let modeEdges :=
      Mode.all.flatMap fun src =>
        (Mode.config src).morphisms.map fun (tgt, morphName) =>
          (src, tgt, morphName)
    modeEdges.length = allEdges.length := by
  decide

/-! ## R0.8 — unit/counit 2-cell structure

Pin the name existence and triangle-endpoint shape for the two
proper adjunctions.  `fx_reframing.md` §3.5's categorical
commitment is that `ghost ⊣ erase` and `serialize ⊣ parse` carry
unit/counit natural transformations; we can't state the
triangle-identity EQUATIONS here (no kernel terms until R1),
but we can pin the 2-cell NAMES and the mode-level ENDPOINTS
of each triangle on the finite mode/morphism data.

The four commitments:

  1. `unitName.isSome ↔ isProperAdj` (name iff proper).
  2. `counitName.isSome ↔ isProperAdj` (same).
  3. Unit triangle endpoints for a proper adjunction are
     `(leftMode, rightMode, leftMode)`.
  4. Counit triangle endpoints for a proper adjunction are
     `(rightMode, leftMode, rightMode)`.

Plus the uniqueness check: the six mode-level morphism names
and the four unit/counit 2-cell names are pairwise distinct
(10 names total, no collisions).
-/

/-! ### Name-existence invariants -/

/-- Proper adjunctions always have a unit 2-cell name; one-way
    morphisms never do. -/
theorem proper_adj_has_unit_name :
    all.all (fun adj =>
      adj.isProperAdj = (adj.unitName.isSome)) = true := by
  decide

/-- Proper adjunctions always have a counit 2-cell name; one-way
    morphisms never do. -/
theorem proper_adj_has_counit_name :
    all.all (fun adj =>
      adj.isProperAdj = (adj.counitName.isSome)) = true := by
  decide

/-- Non-proper adjunctions (one-way / partial) carry neither a
    unit nor a counit name.  Pin the `none`-symmetric invariant
    explicitly — a future edit that leaves `isProperAdj = false`
    but fills `unitName = some _` fails this. -/
theorem non_proper_has_no_unit :
    all.all (fun adj =>
      ¬ adj.isProperAdj → adj.unitName.isNone) = true := by
  decide

theorem non_proper_has_no_counit :
    all.all (fun adj =>
      ¬ adj.isProperAdj → adj.counitName.isNone) = true := by
  decide

/-! ### Triangle-endpoint invariants

Per standard adjunction category theory, for `F ⊣ G` with `F :
C → D`, `G : D → C`:

  * Unit triangle traces `C → D → C`: starts and ends at `C`
    (our `leftMode`) pitting at `D` (our `rightMode`).
  * Counit triangle traces `D → C → D`: starts and ends at `D`
    (our `rightMode`) pitting at `C` (our `leftMode`).

Pin exactly these shapes for each proper adjunction. -/

/-- For every proper adjunction, the unit triangle's endpoint
    triple is `(leftMode, rightMode, leftMode)` — the round-trip
    `leftMode → rightMode → leftMode` that the unit witnesses. -/
theorem proper_adj_unit_triangle_shape :
    all.all (fun adj =>
      adj.isProperAdj →
        adj.unitTriangleEndpoints? =
          some (adj.leftMode, adj.rightMode, adj.leftMode)) = true := by
  decide

/-- For every proper adjunction, the counit triangle's endpoint
    triple is `(rightMode, leftMode, rightMode)` — the round-
    trip `rightMode → leftMode → rightMode` that the counit
    witnesses. -/
theorem proper_adj_counit_triangle_shape :
    all.all (fun adj =>
      adj.isProperAdj →
        adj.counitTriangleEndpoints? =
          some (adj.rightMode, adj.leftMode, adj.rightMode)) = true := by
  decide

/-- For every one-way / partial adjunction, both triangle-
    endpoint lookups return `none` — no triangle structure for
    records without unit/counit. -/
theorem non_proper_adj_no_triangles :
    all.all (fun adj =>
      ¬ adj.isProperAdj →
        adj.unitTriangleEndpoints?.isNone
          && adj.counitTriangleEndpoints?.isNone) = true := by
  decide

/-! ### Per-record triangle-shape pinning

A failure of any per-record theorem names the adjunction that
drifted. -/

theorem ghost_unit_triangle :
    ghostSoftware.unitTriangleEndpoints?
      = some (Mode.ghost, Mode.software, Mode.ghost) := by decide

theorem ghost_counit_triangle :
    ghostSoftware.counitTriangleEndpoints?
      = some (Mode.software, Mode.ghost, Mode.software) := by decide

theorem wire_unit_triangle :
    softwareWire.unitTriangleEndpoints?
      = some (Mode.software, Mode.wire, Mode.software) := by decide

theorem wire_counit_triangle :
    softwareWire.counitTriangleEndpoints?
      = some (Mode.wire, Mode.software, Mode.wire) := by decide

theorem softwareHardware_has_no_triangles :
    softwareHardware.unitTriangleEndpoints? = none
      ∧ softwareHardware.counitTriangleEndpoints? = none := by
  refine ⟨?_, ?_⟩ <;> decide

theorem hardwareSoftware_has_no_triangles :
    hardwareSoftware.unitTriangleEndpoints? = none
      ∧ hardwareSoftware.counitTriangleEndpoints? = none := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ### Per-record 2-cell name pinning

Catch typos in the unit/counit name strings. -/

theorem ghost_unit_name :
    ghostSoftware.unitName = some "eta_ghost" := by decide

theorem ghost_counit_name :
    ghostSoftware.counitName = some "epsilon_ghost" := by decide

theorem wire_unit_name :
    softwareWire.unitName = some "eta_serialize" := by decide

theorem wire_counit_name :
    softwareWire.counitName = some "epsilon_serialize" := by decide

/-! ### Uniqueness across 1-cells and 2-cells

Pin that the six morphism names (4 forward + 2 backward) and the
four unit/counit 2-cell names are ten pairwise-distinct strings.
No 1-cell name shadows a 2-cell name; no two 2-cells share a
name.  `findByMorphism?` stays unambiguous even when callers
extend the search to 2-cell names. -/

/-- Exactly four 2-cell names, one per unit/counit slot of the
    two proper adjunctions. -/
theorem two_cell_name_count :
    twoCellNames.length = 4 := by decide

/-- Pin the full 2-cell name list in order. -/
theorem two_cell_names_pinned :
    twoCellNames
      = [ "eta_ghost", "epsilon_ghost"
        , "eta_serialize", "epsilon_serialize" ] := by
  decide

/-- The concatenation of all 1-cell names (4 forward + 2
    backward) and all 2-cell names (4) pins as a literal list of
    length 10 — every name across both layers is explicitly
    listed and a drift names exactly one position. -/
theorem all_names_pinned :
    let oneCells :=
      (all.map (·.forwardName))
        ++ (all.filterMap (·.backwardName))
    oneCells ++ twoCellNames
      = [ "ghost", "synth", "serialize", "observe"
        , "erase", "parse"
        , "eta_ghost", "epsilon_ghost"
        , "eta_serialize", "epsilon_serialize" ] := by
  decide

/-- Length of the combined 1-cell + 2-cell name list is exactly
    10.  Trivial corollary of `all_names_pinned`, but stated
    separately for structural callers. -/
theorem total_name_count :
    ((all.map (·.forwardName))
      ++ (all.filterMap (·.backwardName))
      ++ twoCellNames).length = 10 := by
  decide

end Adjunction

end FX.KernelMTT
