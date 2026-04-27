import FX.KernelMTT.Mode

/-!
# Modality — 1-cells of the FX mode theory

Enumerates the 20 modalities that live at the four modes per
`fx_reframing.md` §3.2–§3.4.  Each modality is a 1-cell in the
2-category of `Mode.lean`'s 0-cells: a type-level endo-operation
on the mode where it's admissible.

## Count breakdown

  * **18 Software modalities** (`fx_reframing.md` §3.2):
    - 15 Tier S commutative semirings: `usage`, `sec`, `eff`,
      `lifetime`, `provenance`, `trust`, `obs`, `complexity`,
      `precision`, `space`, `overflow`, `fporder`, `mutation`,
      `reentrancy`, `size`.
    - 2 Tier L lattices with validity: `repr`, `clock`.
    - 1 Tier T typestate: `protocol`.
  * **4 Hardware modalities** (`fx_reframing.md` §3.3):
    `clock`, `repr`, `precision`, `complexity` — a strict subset
    of the Software modalities, shared via the same
    constructors.  Hardware's `clock` IS Software's `clock`; the
    admissibility set `[software, hardware]` encodes the
    cross-mode availability.
  * **2 Wire modalities** (`fx_reframing.md` §3.4): `format`,
    `version`.  Distinct from any Software modality — version
    specifically lives at Wire rather than Software per
    `fx_reframing.md` §3.2.4.
  * **0 Ghost modalities** — Ghost is a mode of proof content;
    no endo-modalities apply.  Cross-mode transit to/from Ghost
    goes through the `ghost ⊣ erase` adjunction (R0.4).

Distinct modality constructors: **20** (18 Software ∪ 2 Wire-
only; the 4 Hardware modalities overlap with Software's 18).

## Design choice — single inductive with admissibility set

A modality name like `clock` appears in both Software and
Hardware contexts.  The cleanest encoding uses ONE
`Modality.clock` constructor with `admissibleModes = [software,
hardware]` rather than duplicating the constructor per mode.
This matches the reframing doc's §3.3 "strict subset" framing:
Hardware's clock IS Software's clock, just admissible in a
restricted mode where fewer other modalities coexist.

## Trust layer

Scaffold during Phase R0–R4 (per `FX/KernelMTT/CLAUDE.md`).  No
axioms.  Pinning theorems verify R0.2's `Mode.lean` modality
lists agree with the admissibility functions here — a mismatch
between the two representations fails the build.

## Cross-references

  * `fx_reframing.md` §3.2 (Software modalities)
  * `fx_reframing.md` §3.3 (Hardware's strict subset)
  * `fx_reframing.md` §3.4 (Wire modalities)
  * `fx_reframing.md` §3.6 (2-cells as subsumption — R0.5/R0.6)
  * `fx_design.md` §6.3 (Tier S/L/T classification)
  * `FX/KernelMTT/Mode.lean` — the 0-cells these modalities sit
    above
-/

namespace FX.KernelMTT

/-- Four structural kinds of modalities per `fx_design.md` §6.3
    and `fx_reframing.md` §3.2 / §3.4.  Classification is
    informative — `fx_reframing.md` §3.6.3 notes the Tier L /
    Tier S distinction "collapses under the reframe to 'lattice
    modalities carry conditional 2-cells.'"  Keeping the kind
    annotation here documents the classical tier assignment for
    cross-reference with the grade-algebra files in
    `FX/Kernel/Grade/`.

    Tier S and Tier L are the two shapes the §3 MTT commitment
    preserves; Tier T (typestate) is the only Tier T member
    (protocol); Wire primitives (format, version) are neither
    Tier S nor Tier L nor Tier T — they're named mode-local
    structures on the Wire 0-cell. -/
inductive ModalityKind : Type where
  /-- Tier S.  Commutative semiring on grades (§6.3 Tier S). -/
  | commutativeSemiring : ModalityKind
  /-- Tier L.  Lattice with a validity predicate rejecting
      incompatible joins (§6.3 Tier L). -/
  | latticeWithValidity : ModalityKind
  /-- Tier T.  Typestate; transitions on state instead of
      semiring combine (§6.3 Tier T). -/
  | typestate : ModalityKind
  /-- Wire-mode primitive.  Neither Tier S/L/T — named
      mode-local structure (format binding, version label). -/
  | wirePrimitive : ModalityKind
  deriving DecidableEq, Repr, Inhabited

/-- The 20 FX modalities enumerated per `fx_reframing.md` §3.2–
    §3.4.  Each constructor is a 1-cell in the mode theory's
    2-category; `admissibleModes` (below) identifies which
    0-cells it lives above.

    Order: Software Tier S modalities first (15), then the two
    Tier L (repr, clock), then Tier T (protocol), then the two
    Wire primitives.  Matches the listing order in
    `Mode.softwareModalityNames` extended with Wire.  Stable —
    future additions append at the end. -/
inductive Modality : Type where
  -- 15 Tier S commutative semirings (Software).  Four of them
  -- (`complexity`, `precision`, `repr`, `clock` below in the
  -- Tier L block) are also admissible at Hardware per §3.3.
  | usage       : Modality
  | sec         : Modality
  | eff         : Modality
  | lifetime    : Modality
  | provenance  : Modality
  | trust       : Modality
  | obs         : Modality
  | complexity  : Modality
  | precision   : Modality
  | space       : Modality
  | overflow    : Modality
  | fporder     : Modality
  | mutation    : Modality
  | reentrancy  : Modality
  | size        : Modality
  -- 2 Tier L lattices with validity (Software + Hardware).
  | repr        : Modality
  | clock       : Modality
  -- 1 Tier T typestate (Software).
  | protocol    : Modality
  -- 2 Wire-mode primitives (Wire-only).
  | format      : Modality
  | version     : Modality
  deriving DecidableEq, Repr, Inhabited

namespace Modality

/-- The modality's name as used in `Mode.softwareModalityNames`
    etc.  Names are lowercase without the `◇_` prefix — the
    surface rendering (with the `◇_` prefix) is a
    presentation-layer concern handled by the pretty-printer,
    not a naming-layer decision. -/
def name : Modality → String
  | usage       => "usage"
  | sec         => "sec"
  | eff         => "eff"
  | lifetime    => "lifetime"
  | provenance  => "provenance"
  | trust       => "trust"
  | obs         => "obs"
  | complexity  => "complexity"
  | precision   => "precision"
  | space       => "space"
  | overflow    => "overflow"
  | fporder     => "fporder"
  | mutation    => "mutation"
  | reentrancy  => "reentrancy"
  | size        => "size"
  | repr        => "repr"
  | clock       => "clock"
  | protocol    => "protocol"
  | format      => "format"
  | version     => "version"

/-- Structural kind of the modality per `fx_design.md` §6.3 /
    `fx_reframing.md` §3.2.  The four Tier-S dimensions that
    are also at Hardware (`complexity`, `precision`) stay Tier
    S — admissibility at Hardware is orthogonal to their
    structural kind. -/
def kind : Modality → ModalityKind
  -- Tier S
  | usage | sec | eff | lifetime | provenance
  | trust | obs | complexity | precision | space
  | overflow | fporder | mutation | reentrancy | size =>
    .commutativeSemiring
  -- Tier L
  | repr | clock =>
    .latticeWithValidity
  -- Tier T
  | protocol =>
    .typestate
  -- Wire primitives
  | format | version =>
    .wirePrimitive

/-- The set of modes at which this modality is admissible.
    Cross-references `Mode.softwareModalityNames` /
    `Mode.hardwareModalityNames` / `Mode.wireModalityNames` —
    the `modality_admissibility_agrees_with_mode_config`
    theorem below pins agreement between the two
    representations.

    Four modalities — `complexity`, `precision`, `repr`,
    `clock` — appear at BOTH Software and Hardware per §3.3's
    "strict subset" framing.  Their admissibility list has two
    entries; every other modality has exactly one. -/
def admissibleModes : Modality → List Mode
  -- Software-only Tier S.
  | usage | sec | eff | lifetime | provenance
  | trust | obs | space | overflow | fporder
  | mutation | reentrancy | size =>
    [Mode.software]
  -- Software + Hardware Tier S (the 2 Tier-S dims Hardware
  -- also uses).
  | complexity | precision =>
    [Mode.software, Mode.hardware]
  -- Software + Hardware Tier L.
  | repr | clock =>
    [Mode.software, Mode.hardware]
  -- Software-only Tier T.
  | protocol =>
    [Mode.software]
  -- Wire-only primitives.
  | format | version =>
    [Mode.wire]

/-- `true` iff this modality is admissible at the given mode.
    Convenience wrapper over `admissibleModes`'s membership
    test; used by R1.4 elaboration to reject term shapes that
    place a modality at an unauthorized mode. -/
def isAdmissibleAt (modality : Modality) (mode : Mode) : Bool :=
  (admissibleModes modality).contains mode

/-- All 20 modalities as a list, in constructor order.  The
    canonical enumeration — tests and iteration helpers use
    this. -/
def all : List Modality :=
  [ usage, sec, eff, lifetime, provenance
  , trust, obs, complexity, precision, space
  , overflow, fporder, mutation, reentrancy, size
  , repr, clock, protocol
  , format, version
  ]

/-- Subset of modalities admissible at a given mode.  Derived
    from `all` filtered by `isAdmissibleAt`.  Acts as the
    inductive-level mirror of `Mode.canHoldModality?` — the
    pinning theorem below asserts equivalence. -/
def admissibleAt (mode : Mode) : List Modality :=
  all.filter (fun m => isAdmissibleAt m mode)

/-- Lookup a modality by name.  Returns `none` for unknown
    names.  Used by R1.12's diagnostic mapping and by any
    textual interface (pretty-printer, CLI, test tooling) that
    needs to round-trip string ↔ Modality. -/
def byName? : String → Option Modality
  | "usage"       => some usage
  | "sec"         => some sec
  | "eff"         => some eff
  | "lifetime"    => some lifetime
  | "provenance"  => some provenance
  | "trust"       => some trust
  | "obs"         => some obs
  | "complexity"  => some complexity
  | "precision"   => some precision
  | "space"       => some space
  | "overflow"    => some overflow
  | "fporder"     => some fporder
  | "mutation"    => some mutation
  | "reentrancy"  => some reentrancy
  | "size"        => some size
  | "repr"        => some repr
  | "clock"       => some clock
  | "protocol"    => some protocol
  | "format"      => some format
  | "version"     => some version
  | _             => none

/-! ## Shape sanity theorems

Pin the enumeration counts and the Mode ↔ Modality cross-
agreement.  Proved by `decide` — no induction required. -/

/-- Exactly 20 distinct modalities across all modes. -/
theorem total_count : all.length = 20 := by decide

/-- Eighteen modalities are admissible at Software per §3.2.
    Cross-checks agreement with
    `Mode.software_modality_count`. -/
theorem software_admissible_count :
    (admissibleAt Mode.software).length = 18 := by decide

/-- Four modalities are admissible at Hardware per §3.3. -/
theorem hardware_admissible_count :
    (admissibleAt Mode.hardware).length = 4 := by decide

/-- Two modalities are admissible at Wire per §3.4. -/
theorem wire_admissible_count :
    (admissibleAt Mode.wire).length = 2 := by decide

/-- Zero modalities are admissible at Ghost per §3.1. -/
theorem ghost_admissible_count :
    (admissibleAt Mode.ghost).length = 0 := by decide

/-! ### Mode ↔ Modality agreement theorems

The two independent representations of mode-admissibility —
`Mode.softwareModalityNames` / `hardwareModalityNames` /
`wireModalityNames` as `List String` in `Mode.lean`, and
`Modality.admissibleAt mode |>.map .name` as a derived list
here — MUST describe the same set.  These theorems pin the
agreement so any future drift fails the build.

Four separate theorems (one per mode) rather than a single
theorem over `Mode.all` — keeps each failure site localized to
the specific mode whose lists disagree. -/

/-- Software's modality names from `Mode.lean` match the names
    derived from `Modality.admissibleAt software`. -/
theorem software_names_agree :
    (admissibleAt Mode.software).map name
      = (Mode.config Mode.software).modalityNames := by
  decide

/-- Hardware's modality names from `Mode.lean` match the names
    derived from `Modality.admissibleAt hardware`. -/
theorem hardware_names_agree :
    (admissibleAt Mode.hardware).map name
      = (Mode.config Mode.hardware).modalityNames := by
  decide

/-- Wire's modality names from `Mode.lean` match the names
    derived from `Modality.admissibleAt wire`. -/
theorem wire_names_agree :
    (admissibleAt Mode.wire).map name
      = (Mode.config Mode.wire).modalityNames := by
  decide

/-- Ghost's empty modality list from `Mode.lean` matches the
    empty list derived here (vacuously). -/
theorem ghost_names_agree :
    (admissibleAt Mode.ghost).map name
      = (Mode.config Mode.ghost).modalityNames := by
  decide

/-! ### Kind distribution pinning

Three Tier S + Tier L + Tier T modalities (18 Software ones)
decompose as 15 + 2 + 1.  Pinning the counts keeps any
accidental kind-reclassification visible. -/

/-- Exactly 15 Tier S modalities. -/
theorem tierS_count :
    (all.filter (fun m => m.kind = .commutativeSemiring)).length = 15 := by
  decide

/-- Exactly 2 Tier L modalities (`repr`, `clock`). -/
theorem tierL_count :
    (all.filter (fun m => m.kind = .latticeWithValidity)).length = 2 := by
  decide

/-- Exactly 1 Tier T modality (`protocol`). -/
theorem tierT_count :
    (all.filter (fun m => m.kind = .typestate)).length = 1 := by
  decide

/-- Exactly 2 Wire primitives (`format`, `version`). -/
theorem wirePrim_count :
    (all.filter (fun m => m.kind = .wirePrimitive)).length = 2 := by
  decide

end Modality

end FX.KernelMTT
