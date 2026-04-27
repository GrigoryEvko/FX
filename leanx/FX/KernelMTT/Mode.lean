/-!
# Mode — 0-cells of the FX mode theory

The mode theory's 0-cells per `fx_reframing.md` §3.1.  Four modes
organize FX's semantic domains under the MTT reframe:

  * `Ghost` — compile-time-only content.  Proofs, specifications,
    refinement predicates, ghost-grade bindings.  Erased at
    runtime per `fx_design.md` §1.5.  Target of the `erase`
    adjoint from `Software`.
  * `Software` — the main programming domain.  Every user-written
    function, runtime value, effect operation lives here.  What
    programmers think of as "FX code."
  * `Hardware` — synthesizable subset per `fx_design.md` §18.8.  A
    restricted mode admitting only clock-domain-respecting, bit-
    vector-representable, bounded-loop-free terms.  Target of the
    `synth` (partial) morphism from `Software`.
  * `Wire` — cross-boundary serialized domain where contracts
    live per `fx_design.md` §14.  Carries the modal-univalence
    modality (`fx_reframing.md` §4.4) so equivalent wire formats
    are interchangeable.

This is **phase R0 scaffold** — the types are the foundation that
R0.3 (Modality enumeration), R0.4 (cross-mode adjunctions), and
R0.5–R0.6 (2-cell registry) build on.  Kernel-level typing wiring
(R1.4) consumes `Mode.config` to decide which modalities are
admissible for a given term's mode.

## Trust layer

`FX/KernelMTT/**` is scaffold during Phase R1 and graduates to the
TRUSTED layer at the Phase R5 migration (per
`fx_reframing.md` §8.7).  During scaffolding: no new axioms, zero
`sorry`.  The axiom-audit CI gate already covers the allowlist.

## Cross-references

  * `fx_reframing.md` §3.1 — modes as 0-cells
  * `fx_reframing.md` §3.2 — Software modalities (18 endo)
  * `fx_reframing.md` §3.3 — Hardware modalities (4)
  * `fx_reframing.md` §3.4 — Wire modalities (2 + univalence)
  * `fx_reframing.md` §3.5 — four cross-mode adjunctions
  * `fx_modecat.md` — (forthcoming per R0.1) formal mode-theory
    spec; this file is the Lean mechanization of §3 of that spec
-/

namespace FX.KernelMTT

/-- The four modes FX commits to per `fx_reframing.md` §3.1.  No
    fifth mode is admitted at the current reframe version; user-
    defined modes are explicitly out of scope per
    `fx_reframing.md` §2.5.

    Distinct inductive rather than a `String` tag because the
    set is closed and DecidableEq is mechanical — any mode-
    indexed lookup uses structural pattern matching, not string
    comparison.  Naming follows the convention of
    `fx_reframing.md` §3.1 (lowercase per-mode identifier; the
    spec uses `Ghost` / `Software` / `Hardware` / `Wire`
    title-case only in prose). -/
inductive Mode : Type where
  /-- Compile-time-only content.  Erased at runtime. -/
  | ghost    : Mode
  /-- The main programming domain.  Every runtime value lives here. -/
  | software : Mode
  /-- Synthesizable subset.  Target of `synth` from `software`. -/
  | hardware : Mode
  /-- Cross-boundary serialized domain.  Contract data lives here. -/
  | wire     : Mode
  deriving DecidableEq, Repr, Inhabited

namespace Mode

/-- Human-readable name for a mode.  Matches the prose form used
    in `fx_reframing.md` §3.1 (title-case per mode). -/
def name : Mode → String
  | ghost    => "Ghost"
  | software => "Software"
  | hardware => "Hardware"
  | wire     => "Wire"

/-- Configuration for a single mode: which modalities live at
    this mode, which outgoing morphisms connect it to other modes,
    and whether values at this mode are runtime-preserved.

    Fields:

      * `modalityNames` — endo-modality names that a type at this
        mode may be decorated with.  Names follow
        `fx_reframing.md` §3.2–§3.4 convention (without the `◇_`
        prefix — that's a surface-level rendering concern).  The
        list is the complete set; a modality not on the list is
        NOT admissible at this mode (the hard content of
        `fx_reframing.md` §3.3 "strict subset" for Hardware).

      * `morphisms` — outgoing cross-mode morphisms from this
        mode.  Pair of (target mode, morphism name).  Whether
        the morphism is a full adjunction (partner on the other
        side) or a one-way morphism is documented in
        `fx_reframing.md` §3.5 per pair; `ModeConfig` just
        carries the directed edges.  R0.4 adds the structured
        `Adjunction` record capturing unit/counit.

      * `isPreserved` — `false` for `Ghost` (erased at runtime
        per `fx_design.md` §1.5), `true` for every other mode.
        This is the 2LTT preservation discipline of
        `fx_reframing.md` §4.6.  Ghost terms exist in the
        proof-level universe and disappear at codegen; the
        other three all leave some runtime witness. -/
structure ModeConfig : Type where
  modalityNames : List String
  morphisms     : List (Mode × String)
  isPreserved   : Bool
  deriving Repr, Inhabited

/-- The `Software` mode's 18 endo-modalities per
    `fx_reframing.md` §3.2.  Decomposition: 15 Tier-S commutative
    (Usage, Sec, Eff, Lifetime, Provenance, Trust, Obs,
    Complexity, Precision, Space, Overflow, FPOrder, Mutation,
    Reentrancy, Size) + 2 Tier-L (Repr, Clock) + 1 Tier-T
    (Protocol).

    Note: `Version` is NOT on this list — it lives at `Wire`
    per `fx_reframing.md` §3.2.4.  An earlier §3.2 draft placed
    version at Software; the reframing commitment clarifies
    that version transitions happen at the wire boundary, so
    the modality lives there. -/
def softwareModalityNames : List String :=
  -- Tier S (15 commutative semiring modalities)
  [ "usage", "sec", "eff", "lifetime", "provenance"
  , "trust", "obs", "complexity", "precision", "space"
  , "overflow", "fporder", "mutation", "reentrancy", "size"
  -- Tier L (2 lattice modalities)
  , "repr", "clock"
  -- Tier T (1 typestate modality)
  , "protocol"
  ]

/-- Hardware's strict subset per `fx_reframing.md` §3.3.  The
    remaining 14 Software modalities are ABSENT from Hardware —
    attempting to construct a Hardware-mode term with (say) a
    `usage` grade is a compile error once R1.4 wires the check.
    Absence is the mechanism that gives rise to §18.8's
    synthesizability rules under the R4.2 derivation.

    Order: canonical per `Modality.all` (§3.2 Tier S order
    followed by Tier L).  §3.3's listing
    (`clock`/`repr`/`precision`/`complexity`) was spec-prose
    order, which we translate to canonical here so the R0.3
    `software_names_agree` etc. theorems pin agreement by list
    equality without needing a permutation-quotient decidable
    procedure. -/
def hardwareModalityNames : List String :=
  [ "complexity", "precision", "repr", "clock" ]

/-- Wire's two modalities per `fx_reframing.md` §3.4.  Modal
    univalence (`fx_reframing.md` §4.4) is a further Wire-only
    structure that arrives with R2d.1; it's NOT listed here
    because it's an axiom/rule on the mode, not a modality. -/
def wireModalityNames : List String :=
  [ "format", "version" ]

/-- `Ghost` has NO endo-modalities per se — it's a mode of
    proof content.  The `ghost ⊣ erase` adjunction (§3.5.1)
    handles transit to/from `Software`, and Ghost-mode values
    participate in the full MTT instance without needing
    Software-style graded modalities.  An empty modality set
    encodes this cleanly. -/
def ghostModalityNames : List String := []

/-- Outgoing morphisms from each mode per `fx_reframing.md` §3.5.
    Each entry is (target mode, morphism name).  The adjunction
    direction and unit/counit laws arrive with R0.4; here we
    just enumerate directed edges so R0.3's modality list and
    R0.4's adjunction record can both reference them.

    Diagrammed:

        Ghost ──ghost──> Software ──synth──> Hardware
             <──erase──           <──observe──
                          ┌──serialize──> Wire
                          └──parse──────
-/
def ghostMorphisms    : List (Mode × String) := [ (software, "ghost")    ]
def softwareMorphisms : List (Mode × String) :=
  [ (ghost,    "erase")
  , (hardware, "synth")
  , (wire,     "serialize")
  ]
def hardwareMorphisms : List (Mode × String) := [ (software, "observe")  ]
def wireMorphisms     : List (Mode × String) := [ (software, "parse")    ]

/-- Lookup the mode's config.  Dispatch is a pure pattern match
    — there's no registry structure the table could be threaded
    through, because the mode theory is FIXED per reframe
    version (per `fx_reframing.md` §2.4 "The spine's mode theory
    is fixed per reframe version").  User-defined grade
    dimensions (§5.4 peripheral) may add modality names at the
    user's scope; those live OUTSIDE this spine-level config
    and are resolved separately. -/
def config : Mode → ModeConfig
  | ghost =>
    { modalityNames := ghostModalityNames
    , morphisms     := ghostMorphisms
    , isPreserved   := false  -- erases at codegen
    }
  | software =>
    { modalityNames := softwareModalityNames
    , morphisms     := softwareMorphisms
    , isPreserved   := true
    }
  | hardware =>
    { modalityNames := hardwareModalityNames
    , morphisms     := hardwareMorphisms
    , isPreserved   := true
    }
  | wire =>
    { modalityNames := wireModalityNames
    , morphisms     := wireMorphisms
    , isPreserved   := true
    }

/-- `true` iff the modality named `modalityName` is admissible at
    `mode`.  Used by R1.4 elaboration to check that a term's
    declared modality spectrum is a subset of its mode's
    admissible modalities.  Attempting to use (say) the `eff`
    modality at `Hardware` mode fails this predicate and produces
    a structured diagnostic once R1.12 wires the error-code
    mapping. -/
def canHoldModality? (mode : Mode) (modalityName : String) : Bool :=
  (config mode).modalityNames.contains modalityName

/-- `true` when values at this mode are runtime-preserved.
    Equivalent to `(config mode).isPreserved`; the convenience
    accessor lets callers spell `Mode.isPreserved m` directly
    instead of projecting through the config.  Matches the
    §1.5 erasure discipline — Ghost is the only mode that
    erases at codegen. -/
def isPreserved (mode : Mode) : Bool :=
  (config mode).isPreserved

/-- `true` iff a morphism of the given name exists from `source`
    to `target`.  Consults the source mode's morphism list.
    Used by R1.6 mode-transition checking to validate that a
    term crossing modes via a named morphism uses a declared
    edge.  Returns `false` for spurious morphism names or
    source→target pairs that aren't edges in the mode-theory
    graph — the caller reports the specific missing-edge
    diagnostic. -/
def hasMorphism (source target : Mode) (morphismName : String) : Bool :=
  (config source).morphisms.any fun (edgeTarget, edgeName) =>
    edgeTarget = target && edgeName == morphismName

/-- All four modes as a list, in canonical order matching the
    `Mode` inductive's constructor order.  Useful for tests and
    for emitting per-mode diagnostics. -/
def all : List Mode :=
  [ ghost, software, hardware, wire ]

/-! ## Shape sanity lemmas

These are immediate from `config`'s definition but calling them
out keeps future refactors from silently drifting the mode-
theory shape.  Each is proved by `decide` — no induction
required because `Mode` has four constructors and the
predicate is decidable at each. -/

/-- Software admits exactly 18 endo-modalities (15 Tier-S + 2
    Tier-L + 1 Tier-T).  Pin the count so any accidental list
    edit that changes it fails the build. -/
theorem software_modality_count :
    (config software).modalityNames.length = 18 := by
  decide

/-- Hardware admits exactly 4 endo-modalities (clock, repr,
    precision, complexity).  Pin the count. -/
theorem hardware_modality_count :
    (config hardware).modalityNames.length = 4 := by
  decide

/-- Wire admits exactly 2 endo-modalities (format, version).
    Pin the count — version lives at Wire per §3.2.4, NOT
    Software.  A future refactor that accidentally moves
    version would drop this count and fail the build. -/
theorem wire_modality_count :
    (config wire).modalityNames.length = 2 := by
  decide

/-- Ghost has no endo-modalities.  Pin the count — if a
    modality is ever added to Ghost, this count fails and
    forces explicit consideration. -/
theorem ghost_modality_count :
    (config ghost).modalityNames.length = 0 := by
  decide

/-- Ghost is the only mode that erases at codegen.  Directly
    from `config`'s per-mode `isPreserved` field. -/
theorem ghost_not_preserved : ¬ isPreserved ghost := by decide

/-- Software, Hardware, Wire all preserve at runtime. -/
theorem software_preserved : isPreserved software := by decide
theorem hardware_preserved : isPreserved hardware := by decide
theorem wire_preserved     : isPreserved wire     := by decide

end Mode

end FX.KernelMTT
