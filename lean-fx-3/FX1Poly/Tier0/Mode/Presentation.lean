/-! # mode-27 — Fitch-style vs dual-context vs MTT: the presentation equivalence

The three standard PRESENTATIONS of (necessity-style) modal type theory differ only in how the CONTEXT records
modal structure — and they are inter-translatable.  This rung mechanizes the context-level presentation equivalence
for the single-mode necessity fragment (Pfenning-Davies dual-context ≃ Clouston Fitch-style ≃ Gratzer-et-al MTT):

  * **Fitch-style** (Clouston, "Fitch-Style Modal Lambda Calculi"): the context is a list of ZONES separated by
    LOCKS; `box` opens a fresh zone (adds a lock), `unbox` consumes one.  Modal depth = number of locks.
  * **dual-context** (Pfenning-Davies / Kavvos): TWO zones `(Δ; Γ)` — Δ the modal/valid zone (necessitated
    hypotheses), Γ the local/true zone.  This is exactly the SINGLE-LOCK Fitch context.
  * **MTT** (Gratzer-Kavvos-Nuyts-Birkedal): a flat list of ENTRIES, each a hypothesis or a lock `{🔒}`.  Fitch
    zones flatten to lock-separated hypothesis runs.

## What this file ships (each piece zero-axiom)

  * the three context representations: `FitchContext` (= list of zones), `DualContext` (the two-zone structure),
    `MttContext` (= list of `MttEntry` hyp/lock) + `lockDepth` / `lockCount` (the modal box-depth in each).
  * ★ the **Fitch ↔ dual-context bijection** — `dualToFitch` / `fitchToDual` + BOTH round trips
    (`fitchToDual_dualToFitch`, `dualToFitch_fitchToDual` on the two-zone fragment), each by `rfl` (structure eta).
    This is the Pfenning-Davies = single-lock-Fitch presentation equivalence, machine-checked.
  * the **Fitch → MTT** flattening `fitchToMtt` (zones → lock-separated runs) + `mttToFitch` (split at locks), with
    ★ `fitchToMtt_lockCount` — the modal box-DEPTH is PRESERVED across the translation (locks ↦ locks).
  * the tri-presentation depth agreement: `dualToFitch_lockDepth = 1` and `dual_fitchToMtt_lockCount = 1` — a
    dual-context's single box is one Fitch lock is one MTT lock.

## What is DEFERRED (markers)

  * the full MTT context round trip `mttToFitch ∘ fitchToMtt = id` (the splitting/joining bijection — needs the
    no-empty-zone invariant) (`hasMttContextRoundTrip`);
  * MTT's general MULTI-mode structure (mode-annotated locks `{🔒_μ}` over a mode theory — here a single necessity
    mode) (`hasMultiModePresentation`);
  * the TERM-level translation (box / unbox / let-box across the three calculi) + the type-preservation /
    cut-admissibility transport (here only CONTEXTS) (`hasTermLevelTranslation`);
  * the DEFINITIONAL-vs-propositional strength of the equivalence (here strict, `rfl`; the full biequivalence of
    the syntactic categories) (`hasBiequivalenceStrength`);
  * the kernel lock `◐_μ` / `MttEntry.lock` fibred into the mode doctrine (cross-axis, `fib`)
    (`hasKernelLockFibration`).

Zero external dependencies; raw Lean 4 + Init only (no mode-core import needed — this is the structural
presentation layer).
-/

namespace FX1Poly.Tier0

/-! ## The three context representations -/

/-- An **MTT context entry**: a hypothesis or a lock `{🔒}` (the modal separator). -/
inductive MttEntry (Hypothesis : Type) where
  /-- An ordinary hypothesis. -/
  | hyp (hypothesis : Hypothesis)
  /-- A modal lock (the `box`/`unbox` separator). -/
  | lock

/-- An **MTT context** — a flat list of entries (hypotheses interleaved with locks). -/
abbrev MttContext (Hypothesis : Type) : Type := List (MttEntry Hypothesis)

/-- The **modal depth** of an MTT context: the number of locks. -/
def MttContext.lockCount {Hypothesis : Type} : MttContext Hypothesis → Nat
  | [] => 0
  | MttEntry.hyp _ :: rest => MttContext.lockCount rest
  | MttEntry.lock :: rest => MttContext.lockCount rest + 1

/-- A **Fitch-style context** — a list of zones; the LOCKS are the separators between consecutive zones.  The head
zone is the innermost (current/local) zone. -/
abbrev FitchContext (Hypothesis : Type) : Type := List (List Hypothesis)

/-- The **modal depth** of a Fitch context: the number of locks = zone boundaries (zones minus one). -/
def FitchContext.lockDepth {Hypothesis : Type} : FitchContext Hypothesis → Nat
  | [] => 0
  | [_] => 0
  | _ :: (nextZone :: deeperZones) => FitchContext.lockDepth (nextZone :: deeperZones) + 1

/-- A **dual-context** (Pfenning-Davies): the modal/valid zone `Δ` and the local/true zone `Γ`. -/
structure DualContext (Hypothesis : Type) where
  /-- The modal (valid / necessitated) zone Δ. -/
  modalZone : List Hypothesis
  /-- The local (true) zone Γ. -/
  localZone : List Hypothesis

/-! ## The Fitch ↔ dual-context bijection (Pfenning-Davies = single-lock Fitch) -/

/-- A dual-context becomes the two-zone (single-lock) Fitch context `[Γ, Δ]` (head = local, then a lock, then modal). -/
def dualToFitch {Hypothesis : Type} (dual : DualContext Hypothesis) : FitchContext Hypothesis :=
  [dual.localZone, dual.modalZone]

/-- A Fitch context collapses to a dual-context: head = local zone, second = modal zone (deeper zones merged away —
the bijection holds exactly on the two-zone fragment). -/
def fitchToDual {Hypothesis : Type} : FitchContext Hypothesis → DualContext Hypothesis
  | localZone :: modalZone :: _ => { localZone := localZone, modalZone := modalZone }
  | [localZone] => { localZone := localZone, modalZone := [] }
  | [] => { localZone := [], modalZone := [] }

/-- ★ Round trip one: `fitchToDual ∘ dualToFitch = id` (every dual-context survives the translation, by structure eta). -/
theorem fitchToDual_dualToFitch {Hypothesis : Type} (dual : DualContext Hypothesis) :
    fitchToDual (dualToFitch dual) = dual := rfl

/-- ★ Round trip two: `dualToFitch ∘ fitchToDual = id` on the two-zone fragment (the single-lock Fitch contexts —
exactly the dual-context calculus). -/
theorem dualToFitch_fitchToDual {Hypothesis : Type} (localZone modalZone : List Hypothesis) :
    dualToFitch (fitchToDual [localZone, modalZone]) = [localZone, modalZone] := rfl

/-- The dual-context's image has modal depth exactly `1` — a single box. -/
theorem dualToFitch_lockDepth {Hypothesis : Type} (dual : DualContext Hypothesis) :
    (dualToFitch dual).lockDepth = 1 := rfl

/-! ## The Fitch → MTT flattening (zones ↦ lock-separated runs) -/

/-- Flatten a Fitch context to an MTT context: each zone's hypotheses become `hyp` entries, with a `lock` between
consecutive zones. -/
def fitchToMtt {Hypothesis : Type} : FitchContext Hypothesis → MttContext Hypothesis
  | [] => []
  | zone :: [] => zone.map MttEntry.hyp
  | zone :: (nextZone :: deeperZones) =>
      zone.map MttEntry.hyp ++ MttEntry.lock :: fitchToMtt (nextZone :: deeperZones)

/-- Split an MTT context back into Fitch zones at the locks (head zone = innermost). -/
def mttToFitch {Hypothesis : Type} : MttContext Hypothesis → FitchContext Hypothesis
  | [] => [[]]
  | MttEntry.hyp hypothesis :: rest =>
      match mttToFitch rest with
      | currentZone :: outerZones => (hypothesis :: currentZone) :: outerZones
      | [] => [[hypothesis]]
  | MttEntry.lock :: rest => [] :: mttToFitch rest

/-- A run of mapped hypotheses contributes no locks. -/
theorem lockCount_mapHyp {Hypothesis : Type} (zone : List Hypothesis) :
    MttContext.lockCount (zone.map MttEntry.hyp) = 0 := by
  induction zone with
  | nil => rfl
  | cons _ rest ih => exact ih

/-- `lockCount` distributes over append. -/
theorem lockCount_append {Hypothesis : Type} (entriesLeft entriesRight : MttContext Hypothesis) :
    (entriesLeft ++ entriesRight).lockCount = entriesLeft.lockCount + entriesRight.lockCount := by
  induction entriesLeft with
  | nil => rw [List.nil_append, MttContext.lockCount, Nat.zero_add]
  | cons entry rest ih =>
    cases entry with
    | hyp _ => rw [List.cons_append, MttContext.lockCount, MttContext.lockCount, ih]
    | lock =>
      rw [List.cons_append, MttContext.lockCount, MttContext.lockCount, ih, Nat.succ_add]

/-- ★ The modal box-DEPTH is preserved by the Fitch → MTT flattening: locks map to locks. -/
theorem fitchToMtt_lockCount {Hypothesis : Type} (context : FitchContext Hypothesis) :
    (fitchToMtt context).lockCount = context.lockDepth := by
  induction context with
  | nil => rfl
  | cons zone rest ih =>
    cases rest with
    | nil => exact lockCount_mapHyp zone
    | cons nextZone deeperZones =>
      show MttContext.lockCount ((zone.map MttEntry.hyp) ++ MttEntry.lock :: fitchToMtt (nextZone :: deeperZones))
        = FitchContext.lockDepth (nextZone :: deeperZones) + 1
      rw [lockCount_append, lockCount_mapHyp, MttContext.lockCount, ih, Nat.zero_add]

/-- ★ The tri-presentation depth agreement: a dual-context flattens (via its Fitch image) to an MTT context with
exactly one lock — its single box is one Fitch lock is one MTT lock. -/
theorem dual_fitchToMtt_lockCount {Hypothesis : Type} (dual : DualContext Hypothesis) :
    (fitchToMtt (dualToFitch dual)).lockCount = 1 := by
  rw [fitchToMtt_lockCount, dualToFitch_lockDepth]

/-! ## Honesty markers -/

/-- **Honesty marker.**  The full MTT context round trip `mttToFitch ∘ fitchToMtt = id` (the splitting/joining
bijection — requires the no-empty-zone invariant on `mttToFitch`) is deferred.  `= false`. -/
def fxMode_hasMttContextRoundTrip : Bool := false

/-- **Honesty marker.**  MTT's general MULTI-mode structure (mode-annotated locks `{🔒_μ}` over a mode theory — here
a single necessity mode) is deferred.  `= false`. -/
def fxMode_hasMultiModePresentation : Bool := false

/-- **Honesty marker.**  The TERM-level translation (box / unbox / let-box across the three calculi) + the
type-preservation / cut-admissibility transport (here only CONTEXTS) is deferred.  `= false`. -/
def fxMode_hasTermLevelTranslation : Bool := false

/-- **Honesty marker.**  The DEFINITIONAL-vs-propositional strength of the equivalence (here strict `rfl`; the full
biequivalence of the syntactic categories) is deferred.  `= false`. -/
def fxMode_hasBiequivalenceStrength : Bool := false

/-- **Honesty marker.**  The kernel lock `◐_μ` / `MttEntry.lock` fibred into the mode doctrine (cross-axis, `fib`)
is deferred.  `= false`. -/
def fxMode_hasKernelLockFibration : Bool := false

end FX1Poly.Tier0
