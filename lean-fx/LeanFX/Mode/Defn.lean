/-! # FX modes — the four mode endpoints of FX's mode 2-category.

Per `fx_modecat.md`, FX's mode theory has four mode endpoints:

  * `ghost`     — proof-only, erased at runtime, zero observable cost.
  * `software`  — runtime values produced and consumed by the executor.
  * `hardware`  — synthesisable signals living inside `hardware` blocks.
  * `wire`      — combinational wires inside `hardware` (pure subset).

This file is part of the **FX trust base**.  Everything in `lean-fx/`
that defines what "well-typed FX program" means depends on this enum.
A typo in a constructor name or a mistake in the derived equality would
silently miscategorise programs.  Keep the file small, exhaustive, and
audited.

The 1-cells of the mode 2-category (modalities) live in
`LeanFX.Mode.Modality`.  The 2-cells (subsumption preorder per §6.8
collision catalog) live in `LeanFX.Mode.TwoCell`.  The 2-category laws
are proven as theorems — never axioms — in `LeanFX.Mode.Laws`. -/

namespace LeanFX.Mode

/-- The four FX modes.  Closed enumeration; no other mode is reachable. -/
inductive Mode : Type
  | ghost
  | software
  | hardware
  | wire
  deriving DecidableEq, Repr

/-- The default surface mode — used when source elision omits the prefix. -/
@[inline] def Mode.surfaceDefault : Mode := .software

/-- Concrete FX modality syntax between the four kernel modes.

The abstract categorical laws live in `LeanFX.Mode.Modality`; this
syntax is the concrete payload used by modal contexts.  Composition is
kept as syntax so `Ctx.lock` can normalize identity and composed locks
without postulating quotient laws. -/
inductive Modality : Mode → Mode → Type
  /-- Identity modality at a mode. -/
  | identity : (mode : Mode) → Modality mode mode
  /-- Erase proof-only ghost content into software computation. -/
  | eraseGhost : Modality .ghost .software
  /-- Reflect software specifications into ghost reasoning. -/
  | reflectGhost : Modality .software .ghost
  /-- Synthesize software descriptions into hardware mode. -/
  | synthesize : Modality .software .hardware
  /-- Reify hardware signals into software observations. -/
  | observeHardware : Modality .hardware .software
  /-- Serialize software values into wire mode. -/
  | serialize : Modality .software .wire
  /-- Deserialize wire values into software mode. -/
  | deserialize : Modality .wire .software
  /-- Embed wire expressions into hardware mode. -/
  | wireToHardware : Modality .wire .hardware
  /-- Project hardware combinational fragments into wire mode. -/
  | hardwareToWire : Modality .hardware .wire
  /-- Syntactic composition of modalities. -/
  | compose :
      {sourceMode middleMode targetMode : Mode} →
      Modality sourceMode middleMode →
      Modality middleMode targetMode →
      Modality sourceMode targetMode

deriving instance DecidableEq for Modality

namespace Modality

/-- Identity modality wrapper. -/
@[inline]
def idModality (mode : Mode) : Modality mode mode :=
  Modality.identity mode

/-- Modality composition wrapper. -/
@[inline]
def composeModality {sourceMode middleMode targetMode : Mode}
    (firstModality : Modality sourceMode middleMode)
    (secondModality : Modality middleMode targetMode) :
    Modality sourceMode targetMode :=
  Modality.compose firstModality secondModality

end Modality

end LeanFX.Mode
