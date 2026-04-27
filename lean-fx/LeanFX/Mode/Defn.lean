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

end LeanFX.Mode
