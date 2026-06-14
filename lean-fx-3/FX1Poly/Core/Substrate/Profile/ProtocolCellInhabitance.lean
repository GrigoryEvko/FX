import FX1Poly.Tier0.Term.Generator.GeneratorMetadata

/-! # ProtocolCellInhabitance — the `.protocol` cell sort is inhabited

The session/channel generators are protocol-state formers, not value formers:
a channel endpoint carries protocol data, not a term.  After CELLSORT-REWIRE
brick 1 the seven session/channel generators inhabit the `.protocol` cell sort
(and take protocol-sorted channel children), so `.protocol` is no longer a dead
enum slot.

These pins are the regression guard — reverting any session generator back to
`.term` breaks the corresponding `rfl`.  Each is a single `rfl` over the
concrete `cellSort` / `childSpecs` table entry, so this module is zero-axiom by
construction (no `propext`, `Quot.sound`, `Classical.choice`). -/

namespace FX1Poly.Core

/-- `gen_sessionSend` outputs a `.protocol` cell. -/
theorem sessionSend_inhabitsProtocolSort :
    Generator.cellSort .gen_sessionSend = .protocol := rfl

/-- `gen_sessionRecv` outputs a `.protocol` cell. -/
theorem sessionRecv_inhabitsProtocolSort :
    Generator.cellSort .gen_sessionRecv = .protocol := rfl

/-- `gen_sessionSelect` outputs a `.protocol` cell. -/
theorem sessionSelect_inhabitsProtocolSort :
    Generator.cellSort .gen_sessionSelect = .protocol := rfl

/-- `gen_sessionOffer` outputs a `.protocol` cell. -/
theorem sessionOffer_inhabitsProtocolSort :
    Generator.cellSort .gen_sessionOffer = .protocol := rfl

/-- `gen_sessionClose` outputs a `.protocol` cell. -/
theorem sessionClose_inhabitsProtocolSort :
    Generator.cellSort .gen_sessionClose = .protocol := rfl

/-- `gen_channelSplit` outputs a `.protocol` cell. -/
theorem channelSplit_inhabitsProtocolSort :
    Generator.cellSort .gen_channelSplit = .protocol := rfl

/-- `gen_channelJoin` outputs a `.protocol` cell. -/
theorem channelJoin_inhabitsProtocolSort :
    Generator.cellSort .gen_channelJoin = .protocol := rfl

/-- `gen_sessionSend` takes a protocol-sorted channel child and a term payload —
the spine certifier now rejects a non-protocol channel argument. -/
theorem sessionSend_channelChildIsProtocol :
    Generator.childSpecs .gen_sessionSend
      = [ChildSpec.protocolSameScope, ChildSpec.termSameScope] := rfl

/-- `gen_channelJoin` takes two protocol-sorted channel children. -/
theorem channelJoin_bothChildrenAreProtocol :
    Generator.childSpecs .gen_channelJoin
      = [ChildSpec.protocolSameScope, ChildSpec.protocolSameScope] := rfl

/-- Honesty boundary: `gen_channelCapacity` is Shannon channel capacity
(information theory — a real value), NOT a protocol former, so it stays a
`.term`.  This pin keeps the boundary from drifting in a later sweep. -/
theorem channelCapacity_staysTermSort :
    Generator.cellSort .gen_channelCapacity = .term := rfl

end FX1Poly.Core
