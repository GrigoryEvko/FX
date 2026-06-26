import FX1Poly.Core.Fib.UniverseCodeBridge
import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Core.Metatheory.Reducibility.Stratified.StratifiedReducibleUniverseDecode

/-! # FX1Poly/Core/Fib/UniverseElDecode — fib-2b: the bridge's typing tie-in + the El decode

fib-2a (`UniverseCodeBridge`) established the on-the-nose DATA bridge `axisCodeToCell : UniverseCode →
RawTerm` (the type axis's Tarski code = the kernel's `gen_universeCode` term-payload).  fib-2b lifts that data
bridge to the two SEMANTIC connections that make it a genuine `type ↔ term` gluing:

  * **The typing tie-in.** The bridged code, AS A KERNEL TERM, is typed at the bridged successor:
    `HasTypeUnion Γ (axisCodeToCell code) (axisCodeToCell (successor code))`.  This is exactly the kernel rule
    `HasTypeUnion.universeFormation` (`Type@L : Type@(L+1)`) read through the bridge — the type axis's abstract
    `successor` IS the kernel's universe-formation classifier, at the TYPING level (fib-2a only matched them at
    the code level).

  * **The El decode.** The bridged code, AS A KERNEL UNIVERSE, carries the kernel's Tarski El semantics: a
    reducible MEMBER of `axisCodeToCell code` at reducibility level `predLevel+1` decodes to a reducible TYPE at
    `predLevel` (`tarskiDecode`), and membership is PRECISELY the SN reducible types one level down
    (`universeMembership_iff`).  This is the "El gluing term and type": the universe term decodes to the
    type-of-types.  The kernel already ships this El (`StratifiedReducibleUniverseDecode`); fib-2b instantiates
    it AT THE BRIDGE so the type axis's standalone universe (which omits a decode field) inherits the kernel's.

fib-2c flips `fxFib_hasTypeTermUniverseReflection` and closes the type-20 Tarski↔Russell coherence.

## Zero-axiom

The typing tie-in is `HasTypeUnion.universeFormation` (defeq through `axisCodeToCell`); the El connections are
the shipped Tarski decode lemmas instantiated at the bridged payload.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core.Fib

open FX1Poly.Core FX1Poly.Core.StepStar FX1Poly.Tier0 FX1Poly.Typed FX1Poly.Universe

/-- **★ The typing tie-in.**  The bridged universe code is typed at the bridged successor — the type axis's
`successor` IS the kernel's `HasTypeUnion.universeFormation` classifier (`Type@L : Type@(L+1)`), now at the
TYPING level (fib-2a matched them only at the code level). -/
theorem axisCodeToCell_typedAtSuccessor {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (code : UniverseCode) :
    HasTypeUnion profile context (axisCodeToCell code) (axisCodeToCell (fxTarskiUniverse.successor code)) :=
  HasTypeUnion.universeFormation context code.level code.flag

/-- **★ The El decode at the bridge.**  A reducible member of the bridged universe `axisCodeToCell code` (at
reducibility level `predLevel + 1`) decodes to a reducible TYPE at `predLevel` — the universe term decodes to a
type.  The kernel's Tarski decode (`IsReducibleMemberAt.tarskiDecode`) instantiated at the bridged payload. -/
theorem axisCodeToCell_tarskiDecode {scope : Nat} {predLevel : Nat} (code : UniverseCode)
    {typeCode : RawTerm scope}
    (member : IsReducibleMemberAt (predLevel + 1) (axisCodeToCell code) typeCode) :
    IsReducibleTypeAt predLevel typeCode :=
  IsReducibleMemberAt.tarskiDecode member

/-- **★ The El membership characterization at the bridge.**  A term is a reducible member of the bridged
universe `axisCodeToCell code` (at reducibility level `predLevel + 1`) IFF it is an SN reducible type at
`predLevel` — the bridged universe is PRECISELY the SN reducible types one level down.  The full Tarski
semantics of the type axis's universe, inherited from the kernel's `universeMembership_iff`. -/
theorem axisCodeToCell_universeMembership_iff {scope : Nat} {predLevel : Nat} (code : UniverseCode)
    {typeCode : RawTerm scope} :
    IsReducibleMemberAt (predLevel + 1) (axisCodeToCell code) typeCode ↔
      IsStronglyNormalizing typeCode ∧ IsReducibleTypeAt predLevel typeCode :=
  IsReducibleMemberAt.universeMembership_iff

/-- **★ The type ↔ term universe reflection (the fib-2 headline).**  For the bridged universe code
`axisCodeToCell code`: (1) it is itself a KERNEL TYPE, classified at the bridged successor (`Type@L : Type@(L+1)`
via `universeFormation`) — term IS type, typed; and (2) its reducible members are PRECISELY the SN reducible
types one level down (the Tarski El decode).  Together the type axis's standalone universe and the kernel's
term-level universe are ONE object: a universe term that reflects, via El, to the type-of-types.  This is the
certificate the fib-0 ledger flag `fxFib_hasTypeTermUniverseReflection` (now `true`) points to; the remaining
type-20 strengthening (decode injectivity + η for El over the WHOLE type system) stays #1532. -/
theorem typeTermUniverseReflection {profile : PolyProfile} {scope : Nat} {predLevel : Nat}
    (context : TypingContext profile scope) (code : UniverseCode) (typeCode : RawTerm scope) :
    HasTypeUnion profile context (axisCodeToCell code) (axisCodeToCell (fxTarskiUniverse.successor code))
      ∧ (IsReducibleMemberAt (predLevel + 1) (axisCodeToCell code) typeCode ↔
          IsStronglyNormalizing typeCode ∧ IsReducibleTypeAt predLevel typeCode) :=
  ⟨axisCodeToCell_typedAtSuccessor context code, axisCodeToCell_universeMembership_iff code⟩

end FX1Poly.Core.Fib
