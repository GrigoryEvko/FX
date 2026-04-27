import FX.CodeGen.FXCore

/-!
# FXLow IR — Phase 7+ stub per `fx_design.md` §20.3

FXLow is the second binary intermediate representation, produced
from FXCore by type-directed lowering (§20.3).  Unlike FXCore,
FXLow values are **flat, sized virtual registers** — no kernel
`Term` types remain, just bit widths.  Sizes were computed in
FXCore from types, so FXLow is target-independent but
physically-descriptive.

Per §20.1 layering:

  FX      (.fx)   full language, 21 dimensions
  FXCore  (.fxc)  typed, monomorphic, SSA
  FXLow   (.fxl)  flat, virtual registers                 ← this file
  FXAsm   (.fxa)  target instructions, physical regs
  Object  (.o)    raw instruction bytes

## What this file is (Phase 2)

  * `FXLowOpKind` — enum of ~45 operation kinds per §20.3's
    FXLow section.  Sizes on arithmetic ops live on the operand
    payload at real-lowering time (integer width `i8..i64`, float
    `f32/f64`, SIMD `width × lanes`); this stub names the op
    families without exploding the enum to every size variant.
    Phase 7 will either split out size-specific constructors or
    carry size as an explicit payload field; deferred to keep
    this stub's surface area bounded.
  * `FXLowOp` — a single op with operand VRegs, optional dest,
    and a `Width` field for sized arithmetic.
  * `FXLowFunction` / `FXLowBlock` / `FXLowModule` — same layering
    as FXCore, rewritten for flat values.

No lowering from FXCore → FXLow.  That's the Phase 7 body —
task H3 threads through the per-arch emit tables once this
enum is stable.

## Spec acknowledgment

  * §20.3 catalogs FXLow ops.  Spec says "~100 operations"; that
    count assumes every size variant is a distinct constructor.
    This stub picks the coarser "op family" count (~45) and
    carries size as data.  Both encodings will roundtrip through
    the real lowering — the choice is about what fits in a
    stub file.
  * §20.4 consumes this IR into FXAsm.

**Deferred to Phase 7+ per SPEC.md.**
-/

namespace FX.CodeGen

/--
Bit-width tag for sized FXLow operands.  Matches the spec's
§20.3 arithmetic categories.  Real lowering populates this per-
operand; the stub leaves it as metadata on the op envelope. -/
inductive FXLowWidth : Type where
  /-- 8-bit integer or bit-vector. -/
  | w8 : FXLowWidth
  /-- 16-bit. -/
  | w16 : FXLowWidth
  /-- 32-bit — also the integer-side of `f32`. -/
  | w32 : FXLowWidth
  /-- 64-bit — also the integer-side of `f64`. -/
  | w64 : FXLowWidth
  /-- 128-bit.  Wider fixed-width integer / SSE register-size. -/
  | w128 : FXLowWidth
  /-- SIMD width/lane pair: `vec laneCount laneWidth` — e.g.,
      `vec 8 .w32` is an AVX `__m256` holding 8 × i32/f32. -/
  | vec (laneCount : Nat) (laneWidth : FXLowWidth) : FXLowWidth
  /-- Unspecified width — used for stub ops where §20.3 doesn't
      pin a size (control flow, linear bookkeeping). -/
  | unspecified : FXLowWidth
  deriving Repr, Inhabited

/--
Memory-ordering tag for atomic FXLow ops, per §11.10.  Semantics
match the spec's five @Ord annotations; Phase-7 lowering to
FXAsm (§20.5 tables) picks the concrete instruction sequence per
arch given this tag.  Stub carries the enum; no constraint-
checking on which orderings are valid per op (deferred with the
real lowering). -/
inductive FXLowOrdering : Type where
  | relaxed | acquire | release | acqRel | seqCst
  deriving Repr, DecidableEq, Inhabited

/--
FXLow operation kinds per `fx_design.md` §20.3 (FXLow section).
One constructor per op family; bit widths live on the op
envelope (`FXLowOp.width`) rather than as per-width
constructors.  Spec's "~100 operations" emerges after Phase-7
lowering splits these by concrete width — this stub covers the
~45 kind-level entries.
-/
inductive FXLowOpKind : Type where
  -- Integer arithmetic (sized via `width`)
  | iAdd | iSub | iMul | iDiv | iMod
  -- Float arithmetic (sized via `width`)
  | fAdd | fSub | fMul | fDiv
  -- SIMD/vector (width + lanes via `FXLowWidth.vec`)
  | vecAdd | vecSub | vecMul | vecDiv
  -- Memory
  | loadOp | storeOp
  | stackAlloc | frameSlot
  | regionBump
  | slabAlloc | slabFree
  | poolAlloc | poolFree
  -- Control flow
  | branchOp | jumpOp | switchOp
  | callOp | indirectCall | returnOp
  -- Conversion
  | trunc | zExt | sExt | fpExt | fpTrunc | bitCast
  -- Synchronization
  | fenceOp | atomicLoad | atomicStore | atomicCAS
  | lockAcquire | lockRelease
  -- Linear
  | dropOp | secureZero
  -- SSA infrastructure
  | phi
  deriving Repr, DecidableEq, Inhabited

namespace FXLowOpKind

/-- Short human-readable name for diagnostics.  Matches the
    spec's §20.3 bullet names verbatim. -/
def name : FXLowOpKind → String
  | .iAdd           => "IAdd"
  | .iSub           => "ISub"
  | .iMul           => "IMul"
  | .iDiv           => "IDiv"
  | .iMod           => "IMod"
  | .fAdd           => "FAdd"
  | .fSub           => "FSub"
  | .fMul           => "FMul"
  | .fDiv           => "FDiv"
  | .vecAdd         => "VecAdd"
  | .vecSub         => "VecSub"
  | .vecMul         => "VecMul"
  | .vecDiv         => "VecDiv"
  | .loadOp         => "Load"
  | .storeOp        => "Store"
  | .stackAlloc     => "StackAlloc"
  | .frameSlot      => "FrameSlot"
  | .regionBump     => "RegionBump"
  | .slabAlloc      => "SlabAlloc"
  | .slabFree       => "SlabFree"
  | .poolAlloc      => "PoolAlloc"
  | .poolFree       => "PoolFree"
  | .branchOp       => "Branch"
  | .jumpOp         => "Jump"
  | .switchOp       => "Switch"
  | .callOp         => "Call"
  | .indirectCall   => "IndirectCall"
  | .returnOp       => "Return"
  | .trunc          => "Trunc"
  | .zExt           => "ZExt"
  | .sExt           => "SExt"
  | .fpExt          => "FPExt"
  | .fpTrunc        => "FPTrunc"
  | .bitCast        => "BitCast"
  | .fenceOp        => "Fence"
  | .atomicLoad     => "AtomicLoad"
  | .atomicStore    => "AtomicStore"
  | .atomicCAS      => "AtomicCAS"
  | .lockAcquire    => "LockAcquire"
  | .lockRelease    => "LockRelease"
  | .dropOp         => "Drop"
  | .secureZero     => "SecureZero"
  | .phi            => "Phi"

end FXLowOpKind

/--
One FXLow operation in context.  Unlike `FXCoreOp`, result
"type" is represented as a bit width (`FXLowWidth`) rather than
a kernel `Term` — FXLow has lost type-level information after
the FXCore → FXLow lowering pass.  Atomic ops additionally
carry an ordering tag. -/
structure FXLowOp : Type where
  /-- Which operation kind (see §20.3 FXLow catalogue). -/
  kind : FXLowOpKind
  /-- Virtual-register ids of operands. -/
  operands : List VReg := []
  /-- Result register, or `none` for sink ops. -/
  dest : Option VReg := none
  /-- Bit width of the operation's primary datum.  Applies to
      arithmetic, memory loads/stores, vector ops, conversions.
      Control flow uses `.unspecified`. -/
  width : FXLowWidth := .unspecified
  /-- Memory-ordering tag for atomic and fence ops; `none` on
      non-atomic ops. -/
  ordering : Option FXLowOrdering := none
  /-- For phi: list of (block-id, vreg-in-that-block) pairs the
      value flows from.  Empty for non-phi ops. -/
  phiIncoming : List (BlockId × VReg) := []
  deriving Repr, Inhabited

/-- FXLow basic block: SSA-form ops. -/
structure FXLowBlock : Type where
  id  : BlockId
  ops : List FXLowOp
  deriving Repr, Inhabited

/-- FXLow function body: blocks plus entry, with parameter widths
    (not `Term`s — FXLow has no type-level data). -/
structure FXLowFunction : Type where
  name        : String
  paramWidths : List FXLowWidth := []
  returnWidth : FXLowWidth := .unspecified
  entry       : BlockId := 0
  blocks      : List FXLowBlock := []
  deriving Repr, Inhabited

/-- FXLow module: functions + a symbol table (names). -/
structure FXLowModule : Type where
  name      : String
  functions : List FXLowFunction := []
  deriving Repr, Inhabited

end FX.CodeGen
