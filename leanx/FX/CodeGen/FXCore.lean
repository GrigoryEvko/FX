import FX.Kernel.Term

/-!
# FXCore IR — Phase 7+ stub per `fx_design.md` §20.3

FXCore is the first binary intermediate representation in the
compilation pipeline.  Per §20.1 the layering is:

  FX      (.fx)   full language, 21 dimensions
  FXCore  (.fxc)  typed, monomorphic, SSA           ← this file
  FXLow   (.fxl)  flat, virtual registers
  FXAsm   (.fxa)  target instructions, physical regs
  Object  (.o)    raw instruction bytes

FXCore sits immediately below surface FX: the elaborator lowers a
typed kernel term into an SSA-form FXCore program; everything
below consumes FXCore.  This file is the **type catalogue** —
one constructor per operation kind per §20.3 — so downstream
work (task H3 per-arch tables, the real lowering pass) has a
stable referent.

## What this file is (Phase 2)

  * `FXCoreOpKind` — enum of ~70 operation kinds, one per §20.3
    bullet.  Names match the spec verbatim (CamelCase ↔
    camelCase; Lean-reserved words like `not`, `or`, `let`, `if`
    suffixed with a trailing underscore or operatorized name).
  * `FXCoreOp` — a single operation in context: its kind,
    operand references (virtual-register ids), and optional
    result type (drawn from the kernel's `Term` universe).

No logic.  No lowering from kernel `Term` to `FXCoreOp` —
that's the real H3 / Phase 7 body, blocked on stream streams
D and E having enough surface coverage for a meaningful pass.

## Spec acknowledgment

  * §20.2 is the "FX to FXCore" phase that produces this IR.
  * §20.3 is the op catalogue (this file mirrors it).
  * §20.4 consumes this IR into FXLow.

**Deferred to Phase 7+ per SPEC.md.**
-/

namespace FX.CodeGen

open FX.Kernel

/-- Virtual-register id in FXCore's SSA form.  A non-negative
    integer that uniquely names an SSA value within a function
    body. -/
abbrev VReg : Type := Nat

/-- Basic-block label within a function body. -/
abbrev BlockId : Type := Nat

/-- Field index — used by aggregate data ops (`projectOp`,
    `tupleProj`, closure env project) to pick one component
    out of a record/tuple/env. -/
abbrev FieldIndex : Type := Nat

/--
FXCore operation kinds per `fx_design.md` §20.3.  Every
operation type is enumerated here; operand packaging and
typing constraints live on the `FXCoreOp` envelope below.

Structure mirrors the spec's category headings for future
maintainers cross-referencing §20.3.
-/
inductive FXCoreOpKind : Type where
  -- Integer arithmetic
  | iAdd | iSub | iMul | iDiv | iMod | iNeg
  -- Float arithmetic
  | fAdd | fSub | fMul | fDiv | fNeg | fSqrt
  -- Bit-vector arithmetic
  | bAdd | bSub | bMul
  -- Comparison (returns bool)
  | iCmp | fCmp | bCmp
  -- Logical (boolean)
  | logAnd | logOr | logNot | logXor
  -- Bitwise
  | bAnd | bOr | bXor | bNot | bShl | bShr | bAshr
  | bConcat | bSlice | bZeroExt | bSignExt
  -- Conversion
  | intToFloat | floatToInt | narrow | widen | bitCast
  -- Control flow
  | ifOp | matchOp | callOp | tailCall | returnOp
  -- Binding
  | letOp | letRec
  -- Allocation (strategy encoded in operand payload at real
  -- lowering time; placeholder at stub layer)
  | allocOp | freeOp
  -- Memory
  | loadOp | storeOp
  -- Linear
  | dropOp | secureZero | moveOp | cloneOp
  -- Data (ADTs + tuples)
  | constructOp | projectOp | tupleOp | tupleProj
  -- Closure
  | makeClosure | callClosure | closureEnvProj
  -- Effect
  | performOp | handleOp
  -- Atomic
  | atomicLoad | atomicStore | atomicCAS | fenceOp
  -- Ghost (erased at codegen)
  | ghostCreate | ghostConsume
  -- Contract (boundary validators)
  | validateOp | encodeOp | decodeOp
  deriving Repr, DecidableEq, Inhabited

namespace FXCoreOpKind

/-- Short human-readable name for diagnostics and `fxi dump --core`.
    Matches the spec's §20.3 bullet names verbatim (apart from
    Lean-reserved-word suffixes like `ifOp`). -/
def name : FXCoreOpKind → String
  | .iAdd          => "IAdd"
  | .iSub          => "ISub"
  | .iMul          => "IMul"
  | .iDiv          => "IDiv"
  | .iMod          => "IMod"
  | .iNeg          => "INeg"
  | .fAdd          => "FAdd"
  | .fSub          => "FSub"
  | .fMul          => "FMul"
  | .fDiv          => "FDiv"
  | .fNeg          => "FNeg"
  | .fSqrt         => "FSqrt"
  | .bAdd          => "BAdd"
  | .bSub          => "BSub"
  | .bMul          => "BMul"
  | .iCmp          => "ICmp"
  | .fCmp          => "FCmp"
  | .bCmp          => "BCmp"
  | .logAnd        => "And"
  | .logOr         => "Or"
  | .logNot        => "Not"
  | .logXor        => "Xor"
  | .bAnd          => "BAnd"
  | .bOr           => "BOr"
  | .bXor          => "BXor"
  | .bNot          => "BNot"
  | .bShl          => "BShl"
  | .bShr          => "BShr"
  | .bAshr         => "BAshr"
  | .bConcat       => "BConcat"
  | .bSlice        => "BSlice"
  | .bZeroExt      => "BZeroExt"
  | .bSignExt      => "BSignExt"
  | .intToFloat    => "IntToFloat"
  | .floatToInt    => "FloatToInt"
  | .narrow        => "Narrow"
  | .widen         => "Widen"
  | .bitCast       => "BitCast"
  | .ifOp          => "If"
  | .matchOp       => "Match"
  | .callOp        => "Call"
  | .tailCall      => "TailCall"
  | .returnOp      => "Return"
  | .letOp         => "Let"
  | .letRec        => "LetRec"
  | .allocOp       => "Alloc"
  | .freeOp        => "Free"
  | .loadOp        => "Load"
  | .storeOp       => "Store"
  | .dropOp        => "Drop"
  | .secureZero    => "SecureZero"
  | .moveOp        => "Move"
  | .cloneOp       => "Clone"
  | .constructOp   => "Construct"
  | .projectOp     => "Project"
  | .tupleOp       => "Tuple"
  | .tupleProj     => "TupleProj"
  | .makeClosure   => "MakeClosure"
  | .callClosure   => "CallClosure"
  | .closureEnvProj => "ClosureEnvProj"
  | .performOp     => "Perform"
  | .handleOp      => "Handle"
  | .atomicLoad    => "AtomicLoad"
  | .atomicStore   => "AtomicStore"
  | .atomicCAS     => "AtomicCAS"
  | .fenceOp       => "Fence"
  | .ghostCreate   => "GhostCreate"
  | .ghostConsume  => "GhostConsume"
  | .validateOp    => "Validate"
  | .encodeOp      => "Encode"
  | .decodeOp      => "Decode"

end FXCoreOpKind

/--
One FXCore operation in context.  Carries the operation kind,
a list of operand virtual-register references, an optional
result register (operations like `storeOp` have no dest; most
do), and an optional result type drawn from the kernel's `Term`
universe (present on typed ops, absent on control flow).

Operand semantics per kind are documented on §20.3 and will be
enforced by the real lowering pass.  This envelope is
deliberately loose — Phase 2 uses it as a hook for
`fxi dump --core` rendering, not as a typing front-end. -/
structure FXCoreOp : Type where
  /-- Which operation kind (see §20.3 catalogue above). -/
  kind : FXCoreOpKind
  /-- Virtual-register ids of operands, left to right per the
      spec's argument order for the op kind. -/
  operands : List VReg := []
  /-- Result register when the op produces a value; `none` for
      pure-effect ops like `storeOp`, `returnOp`, `fenceOp`. -/
  dest : Option VReg := none
  /-- Result type (from the kernel's `Term` universe) when the
      op produces a typed value.  Control-flow ops leave this
      `none`. -/
  destType : Option Term := none
  deriving Repr, Inhabited

/--
A basic block: an SSA-form list of operations followed by a
terminator.  Phase 2 doesn't distinguish terminator from body;
the real lowering will.  Carries a block id for branch targets. -/
structure FXCoreBlock : Type where
  id     : BlockId
  ops    : List FXCoreOp
  deriving Repr, Inhabited

/--
An FXCore function body: a list of basic blocks plus the entry
block id.  Parameter list and return type are stored as typed
kernel `Term`s so the layered pipeline sees one type universe
across FX and FXCore. -/
structure FXCoreFunction : Type where
  name        : String
  paramTypes  : List Term := []
  returnType  : Term := .type .zero
  entry       : BlockId := 0
  blocks      : List FXCoreBlock := []
  deriving Repr, Inhabited

/--
An FXCore module: a named collection of functions.  Phase 7
will add per-module constant pools, contract tables, and
dispatch vtables; Phase 2 stops here. -/
structure FXCoreModule : Type where
  name      : String
  functions : List FXCoreFunction := []
  deriving Repr, Inhabited

end FX.CodeGen
