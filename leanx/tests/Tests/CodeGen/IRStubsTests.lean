import FX.CodeGen.FXCore
import FX.CodeGen.FXLow

/-!
# FXCore / FXLow IR stub smoke tests (H1 + H2)

Compile-time tests pinning the two Phase-7-deferred IR stubs'
surface areas.  The stubs carry no logic — these tests verify:

  * Every `FXCoreOpKind` / `FXLowOpKind` constructor has a
    `name` entry (name lookup is total).
  * `Inhabited` defaults produce syntactically valid terms for
    all envelope structures.
  * Basic construction of a module → function → block → op
    round-trips through the stub types.

If a future iteration adds a new op kind, the `name` match
extends; the tests below continue to pass as long as every
new constructor gets a corresponding `name` arm (Lean's
exhaustive-match check forces this).
-/

namespace Tests.CodeGen.IRStubs

open FX.CodeGen

/-! ## 1. FXCore names are total (spot-check representatives) -/

example : FXCoreOpKind.iAdd.name         = "IAdd"         := rfl
example : FXCoreOpKind.fSqrt.name        = "FSqrt"        := rfl
example : FXCoreOpKind.logAnd.name       = "And"          := rfl
example : FXCoreOpKind.logNot.name       = "Not"          := rfl
example : FXCoreOpKind.bConcat.name      = "BConcat"      := rfl
example : FXCoreOpKind.intToFloat.name   = "IntToFloat"   := rfl
example : FXCoreOpKind.ifOp.name         = "If"           := rfl
example : FXCoreOpKind.returnOp.name     = "Return"       := rfl
example : FXCoreOpKind.secureZero.name   = "SecureZero"   := rfl
example : FXCoreOpKind.makeClosure.name  = "MakeClosure"  := rfl
example : FXCoreOpKind.atomicCAS.name    = "AtomicCAS"    := rfl
example : FXCoreOpKind.ghostCreate.name  = "GhostCreate"  := rfl
example : FXCoreOpKind.encodeOp.name     = "Encode"       := rfl

/-! ## 2. FXLow names are total (spot-check representatives) -/

example : FXLowOpKind.iAdd.name        = "IAdd"         := rfl
example : FXLowOpKind.vecMul.name      = "VecMul"       := rfl
example : FXLowOpKind.stackAlloc.name  = "StackAlloc"   := rfl
example : FXLowOpKind.atomicLoad.name  = "AtomicLoad"   := rfl
example : FXLowOpKind.switchOp.name    = "Switch"       := rfl
example : FXLowOpKind.fpExt.name       = "FPExt"        := rfl
example : FXLowOpKind.phi.name         = "Phi"          := rfl
example : FXLowOpKind.lockRelease.name = "LockRelease"  := rfl

/-! ## 3. DecidableEq — enum equality decides -/

example : (FXCoreOpKind.iAdd == FXCoreOpKind.iAdd) = true   := by native_decide
example : (FXCoreOpKind.iAdd == FXCoreOpKind.iSub) = false  := by native_decide
example : (FXLowOpKind.phi == FXLowOpKind.phi) = true       := by native_decide
example : (FXLowOpKind.phi == FXLowOpKind.iAdd) = false     := by native_decide
example : (FXLowOrdering.seqCst == FXLowOrdering.seqCst) = true := by native_decide
example : (FXLowOrdering.relaxed == FXLowOrdering.seqCst) = false := by native_decide

/-! ## 4. Inhabited defaults compile

`deriving Inhabited` on a `structure` synthesizes `default` by
calling `default` on each field, which IGNORES the struct's
field-default values.  So `(default : FXLowOp).width` is
`FXLowWidth`'s first-constructor default (`.w8`), not the
struct's declared `.unspecified` default.  The struct defaults
apply when `{}`-syntax constructs a value; `default` is the
Inhabited instance.  This section pins the distinction so a
future reader doesn't assume struct defaults flow through
Inhabited. -/

example : (default : FXCoreOp).kind = FXCoreOpKind.iAdd := rfl
example : (default : FXCoreOp).operands = [] := rfl
example : (default : FXCoreOp).dest = none := rfl
example : (default : FXCoreOp).destType = none := rfl

example : (default : FXLowOp).kind = FXLowOpKind.iAdd := rfl
example : (default : FXLowOp).operands = [] := rfl
example : (default : FXLowOp).ordering = none := rfl

-- `{}`-syntax DOES pick up struct field defaults, so this
-- uses the declared `.unspecified`:
example : ({ kind := FXLowOpKind.phi } : FXLowOp).width
            = FXLowWidth.unspecified := rfl

example : (default : FXCoreBlock).id = 0 := rfl
example : (default : FXCoreBlock).ops = [] := rfl
example : (default : FXLowBlock).id = 0 := rfl

example : (default : FXCoreFunction).entry = 0 := rfl
example : (default : FXCoreFunction).blocks = [] := rfl
example : (default : FXLowFunction).entry = 0 := rfl

/-! ## 5. Module construction round-trip -/

/-- A minimal FXCore module: one function (`main`), one block
    (`0`), one op (return).  Exercises the full envelope
    chain: Module → Function → Block → Op. -/
def exampleFXCoreModule : FXCoreModule :=
  { name      := "example"
  , functions :=
      [{ name       := "main"
       , paramTypes := []
       , returnType := .type .zero
       , entry      := 0
       , blocks     :=
           [{ id  := 0
            , ops := [{ kind := .returnOp, operands := [], dest := none }] }]
       }] }

example : exampleFXCoreModule.functions.length = 1 := rfl
example : exampleFXCoreModule.name = "example" := rfl

/-- Same shape for FXLow. -/
def exampleFXLowModule : FXLowModule :=
  { name      := "example"
  , functions :=
      [{ name        := "main"
       , paramWidths := []
       , returnWidth := FXLowWidth.unspecified
       , entry       := 0
       , blocks      :=
           [{ id  := 0
            , ops := [{ kind := .returnOp, width := .unspecified }] }]
       }] }

example : exampleFXLowModule.functions.length = 1 := rfl
example : exampleFXLowModule.functions[0]!.blocks.length = 1 := rfl

/-! ## 6. FXLowWidth — constructors apply and pattern-match

`FXLowWidth` deliberately omits `BEq`/`DecidableEq` at the stub
layer — the recursive `vec` constructor makes auto-derivation
mildly noisy and Phase 7 will add the instance when it's
actually used.  These tests verify the constructors compose
and pattern-match correctly. -/

/-- Extract the lane count from a `vec` width, else `none`.
    Local helper, not a stable API — only used here to exercise
    pattern-matching on the recursive `vec` case. -/
def laneCount? : FXLowWidth → Option Nat
  | .vec n _ => some n
  | _        => none

example : laneCount? (FXLowWidth.vec 8 FXLowWidth.w32) = some 8 := rfl
example : laneCount? FXLowWidth.w64 = none := rfl
example : laneCount? (FXLowWidth.vec 4 (FXLowWidth.vec 2 FXLowWidth.w8))
            = some 4 := rfl
example : laneCount? FXLowWidth.unspecified = none := rfl

end Tests.CodeGen.IRStubs
