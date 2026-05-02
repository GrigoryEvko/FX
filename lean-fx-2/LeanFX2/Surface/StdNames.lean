import LeanFX2.Surface.AST

/-! # Surface/StdNames — canonical stdlib qualified names

Closes kernel gap #2 (operators) from
`Surface/KernelBridge.lean`'s docstring.

Surface operators (`+`, `*`, `<`, etc.) have no kernel
primitive — they desugar to applications of stdlib functions
(`Std.Int.add`, `Std.Int.mul`, `Std.Ord.lt`, ...).  This module
provides the CANONICAL MAPPING from `BinaryOp` / `UnaryOp` to
their stdlib `QualifiedName`.

When the env-aware bridge encounters `rawBinop op lhs rhs`, it
looks up `op.toQualifiedName` in the env's symbol table; if
resolved, it builds `app (app opDef lhsRaw) rhsRaw`.

## Naming convention

* Arithmetic: `Std.Int.add`, `Std.Int.mul`, `Std.Int.sub`,
  `Std.Int.div`, `Std.Int.mod`
* Comparison: `Std.Ord.eq`, `Std.Ord.ne`, `Std.Ord.lt`,
  `Std.Ord.gt`, `Std.Ord.le`, `Std.Ord.ge`
* Logical: `Std.Bool.and`, `Std.Bool.or`, `Std.Bool.not`
* Bitwise: `Std.Bits.and`, `Std.Bits.or`, `Std.Bits.xor`,
  `Std.Bits.shl`, `Std.Bits.shr`
* Range: `Std.Range.exclusive`, `Std.Range.inclusive`
* Pipe: `Std.Pipe.apply`
* Function arrow: not desugared — type-level only
* Propositional: `Std.Prop.iff`, `Std.Prop.implies`
* Constructor test: `Std.Pat.isCtor`
* Negation: `Std.Int.neg`
* Bit-NOT: `Std.Bits.not`

## Construction discipline

Every literal identifier is a `LowerIdent` / `UpperIdent`
constructed with `by decide` — Lean checks the shape proof
(plus the keyword-clean obligation for lowercase) at build
time, so misspelled names fail at compile time.

Zero-axiom under `#print axioms`.
-/

namespace LeanFX2.Surface

/-! ## Module-path UpperIdent literals -/

def UpperIdent.std : UpperIdent :=
  { chars := ['S', 't', 'd'], isShape := by decide }

def UpperIdent.intMod : UpperIdent :=
  { chars := ['I', 'n', 't'], isShape := by decide }

def UpperIdent.boolMod : UpperIdent :=
  { chars := ['B', 'o', 'o', 'l'], isShape := by decide }

def UpperIdent.bitsMod : UpperIdent :=
  { chars := ['B', 'i', 't', 's'], isShape := by decide }

def UpperIdent.ordMod : UpperIdent :=
  { chars := ['O', 'r', 'd'], isShape := by decide }

def UpperIdent.rangeMod : UpperIdent :=
  { chars := ['R', 'a', 'n', 'g', 'e'], isShape := by decide }

def UpperIdent.pipeMod : UpperIdent :=
  { chars := ['P', 'i', 'p', 'e'], isShape := by decide }

def UpperIdent.propMod : UpperIdent :=
  { chars := ['P', 'r', 'o', 'p'], isShape := by decide }

def UpperIdent.patMod : UpperIdent :=
  { chars := ['P', 'a', 't'], isShape := by decide }

/-! ## Operation LowerIdent literals -/

def LowerIdent.add : LowerIdent :=
  { chars := ['a', 'd', 'd'], isShape := by decide, notKeyword := by decide }

def LowerIdent.sub : LowerIdent :=
  { chars := ['s', 'u', 'b'], isShape := by decide, notKeyword := by decide }

def LowerIdent.mul : LowerIdent :=
  { chars := ['m', 'u', 'l'], isShape := by decide, notKeyword := by decide }

def LowerIdent.divName : LowerIdent :=
  { chars := ['d', 'i', 'v'], isShape := by decide, notKeyword := by decide }

def LowerIdent.modName : LowerIdent :=
  { chars := ['m', 'o', 'd'], isShape := by decide, notKeyword := by decide }

def LowerIdent.eq : LowerIdent :=
  { chars := ['e', 'q'], isShape := by decide, notKeyword := by decide }

def LowerIdent.ne : LowerIdent :=
  { chars := ['n', 'e'], isShape := by decide, notKeyword := by decide }

def LowerIdent.lt : LowerIdent :=
  { chars := ['l', 't'], isShape := by decide, notKeyword := by decide }

def LowerIdent.gt : LowerIdent :=
  { chars := ['g', 't'], isShape := by decide, notKeyword := by decide }

def LowerIdent.le : LowerIdent :=
  { chars := ['l', 'e'], isShape := by decide, notKeyword := by decide }

def LowerIdent.ge : LowerIdent :=
  { chars := ['g', 'e'], isShape := by decide, notKeyword := by decide }

def LowerIdent.andOp : LowerIdent :=
  { chars := ['l', 'a', 'n', 'd'], isShape := by decide, notKeyword := by decide }

def LowerIdent.orOp : LowerIdent :=
  { chars := ['l', 'o', 'r'], isShape := by decide, notKeyword := by decide }

def LowerIdent.notOp : LowerIdent :=
  { chars := ['l', 'n', 'o', 't'], isShape := by decide, notKeyword := by decide }

def LowerIdent.bitAndOp : LowerIdent :=
  { chars := ['b', 'a', 'n', 'd'], isShape := by decide, notKeyword := by decide }

def LowerIdent.bitOrOp : LowerIdent :=
  { chars := ['b', 'o', 'r'], isShape := by decide, notKeyword := by decide }

def LowerIdent.bitXorOp : LowerIdent :=
  { chars := ['x', 'o', 'r'], isShape := by decide, notKeyword := by decide }

def LowerIdent.bitNotOp : LowerIdent :=
  { chars := ['b', 'n', 'o', 't'], isShape := by decide, notKeyword := by decide }

def LowerIdent.shl : LowerIdent :=
  { chars := ['s', 'h', 'l'], isShape := by decide, notKeyword := by decide }

def LowerIdent.shr : LowerIdent :=
  { chars := ['s', 'h', 'r'], isShape := by decide, notKeyword := by decide }

def LowerIdent.exclusive : LowerIdent :=
  { chars := ['e', 'x', 'c', 'l', 'u', 's', 'i', 'v', 'e'],
    isShape := by decide, notKeyword := by decide }

def LowerIdent.inclusive : LowerIdent :=
  { chars := ['i', 'n', 'c', 'l', 'u', 's', 'i', 'v', 'e'],
    isShape := by decide, notKeyword := by decide }

def LowerIdent.apply : LowerIdent :=
  { chars := ['a', 'p', 'p', 'l', 'y'], isShape := by decide, notKeyword := by decide }

def LowerIdent.iffName : LowerIdent :=
  { chars := ['i', 'f', 'f'], isShape := by decide, notKeyword := by decide }

def LowerIdent.impliesName : LowerIdent :=
  { chars := ['i', 'm', 'p', 'l', 'i', 'e', 's'],
    isShape := by decide, notKeyword := by decide }

def LowerIdent.isCtor : LowerIdent :=
  { chars := ['i', 's', 'C', 't', 'o', 'r'],
    isShape := by decide, notKeyword := by decide }

def LowerIdent.neg : LowerIdent :=
  { chars := ['n', 'e', 'g'], isShape := by decide, notKeyword := by decide }

def LowerIdent.arrowName : LowerIdent :=
  { chars := ['a', 'r', 'r', 'o', 'w'],
    isShape := by decide, notKeyword := by decide }

/-! ## Path-builder utilities -/

/-- Construct a `QualifiedName` from a list of upper-ident
module components and a final lower-ident. -/
def QualifiedName.ofPath (modules : List UpperIdent)
    (final : LowerIdent) : QualifiedName :=
  { modulePath := modules, finalSegment := AnyIdent.lower final }

/-- Convenient: `Std.<module>.<final>` for two-level paths
from the standard library. -/
def QualifiedName.stdPath (mod : UpperIdent) (final : LowerIdent) :
    QualifiedName :=
  QualifiedName.ofPath [UpperIdent.std, mod] final

/-! ## Operator → QualifiedName mapping -/

/-- Canonical stdlib qualified name for each binary operator.
This is the SOURCE OF TRUTH that the env-aware bridge consults
when resolving `rawBinop op lhs rhs`. -/
def BinaryOp.toQualifiedName : BinaryOp → QualifiedName
  | .plus => QualifiedName.stdPath UpperIdent.intMod LowerIdent.add
  | .minus => QualifiedName.stdPath UpperIdent.intMod LowerIdent.sub
  | .star => QualifiedName.stdPath UpperIdent.intMod LowerIdent.mul
  | .slash => QualifiedName.stdPath UpperIdent.intMod LowerIdent.divName
  | .percent => QualifiedName.stdPath UpperIdent.intMod LowerIdent.modName
  | .eqEq => QualifiedName.stdPath UpperIdent.ordMod LowerIdent.eq
  | .notEq => QualifiedName.stdPath UpperIdent.ordMod LowerIdent.ne
  | .lt => QualifiedName.stdPath UpperIdent.ordMod LowerIdent.lt
  | .gt => QualifiedName.stdPath UpperIdent.ordMod LowerIdent.gt
  | .le => QualifiedName.stdPath UpperIdent.ordMod LowerIdent.le
  | .ge => QualifiedName.stdPath UpperIdent.ordMod LowerIdent.ge
  | .logicalAnd => QualifiedName.stdPath UpperIdent.boolMod LowerIdent.andOp
  | .logicalOr => QualifiedName.stdPath UpperIdent.boolMod LowerIdent.orOp
  | .bitAnd => QualifiedName.stdPath UpperIdent.bitsMod LowerIdent.bitAndOp
  | .bitOr => QualifiedName.stdPath UpperIdent.bitsMod LowerIdent.bitOrOp
  | .bitXor => QualifiedName.stdPath UpperIdent.bitsMod LowerIdent.bitXorOp
  | .shiftLeft => QualifiedName.stdPath UpperIdent.bitsMod LowerIdent.shl
  | .shiftRight => QualifiedName.stdPath UpperIdent.bitsMod LowerIdent.shr
  | .rangeExcl => QualifiedName.stdPath UpperIdent.rangeMod LowerIdent.exclusive
  | .rangeIncl => QualifiedName.stdPath UpperIdent.rangeMod LowerIdent.inclusive
  | .arrow => QualifiedName.stdPath UpperIdent.intMod LowerIdent.arrowName
                -- arrow is type-level; this name is a placeholder
  | .pipe => QualifiedName.stdPath UpperIdent.pipeMod LowerIdent.apply
  | .iff => QualifiedName.stdPath UpperIdent.propMod LowerIdent.iffName
  | .implies => QualifiedName.stdPath UpperIdent.propMod LowerIdent.impliesName
  | .isCtor => QualifiedName.stdPath UpperIdent.patMod LowerIdent.isCtor

/-- Canonical stdlib qualified name for each unary operator. -/
def UnaryOp.toQualifiedName : UnaryOp → QualifiedName
  | .negate => QualifiedName.stdPath UpperIdent.intMod LowerIdent.neg
  | .bitNot => QualifiedName.stdPath UpperIdent.bitsMod LowerIdent.bitNotOp
  | .logicalNot => QualifiedName.stdPath UpperIdent.boolMod LowerIdent.notOp

end LeanFX2.Surface
