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

/-! ## Keyword-clean batch witness (kernel-recheck optimization)

`KeywordKind.fromCharsExact` recognizes keywords by routing the
char list through `String.ofList` and matching String literals.
Each such match reduces, in the kernel, to a `Decidable.casesOn`
chain of `String.decEq` (ByteArray) comparisons over the whole
~92-keyword table.  Proving each `notKeyword` obligation with a
separate `by decide` forces that full reduction once PER name, so
the per-declaration kernel re-check (and the elaborator `whnf`
trace) scales as names times table-size.

Instead we run the recognizer over EVERY operation name in one
`List.all` and discharge it with a single `decide`; each individual
`notKeyword` field then follows by a structural list-membership
lookup that NEVER re-reduces `fromCharsExact`.  Zero axioms: the
extraction is structural induction on `List.Mem` plus
`Bool.noConfusion`; the conversion is `Option.isNone_iff_eq_none`. -/

/-- Every operation-name char list, in declaration order. -/
private def operationNameChars : List (List Char) :=
  [ ['a', 'd', 'd']
  , ['s', 'u', 'b']
  , ['m', 'u', 'l']
  , ['d', 'i', 'v']
  , ['m', 'o', 'd']
  , ['e', 'q']
  , ['n', 'e']
  , ['l', 't']
  , ['g', 't']
  , ['l', 'e']
  , ['g', 'e']
  , ['l', 'a', 'n', 'd']
  , ['l', 'o', 'r']
  , ['l', 'n', 'o', 't']
  , ['b', 'a', 'n', 'd']
  , ['b', 'o', 'r']
  , ['x', 'o', 'r']
  , ['b', 'n', 'o', 't']
  , ['s', 'h', 'l']
  , ['s', 'h', 'r']
  , ['e', 'x', 'c', 'l', 'u', 's', 'i', 'v', 'e']
  , ['i', 'n', 'c', 'l', 'u', 's', 'i', 'v', 'e']
  , ['a', 'p', 'p', 'l', 'y']
  , ['i', 'f', 'f']
  , ['i', 'm', 'p', 'l', 'i', 'e', 's']
  , ['i', 's', 'C', 't', 'o', 'r']
  , ['n', 'e', 'g']
  , ['a', 'r', 'r', 'o', 'w'] ]

/-- Single batched recognizer pass: NONE of the operation names is a
reserved keyword.  One `decide` reduces the whole table once. -/
private theorem operationNamesKeywordClean :
    operationNameChars.all
      (fun chars => (KeywordKind.fromCharsExact chars).isNone) = true := by
  decide

/-- Structural extraction: an element of a list whose `List.all` of a
`Bool` predicate holds itself satisfies the predicate.  Induction on
the membership witness; the impossible `false` arms close by
`Bool.noConfusion`.  No `propext`/`Quot.sound`. -/
private theorem predTrueOfMemAll
    {items : List (List Char)} {pred : List Char → Bool}
    (allTrue : items.all pred = true) :
    ∀ {entry : List Char}, entry ∈ items → pred entry = true := by
  intro entry isMember
  induction isMember with
  | head remaining =>
      rw [List.all_cons] at allTrue
      cases predValue : pred entry with
      | true => rfl
      | false =>
          rw [predValue, Bool.false_and] at allTrue
          exact Bool.noConfusion allTrue
  | tail headEntry isMemberTail extractTail =>
      rw [List.all_cons] at allTrue
      cases headValue : pred headEntry with
      | true =>
          rw [headValue, Bool.true_and] at allTrue
          exact extractTail allTrue
      | false =>
          rw [headValue, Bool.false_and] at allTrue
          exact Bool.noConfusion allTrue

/-- Per-name `notKeyword` proof from the batch witness + a membership
witness, with no re-reduction of `KeywordKind.fromCharsExact`. -/
private theorem notKeywordOfMember {chars : List Char}
    (isMember : chars ∈ operationNameChars) :
    KeywordKind.fromCharsExact chars = none :=
  Option.isNone_iff_eq_none.mp
    (predTrueOfMemAll operationNamesKeywordClean isMember)

/-! ## Operation LowerIdent literals -/

def LowerIdent.add : LowerIdent :=
  { chars := ['a', 'd', 'd'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.head _) }

def LowerIdent.sub : LowerIdent :=
  { chars := ['s', 'u', 'b'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.head _)) }

def LowerIdent.mul : LowerIdent :=
  { chars := ['m', 'u', 'l'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) }

def LowerIdent.divName : LowerIdent :=
  { chars := ['d', 'i', 'v'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) }

def LowerIdent.modName : LowerIdent :=
  { chars := ['m', 'o', 'd'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) }

def LowerIdent.eq : LowerIdent :=
  { chars := ['e', 'q'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) }

def LowerIdent.ne : LowerIdent :=
  { chars := ['n', 'e'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) }

def LowerIdent.lt : LowerIdent :=
  { chars := ['l', 't'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))) }

def LowerIdent.gt : LowerIdent :=
  { chars := ['g', 't'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))) }

def LowerIdent.le : LowerIdent :=
  { chars := ['l', 'e'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))) }

def LowerIdent.ge : LowerIdent :=
  { chars := ['g', 'e'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))) }

def LowerIdent.andOp : LowerIdent :=
  { chars := ['l', 'a', 'n', 'd'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))) }

def LowerIdent.orOp : LowerIdent :=
  { chars := ['l', 'o', 'r'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))) }

def LowerIdent.notOp : LowerIdent :=
  { chars := ['l', 'n', 'o', 't'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))) }

def LowerIdent.bitAndOp : LowerIdent :=
  { chars := ['b', 'a', 'n', 'd'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))) }

def LowerIdent.bitOrOp : LowerIdent :=
  { chars := ['b', 'o', 'r'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))) }

def LowerIdent.bitXorOp : LowerIdent :=
  { chars := ['x', 'o', 'r'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))) }

def LowerIdent.bitNotOp : LowerIdent :=
  { chars := ['b', 'n', 'o', 't'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))) }

def LowerIdent.shl : LowerIdent :=
  { chars := ['s', 'h', 'l'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))) }

def LowerIdent.shr : LowerIdent :=
  { chars := ['s', 'h', 'r'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))) }

def LowerIdent.exclusive : LowerIdent :=
  { chars := ['e', 'x', 'c', 'l', 'u', 's', 'i', 'v', 'e'],
    isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))) }

def LowerIdent.inclusive : LowerIdent :=
  { chars := ['i', 'n', 'c', 'l', 'u', 's', 'i', 'v', 'e'],
    isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))) }

def LowerIdent.apply : LowerIdent :=
  { chars := ['a', 'p', 'p', 'l', 'y'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))) }

def LowerIdent.iffName : LowerIdent :=
  { chars := ['i', 'f', 'f'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))) }

def LowerIdent.impliesName : LowerIdent :=
  { chars := ['i', 'm', 'p', 'l', 'i', 'e', 's'],
    isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))) }

def LowerIdent.isCtor : LowerIdent :=
  { chars := ['i', 's', 'C', 't', 'o', 'r'],
    isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))) }

def LowerIdent.neg : LowerIdent :=
  { chars := ['n', 'e', 'g'], isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))) }

def LowerIdent.arrowName : LowerIdent :=
  { chars := ['a', 'r', 'r', 'o', 'w'],
    isShape := by decide, notKeyword := notKeywordOfMember (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))) }

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

/-- Canonical stdlib qualified name for each binary operator
that desugars to a STDLIB FUNCTION CALL.

Returns `none` for operators that DON'T desugar to a function:
* `arrow` (`->`) — type-level only, never appears in value
  position; bridge should produce a kernel arrow type directly
* `pipe` (`|>`) — `x |> f` desugars structurally to `f x`
  (function application with arg-fn swap), no stdlib def needed
* `isCtor` (`is`) — pattern-matching primitive, not a function;
  desugars to a `match` arm at the kernel

This catches an earlier soundness bug where these three were
mapped to placeholder stdlib names — the env-aware bridge would
have looked them up and produced semantically-wrong applications.

Per fx_grammar.md §3 + §6.2: arrow / pipe / `is` have distinct
syntactic roles; treating them as functions would misinterpret
type expressions, pipe-chains, and constructor tests. -/
def BinaryOp.toQualifiedName : BinaryOp → Option QualifiedName
  | .plus => some <| QualifiedName.stdPath UpperIdent.intMod LowerIdent.add
  | .minus => some <| QualifiedName.stdPath UpperIdent.intMod LowerIdent.sub
  | .star => some <| QualifiedName.stdPath UpperIdent.intMod LowerIdent.mul
  | .slash => some <| QualifiedName.stdPath UpperIdent.intMod LowerIdent.divName
  | .percent => some <| QualifiedName.stdPath UpperIdent.intMod LowerIdent.modName
  | .eqEq => some <| QualifiedName.stdPath UpperIdent.ordMod LowerIdent.eq
  | .notEq => some <| QualifiedName.stdPath UpperIdent.ordMod LowerIdent.ne
  | .lt => some <| QualifiedName.stdPath UpperIdent.ordMod LowerIdent.lt
  | .gt => some <| QualifiedName.stdPath UpperIdent.ordMod LowerIdent.gt
  | .le => some <| QualifiedName.stdPath UpperIdent.ordMod LowerIdent.le
  | .ge => some <| QualifiedName.stdPath UpperIdent.ordMod LowerIdent.ge
  | .logicalAnd => some <| QualifiedName.stdPath UpperIdent.boolMod LowerIdent.andOp
  | .logicalOr => some <| QualifiedName.stdPath UpperIdent.boolMod LowerIdent.orOp
  | .bitAnd => some <| QualifiedName.stdPath UpperIdent.bitsMod LowerIdent.bitAndOp
  | .bitOr => some <| QualifiedName.stdPath UpperIdent.bitsMod LowerIdent.bitOrOp
  | .bitXor => some <| QualifiedName.stdPath UpperIdent.bitsMod LowerIdent.bitXorOp
  | .shiftLeft => some <| QualifiedName.stdPath UpperIdent.bitsMod LowerIdent.shl
  | .shiftRight => some <| QualifiedName.stdPath UpperIdent.bitsMod LowerIdent.shr
  | .rangeExcl => some <| QualifiedName.stdPath UpperIdent.rangeMod LowerIdent.exclusive
  | .rangeIncl => some <| QualifiedName.stdPath UpperIdent.rangeMod LowerIdent.inclusive
  | .iff => some <| QualifiedName.stdPath UpperIdent.propMod LowerIdent.iffName
  | .implies => some <| QualifiedName.stdPath UpperIdent.propMod LowerIdent.impliesName
  -- Distinct syntactic roles — NOT stdlib functions:
  | .arrow => none      -- type-level
  | .pipe => none       -- `x |> f` structural-desugar to `f x`
  | .isCtor => none     -- pattern match, kernel special

/-- Canonical stdlib qualified name for each unary operator. -/
def UnaryOp.toQualifiedName : UnaryOp → QualifiedName
  | .negate => QualifiedName.stdPath UpperIdent.intMod LowerIdent.neg
  | .bitNot => QualifiedName.stdPath UpperIdent.bitsMod LowerIdent.bitNotOp
  | .logicalNot => QualifiedName.stdPath UpperIdent.boolMod LowerIdent.notOp

/-! ## G05/G06 — propositional + range desugaring smoke (#1257, #1258)

The `toQualifiedName` mapping is the single source of truth for
how surface-level `BinaryOp` ctors desugar through the env-aware
bridge.  Rfl smoke theorems pin the four entries that fx_grammar.md
calls out as semantically load-bearing:

* `iff` / `implies` (G05) — these are propositional connectives,
  NOT plain function calls; they desugar to `Std.Prop.iffName` /
  `Std.Prop.impliesName` so the elaborator can apply specialized
  type rules (`Prop ↔ Prop`, `Prop → Prop`).
* `rangeExcl` / `rangeIncl` (G06) — `0..10` and `0..=10` desugar
  to `Std.Range.exclusive` / `Std.Range.inclusive`, distinct
  semantic roles (half-open vs closed).

A typo in either function would break this theorem — the rfl
proof IS the regression check. -/

/-- G05: `iff` desugars to `Std.Prop.iffName`. -/
theorem BinaryOp.toQualifiedName_iff :
    BinaryOp.iff.toQualifiedName =
      some (QualifiedName.stdPath UpperIdent.propMod LowerIdent.iffName) := rfl

/-- G05: `implies` desugars to `Std.Prop.impliesName`. -/
theorem BinaryOp.toQualifiedName_implies :
    BinaryOp.implies.toQualifiedName =
      some (QualifiedName.stdPath UpperIdent.propMod LowerIdent.impliesName) := rfl

/-- G06: `rangeExcl` (`..`) desugars to `Std.Range.exclusive`. -/
theorem BinaryOp.toQualifiedName_rangeExcl :
    BinaryOp.rangeExcl.toQualifiedName =
      some (QualifiedName.stdPath UpperIdent.rangeMod LowerIdent.exclusive) := rfl

/-- G06: `rangeIncl` (`..=`) desugars to `Std.Range.inclusive`. -/
theorem BinaryOp.toQualifiedName_rangeIncl :
    BinaryOp.rangeIncl.toQualifiedName =
      some (QualifiedName.stdPath UpperIdent.rangeMod LowerIdent.inclusive) := rfl

end LeanFX2.Surface
