-- FX.Smt.Sort — SMT-LIB2 sort lattice for the encoder.
--
-- Untrusted layer.  The encoder must map every kernel `Term`
-- type position to a member of the SMT-LIB2 sort universe; this
-- file enumerates the sorts the encoder knows how to emit and
-- the textual form each takes.
--
-- Map from FX kernel inductive names to SMT sorts:
--
--    Bool                 -> Bool
--    Nat / Int / nat      -> Int
--    Pos / posNat         -> Int (with refinement assumption)
--    bits(n) / signed_bits(n)
--                         -> (_ BitVec n)
--    f32 / f64            -> Real (approximate; FP theory not
--                                  used for refinements)
--    decimal / fracN      -> Real
--    string               -> String (SMT-LIB2 strings theory)
--    Anything else        -> uninterpreted (named after the FX
--                                            inductive)
--
-- `SmtSort.ofIndName?` consults this table.  See `Encode.lean`
-- for the walk that calls it.
--
-- Naming: the type is `SmtSort` not `Sort` because `Sort` is
-- Lean 4's reserved name for the type-universe family
-- (`Prop = Sort 0`, `Type u = Sort (u+1)`).  Same reason every
-- SMT library that targets a dependent host language uses a
-- dedicated name.

namespace FX.Smt

/-- An SMT-LIB2 sort the encoder can emit.  The textual SMT-LIB
    form is produced by `SmtSort.toSmtLib`. -/
inductive SmtSort : Type where
  /-- SMT-LIB2 `Bool` sort — true / false / standard logical
      connectives. -/
  | boolSort  : SmtSort
  /-- SMT-LIB2 `Int` sort — arbitrary-precision integers used
      for FX `nat`, `int`, refinement-bounded numerics. -/
  | intSort   : SmtSort
  /-- SMT-LIB2 `Real` sort — arbitrary-precision rationals used
      for FX `f32`, `f64`, `decimal`, fraction types.  This is
      an approximation: FP semantics differ subtly from rationals
      (NaN, denormals) but for refinement obligations the
      approximation is sound when refinements are over the real
      value, and the elaborator gates FP refinements by the
      Precision dimension before they reach this layer. -/
  | realSort  : SmtSort
  /-- SMT-LIB2 fixed-width bitvector sort `(_ BitVec width)`
      used for `bits(n)` and `signed_bits(n)`. -/
  | bitVec    (width : Nat) : SmtSort
  /-- SMT-LIB2 `String` sort (CVC4/Z3 strings theory). -/
  | stringSort : SmtSort
  /-- An uninterpreted sort introduced for FX inductives the
      encoder doesn't know how to project onto a built-in SMT
      sort.  The `name` field is the SMT-LIB declaration name
      and is used both in the `(declare-sort)` line and in any
      `(declare-fun)` lines that reference the sort. -/
  | uninterpreted (name : String) : SmtSort
  deriving Repr, BEq, Inhabited

namespace SmtSort

/-- Render a sort to its SMT-LIB2 textual form. -/
def toSmtLib : SmtSort -> String
  | .boolSort       => "Bool"
  | .intSort        => "Int"
  | .realSort       => "Real"
  | .bitVec width   => s!"(_ BitVec {width})"
  | .stringSort     => "String"
  | .uninterpreted name => name

/-- Map a kernel inductive type-name (the string stored in
    `Term.ind name args`) to the SMT-LIB sort the encoder should
    use for values of that type.  Returns `none` when the encoder
    has no projection — the caller falls back to an uninterpreted
    sort named after the inductive. -/
def ofIndName? : String -> Option SmtSort
  | "Bool"        => some .boolSort
  | "Nat"         => some .intSort
  | "Int"         => some .intSort
  | "nat"         => some .intSort
  | "int"         => some .intSort
  | "Pos"         => some .intSort
  | "posNat"      => some .intSort
  | "f32"         => some .realSort
  | "f64"         => some .realSort
  | "decimal"     => some .realSort
  | "frac"        => some .realSort
  | "frac64"      => some .realSort
  | "frac128"     => some .realSort
  | "frac256"     => some .realSort
  | "string"      => some .stringSort
  | "String"      => some .stringSort
  | _             => none

/-- Return the SMT-LIB logic that supports the given sorts.  The
    encoder picks the most permissive logic needed: starts at
    AUFLIA (closed-world Int + uninterpreted functions), lifts to
    AUFLIRA / AUFBV / ALL as the sort menu grows. -/
def chooseLogic (sorts : List SmtSort) : String :=
  let hasBitVec := sorts.any (fun s => match s with | .bitVec _ => true | _ => false)
  let hasReal   := sorts.contains .realSort
  let hasString := sorts.contains .stringSort
  let hasUninterp := sorts.any (fun s => match s with | .uninterpreted _ => true | _ => false)
  if hasString then
    "ALL"        -- strings + ints requires general logic
  else if hasBitVec && hasReal then
    "ALL"
  else if hasBitVec then
    if hasUninterp then "AUFBV" else "QF_BV"
  else if hasReal then
    if hasUninterp then "AUFLIRA" else "AUFLIA"
  else
    "AUFLIA"

end SmtSort

end FX.Smt
