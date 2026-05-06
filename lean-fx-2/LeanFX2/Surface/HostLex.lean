import LeanFX2.Surface.Lex

/-! # Surface/HostLex — explicit host `String` lexer boundary

`Surface/Lex.lean` is the zero-axiom lexer over `List Char`.  This
module contains the one ergonomic host shim that accepts Lean `String`.

`String.toList` in Lean 4 v4.29.1 deserialises the UTF-8 byte array and
pulls in `propext`, `Classical.choice`, and `Quot.sound`.  For TCB
accounting, this module is deliberately excluded from the public
`LeanFX2` umbrella and from production namespace axiom sweeps.  Use it
only at CLI/API/smoke-test boundaries; kernel and surface proofs should
call `Lex.run` on explicit `List Char`.
-/

namespace LeanFX2.Surface

namespace HostLex

/-- Consume an in-memory host `String` by crossing the documented
`String.toList` boundary, then run the zero-axiom `List Char` lexer. -/
def runFromString (source : String) :
    Except (Array LexError) (Array PositionedToken) :=
  Lex.run source.toList

end HostLex

end LeanFX2.Surface
