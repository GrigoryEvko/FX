import LeanFX2.Surface.Lex
import LeanFX2.Surface.Parse
import LeanFX2.Surface.Elab
import LeanFX2.Algo.Check
import LeanFX2.Algo.Eval

/-! # Pipeline — end-to-end FX compilation

```lean
def Pipeline.compile (source : String) :
    Except CompileError CompiledModule
```

Composes the full pipeline:

```
String          (FX source)
  → lex          (Surface/Lex.lean)
  → parse        (Surface/Parse.lean)
  → elab         (Surface/Elab.lean)
  → check        (Algo/Check.lean — already happens inside elab)
  → eval / emit  (Algo/Eval.lean or backend)
  → CompiledModule
```

## CompileError unification

Errors from lex/parse/elab/check unify into one type with the
originating phase tagged + source position preserved:

```lean
inductive CompileError
  | lex (err : LexError) (pos : Pos)
  | parse (err : ParseError) (pos : Pos)
  | elab (err : ElabError) (pos : Pos)
  | check (err : CheckError) (pos : Pos)
```

Diagnostics: each error renders with source-line context
(reconstruct via Surface/Print or carry source string).

## End-to-end smoke

```lean
example : Pipeline.compile "fn main() : unit = ();" = .ok ... := by
  -- Should produce a CompiledModule with main : unit at the kernel
```

## Dependencies

* All Surface/* + Algo/*

## Downstream

* User-facing CLI / API — `fxc` invokes `Pipeline.compile`

## Implementation plan (Layer 11)

1. Unify CompileError across phases
2. Compose lex → parse → elab → check
3. Define `CompiledModule` (typed kernel + metadata)
4. End-to-end smoke

Target: ~400 lines.
-/

namespace LeanFX2

-- TODO Layer 11: Pipeline.compile end-to-end

end LeanFX2
