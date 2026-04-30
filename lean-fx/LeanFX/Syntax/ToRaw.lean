import LeanFX.Syntax.TermSubst

/-! # `Term.toRaw` re-export.

`Term.toRaw` itself was moved into `LeanFX.Syntax.TypedTerm` so it is
available before `LeanFX.Syntax.TermSubst`.  This file is kept as a
thin shim that pulls in `TermSubst` (and transitively the bridge
infrastructure) — modules that imported `LeanFX.Syntax.ToRaw`
continue to compile unchanged. -/

namespace LeanFX.Syntax

end LeanFX.Syntax
