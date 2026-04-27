import FX.Kernel.Pretty
import FX.Kernel.Grade
import FX.Kernel.Term

/-!
# Q57 — `Term.prettyCompact` regression pins

`Term.prettyCompact` is the kernel-local alternative to `repr`
for `TypeError` messages.  The CLI output at `fxi check` time
is what developers read when a check fails, and a regression
that silently unrolls grades back to the full 30-line `repr`
dump would degrade the error UX immediately.

Pins three invariants via `native_decide`:

  1. **Named grades are name-rendered.**  `Grade.default` →
     `"def"`, `Grade.ghost` → `"ghost"`, `Grade.shared` →
     `"ω"`.  Any future grade named `Grade.foo` needs an
     arm here; the default fallback shows just `.usage`.

  2. **Pi / Lam / Sigma render in a single line each.**  A Pi
     type's compact form is `Π(_:A :_g){effects?}. B` — the
     effect suffix is empty iff the return effect is `Tot`.

  3. **Common term shapes don't regress the grade
     abbreviation.**  A `Π Grade.default domain codomain`
     renders `_:_def`, NOT `_:_{usage := .one, security := …}`.
-/

namespace Tests.Kernel.PrettyCompactTests

open FX.Kernel

/-! ## Grade.prettyCompact -/

example : Grade.prettyCompact Grade.default = "def" := by native_decide
example : Grade.prettyCompact Grade.ghost = "ghost" := by native_decide
example : Grade.prettyCompact Grade.shared = "ω" := by native_decide

/-! ## Effect.prettyCompact -/

example : Effect.prettyCompact Effect.tot = "" := by native_decide
example : Effect.prettyCompact { io := true } = "IO" := by native_decide
example : Effect.prettyCompact { io := true, alloc := true }
          = "IO, Alloc" := by native_decide
example : Effect.prettyCompact { exn := true, async := true }
          = "Exn, Async" := by native_decide

/-! ## Level.prettyCompact -/

example : Level.prettyCompact Level.zero = "0" := by native_decide
example : Level.prettyCompact (.succ .zero) = "(0 +1)" := by native_decide

/-! ## Term.prettyCompact — core shapes -/

example : Term.prettyCompact (.type .zero) = "Type<0>" := by native_decide
example : Term.prettyCompact (.const "foo") = "foo" := by native_decide
example : Term.prettyCompact (.var 3) = "#3" := by native_decide
example : Term.prettyCompact (.ind "Nat" []) = "Nat" := by native_decide

/-! ## Term.prettyCompact — Pi preserves named grade -/

example :
  Term.prettyCompact
    (.pi Grade.default (.ind "Nat" []) (.ind "Nat" []) Effect.tot)
    = "Π(_:Nat :_def). Nat" := by native_decide

example :
  Term.prettyCompact
    (.pi Grade.shared (.ind "Nat" []) (.ind "Nat" []) Effect.tot)
    = "Π(_:Nat :_ω). Nat" := by native_decide

example :
  Term.prettyCompact
    (.pi Grade.ghost (.ind "Nat" []) (.ind "Nat" []) Effect.tot)
    = "Π(_:Nat :_ghost). Nat" := by native_decide

/-! ## Term.prettyCompact — Pi with effect suffix -/

example :
  Term.prettyCompact
    (.pi Grade.default (.ind "Nat" []) (.ind "Nat" [])
         { io := true })
    = "Π(_:Nat :_def) →{IO}. Nat" := by native_decide

/-! ## Term.prettyCompact — Lam renders similarly to Pi. -/

example :
  Term.prettyCompact
    (.lam Grade.default (.ind "Nat" []) (.var 0))
    = "λ(_:Nat :_def). #0" := by native_decide

/-! ## Term.prettyCompact — Output stays one-line for nested
Pi (the historical T002 pain point). -/

example :
  let piNatNat := Term.pi Grade.default (.ind "Nat" [])
                   (.ind "Nat" []) Effect.tot
  let nestedPi := Term.pi Grade.default piNatNat
                   (.ind "Nat" []) Effect.tot
  (Term.prettyCompact nestedPi).splitOn "\n" |>.length
  = 1 := by native_decide

end Tests.Kernel.PrettyCompactTests
