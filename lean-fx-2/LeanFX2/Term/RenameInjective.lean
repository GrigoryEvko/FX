import LeanFX2.Term.RenameInjective.EquivIntro

/-! # Term/RenameInjective

Public shim for the term-renaming injectivity cascade.  The semantic leaves
under `Term/RenameInjective/` keep the proof families small enough for Lean's
incremental cache to reuse them independently.
-/
