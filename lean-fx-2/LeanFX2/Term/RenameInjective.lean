import LeanFX2.Term.RenameInjective.ConstructorFamilies
import LeanFX2.Term.RenameInjective.BinderInversions
import LeanFX2.Term.RenameInjective.CastInversions
import LeanFX2.Term.RenameInjective.ClosedData
import LeanFX2.Term.RenameInjective.CubicalCollections
import LeanFX2.Term.RenameInjective.IdentityEliminators
import LeanFX2.Term.RenameInjective.ReflexivityInterval
import LeanFX2.Term.RenameInjective.IdentityInterval
import LeanFX2.Term.RenameInjective.ModalStructural
import LeanFX2.Term.RenameInjective.TypeCodes
import LeanFX2.Term.RenameInjective.EquivIntro

/-! # Term/RenameInjective

Public shim for the term-renaming injectivity cascade.  The semantic leaves
under `Term/RenameInjective/` keep the proof families small enough for Lean's
incremental cache to reuse them independently.
-/
