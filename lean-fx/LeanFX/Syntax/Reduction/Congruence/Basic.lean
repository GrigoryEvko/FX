import LeanFX.Syntax.Reduction.Conv

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! StepStar/Conv generic lifters now live in their respective files
(`StepStar.mapStep` in StepStar.lean, `Conv.mapStep` in Conv.lean) so
constructor-specific `*_cong` lemmas can use them in those files
without circular imports.  This file is kept for any future
basic-congruence helpers that genuinely require both Conv and
StepStar in scope. -/

end LeanFX.Syntax
