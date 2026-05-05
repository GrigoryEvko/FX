import Lake
open Lake DSL

package «lean-fx-2» where
  version := v!"0.1.0-skeleton"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩,
    ⟨`maxHeartbeats, (20000000 : Nat)⟩,
    ⟨`synthInstance.maxHeartbeats, 20000000⟩
  ]

@[default_target]
lean_lib LeanFX2 where
  globs := #[.andSubmodules `LeanFX2]
