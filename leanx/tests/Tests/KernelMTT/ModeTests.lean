import FX.KernelMTT.Mode

/-!
# Mode tests (R0.2)

Compile-time tests pinning the FX mode theory's four 0-cells
and their configs per `fx_reframing.md` §3.1–§3.4.  Tests are
`example : _ := by decide` so the assertions fire when the
`Tests` library is built — no runtime suite.

Coverage:

  * Four modes are pairwise distinct under `DecidableEq`.
  * Per-mode modality lists match the §3.2–§3.4 counts.
  * `canHoldModality?` accepts admissible modalities and
    rejects absent ones at each mode.
  * `isPreserved` is `false` for `ghost`, `true` elsewhere.
  * `hasMorphism` accepts declared cross-mode edges, rejects
    spurious names and reversed directions where one-way.
-/

namespace Tests.KernelMTT.ModeTests

open FX.KernelMTT
open FX.KernelMTT.Mode

/-! ## Four modes are pairwise distinct -/

-- Each mode equals itself.
example : ghost    = ghost    := rfl
example : software = software := rfl
example : hardware = hardware := rfl
example : wire     = wire     := rfl

-- Each mode is distinct from every other mode.  With 4 modes
-- we have 6 pairs; every pair is covered.
example : ghost    ≠ software := by decide
example : ghost    ≠ hardware := by decide
example : ghost    ≠ wire     := by decide
example : software ≠ hardware := by decide
example : software ≠ wire     := by decide
example : hardware ≠ wire     := by decide

/-! ## Mode list — all four, no duplicates

`Mode.all` enumerates the four modes in constructor order.
The length and Nodup properties pin the enumeration shape.
-/

example : Mode.all.length = 4 := by decide
example : Mode.all = [ghost, software, hardware, wire] := by decide

/-! ## Modality counts match §3.2–§3.4

The per-mode modality count theorems already live in
`Mode.lean` (`software_modality_count` etc.).  Below we also
check that specific named modalities resolve correctly —
confirming the enumeration's contents, not just its length.
-/

-- Software admits the 15 Tier-S modalities.
example : canHoldModality? software "usage"     = true := by decide
example : canHoldModality? software "sec"       = true := by decide
example : canHoldModality? software "eff"       = true := by decide
example : canHoldModality? software "lifetime"  = true := by decide
example : canHoldModality? software "provenance" = true := by decide
example : canHoldModality? software "trust"     = true := by decide
example : canHoldModality? software "obs"       = true := by decide
example : canHoldModality? software "complexity" = true := by decide
example : canHoldModality? software "precision" = true := by decide
example : canHoldModality? software "space"     = true := by decide
example : canHoldModality? software "overflow"  = true := by decide
example : canHoldModality? software "fporder"   = true := by decide
example : canHoldModality? software "mutation"  = true := by decide
example : canHoldModality? software "reentrancy" = true := by decide
example : canHoldModality? software "size"      = true := by decide

-- Software admits 2 Tier-L modalities.
example : canHoldModality? software "repr"     = true := by decide
example : canHoldModality? software "clock"    = true := by decide

-- Software admits 1 Tier-T modality (Protocol).
example : canHoldModality? software "protocol" = true := by decide

-- Software does NOT admit `version` — version lives at wire
-- per §3.2.4.  This test is explicitly placed so a future
-- refactor that mistakenly re-locates version to Software
-- flips it and fails the build.
example : canHoldModality? software "version"  = false := by decide

-- Hardware admits only clock, repr, precision, complexity.
example : canHoldModality? hardware "clock"      = true := by decide
example : canHoldModality? hardware "repr"       = true := by decide
example : canHoldModality? hardware "precision"  = true := by decide
example : canHoldModality? hardware "complexity" = true := by decide

-- Hardware does NOT admit Software-only modalities.  Sample
-- the four that would be most harmful at Hardware (IO/Alloc
-- in `eff`, arbitrary `usage` linearity, `mutation`, `size`).
example : canHoldModality? hardware "eff"        = false := by decide
example : canHoldModality? hardware "usage"      = false := by decide
example : canHoldModality? hardware "mutation"   = false := by decide
example : canHoldModality? hardware "size"       = false := by decide
example : canHoldModality? hardware "sec"        = false := by decide
example : canHoldModality? hardware "protocol"   = false := by decide

-- Wire admits only format and version.
example : canHoldModality? wire "format"  = true := by decide
example : canHoldModality? wire "version" = true := by decide

-- Wire does NOT admit the Software-mode modalities.
example : canHoldModality? wire "usage"    = false := by decide
example : canHoldModality? wire "eff"      = false := by decide
example : canHoldModality? wire "protocol" = false := by decide

-- Ghost admits NO endo-modalities.
example : canHoldModality? ghost "usage"    = false := by decide
example : canHoldModality? ghost "eff"      = false := by decide
example : canHoldModality? ghost "format"   = false := by decide
example : canHoldModality? ghost "anything" = false := by decide

-- Spurious modality names are rejected at every mode.
example : canHoldModality? ghost    "bogus" = false := by decide
example : canHoldModality? software "bogus" = false := by decide
example : canHoldModality? hardware "bogus" = false := by decide
example : canHoldModality? wire     "bogus" = false := by decide

/-! ## Preservation discipline

Ghost is the ONLY non-preserved mode.  This is the 2LTT
separation per §4.6 — Ghost erases at codegen, the other
three all leave runtime witnesses.
-/

example : isPreserved ghost    = false := by decide
example : isPreserved software = true  := by decide
example : isPreserved hardware = true  := by decide
example : isPreserved wire     = true  := by decide

/-! ## Cross-mode morphisms per §3.5

Diagrammed:

    Ghost ──ghost──> Software ──synth──> Hardware
         <──erase──           <──observe──
                      ┌──serialize──> Wire
                      └──parse──────
-/

-- Ghost → Software via "ghost" lift.
example : hasMorphism ghost software "ghost" = true := by decide

-- Software → Ghost via "erase".
example : hasMorphism software ghost "erase" = true := by decide

-- Software → Hardware via "synth".
example : hasMorphism software hardware "synth" = true := by decide

-- Hardware → Software via "observe".
example : hasMorphism hardware software "observe" = true := by decide

-- Software → Wire via "serialize".
example : hasMorphism software wire "serialize" = true := by decide

-- Wire → Software via "parse".
example : hasMorphism wire software "parse" = true := by decide

/-! ### Morphism rejections — wrong name, wrong direction

`hasMorphism` rejects spurious names and directional mismatches.
The graph is directed; "synth" exists Software→Hardware but
NOT Hardware→Software (that edge is "observe").  These tests
pin the directionality.
-/

-- "synth" does NOT go Hardware → Software (that's "observe").
example : hasMorphism hardware software "synth" = false := by decide

-- "erase" does NOT go Ghost → Software (that's "ghost").
example : hasMorphism ghost software "erase" = false := by decide

-- No direct Ghost → Hardware edge.
example : hasMorphism ghost hardware "anything" = false := by decide

-- No direct Ghost → Wire edge.
example : hasMorphism ghost wire "anything" = false := by decide

-- No direct Hardware → Wire edge.
example : hasMorphism hardware wire "anything" = false := by decide

-- No direct Wire → Hardware edge.
example : hasMorphism wire hardware "anything" = false := by decide

-- Bogus morphism name — rejected even on valid mode pair.
example : hasMorphism software hardware "magic" = false := by decide
example : hasMorphism software ghost    "magic" = false := by decide

/-! ## Name rendering

`Mode.name` matches the prose form used in `fx_reframing.md`
§3.1.  Keeps diagnostics consistent with the spec's vocabulary.
-/

example : name ghost    = "Ghost"    := by decide
example : name software = "Software" := by decide
example : name hardware = "Hardware" := by decide
example : name wire     = "Wire"     := by decide

end Tests.KernelMTT.ModeTests
