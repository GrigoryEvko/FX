import FX.KernelMTT.Collisions

/-!
# Collision catalog tests (R0.6)

Compile-time tests pinning the nine §6.8 primary collision
rules + three reductions.  Complements the pinning theorems
in `Collisions.lean` with per-rule field checks and lookup
round-trips.

Coverage:

  * Per-rule field pinning for all 9 rules (error code, name,
    gap ref, refinement presence/content, source list).
  * Per-reduction field pinning for all 3 entries.
  * `byErrorCode?` round-trip for all 9 codes + negative
    cases (unknown code, reduction-gap code, empty).
  * `byGapRef?` round-trip for primary and reduction gaps.
  * Source-count classification (2-way vs 3-way rules).
  * Refinement presence/absence classification.
-/

namespace Tests.KernelMTT.CollisionsTests

open FX.KernelMTT

/-! ## I002 — classified × Fail (gap #102) -/

example : CollisionRule.i002.errorCode  = "I002" := rfl
example : CollisionRule.i002.name       = "classified × Fail" := rfl
example : CollisionRule.i002.gapRef     = "#102" := rfl
example : CollisionRule.i002.docSection = "§6.8" := rfl
example : CollisionRule.i002.refinement = some "declare 'Fail(secret E)'" := rfl
example : CollisionRule.i002.sources.length = 2 := by decide

/-! ## L002 — borrow × Async (gap #104) -/

example : CollisionRule.l002.errorCode  = "L002" := rfl
example : CollisionRule.l002.name       = "borrow × Async" := rfl
example : CollisionRule.l002.gapRef     = "#104" := rfl
example : CollisionRule.l002.refinement.isSome = true := by decide
example : CollisionRule.l002.sources.length = 2 := by decide

/-! ## E044 — CT × Async (gap #105) — UNCONDITIONAL -/

example : CollisionRule.e044.errorCode  = "E044" := rfl
example : CollisionRule.e044.name       = "CT × Async" := rfl
example : CollisionRule.e044.gapRef     = "#105" := rfl
example : CollisionRule.e044.refinement = none := rfl  -- unconditional
example : CollisionRule.e044.sources.length = 2 := by decide

/-! ## I003 — CT × Fail on secret (gap #106) — THREE-WAY -/

example : CollisionRule.i003.errorCode  = "I003" := rfl
example : CollisionRule.i003.name       = "CT × Fail on secret" := rfl
example : CollisionRule.i003.gapRef     = "#106" := rfl
example : CollisionRule.i003.refinement.isSome = true := by decide
example : CollisionRule.i003.sources.length = 3 := by decide

/-! ## M012 — monotonic × concurrent (gap #108) — THREE-WAY -/

example : CollisionRule.m012.errorCode  = "M012" := rfl
example : CollisionRule.m012.name       = "monotonic × concurrent" := rfl
example : CollisionRule.m012.gapRef     = "#108" := rfl
example : CollisionRule.m012.refinement.isSome = true := by decide
example : CollisionRule.m012.sources.length = 3 := by decide

/-! ## P002 — ghost × runtime conditional (gap #109) — UNCONDITIONAL -/

example : CollisionRule.p002.errorCode  = "P002" := rfl
example : CollisionRule.p002.name       = "ghost × runtime conditional" := rfl
example : CollisionRule.p002.gapRef     = "#109" := rfl
example : CollisionRule.p002.refinement = none := rfl  -- unconditional
example : CollisionRule.p002.sources.length = 2 := by decide

/-! ## I004 — classified × async × session (gap #112) — THREE-WAY -/

example : CollisionRule.i004.errorCode  = "I004" := rfl
example : CollisionRule.i004.name       = "classified × async × session" := rfl
example : CollisionRule.i004.gapRef     = "#112" := rfl
example : CollisionRule.i004.refinement.isSome = true := by decide
example : CollisionRule.i004.sources.length = 3 := by decide

/-! ## N002 — decimal × overflow(wrap) (gap #113) -/

example : CollisionRule.n002.errorCode  = "N002" := rfl
example : CollisionRule.n002.name       = "decimal × overflow(wrap)" := rfl
example : CollisionRule.n002.gapRef     = "#113" := rfl
example : CollisionRule.n002.refinement.isSome = true := by decide
example : CollisionRule.n002.sources.length = 2 := by decide

/-! ## L003 — borrow × unscoped spawn (gap #114) -/

example : CollisionRule.l003.errorCode  = "L003" := rfl
example : CollisionRule.l003.name       = "borrow × unscoped spawn" := rfl
example : CollisionRule.l003.gapRef     = "#114" := rfl
example : CollisionRule.l003.refinement.isSome = true := by decide
example : CollisionRule.l003.sources.length = 2 := by decide

/-! ## Three reductions -/

example : Reduction.sessionFail.gapRef     = "#103" := rfl
example : Reduction.sessionFail.name       = "session × Fail" := rfl
example : Reduction.sessionFail.docSection = "§6.8" := rfl

example : Reduction.classifiedLinearFail.gapRef = "#111" := rfl
example : Reduction.classifiedLinearFail.name
            = "classified × linear × Fail" := rfl

example : Reduction.multipleFail.gapRef = "#110" := rfl
example : Reduction.multipleFail.name
            = "multiple Fail effects" := rfl

/-! ## `CollisionRule.all` shape -/

example : CollisionRule.all.length = 9 := by decide

-- Pin the full error-code sequence so any reorder surfaces.
example :
    CollisionRule.all.map (·.errorCode)
      = [ "I002", "L002", "E044", "I003", "M012"
        , "P002", "I004", "N002", "L003" ] := by
  decide

-- Pin the full gap-ref sequence.
example :
    CollisionRule.all.map (·.gapRef)
      = [ "#102", "#104", "#105", "#106", "#108"
        , "#109", "#112", "#113", "#114" ] := by
  decide

/-! ## `Reduction.all` shape -/

example : Reduction.all.length = 3 := by decide

example :
    Reduction.all.map (·.gapRef) = [ "#103", "#111", "#110" ] := by
  decide

/-! ## `CollisionRule.byErrorCode?` — positive lookups -/

example : CollisionRule.byErrorCode? "I002" = some CollisionRule.i002 := by decide
example : CollisionRule.byErrorCode? "L002" = some CollisionRule.l002 := by decide
example : CollisionRule.byErrorCode? "E044" = some CollisionRule.e044 := by decide
example : CollisionRule.byErrorCode? "I003" = some CollisionRule.i003 := by decide
example : CollisionRule.byErrorCode? "M012" = some CollisionRule.m012 := by decide
example : CollisionRule.byErrorCode? "P002" = some CollisionRule.p002 := by decide
example : CollisionRule.byErrorCode? "I004" = some CollisionRule.i004 := by decide
example : CollisionRule.byErrorCode? "N002" = some CollisionRule.n002 := by decide
example : CollisionRule.byErrorCode? "L003" = some CollisionRule.l003 := by decide

/-! ## `CollisionRule.byErrorCode?` — negative lookups -/

-- Unknown codes.
example : CollisionRule.byErrorCode? "X999" = none := by decide
example : CollisionRule.byErrorCode? ""     = none := by decide

-- Reduction gap refs are NOT error codes.
example : CollisionRule.byErrorCode? "#103" = none := by decide
example : CollisionRule.byErrorCode? "#110" = none := by decide
example : CollisionRule.byErrorCode? "#111" = none := by decide

-- Case-sensitive.
example : CollisionRule.byErrorCode? "i002" = none := by decide

/-! ## `CollisionRule.byGapRef?` -/

example : CollisionRule.byGapRef? "#102" = some CollisionRule.i002 := by decide
example : CollisionRule.byGapRef? "#109" = some CollisionRule.p002 := by decide
example : CollisionRule.byGapRef? "#114" = some CollisionRule.l003 := by decide

-- Reduction gap refs are NOT primary rules.
example : CollisionRule.byGapRef? "#103" = none := by decide
example : CollisionRule.byGapRef? "#111" = none := by decide
example : CollisionRule.byGapRef? "#110" = none := by decide

/-! ## `Reduction.byGapRef?` -/

example : Reduction.byGapRef? "#103" = some Reduction.sessionFail := by decide
example : Reduction.byGapRef? "#111" = some Reduction.classifiedLinearFail := by decide
example : Reduction.byGapRef? "#110" = some Reduction.multipleFail := by decide

-- Primary rule gap refs are NOT reductions.
example : Reduction.byGapRef? "#102" = none := by decide
example : Reduction.byGapRef? "#109" = none := by decide
example : Reduction.byGapRef? "#114" = none := by decide

-- Unknown gap.
example : Reduction.byGapRef? "#999" = none := by decide

/-! ## Classification groups

Unconditional rejections (E044, P002) vs conditional (the other 7).
Two-way rules vs three-way rules.
-/

-- Unconditional list — exactly E044 and P002.
example :
    (CollisionRule.all.filter (fun rule => rule.refinement.isNone)).map (·.errorCode)
      = [ "E044", "P002" ] := by
  decide

-- Conditional list — the other 7 in order.
example :
    (CollisionRule.all.filter (fun rule => rule.refinement.isSome)).map (·.errorCode)
      = [ "I002", "L002", "I003", "M012", "I004", "N002", "L003" ] := by
  decide

-- Three-way rules — I003, M012, I004.
example :
    (CollisionRule.all.filter (fun rule => rule.sources.length = 3)).map (·.errorCode)
      = [ "I003", "M012", "I004" ] := by
  decide

-- Two-way rules — the other 6.
example :
    (CollisionRule.all.filter (fun rule => rule.sources.length = 2)).map (·.errorCode)
      = [ "I002", "L002", "E044", "P002", "N002", "L003" ] := by
  decide

/-! ## docSection uniformity

Every R0.6 entry references "§6.8" exactly. -/

example :
    CollisionRule.all.all (fun rule => rule.docSection == "§6.8") = true := by
  decide

example :
    Reduction.all.all (fun red => red.docSection == "§6.8") = true := by
  decide

end Tests.KernelMTT.CollisionsTests
