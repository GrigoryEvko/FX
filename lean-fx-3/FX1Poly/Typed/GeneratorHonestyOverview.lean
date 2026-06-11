import FX1Poly.Typed.GeneratorSemanticTier
import FX1Poly.Core.GeneratorFinitePolygraph
import FX1Poly.Core.GeneratorTagRoundTrip
import FX1Poly.Core.GeneratorCountPin

/-! # FX1Poly/Typed/GeneratorHonestyOverview — the build-time honesty overview (HON-4)

The forcing function for the generator-honesty ledger: a `#eval` that PRINTS, on every build of this file, the
honest semantic scope of the 203-generator table — how many generators are statically typed, operationally
reducing, semantically live (either), and how many are genuinely RESERVED (bare names, no encoded meaning).  It
keeps the gap visible — and the conspicuous RESERVED line in front of us — so the honesty work does not
quietly stall.

  * `allGenerators` — all 203 generators, enumerated via the total tag-inverse `Generator.fromTag` over the tag
    range `0..202` (`(List.range 203).filterMap Generator.fromTag`).
  * `typedGeneratorCount` / `redexHeadGeneratorCount` / `liveGeneratorCount` / `reservedGeneratorCount` — the
    honest counts, folding the HON-1 (`hasSomeTypingRule`), HON-2 (`hasRedexHead`) and HON-3 (`semanticTier =
    typed ∨ reduces) classifiers over the enumeration.
  * `#eval IO.println …` — the build-time printout.  Prints whenever this file (re)elaborates, e.g. on every
    `lake build FX1Poly` that touches the kernel.

The current snapshot is printed by the `#eval` below on every build — i.e. the bulk of the table is reserved
vocabulary with no static OR operational semantics.

The `s!` interpolation is confined to the `#eval` COMMAND (not a declaration), so the `Nat.toString` `propext`
dependency it carries never touches a gated kernel theorem; the four count DEFS are pure `List.filter`/`length`
over the zero-axiom classifiers and are themselves zero-axiom.  (A machine-checked `… = reservedGeneratorCount`
count theorem is HON-9 / the count pin — deferred, as kernel-reducing a 203-element filter is heavyweight; the
`#eval` reports the count by compiled execution.)

## Zero-axiom

`allGenerators` and the four count defs are `List.range`/`filterMap`/`filter`/`length` over the gated
classifiers — no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  The `#eval`
is a print command, not an audited declaration.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- ALL generators, enumerated via the total tag-inverse `Generator.fromTag` over the tag range
`0..generatorCount-1`.  The range is DERIVED from the pinned `generatorCount` (whose theorems break
on any enum-size change), so growing the table automatically extends this enumeration — a hardcoded
literal here once silently dropped the newest generator from every honesty count (the UNIT-1
landing caught it summing to 197 of 198). -/
def allGenerators : List Generator := (List.range generatorCount).filterMap Generator.fromTag

/-- Count of statically-typed generators (HON-1: typed by some engine). -/
def typedGeneratorCount : Nat := (allGenerators.filter hasSomeTypingRule).length

/-- Count of operational redex-head generators (HON-2: a `Step` fires at the root). -/
def redexHeadGeneratorCount : Nat := (allGenerators.filter (·.hasRedexHead)).length

/-- Count of semantically-live generators (HON-3: typed OR reduces). -/
def liveGeneratorCount : Nat :=
  (allGenerators.filter (fun g => hasSomeTypingRule g || g.hasRedexHead)).length

/-- Count of RESERVED generators — bare names with neither static nor operational meaning. -/
def reservedGeneratorCount : Nat := allGenerators.length - liveGeneratorCount

-- ★ The build-time honesty overview.  Prints the live/reserved scope of the 203-generator table on every build
-- that (re)elaborates this file — the forcing function that keeps the honesty gap visible.  (A `#eval` print
-- command takes no doc comment, so this is a plain line comment.)
#eval IO.println s!"FX1Poly generator honesty: total {allGenerators.length} | statically-typed {typedGeneratorCount} | operational redex-heads {redexHeadGeneratorCount} | semantically-live {liveGeneratorCount} | RESERVED {reservedGeneratorCount}"

end FX1Poly.Typed
