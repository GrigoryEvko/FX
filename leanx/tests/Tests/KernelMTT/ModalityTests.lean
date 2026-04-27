import FX.KernelMTT.Modality

/-!
# Modality tests (R0.3)

Compile-time tests pinning the 20-modality enumeration and
its admissibility-at-mode discipline per `fx_reframing.md`
§3.2–§3.4.  Cross-validates against `Mode.lean`'s independent
modality-name lists.

Coverage:

  * `name` returns the expected string for every constructor
    (20 pinning tests).
  * `byName?` round-trips: `byName? m.name = some m` for every
    `m ∈ Modality.all`.
  * `byName?` rejects unknown names, returns `none`.
  * `admissibleModes` returns the expected list per modality,
    encoding the §3.2–§3.4 mode-assignment table.
  * `isAdmissibleAt` agrees with `admissibleModes` membership.
  * `kind` classifies each modality per §6.3 Tier S/L/T or as
    a Wire primitive.
  * `Mode.canHoldModality?` AGREES with
    `Modality.isAdmissibleAt` — the two independent
    representations describe the same admissibility relation.
-/

namespace Tests.KernelMTT.ModalityTests

open FX.KernelMTT
open FX.KernelMTT.Modality

/-! ## `name` returns the expected string per modality

Twenty tests — one per constructor.  A typo in the `name`
function or an accidental constructor rename flips one of
these and fails the build.  The string names are what
`Mode.canHoldModality?` uses at the string layer, so drift
between the two representations shows up immediately.
-/

example : usage.name       = "usage"       := rfl
example : sec.name         = "sec"         := rfl
example : eff.name         = "eff"         := rfl
example : lifetime.name    = "lifetime"    := rfl
example : provenance.name  = "provenance"  := rfl
example : trust.name       = "trust"       := rfl
example : obs.name         = "obs"         := rfl
example : complexity.name  = "complexity"  := rfl
example : precision.name   = "precision"   := rfl
example : space.name       = "space"       := rfl
example : overflow.name    = "overflow"    := rfl
example : fporder.name     = "fporder"     := rfl
example : mutation.name    = "mutation"    := rfl
example : reentrancy.name  = "reentrancy"  := rfl
example : size.name        = "size"        := rfl
example : repr.name        = "repr"        := rfl
example : clock.name       = "clock"       := rfl
example : protocol.name    = "protocol"    := rfl
example : format.name      = "format"      := rfl
example : version.name     = "version"     := rfl

/-! ## `byName?` round-trips

`byName? m.name = some m` for every modality.  Critical for
the R1.12 diagnostic-mapping layer which will convert string
errors back into structured modality identities. -/

example : byName? "usage"       = some usage       := rfl
example : byName? "sec"         = some sec         := rfl
example : byName? "eff"         = some eff         := rfl
example : byName? "lifetime"    = some lifetime    := rfl
example : byName? "provenance"  = some provenance  := rfl
example : byName? "trust"       = some trust       := rfl
example : byName? "obs"         = some obs         := rfl
example : byName? "complexity"  = some complexity  := rfl
example : byName? "precision"   = some precision   := rfl
example : byName? "space"       = some space       := rfl
example : byName? "overflow"    = some overflow    := rfl
example : byName? "fporder"     = some fporder     := rfl
example : byName? "mutation"    = some mutation    := rfl
example : byName? "reentrancy"  = some reentrancy  := rfl
example : byName? "size"        = some size        := rfl
example : byName? "repr"        = some repr        := rfl
example : byName? "clock"       = some clock       := rfl
example : byName? "protocol"    = some protocol    := rfl
example : byName? "format"      = some format      := rfl
example : byName? "version"     = some version     := rfl

/-- Unknown names return `none`. -/
example : byName? "bogus"              = none := by decide
example : byName? ""                   = none := by decide
example : byName? "USAGE"              = none := by decide  -- case-sensitive
example : byName? "Usage"              = none := by decide
example : byName? "◇_usage"            = none := by decide  -- no prefix
example : byName? "user-defined-grade" = none := by decide

/-! ## Total enumeration

`Modality.all` lists all 20 in constructor order.  Pin both
the length and the head/tail structure.
-/

example : Modality.all.length = 20 := by decide

-- First seven Tier-S modalities — pin the opening of the
-- enumeration.
example : Modality.all.take 7 = [usage, sec, eff, lifetime, provenance, trust, obs] := by
  decide

-- Last four — pin the closing.  `all`'s final entries are
-- one Tier-L (`clock`), one Tier-T (`protocol`), then the two
-- Wire primitives.  Mirrors the `Modality` inductive's
-- declaration order.
example : (Modality.all.reverse.take 4).reverse
        = [clock, protocol, format, version] := by
  decide

/-! ## Admissible modes per modality

Every modality has a non-empty admissibility set.  Four (with
cross-mode availability per §3.3) have 2-element lists; the
other 16 have singletons.  The counts here together with the
`software_admissible_count` etc. theorems in `Modality.lean`
over-constrain the admissibility relation — any inconsistency
fails at one of them.
-/

-- Pure Software-only Tier S (13 of the Tier-S modalities).
example : usage.admissibleModes       = [Mode.software] := rfl
example : sec.admissibleModes         = [Mode.software] := rfl
example : eff.admissibleModes         = [Mode.software] := rfl
example : lifetime.admissibleModes    = [Mode.software] := rfl
example : provenance.admissibleModes  = [Mode.software] := rfl
example : trust.admissibleModes       = [Mode.software] := rfl
example : obs.admissibleModes         = [Mode.software] := rfl
example : space.admissibleModes       = [Mode.software] := rfl
example : overflow.admissibleModes    = [Mode.software] := rfl
example : fporder.admissibleModes     = [Mode.software] := rfl
example : mutation.admissibleModes    = [Mode.software] := rfl
example : reentrancy.admissibleModes  = [Mode.software] := rfl
example : size.admissibleModes        = [Mode.software] := rfl

-- Software + Hardware (the two Tier S dims Hardware uses).
example : complexity.admissibleModes  = [Mode.software, Mode.hardware] := rfl
example : precision.admissibleModes   = [Mode.software, Mode.hardware] := rfl

-- Software + Hardware Tier L.
example : repr.admissibleModes   = [Mode.software, Mode.hardware] := rfl
example : clock.admissibleModes  = [Mode.software, Mode.hardware] := rfl

-- Software-only Tier T.
example : protocol.admissibleModes = [Mode.software] := rfl

-- Wire-only primitives.
example : format.admissibleModes  = [Mode.wire] := rfl
example : version.admissibleModes = [Mode.wire] := rfl

/-! ## `isAdmissibleAt` agrees with `admissibleModes` -/

-- Sample across modalities: Software-admissible ones return
-- `true` at Software, `false` elsewhere.
example : usage.isAdmissibleAt Mode.software = true  := by decide
example : usage.isAdmissibleAt Mode.hardware = false := by decide
example : usage.isAdmissibleAt Mode.wire     = false := by decide
example : usage.isAdmissibleAt Mode.ghost    = false := by decide

-- Hardware-admissible ones (sample: clock) return `true` at
-- Software AND Hardware.
example : clock.isAdmissibleAt Mode.software = true  := by decide
example : clock.isAdmissibleAt Mode.hardware = true  := by decide
example : clock.isAdmissibleAt Mode.wire     = false := by decide
example : clock.isAdmissibleAt Mode.ghost    = false := by decide

-- Wire-only (sample: format) — only Wire.
example : format.isAdmissibleAt Mode.software = false := by decide
example : format.isAdmissibleAt Mode.hardware = false := by decide
example : format.isAdmissibleAt Mode.wire     = true  := by decide
example : format.isAdmissibleAt Mode.ghost    = false := by decide

-- `version` specifically — pins §3.2.4's relocation to Wire.
-- If version ever drifts back to Software, this test flips.
example : version.isAdmissibleAt Mode.software = false := by decide
example : version.isAdmissibleAt Mode.wire     = true  := by decide

/-! ## Kind classification per §6.3

Pinning the tier assignment.  15 Tier S + 2 Tier L + 1 Tier T
+ 2 wire-primitive = 20.  Each group's count is pinned by a
`_count` theorem in `Modality.lean`; here we spot-check that
the classification resolves correctly per modality.
-/

example : usage.kind      = .commutativeSemiring  := rfl
example : sec.kind        = .commutativeSemiring  := rfl
example : eff.kind        = .commutativeSemiring  := rfl
example : complexity.kind = .commutativeSemiring  := rfl
example : size.kind       = .commutativeSemiring  := rfl

example : repr.kind   = .latticeWithValidity := rfl
example : clock.kind  = .latticeWithValidity := rfl

example : protocol.kind = .typestate := rfl

example : format.kind   = .wirePrimitive := rfl
example : version.kind  = .wirePrimitive := rfl

/-! ## Mode-config cross-validation

The `Modality.lean` theorems `software_names_agree` etc.
already pin list equality between
`(admissibleAt Mode.M).map name` and
`(Mode.config Mode.M).modalityNames`.  Here we confirm the
other direction: every string in `Mode.softwareModalityNames`
resolves via `byName?` to a Modality that IS admissible at
Software.  Same for hardware and wire.

This is a round-trip check — catching the case where a name
appears in `Mode.lean` but isn't wired into `Modality.byName?`
(or vice versa).
-/

-- Every name in Mode's softwareModalityNames resolves.
example :
    (Mode.config Mode.software).modalityNames.all
      (fun nm => (byName? nm).isSome) = true := by
  decide

example :
    (Mode.config Mode.hardware).modalityNames.all
      (fun nm => (byName? nm).isSome) = true := by
  decide

example :
    (Mode.config Mode.wire).modalityNames.all
      (fun nm => (byName? nm).isSome) = true := by
  decide

-- And for every Mode's modalityNames, the resolved modality
-- IS admissible at that mode.  Over-constrained test — if
-- Mode says "X lives at Software" but Modality says "X only
-- at Wire", this check fails.
example :
    (Mode.config Mode.software).modalityNames.all
      (fun nm => match byName? nm with
                  | some m => m.isAdmissibleAt Mode.software
                  | none   => false) = true := by
  decide

example :
    (Mode.config Mode.hardware).modalityNames.all
      (fun nm => match byName? nm with
                  | some m => m.isAdmissibleAt Mode.hardware
                  | none   => false) = true := by
  decide

example :
    (Mode.config Mode.wire).modalityNames.all
      (fun nm => match byName? nm with
                  | some m => m.isAdmissibleAt Mode.wire
                  | none   => false) = true := by
  decide

end Tests.KernelMTT.ModalityTests
