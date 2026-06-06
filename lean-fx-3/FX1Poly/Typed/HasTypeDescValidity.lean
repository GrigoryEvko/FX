import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Typed.HasTypeValidity
import FX1Poly.Typed.IsTypeDesc

/-! # FX1Poly/Typed/HasTypeDescValidity — INTRINSIC validity of the description engine
    (the first brick of the HasTypeDesc-from-HasType DECOUPLE).

The description engine `HasTypeDesc` is currently anchored to the trusted bespoke
`HasType` by the `⟺` equivalence (completeness `HasType.toHasTypeDesc` + soundness
`HasTypeDesc.toHasType`).  That equivalence VALIDATES the engine, but it is also a
STRAITJACKET: `HasTypeDesc.toHasType` is total, so adding ANY new `gen` row the
bespoke engine lacks (an eliminator, or a new former such as Id/arrow/product)
would break soundness — forcing a matching bespoke `HasType` arm, i.e. the very
per-feature cascade the description engine exists to kill.  To grow the engine
FREELY we must DECOUPLE: give `HasTypeDesc` its own metatheory, proved by induction
on `HasTypeDesc` itself rather than routed through `HasType`.

This file carries the intrinsic VALIDITY metatheorem (a.k.a. regularity /
type-correctness, P3) — the classifier of any well-typed cell is itself a type, AS
SEEN BY THE DESCRIPTION ENGINE.  It is stated against an INTRINSIC `IsTypeDesc`
(`∃ ℓ f, HasTypeDesc Γ T (universeCodeCell ℓ f)`, mirroring the bespoke `IsType` but
over `HasTypeDesc`), and proved by case analysis on the engine — no `Conv.trans`,
no `HasType` induction.

## Why each arm closes intrinsically

* `var` — the only arm needing `WfContext`: the looked-up entry is a type in the
  well-formed context.  Bespoke `WfContext.lookupIsType` gives `HasType Γ (lookup) :
  universe`; `HasType.toHasTypeDesc` (completeness) lifts that universe-typing into
  `HasTypeDesc`, hence `IsTypeDesc`.  (Completeness is sound to use here — it does
  not route the CONCLUSION through `HasType`; it only imports the context's
  well-formedness, which is a `HasType`-defined notion to begin with.)
* `conv` — the reclassifier carries its OWN well-formedness witness
  (`reclassifierTyped : HasTypeDesc Γ reclassifier (universeCodeCell ℓ f)`), which IS
  the `IsTypeDesc` witness verbatim.  No `Conv` reasoning needed — the cleanest arm.
* `universeFormation` — the classifier `universeCodeCell ℓ.lsucc f` is a universe
  code, typed one level up by `universeFormation`.
* `genFormation` — the classifier is `rule.outputType scope levels flag`; pinning the
  generator (Π/Σ, the only `typingRuleDescOf` rows — same `by_cases` + `exfalso`
  generator-pin as `HasTypeDesc.toHasType`) reduces it to `universeCodeCell (lmaxAll
  levels) flag`, a universe code typed one level up.  The `exfalso` branch proves a
  non-whitelisted generator cannot fire the arm (the 0-FP core, reused).

## Zero-axiom

Full-enumeration term-mode `match` on the derivation (the propext-free structural
form used by `HasTypeDesc.toHasType` / `DescTelescope.toHasTypeTelescope`)
— no wildcard, no partial/impossible-case inversion.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

-- The intrinsic native type-predicate `IsTypeDesc` was extracted to `FX1Poly.Typed.IsTypeDesc`
-- (imported above) so the native `WfContextDesc` can depend on the predicate ALONE, without this
-- file's `HasTypeValidity` (old-engine) coupling — the cycle-break prerequisite for the
-- `WfContext := WfContextDesc` rethread.  `classifierIsTypeDesc` below is the OLD bridge-routed
-- validity (its `var` arm reads `WfContext.lookupIsType` + lifts via `HasType.toHasTypeDesc`) and
-- stays here as a rethread/HT-C target; the native twin is `classifierIsTypeDescNative`
-- (`WfContextDescValidity.lean`).

/-- VALIDITY (P3) for the description engine, proved INTRINSICALLY (by case analysis
on `HasTypeDesc`, not via `HasType`): the classifier of any `HasTypeDesc`-typed cell
is itself a description-engine type.  The first brick of the decouple — an invariant
`HasTypeDesc` owns without `HasType`. -/
theorem HasTypeDesc.classifierIsTypeDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContext context)
    (derivation : HasTypeDesc profile context subject classifier) :
    IsTypeDesc profile context classifier :=
  match derivation with
  | .var context index => by
      obtain ⟨levelExpr, flag, universeTyped⟩ :=
        WfContext.lookupIsType context wellFormed index
      exact ⟨levelExpr, flag, HasType.toHasTypeDesc universeTyped⟩
  | .conv levelExpr flag _typed _converts reclassifierTyped =>
      ⟨levelExpr, flag, reclassifierTyped⟩
  | .universeFormation context levelExpr flag =>
      ⟨_, _, HasTypeDesc.universeFormation context levelExpr.lsucc flag⟩
  | .genFormation context generator _payload _children levels flag rule
      isFormation _premises => by
      -- Table-generic: the FORMATION-FAMILY invariant gives `rule.outputType = universeFormerOutput` for
      -- ANY current or future row, so the output is the universe code `Type@(lmaxAll levels)` with no
      -- per-generator (pi/sigma) enumeration here — a new `universeFormerOutput` row is absorbed for free.
      rw [typingRuleDescOf_outputIsUniverseFormer isFormation]
      exact ⟨(lmaxAll levels).lsucc, flag,
        HasTypeDesc.universeFormation context (lmaxAll levels) flag⟩

end FX1Poly.Typed
