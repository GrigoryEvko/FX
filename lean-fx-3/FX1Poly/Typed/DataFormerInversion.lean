import FX1Poly.Typed.HasTypeDescFormerTelescopeInversion
import FX1Poly.Typed.ListCodeShape
import FX1Poly.Typed.OptionCodeShape

/-! # FX1Poly/Typed/DataFormerInversion
    — per-former inversion corollaries for the DATA type-code formers (GTL-10)

The two-child Π / Σ formation formers have hand-written per-former inversion corollaries
(`inversionPiCodeWithConv` / `inversionSigmaCodeWithConv`, `HasTypeDescInversion.lean`): from a typed
`piTyCode` / `sigmaTyCode` cell, recover the component typings and the classifier `Conv`.  The one-child
DATA type-code formers added by GTL-11 / GTL-13 — `listCode`, `optionCode` — had the generic former inversion
(`inversionFormerWithConvGeneric`, GTL-08) but no NAMED per-former corollary.  This file supplies them, giving
the data formers inversion parity with Π / Σ, by specializing the generic inversion at the `listCode` /
`optionCode` rows of `typingRuleDescOf` and projecting the one-child premise telescope.

## The arity-generic story (the GTL-10 census)

With these the per-former inversion family is complete across the four shipped `typingRuleDescOf` formation
rows:

  * **two-child** (`binderShifts = [0,1]`): `piTyCode`, `sigmaTyCode` — `inversionPiCodeWithConv`,
    `inversionSigmaCodeWithConv` (telescope projected by `DescTelescope.twoChildComponents`).
  * **one-child** (`binderShifts = [0]`): `listCode`, `optionCode` — `inversionListCode`, `inversionOptionCode`
    (telescope projected by `DescTelescope.oneChildComponent`).

Everything ELSE in the formation metatheory is already TABLE-GENERIC (one theorem over `typingRuleDescOf`, no
per-former enumeration): the generic inversion (`inversionFormerWithConvGeneric`, GTL-08), uniqueness
(`HasTypeDescUniqueness`, GTL-09), subject reduction (`subjectReductionAtFormerGeneric`, TG-2), and SN
(TG-6).  The only per-former residual is exactly this arity-bound telescope projection — the GTL-07 census
finding, now closed: the per-arity inversion corollaries are the unique place a former's child-arity is
spelled out, and both shipped arities (1 and 2) are covered.

## Zero-axiom verification

Each corollary `obtain`s the generic inversion's `∃ levels flag, DescTelescope … ∧ Conv …` and then `cases`
the one-child telescope (single live `cons` then `nil`, the `[0]` child spine refuting the other arms by
index — no `propext` / `Quot.sound` leak); the classifier `Conv` is reported at the honest canonical level
`lmaxAll [elementLevel]` (the data former's output universe), so NO level normalization is needed.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **`listCode` per-former inversion.**  A typed `listCode` cell `List element` recovers the element child's
typing at its universe code and the classifier `Conv` to the canonical `Type@(lmaxAll [elementLevel])` — the
data-former twin of `inversionPiCodeWithConv`.  Specializes the generic former inversion (GTL-08) at the
`listCode` row, projecting the one-child premise telescope. -/
theorem HasTypeDesc.inversionListCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {element reachedClassifier : RawTerm scope}
    (derivation : HasTypeDesc profile context
      (.mkGen .gen_listCode () (.childCons element .childNil)) reachedClassifier) :
    ∃ (elementLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeDesc profile context element (universeCodeCell elementLevel flag) ∧
      Conv reachedClassifier (universeCodeCell (lmaxAll [elementLevel]) flag) := by
  obtain ⟨levels, flag, telescope, convToCode⟩ :=
    HasTypeDesc.inversionFormerWithConvGeneric derivation typingRuleDescOf_listCode rfl
  cases telescope with
  | cons _context _head elementLevel _restLevels _flag _rest elementTyped restTelescope =>
      cases restTelescope with
      | nil => exact ⟨elementLevel, flag, elementTyped, convToCode⟩

/-- **`optionCode` per-former inversion.**  The `optionCode` twin of `inversionListCode`: a typed `optionCode`
cell `Option element` recovers the element child's typing and the classifier `Conv` to
`Type@(lmaxAll [elementLevel])`. -/
theorem HasTypeDesc.inversionOptionCode {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {element reachedClassifier : RawTerm scope}
    (derivation : HasTypeDesc profile context
      (.mkGen .gen_optionCode () (.childCons element .childNil)) reachedClassifier) :
    ∃ (elementLevel : LevelExpr) (flag : UniverseFlag),
      HasTypeDesc profile context element (universeCodeCell elementLevel flag) ∧
      Conv reachedClassifier (universeCodeCell (lmaxAll [elementLevel]) flag) := by
  obtain ⟨levels, flag, telescope, convToCode⟩ :=
    HasTypeDesc.inversionFormerWithConvGeneric derivation typingRuleDescOf_optionCode rfl
  cases telescope with
  | cons _context _head elementLevel _restLevels _flag _rest elementTyped restTelescope =>
      cases restTelescope with
      | nil => exact ⟨elementLevel, flag, elementTyped, convToCode⟩

end FX1Poly.Typed
