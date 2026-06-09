import FX1Poly.Typed.HasTypeDescFlatValidity
import FX1Poly.Typed.HasTypeDescFlatFormerInversion

/-! # FX1Poly/Typed/HasTypeDescFlatUniqueness
    — the flat-engine TYPING-UNIQUENESS headline: two flat derivations of the same subject have Conv classifiers

`HasTypeDescFlatValidity` shipped the substrate (`FlatDescTelescope.uniquenessAgree`: equal children force equal
levels and — when nonempty — equal flag) and named the headline it would feed: `HasTypeDescFlat.uniquenessNative`,
deferred because it needs a propext-free second-derivation inversion at an `.mkGen` cell.  This file lands that
headline.  It is the flat-engine analogue of the grown `HasTypeDesc.uniquenessNative` — the determinism property a
type-checker rests on (a term has at most one classifier up to definitional equality).

## The propext-free route

The two derivations share the same subject `t`.  Casing the FIRST derivation is clean: its conclusion index `t`
is a FREE variable, so `cases` unifies it with the single `flatFormation` constructor's `.mkGen generator payload
children` shape and prunes nothing (one constructor, no impossible arms, no equation lemmas → no `propext` leak).
That exposes `t = .mkGen generator1 payload1 children1`, so the SECOND derivation is now a derivation over a
CONCRETE `.mkGen` cell.  Casing THAT directly would drill the dependent payload/children equalities and leak
`propext` (the cell-index inversion trap), so the second derivation is inverted by the propext-free
`HasTypeDescFlat.inversionFormerWithConv` — it aligns the head generator via `congrArg headGenerator` BEFORE any
`injection`.  Both inversions yield a `FlatDescTelescope` over the SAME `children1`, so
`FlatDescTelescope.uniquenessAgree` settles their levels (equal) and flag.

The flag agreement is gated on `levels1 ≠ []` (the empty telescope pins no flag).  A flat former has binderShifts
`[0, 0]` (two children, `flatFormerBinderShifts`), and a flat telescope's levels has the same length as its
children (`binderShiftsAreAllZero` gives `binderShifts = List.replicate levels.length 0`); equating the two forces
`levels.length = 2`, hence nonempty.  With levels and flag agreeing, both classifiers reduce (definitionally,
`universeFormerOutput scope levels flag ≡ universeCodeCell (lmaxAll levels) flag`) to the SAME universe code, so
they are `Conv` by the second inversion's `Conv` and symmetry/rewriting.

## Zero-axiom verification

`cases` on the free-index first derivation is propext-clean (single constructor); the second derivation goes
through the propext-free `inversionFormerWithConv`; the nonemptiness contradiction is `nomatch` on `[0,0] = []`
(constructor mismatch, no equation lemmas); `FlatDescTelescope.uniquenessAgree` is itself zero-axiom; `Conv.sym`
is the structural symmetry of the join relation.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ Flat-engine typing uniqueness.**  Two flat-formation derivations of the SAME subject under a well-formed
context have definitionally-equal classifiers.  The flat analogue of `HasTypeDesc.uniquenessNative`: the flat data
formers (product / sum / either / arrow / equiv) classify their subject uniquely up to `Conv`.  Proved via the
propext-free former inversion (`HasTypeDescFlat.inversionFormerWithConv` on the second derivation, after a clean
free-index `cases` on the first) and the telescope agreement (`FlatDescTelescope.uniquenessAgree`), with the flag
settled by the nonemptiness of the two-child flat telescope's level list. -/
theorem HasTypeDescFlat.uniquenessNative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier1 classifier2 : RawTerm scope}
    (derivation1 : HasTypeDescFlat profile context subject classifier1)
    (derivation2 : HasTypeDescFlat profile context subject classifier2)
    (wellFormed : WfContextDesc context) :
    Conv classifier1 classifier2 := by
  cases derivation1 with
  | flatFormation generator1 payload1 children1 levels1 flag1 rule1 isFlat1 premise1 =>
    obtain rfl : rule1 = { outputType := universeFormerOutput } :=
      flatFormationRuleIsUniverseFormer isFlat1
    show Conv (universeCodeCell (lmaxAll levels1) flag1) classifier2
    obtain ⟨levels2, flag2, premise2, convReached⟩ :=
      derivation2.inversionFormerWithConv isFlat1 rfl
    obtain ⟨levelsAgree, flagAgree⟩ :=
      FlatDescTelescope.uniquenessAgree premise1 premise2 wellFormed rfl
    have shiftsAllZero : generator1.binderShifts = List.replicate levels1.length 0 :=
      premise1.binderShiftsAreAllZero
    have shiftsFlat : generator1.binderShifts = [0, 0] :=
      flatFormerBinderShifts isFlat1
    have levelsNonempty : levels1 ≠ [] := by
      intro levelsEmpty
      rw [levelsEmpty] at shiftsAllZero
      have reduced : generator1.binderShifts = [] := shiftsAllZero
      rw [shiftsFlat] at reduced
      nomatch reduced
    have flagEq : flag1 = flag2 := flagAgree levelsNonempty
    rw [levelsAgree, flagEq]
    exact Conv.sym convReached

end FX1Poly.Typed
