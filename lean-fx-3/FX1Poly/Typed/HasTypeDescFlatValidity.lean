import FX1Poly.Typed.HasTypeDescFlat
import FX1Poly.Typed.WfContextDescUniqueness
import FX1Poly.Typed.WfContextDescValidity
import FX1Poly.Typed.UniverseCodeConversion

/-! # FX1Poly/Typed/HasTypeDescFlatValidity
    — validity (regularity) + telescope level/flag-agreement for the flat-former engine

`HasTypeDescFlat` (the standalone flat-former engine, #934) now has its full P6 structural metatheory
(inversion / SR / SN / weakening / substitution).  This file adds the remaining formation-engine-parity
properties: **validity** (the classifier of a flat-typed cell is itself a type) and the **telescope
level/flag-agreement** substrate (two flat telescopes over equal children agree on their levels and flag).

## Validity is UNCONDITIONAL (lighter than the formation engine)

`HasTypeDesc.classifierIsTypeDescNative` (formation) needs a `WfContextDesc context` hypothesis — its `var` arm
reads `WfContextDesc.lookupIsTypeDesc`.  The flat engine has NO `var` arm: a flat-former classifier is ALWAYS the
universe code `universeCodeCell (lmaxAll levels) flag` (via `flatTypingRuleDescOf_outputIsUniverseFormer`), typed
one level up by `HasTypeDesc.universeFormation`.  So flat validity is unconditional — no context-well-formedness
needed.

## The agreement substrate

`FlatDescTelescope.uniquenessAgree` mirrors `DescTelescope.uniquenessAgreeNative` but flat: the rest recursion
keeps the SAME context (the flat `cons` does not extend it, so no `WfContextDesc.cons`).  Each head child's
level/flag is settled by the main-engine `HasTypeDesc.uniquenessNative` (+ `universeCodeCell_inj_of_conv`); it
still needs `WfContextDesc context` (to run the main-engine uniqueness on each child).  This is the substrate the
flat uniqueness headline (`HasTypeDescFlat.uniquenessNative`, deferred — it requires a propext-free `mkGen`
second-derivation inversion) will consume.

## Zero-axiom verification

`classifierIsTypeDescNative` is a single-arm `cases` + the `flatTypingRuleDescOf_outputIsUniverseFormer` table
fact + `HasTypeDesc.universeFormation`.  `uniquenessAgree` is structural `match`-recursion: `nil` is `⟨rfl, …⟩`;
`cons` does the flat `childCons` injection (`scope`/`shift`/`restShifts` drill before the head/tail term
equalities), settles head level/flag via `HasTypeDesc.uniquenessNative` + `universeCodeCell_inj_of_conv`, and
recurses on the tail under the SAME `wellFormed`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Flat validity (regularity).**  The classifier of a flat-typed cell is itself a type (`IsTypeDesc`).
UNCONDITIONAL — no `WfContextDesc` needed (the flat engine has no `var` arm): the classifier is always a universe
code, typed one level up.  The flat twin of `HasTypeDesc.classifierIsTypeDescNative`, lighter (hypothesis-free). -/
theorem HasTypeDescFlat.classifierIsTypeDescNative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescFlat profile context subject classifier) :
    IsTypeDesc profile context classifier := by
  cases derivation with
  | flatFormation generator payload children levels flag rule isFlat premise =>
      rw [flatTypingRuleDescOf_outputIsUniverseFormer isFlat]
      exact ⟨(lmaxAll levels).lsucc, flag,
        HasTypeDesc.universeFormation context (lmaxAll levels) flag⟩

/-- **Flat telescope level/flag agreement.**  Two flat telescopes over EQUAL children agree on their `levels`,
and — when the levels are non-empty — on their `flag`.  Mirrors `DescTelescope.uniquenessAgreeNative` but flat:
the rest recursion keeps the SAME context (no `WfContextDesc.cons` extension), since the flat `cons` does not
bind.  Each head child's level/flag is settled by the main-engine `HasTypeDesc.uniquenessNative` +
`universeCodeCell_inj_of_conv`.  The substrate for the flat uniqueness headline (deferred). -/
theorem FlatDescTelescope.uniquenessAgree {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {binderShifts : List Nat}
    {levels1 levels2 : List LevelExpr} {flag1 flag2 : UniverseFlag}
    {children1 children2 : RawTermChildren binderShifts scope}
    (telescope1 : FlatDescTelescope profile context flag1 levels1 children1)
    (telescope2 : FlatDescTelescope profile context flag2 levels2 children2)
    (wellFormed : WfContextDesc context) :
    children1 = children2 → levels1 = levels2 ∧ (levels1 ≠ [] → flag1 = flag2) :=
  match telescope1, telescope2 with
  | .nil, .nil => fun _ =>
      ⟨rfl, fun emptyContradiction => absurd rfl emptyContradiction⟩
  | .cons head1 headLevel1 restLevels1 rest1 headTyped1 restTyped1,
    .cons head2 headLevel2 restLevels2 rest2 headTyped2 restTyped2 =>
      fun childrenEq => by
        injection childrenEq with _headScopeEq _headShiftEq _restShiftsEq headTermEq restTermEq
        subst headTermEq
        subst restTermEq
        have headConv :
            Conv (universeCodeCell headLevel1 flag1) (universeCodeCell headLevel2 flag2) :=
          HasTypeDesc.uniquenessNative headTyped1 wellFormed headTyped2
        obtain ⟨headLevelEq, flagEq⟩ := universeCodeCell_inj_of_conv headConv
        obtain ⟨restLevelsEq, _restFlagImplication⟩ :=
          FlatDescTelescope.uniquenessAgree restTyped1 restTyped2 wellFormed rfl
        exact ⟨by rw [headLevelEq, restLevelsEq], fun _ => flagEq⟩

end FX1Poly.Typed
