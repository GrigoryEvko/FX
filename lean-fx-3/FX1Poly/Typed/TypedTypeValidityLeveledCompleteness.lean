import FX1Poly.Typed.TypedTypeValidityLeveledTransportUnderWf
import FX1Poly.Typed.HasTypeDescPiFormerInversion
import FX1Poly.Typed.GrownNoTypeInType

/-! # FX1Poly/Typed/TypedTypeValidityLeveledCompleteness
    — LR completeness on the {neutral, universe, Pi} head fragment under wf (closes the route-B loop)

The leveled typed type-validity logical relation (`TypedTypeValidityLeveled`, #1124) has three arms —
`neutral` / `universeType` / `piType` — and two of the three legs of a faithful model were already shipped:

  * SOUNDNESS — `toHasTypeDescPi`: leveled-validity carries the EXACT universe-code typing.
  * TRANSPORT — `transportUnderWf` (#1169): the LR structure survives pointwise-`Conv` context
    conversion, conditional only on target well-formedness.

This file ships the third leg, COMPLETENESS: every grown-typed type code whose head lies in the
fragment {neutral (var-headed eliminator spine), universe code, Π code} IS leveled-valid, under a
well-formed context.  Together the three legs make the LR a faithful wf-conditional model of the
{neutral, universe, Pi} type fragment:

  * `TypedLrHeadFragment` — the fragment, as a structural head predicate (`Π` recurses into BOTH
    components, so fragment membership is hereditary exactly where the LR's `piType` arm recurses).
  * `TypedTypeValidityLeveled.completeOnHeadFragment` — ★ completeness: `WfContextDescPi context →
    HasTypeDescPi context typeCode (universeCodeCell level flag) → ∃ box, leveled-valid`.  The box is
    existential because each arm pins its own candidate (`snKripkeCand` at leaves, `kripkeArrowDep` at
    `Π` with the canonical `snKripkeCodFamily`, #1111).
  * `TypedTypeValidityLeveled.faithfulOnHeadFragment` — the loop closure: on the fragment, under wf,
    leveled-validity at `(level, flag)` IS grown typing at `universeCodeCell level flag`.

## The boundary (which heads CANNOT enter the 3-arm LR)

`TypedLrHeadFragment.headCharacterization` pins membership to the three heads.  Everything else is
OUTSIDE — committed, not silently absorbed:

  * `sigmaTyCodeCell` (proved outside: `sigmaTyCodeCell_notInHeadFragment`) — the LR has no Σ arm; a
    Σ code is not neutral (its root `gen_sigmaTyCode` is no eliminator head) and is neither a universe
    nor a Π cell.
  * The same root argument excludes every other former: data codes (`boolCode`/`natCode`/`listCode`/
    `optionCode`/…), flat codes (`product`/`sum`/`either`/`arrow`/`equiv`), `emptyCode`, modal codes.
    Their MODEL story lives in the denote-keyed bounded reducibility (the §5 candidate bridge:
    emptyType pin + the flat-code pin), not in this 3-arm LR.  Adding arms here is possible follow-on
    work (each arm needs its candidate + a transport case), not claimed.

## Cross-cite: the direct (LR-free) witness

`HasTypeDescPi.convContextUnderWf` (SR-U5, #1133) already transports ANY grown typing across pointwise-
`Conv` context conversion under target wf — with no head restriction.  The LR loop here is NOT the
transport workhorse; its value is the CANDIDATE-CARRYING structure (the Kripke boxes the strengthening /
Abel-reflection campaign consumes).  For bare typing transport, use `convContextUnderWf` directly.

## Zero-axiom verification

Completeness is induction on the fragment: `neutral` → the `neutral` arm directly; `universeType` →
predicativity inversion `universeClassifierLevelIsSucc` pins `(level, flag)` to `(levelExpr.lsucc, flag)`;
`piType` → `invertPiTyCode` + `universeCodeCell_inj_of_conv` pin `(level, flag)` to
`(lmax domainLevel codomainLevel, sharedFlag)`, then the two inductive hypotheses (the codomain under the
wf context extended by the domain's own typing) assemble via the `piType` arm.  The boundary refutations
ride root-generator disequalities (`decide` on the 197-ctor enum, kernel-reduced).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The LR head fragment**: type codes whose head shape the 3-arm leveled LR can interpret — a
neutral (var-headed eliminator spine), a universe code, or a `Π` code whose BOTH components are again
in the fragment (hereditarily, matching where the `piType` arm recurses). -/
inductive TypedLrHeadFragment : {scope : Nat} → RawTerm scope → Prop where
  /-- A neutral type code (var-headed eliminator spine) — the LR's `neutral` arm interprets it. -/
  | neutral {scope : Nat} {typeCode : RawTerm scope}
      (neutralCode : IsNeutral typeCode) : TypedLrHeadFragment typeCode
  /-- A universe code — the LR's `universeType` arm interprets it. -/
  | universeType {scope : Nat} (levelExpr : LevelExpr) (flag : UniverseFlag) :
      TypedLrHeadFragment (universeCodeCell levelExpr flag : RawTerm scope)
  /-- A `Π` code with both components hereditarily in the fragment — the LR's `piType` arm
  interprets it by recursing into exactly these two components. -/
  | piType {scope : Nat} {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
      (domainFragment : TypedLrHeadFragment domainCode)
      (codomainFragment : TypedLrHeadFragment codomainCode) :
      TypedLrHeadFragment (piTyCodeCell domainCode codomainCode)

/-- **The fragment's head characterization (the boundary statement).**  Membership forces one of
exactly three heads: neutral, universe code, or `Π` code.  Σ codes, data codes, flat codes, the empty
code, and modal codes are all OUTSIDE — they satisfy none of the three disjuncts. -/
theorem TypedLrHeadFragment.headCharacterization {scope : Nat} {typeCode : RawTerm scope}
    (fragment : TypedLrHeadFragment typeCode) :
    IsNeutral typeCode ∨
      (∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
        typeCode = universeCodeCell levelExpr flag) ∨
      (∃ (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)),
        typeCode = piTyCodeCell domainCode codomainCode) := by
  cases fragment with
  | neutral neutralCode => exact Or.inl neutralCode
  | universeType levelExpr flag => exact Or.inr (Or.inl ⟨levelExpr, flag, rfl⟩)
  | piType _ _ => exact Or.inr (Or.inr ⟨_, _, rfl⟩)

/-- A neutral term's root is never the Σ-code former: every `IsNeutral` constructor pins the root to a
variable or an eliminator head, and `gen_sigmaTyCode` is none of them. -/
theorem _root_.FX1Poly.Core.IsNeutral.rootGenerator_ne_gen_sigmaTyCode {scope : Nat}
    {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_sigmaTyCode := by
  cases neutral <;> exact fun rootEq => Generator.noConfusion rootEq

/-- **The Σ code is OUTSIDE the LR head fragment** — the committed boundary witness.  The 3-arm LR has
no Σ arm, and a Σ code can enter through none of the three heads: it is not neutral (root
`gen_sigmaTyCode` is no eliminator head), not a universe cell, not a `Π` cell.  The same root argument
excludes every data / flat / empty / modal code (their model story is the §5 candidate bridge, not this
LR). -/
theorem sigmaTyCodeCell_notInHeadFragment {scope : Nat}
    {firstComponentCode : RawTerm scope} {secondComponentCode : RawTerm (scope + 1)}
    (fragment : TypedLrHeadFragment (sigmaTyCodeCell firstComponentCode secondComponentCode)) :
    False := by
  rcases fragment.headCharacterization with neutralCode | ⟨_, _, cellEq⟩ | ⟨_, _, cellEq⟩
  · exact neutralCode.rootGenerator_ne_gen_sigmaTyCode rfl
  · exact Generator.noConfusion (congrArg RawTerm.rootGenerator cellEq)
  · exact Generator.noConfusion (congrArg RawTerm.rootGenerator cellEq)

/-- **★ LR COMPLETENESS on the head fragment, under wf** — the third leg of the route-B loop.  Every
grown-typed type code with fragment head is leveled-valid at its exact universe `(level, flag)`, in a
well-formed context.  By induction on the fragment: the `neutral` arm consumes the typing directly;
the `universeType` arm pins the classifier via the predicativity inversion
(`universeClassifierLevelIsSucc`); the `piType` arm inverts the former typing (`invertPiTyCode`), pins
the level/flag via `universeCodeCell_inj_of_conv`, recurses (the codomain under the wf context extended
by the domain's own inverted typing), and reassembles with the canonical `snKripkeCodFamily`.  The
candidate box is existential — each arm pins its own. -/
theorem TypedTypeValidityLeveled.completeOnHeadFragment {profile : PolyProfile} {scope : Nat}
    {typeCode : RawTerm scope}
    (fragment : TypedLrHeadFragment typeCode) :
    ∀ {context : TypingContext profile scope} {level : LevelExpr} {flag : UniverseFlag},
      WfContextDescPi context →
      HasTypeDescPi profile context typeCode (universeCodeCell level flag) →
      ∃ box : KripkeCandBox scope,
        TypedTypeValidityLeveled profile context typeCode level flag box := by
  induction fragment with
  | neutral neutralCode =>
      intro context level flag _wellFormed typed
      exact ⟨KripkeCandBox.mk snKripkeCand,
        TypedTypeValidityLeveled.neutral neutralCode typed⟩
  | universeType subjectLevel subjectFlag =>
      intro context level flag wellFormed typed
      obtain ⟨levelEq, flagEq⟩ := typed.universeClassifierLevelIsSucc wellFormed
      subst levelEq
      subst flagEq
      exact ⟨KripkeCandBox.mk snKripkeCand, TypedTypeValidityLeveled.universeType typed⟩
  | @piType armScope domainCode codomainCode _domainFragment _codomainFragment
      domainIH codomainIH =>
      intro context level flag wellFormed typed
      obtain ⟨domainLevel, codomainLevel, sharedFlag, domainTyped, codomainTyped, convToCode⟩ :=
        typed.invertPiTyCode
      obtain ⟨levelEq, flagEq⟩ := universeCodeCell_inj_of_conv convToCode
      subst levelEq
      subst flagEq
      obtain ⟨domainBox, domainValid⟩ := domainIH wellFormed domainTyped
      have extendedWf : WfContextDescPi (context.cons domainCode) :=
        WfContextDescPi.cons wellFormed ⟨domainLevel, flag, domainTyped⟩
      obtain ⟨codomainBox, codomainValid⟩ := codomainIH extendedWf codomainTyped
      exact ⟨KripkeCandBox.mk (kripkeArrowDep domainBox.run snKripkeCodFamily),
        TypedTypeValidityLeveled.piType snKripkeCodFamily domainValid codomainValid typed⟩

/-- **★ The route-B loop, closed: on the head fragment, under wf, leveled-validity IS grown typing at
the exact universe code.**  Forward = soundness (`toHasTypeDescPi`); backward = completeness.  With
`transportUnderWf` (#1169) this makes the LR a faithful wf-conditional candidate-carrying model of the
{neutral, universe, Pi} type fragment.  For bare typing transport without candidates, the direct
LR-free witness is `HasTypeDescPi.convContextUnderWf`. -/
theorem TypedTypeValidityLeveled.faithfulOnHeadFragment {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag}
    (fragment : TypedLrHeadFragment typeCode)
    (wellFormed : WfContextDescPi context) :
    (∃ box : KripkeCandBox scope,
        TypedTypeValidityLeveled profile context typeCode level flag box) ↔
      HasTypeDescPi profile context typeCode (universeCodeCell level flag) :=
  ⟨fun ⟨_, relation⟩ => relation.toHasTypeDescPi,
   fun typed =>
     TypedTypeValidityLeveled.completeOnHeadFragment fragment wellFormed typed⟩

/-- Non-vacuity at a genuinely RECURSIVE fragment member: the closed `Π` code over universe codes
`Π (X : Type@0). Type@0` is in the fragment, and completeness produces its leveled validity from its
formation typing — the assembled loop demonstrated end-to-end at scope 0. -/
theorem smoke_completeOnHeadFragment_piOverUniverse {profile : PolyProfile} :
    ∃ box : KripkeCandBox 0,
      TypedTypeValidityLeveled (profile := profile)
        (TypingContext.empty : TypingContext profile 0)
        (piTyCodeCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
          (universeCodeCell LevelExpr.lzero UniverseFlag.standard))
        (LevelExpr.lmax LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc) UniverseFlag.standard box :=
  TypedTypeValidityLeveled.completeOnHeadFragment
    (TypedLrHeadFragment.piType
      (TypedLrHeadFragment.universeType LevelExpr.lzero UniverseFlag.standard)
      (TypedLrHeadFragment.universeType LevelExpr.lzero UniverseFlag.standard))
    WfContextDescPi.emptyIsWellFormed
    (HasTypeDescPi.piFormationViaGenArm (TypingContext.empty : TypingContext profile 0)
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
      LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc UniverseFlag.standard
      (HasTypeDescPi.ofFormation
        (HasTypeDesc.universeFormation (TypingContext.empty : TypingContext profile 0)
          LevelExpr.lzero UniverseFlag.standard))
      (HasTypeDescPi.ofFormation
        (HasTypeDesc.universeFormation
          ((TypingContext.empty : TypingContext profile 0).cons
            (universeCodeCell LevelExpr.lzero UniverseFlag.standard))
          LevelExpr.lzero UniverseFlag.standard)))

end FX1Poly.Typed
