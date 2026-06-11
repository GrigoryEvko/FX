import FX1Poly.Typed.HasTypeDescTermIndexedFormer
import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Typed.HasTypeDescPiSubstitution

/-! # FX1Poly/Typed/HasTypeDescTermIndexedFormerWeakening — NATIVE-13: weakening + substitution (P6) for the
    term-indexed former engine

`HasTypeDescTermIndexedFormer` (NATIVE-12, #1289) types the term-indexed formers `Id A a b` / `Bridge A a b`
through ONE generic `genFormation` arm driven by `termIndexedFormerDescOf` + the children-indexed
`TermIndexedFormerTelescope` premise.  These are type CODES — they appear in OPEN contexts (e.g. `Bridge A a b`
with `A`, `a`, `b` free), so the engine needs the same structural metatheory the formation/flat engines have:
typing is preserved along any context-respecting renaming (weakening) and under any well-typed substitution
(the β leg).  This file supplies the first metatheory brick (P6 first half) — the term-indexed twin of
`HasTypeDescFlatWeakening` / `HasTypeDescFlatSubstitution`.

## The carrier-threaded telescope is even lighter than the flat one

`FlatDescTelescope` renames each head with the BASE renaming (no `iterateLiftRaw`) and re-types it at the SAME
universe code.  The term-indexed `TermIndexedEndpoints` is lighter still: each endpoint is typed at the
RECORDED `carrier` (an EARLIER child, not a universe), so renaming an endpoint re-types it at the RENAMED
carrier `RawTerm.rename rawRenaming carrier` — no `rename_universeCodeCell` per endpoint, just the grown
engine's own `HasTypeDescPi.renameRespectingContext`.  Only the carrier head (typed at a universe) needs the
`rename_universeCodeCell` collapse, exactly once at the `TermIndexedFormerTelescope.mk` head.

The cell-reconstruction arm is identical in shape to the flat/formation one:
`termIndexedFormerRuleImpliesNotVariable` discharges the `≠ gen_var` side condition,
`termIndexedFormerRuleIsCarrierOutput` makes `rule` concrete via `obtain rfl`, and the abstract cell
distributes the renaming/substitution via `RawTerm.rename_mkGen_of_ne_var` / `RawTerm.subst_mkGen_of_ne_var`
— so a future term-indexed former row absorbs here with no edit (table-generic).

## Zero-axiom

The endpoint/carrier transports reuse the shipped grown `HasTypeDescPi.renameRespectingContext` /
`substRespectingContext`; the table helpers are `by_cases` + `Option.some.inj` (the flat-helper idiom); the
`subst0` corollary instantiates `RawTermSubst.singleton` with `subst_singleton_renameWeaken_cancel`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated
in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-! ## Table helpers (the `gen_var` / carrier-output discriminators) -/

/-- **A term-indexed former's generator is not `gen_var`.**  `gen_var` is neither `gen_bridgeCode` nor
`gen_idCode`, so `termIndexedFormerDescOf gen_var = none ≠ some rule`.  Consumed by the cell-reconstruction
(`RawTerm.rename_mkGen_of_ne_var` / `subst_mkGen_of_ne_var` need `generator ≠ gen_var`). -/
theorem termIndexedFormerRuleImpliesNotVariable {generator : Generator} {rule : TermIndexedFormerDesc}
    (isTermIndexed : termIndexedFormerDescOf generator = some rule) :
    generator ≠ Generator.gen_var := by
  intro isVariable
  subst isVariable
  dsimp only [termIndexedFormerDescOf] at isTermIndexed
  rw [if_neg (fun isBridge => Generator.noConfusion isBridge),
    if_neg (fun isId => Generator.noConfusion isId)] at isTermIndexed
  cases isTermIndexed

/-- **A term-indexed former rule IS the carrier-output rule (full structure).**  Since
`TermIndexedFormerDesc` has exactly the `outputType` field and the table returns only
`{ outputType := termIndexedCarrierOutput }`, any `some rule` upgrades to the structure equation — what the
cell-reconstruction consumer needs (`obtain rfl`). -/
theorem termIndexedFormerRuleIsCarrierOutput {generator : Generator} {rule : TermIndexedFormerDesc}
    (isTermIndexed : termIndexedFormerDescOf generator = some rule) :
    rule = { outputType := termIndexedCarrierOutput } := by
  by_cases hBridge : generator = .gen_bridgeCode
  · subst hBridge; exact (Option.some.inj isTermIndexed.symm)
  · by_cases hId : generator = .gen_idCode
    · subst hId; exact (Option.some.inj isTermIndexed.symm)
    · exfalso
      dsimp only [termIndexedFormerDescOf] at isTermIndexed
      rw [if_neg hBridge, if_neg hId] at isTermIndexed
      cases isTermIndexed

/-! ## Renaming / weakening -/

/-- **Endpoint sub-telescope renaming.**  Re-types every endpoint along a context-respecting renaming; the
endpoints stay typed at the RENAMED carrier (each was typed at `carrier`, now at `RawTerm.rename rawRenaming
carrier`).  No `rename_universeCodeCell` — endpoints classify at the carrier, not a universe code.  Structural
`match`-recursion reusing the grown `HasTypeDescPi.renameRespectingContext` on each endpoint. -/
theorem TermIndexedEndpoints.renameRespectingContext {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {carrier : RawTerm scope} {shifts : List Nat}
    {children : RawTermChildren shifts scope}
    (telescope : TermIndexedEndpoints profile context carrier children) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming scope targetScope),
      (∀ index : Fin scope,
        RawTerm.rename rawRenaming (context.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      TermIndexedEndpoints profile targetContext (RawTerm.rename rawRenaming carrier)
        (RawTermChildren.rename rawRenaming children) :=
  match telescope with
  | .nil => fun _targetContext _rawRenaming _contextCondition => TermIndexedEndpoints.nil
  | .cons endpoint rest endpointTyped restTyped =>
      fun targetContext rawRenaming contextCondition =>
        TermIndexedEndpoints.cons (RawTerm.rename rawRenaming endpoint)
          (RawTermChildren.rename rawRenaming rest)
          (HasTypeDescPi.renameRespectingContext endpointTyped targetContext rawRenaming
            contextCondition)
          (TermIndexedEndpoints.renameRespectingContext restTyped targetContext rawRenaming
            contextCondition)

/-- **Term-indexed former telescope renaming.**  Re-types the full premise: the carrier head renames at its
universe code (the one `rename_universeCodeCell` collapse) and the endpoint tail renames at the renamed
carrier (`TermIndexedEndpoints.renameRespectingContext`). -/
theorem TermIndexedFormerTelescope.renameRespectingContext {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {shifts : List Nat}
    {children : RawTermChildren shifts scope} {carrier : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag}
    (telescope : TermIndexedFormerTelescope profile context children carrier level flag) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming scope targetScope),
      (∀ index : Fin scope,
        RawTerm.rename rawRenaming (context.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      TermIndexedFormerTelescope profile targetContext
        (RawTermChildren.rename rawRenaming children)
        (RawTerm.rename rawRenaming carrier) level flag :=
  match telescope with
  | .mk carrier rest level flag carrierTyped endpointsTyped =>
      fun targetContext rawRenaming contextCondition => by
        have carrierRenamed :
            HasTypeDescPi profile targetContext (RawTerm.rename rawRenaming carrier)
              (universeCodeCell level flag) := by
          have raw :=
            HasTypeDescPi.renameRespectingContext carrierTyped targetContext rawRenaming
              contextCondition
          rwa [rename_universeCodeCell] at raw
        exact TermIndexedFormerTelescope.mk (RawTerm.rename rawRenaming carrier)
          (RawTermChildren.rename rawRenaming rest) level flag carrierRenamed
          (TermIndexedEndpoints.renameRespectingContext endpointsTyped targetContext rawRenaming
            contextCondition)

/-- **Term-indexed former renaming.**  A `HasTypeDescTermIndexedFormer` derivation is preserved along any
context-respecting renaming — the term-indexed twin of `HasTypeDescFlat.renameRespectingContext`.  Single-arm
`cases` reusing the telescope rename; the abstract cell reconstructs table-generically via
`RawTerm.rename_mkGen_of_ne_var`. -/
theorem HasTypeDescTermIndexedFormer.renameRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescTermIndexedFormer profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : RawRenaming sourceScope targetScope),
      (∀ index : Fin sourceScope,
        RawTerm.rename rawRenaming (sourceContext.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      HasTypeDescTermIndexedFormer profile targetContext
        (RawTerm.rename rawRenaming subject)
        (RawTerm.rename rawRenaming classifier) := by
  cases derivation with
  | genFormation generator payload children carrier level flag rule isTermIndexed premises =>
      intro targetScope targetContext rawRenaming contextCondition
      have renamedPremises :=
        TermIndexedFormerTelescope.renameRespectingContext premises targetContext rawRenaming
          contextCondition
      have hNotVar : generator ≠ Generator.gen_var :=
        termIndexedFormerRuleImpliesNotVariable isTermIndexed
      obtain rfl : rule = { outputType := termIndexedCarrierOutput } :=
        termIndexedFormerRuleIsCarrierOutput isTermIndexed
      show HasTypeDescTermIndexedFormer profile targetContext
        (RawTerm.rename rawRenaming (RawTerm.mkGen generator payload children))
        (RawTerm.rename rawRenaming (termIndexedCarrierOutput sourceScope level flag))
      rw [show termIndexedCarrierOutput sourceScope level flag
            = universeCodeCell level flag from rfl, rename_universeCodeCell,
          RawTerm.rename_mkGen_of_ne_var rawRenaming hNotVar]
      exact HasTypeDescTermIndexedFormer.genFormation targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.rename rawRenaming children) (RawTerm.rename rawRenaming carrier)
        level flag { outputType := termIndexedCarrierOutput } isTermIndexed renamedPremises

/-- **Term-indexed former weakening.**  A `HasTypeDescTermIndexedFormer` derivation survives extending the
context by one fresh binding, with subject and classifier shifted by `RawRenaming.weaken` — the corollary of
`renameRespectingContext` whose context-condition holds DEFINITIONALLY (`fun _ => rfl`). -/
theorem HasTypeDescTermIndexedFormer.weakenUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (newBinding : RawTerm scope)
    (derivation : HasTypeDescTermIndexedFormer profile context subject classifier) :
    HasTypeDescTermIndexedFormer profile (context.cons newBinding)
      (RawTerm.rename RawRenaming.weaken subject)
      (RawTerm.rename RawRenaming.weaken classifier) :=
  derivation.renameRespectingContext (context.cons newBinding) RawRenaming.weaken (fun _ => rfl)

/-! ## Substitution (the β leg) -/

/-- **Endpoint sub-telescope substitution.**  Re-types every endpoint along a well-typed substitution; the
endpoints stay typed at the SUBSTITUTED carrier.  Structural `match`-recursion reusing the grown
`HasTypeDescPi.substRespectingContext` on each endpoint. -/
theorem TermIndexedEndpoints.substRespectingContext {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {carrier : RawTerm scope} {shifts : List Nat}
    {children : RawTermChildren shifts scope}
    (telescope : TermIndexedEndpoints profile context carrier children) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst scope targetScope),
      (∀ index : Fin scope,
        HasTypeDescPi profile targetContext (substitution index)
          (RawTerm.subst substitution (context.lookup index))) →
      TermIndexedEndpoints profile targetContext (RawTerm.subst substitution carrier)
        (RawTermChildren.subst substitution children) :=
  match telescope with
  | .nil => fun _targetContext _substitution _substitutionTyped => TermIndexedEndpoints.nil
  | .cons endpoint rest endpointTyped restTyped =>
      fun targetContext substitution substitutionTyped =>
        TermIndexedEndpoints.cons (RawTerm.subst substitution endpoint)
          (RawTermChildren.subst substitution rest)
          (HasTypeDescPi.substRespectingContext endpointTyped targetContext substitution
            substitutionTyped)
          (TermIndexedEndpoints.substRespectingContext restTyped targetContext substitution
            substitutionTyped)

/-- **Term-indexed former telescope substitution.**  The carrier head substitutes at its universe code (the
one `subst_universeCodeCell` collapse) and the endpoint tail substitutes at the substituted carrier. -/
theorem TermIndexedFormerTelescope.substRespectingContext {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {shifts : List Nat}
    {children : RawTermChildren shifts scope} {carrier : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag}
    (telescope : TermIndexedFormerTelescope profile context children carrier level flag) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst scope targetScope),
      (∀ index : Fin scope,
        HasTypeDescPi profile targetContext (substitution index)
          (RawTerm.subst substitution (context.lookup index))) →
      TermIndexedFormerTelescope profile targetContext
        (RawTermChildren.subst substitution children)
        (RawTerm.subst substitution carrier) level flag :=
  match telescope with
  | .mk carrier rest level flag carrierTyped endpointsTyped =>
      fun targetContext substitution substitutionTyped => by
        have carrierSubst :
            HasTypeDescPi profile targetContext (RawTerm.subst substitution carrier)
              (universeCodeCell level flag) := by
          have raw :=
            HasTypeDescPi.substRespectingContext carrierTyped targetContext substitution
              substitutionTyped
          rwa [subst_universeCodeCell] at raw
        exact TermIndexedFormerTelescope.mk (RawTerm.subst substitution carrier)
          (RawTermChildren.subst substitution rest) level flag carrierSubst
          (TermIndexedEndpoints.substRespectingContext endpointsTyped targetContext substitution
            substitutionTyped)

/-- **Term-indexed former substitution.**  A `HasTypeDescTermIndexedFormer` derivation is preserved along any
well-typed substitution — the term-indexed twin of `HasTypeDescFlat.substRespectingContext`.  Single-arm
`cases` reusing the telescope subst; the abstract cell reconstructs via `RawTerm.subst_mkGen_of_ne_var`. -/
theorem HasTypeDescTermIndexedFormer.substRespectingContext {profile : PolyProfile} {sourceScope : Nat}
    {sourceContext : TypingContext profile sourceScope} {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescTermIndexedFormer profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      (∀ index : Fin sourceScope,
        HasTypeDescPi profile targetContext (substitution index)
          (RawTerm.subst substitution (sourceContext.lookup index))) →
      HasTypeDescTermIndexedFormer profile targetContext
        (RawTerm.subst substitution subject)
        (RawTerm.subst substitution classifier) := by
  cases derivation with
  | genFormation generator payload children carrier level flag rule isTermIndexed premises =>
      intro targetScope targetContext substitution substitutionTyped
      have substPremises :=
        TermIndexedFormerTelescope.substRespectingContext premises targetContext substitution
          substitutionTyped
      have hNotVar : generator ≠ Generator.gen_var :=
        termIndexedFormerRuleImpliesNotVariable isTermIndexed
      obtain rfl : rule = { outputType := termIndexedCarrierOutput } :=
        termIndexedFormerRuleIsCarrierOutput isTermIndexed
      show HasTypeDescTermIndexedFormer profile targetContext
        (RawTerm.subst substitution (RawTerm.mkGen generator payload children))
        (RawTerm.subst substitution (termIndexedCarrierOutput sourceScope level flag))
      rw [show termIndexedCarrierOutput sourceScope level flag
            = universeCodeCell level flag from rfl, subst_universeCodeCell,
          RawTerm.subst_mkGen_of_ne_var substitution hNotVar]
      exact HasTypeDescTermIndexedFormer.genFormation targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.subst substitution children) (RawTerm.subst substitution carrier)
        level flag { outputType := termIndexedCarrierOutput } isTermIndexed substPremises

/-- **Term-indexed former single-substitution (the β-engine).**  Substituting a well-typed `argument` for de
Bruijn 0 preserves `HasTypeDescTermIndexedFormer` — the corollary the β-rule cites for a term-indexed-typed
subject.  Its side-condition concerns the AMBIENT context's lookups (typed in the grown `HasTypeDescPi`
engine), so the `0` / successor singleton split mirrors the grown/flat proof exactly. -/
theorem HasTypeDescTermIndexedFormer.substituteUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {argType : RawTerm scope}
    {subject classifier : RawTerm (scope + 1)} (argument : RawTerm scope)
    (derivation : HasTypeDescTermIndexedFormer profile (context.cons argType) subject classifier)
    (argumentTyped : HasTypeDescPi profile context argument argType) :
    HasTypeDescTermIndexedFormer profile context
      (RawTerm.subst0 subject argument)
      (RawTerm.subst0 classifier argument) := by
  refine derivation.substRespectingContext context (RawTermSubst.singleton argument) ?_
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show HasTypeDescPi profile context argument
        (RawTerm.subst (RawTermSubst.singleton argument)
          (RawTerm.rename RawRenaming.weaken argType))
      rw [subst_singleton_renameWeaken_cancel]
      exact argumentTyped
  | succ k =>
      show HasTypeDescPi profile context
          (variableCell ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)
        (RawTerm.subst (RawTermSubst.singleton argument)
          (RawTerm.rename RawRenaming.weaken
            (context.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)))
      rw [subst_singleton_renameWeaken_cancel]
      exact HasTypeDescPi.ofFormation
        (HasTypeDesc.var context ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)

end FX1Poly.Typed
