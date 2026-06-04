import FX1Poly.Typed.HasTypeDescPiConsistency

/-! # FX1Poly/Typed/HasTypeDescPiRootGeneric
    — the TABLE-GENERIC grown-engine root classification (un-hard-coding the formation table from the
    metatheory; the cascade-death brick for typed root inversion, toward the generic typing layer)

`HasTypeDescPi.subjectRootGenerator` (in `HasTypeDescPiConsistency`) classifies a grown-typed subject's
root as one of SIX EXPLICIT generators: `gen_var` / `gen_universeCode` / `gen_piTyCode` / `gen_sigmaTyCode`
/ `gen_lam` / `gen_app`.  That enumeration HARD-CODES the formation table: its `genFormationPi` arm proves
the root is `gen_piTyCode` or `gen_sigmaTyCode` by showing `typingRuleDescOf` is `none` for everything else.
The moment a new formation row lands (a data type code — `productCode` / `sumCode` / `listCode` / … — or any
future former), that `none`-everywhere argument FAILS and the lemma stops compiling.  This is the
"proofs hard-code the table" trap (polycell.md §3.16.19, the cascade-death principle): the engine
(`genFormationPi`) is already generic over `typingRuleDescOf`, but the metatheory is not.

This file makes the root classification **table-generic**: a grown-typed subject is rooted at one of the
FOUR non-former heads (`gen_var` / `gen_universeCode` / `gen_lam` / `gen_app`) OR its root carries a
formation rule (`typingRuleDescOf root = some rule`) — for ANY current or future formation row.  The
`genFormationPi` arm becomes a ONE-LINER (`⟨rule, isFormation⟩` — the witness is already in the arm), with
NO `gen_piTyCode`/`gen_sigmaTyCode` case split; adding a formation row cannot break it.  This is the
concrete "make the proofs table-generic, not just the engine" move — the prerequisite for growing
`typingRuleDescOf` (data/cubical/HIT/IR type codes) without a metatheory cascade.

## What this file ships

  * `HasTypeDescPi.subjectRootGeneratorGeneric` — the table-generic root classification (four non-former
    heads ∨ a formation rule).  Strictly more general than (and subsumes) `subjectRootGenerator`:
    `gen_piTyCode` / `gen_sigmaTyCode` are absorbed into the formation-rule disjunct via the existing
    `typingRuleDescOf_piTyCode` / `typingRuleDescOf_sigmaTyCode` table facts.
  * `HasTypeDescPi.cellHasNoTypingWhenRootGenericallyExcluded` — the future-proof refutation: a cell whose
    root is none of the four non-former heads AND carries no formation rule (`typingRuleDescOf gen = none`)
    has no grown typing.  Data CONSTRUCTORS (`gen_pair`, `gen_boolTrue`, …) and data ELIMINATORS
    (`gen_boolElim`, `gen_natElim`, …) all have `typingRuleDescOf = none` permanently, so this refutes them
    for ALL time — even as the formation table grows.  The table-generic successor to
    `cellHasNoTypingWhenRootNotGrownHead` (which hard-codes the six heads).

## Zero-axiom verification

`subjectRootGeneratorGeneric` is a `match` on the derivation mirroring `subjectRootGenerator`, but its
`genFormationPi` arm returns `⟨rule, isFormation⟩` directly (no case split) and its `ofFormation` arm maps
`gen_piTyCode`/`gen_sigmaTyCode` into the formation-rule disjunct via the `rfl`-grade table facts.
`cellHasNoTypingWhenRootGenericallyExcluded` is an `rcases` on it, the formation-rule branch closed by
`Option.noConfusion` on `none = some rule`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The table-generic FORMATION-engine root classification.**  A `HasTypeDesc`-typed subject is rooted at
`gen_var` (`var`) or `gen_universeCode` (`universeFormation`), or its root carries a formation rule
(`typingRuleDescOf root = some rule`, the `genFormation` arm).  Unlike `HasTypeDesc.subjectRootGenerator`,
this does NOT enumerate `gen_piTyCode`/`gen_sigmaTyCode` — they fall into the formation-rule disjunct — so a
new formation row leaves it intact.  The formation-engine basis the grown classification delegates to (its
`ofFormation` arm), removing the last hard-coded-table dependency from grown root inversion.  Term-mode
structural recursion on the `HasTypeDesc` derivation (the `HasTypeDesc`/`DescTelescope` mutual block forbids
`induction`). -/
theorem HasTypeDesc.subjectRootGeneratorGeneric {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDesc profile context subject classifier) :
    subject.rootGenerator = Generator.gen_var ∨
      subject.rootGenerator = Generator.gen_universeCode ∨
      (∃ rule : TypingRuleDesc, typingRuleDescOf subject.rootGenerator = some rule) :=
  match typed with
  | .var _context _index => Or.inl rfl
  | .conv _levelExpr _flag typedPremise _converts _reclassifierTyped =>
      typedPremise.subjectRootGeneratorGeneric
  | .universeFormation _context _levelExpr _flag => Or.inr (Or.inl rfl)
  | .genFormation _context _generator _payload _children _levels _flag rule isFormation _premises =>
      Or.inr (Or.inr ⟨rule, isFormation⟩)

/-- **The table-generic grown-engine root classification.**  A `HasTypeDescPi`-typed subject is rooted at
one of the four non-former heads — `gen_var` (`var`), `gen_universeCode` (`ofFormation ∘
universeFormation`), `gen_lam` (`piIntro`), `gen_app` (`piElim`) — or its root carries a formation rule
(`typingRuleDescOf root = some rule`, the `genFormationPi` arm, generic over the WHOLE formation table).
Unlike `subjectRootGenerator`, this does NOT enumerate `gen_piTyCode`/`gen_sigmaTyCode`: they are absorbed
into the formation-rule disjunct, so adding a formation row leaves the lemma intact.  Term-mode structural
recursion (the `HasTypeDescPi`/`DescTelescopePi` mutual block forbids `induction`). -/
theorem HasTypeDescPi.subjectRootGeneratorGeneric {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier) :
    subject.rootGenerator = Generator.gen_var ∨
      subject.rootGenerator = Generator.gen_universeCode ∨
      subject.rootGenerator = Generator.gen_lam ∨
      subject.rootGenerator = Generator.gen_app ∨
      (∃ rule : TypingRuleDesc, typingRuleDescOf subject.rootGenerator = some rule) :=
  match typed with
  | .ofFormation formationTyped =>
      match formationTyped.subjectRootGeneratorGeneric with
      | Or.inl isVar => Or.inl isVar
      | Or.inr (Or.inl isUniverse) => Or.inr (Or.inl isUniverse)
      | Or.inr (Or.inr formerRule) => Or.inr (Or.inr (Or.inr (Or.inr formerRule)))
  | .conv _levelExpr _flag typedPremise _converts _reclassifierTyped =>
      typedPremise.subjectRootGeneratorGeneric
  | .piIntro _domainLevel _codomainLevel _flag _domainTyped _codomainTyped _bodyTyped =>
      Or.inr (Or.inr (Or.inl rfl))
  | .piElim _functionTyped _argumentTyped =>
      Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | .genFormationPi _context _generator _payload _children _levels _flag rule isFormation _premises =>
      Or.inr (Or.inr (Or.inr (Or.inr ⟨rule, isFormation⟩)))

/-- **No grown typing for a cell that is neither a non-former head nor a formation former.**  A cell whose
root generator differs from all four non-former heads (`gen_var` / `gen_universeCode` / `gen_lam` /
`gen_app`) AND carries no formation rule (`typingRuleDescOf generator = none`) has no grown typing.  Because
data constructors and data eliminators permanently satisfy `typingRuleDescOf = none`, this refutes every
data head — and STAYS valid as the formation table grows (new rows only add `some`-valued generators, never
disturbing the `none` ones).  The table-generic successor to `cellHasNoTypingWhenRootNotGrownHead`. -/
theorem HasTypeDescPi.cellHasNoTypingWhenRootGenericallyExcluded {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    {classifier : RawTerm scope}
    (rootNotVar : generator ≠ Generator.gen_var)
    (rootNotUniverse : generator ≠ Generator.gen_universeCode)
    (rootNotLam : generator ≠ Generator.gen_lam)
    (rootNotApp : generator ≠ Generator.gen_app)
    (rootNotFormer : typingRuleDescOf generator = none)
    (typed : HasTypeDescPi profile context (.mkGen generator payload children) classifier) :
    False := by
  rcases typed.subjectRootGeneratorGeneric with isVar | isUniverse | isLam | isApp | ⟨rule, isFormer⟩
  · exact rootNotVar isVar
  · exact rootNotUniverse isUniverse
  · exact rootNotLam isLam
  · exact rootNotApp isApp
  · -- `(mkGen generator …).rootGenerator` is `generator` definitionally; re-ascribe so `rw` sees it.
    have isFormerAtGenerator : typingRuleDescOf generator = some rule := isFormer
    rw [rootNotFormer] at isFormerAtGenerator
    cases isFormerAtGenerator

/-- **The table-generic CLOSED grown-engine root classification.**  In the empty context a grown-typed
subject cannot be `gen_var`-rooted (the `gen_var` payload is `Fin 0`, uninhabited), so a closed grown subject
is rooted at `gen_universeCode` / `gen_lam` / `gen_app` or carries a formation rule.  The table-generic
successor to `closedSubjectRootGenerator` (which enumerates `gen_piTyCode`/`gen_sigmaTyCode`): consistency
turns on this — of these heads only `gen_app` can classify at a non-universe / non-Π type (a formation-rule
head is universe-code-classified), so `HasTypeDescPi .empty t Empty → False` reduces to ruling out a closed
application, for ANY formation table.  Drops the `gen_var` disjunct off `subjectRootGeneratorGeneric` via the
`Fin 0` payload (refuted by `Nat.not_lt_zero`, NOT `Fin.elim0` which routes through the casesOn propext
trap). -/
theorem HasTypeDescPi.closedSubjectRootGeneratorGeneric {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    subject.rootGenerator = Generator.gen_universeCode ∨
      subject.rootGenerator = Generator.gen_lam ∨
      subject.rootGenerator = Generator.gen_app ∨
      (∃ rule : TypingRuleDesc, typingRuleDescOf subject.rootGenerator = some rule) := by
  rcases typed.subjectRootGeneratorGeneric with isVar | rest
  · exfalso
    cases subject with
    | mkGen generator payload children =>
        have isVarGenerator : generator = Generator.gen_var := isVar
        subst isVarGenerator
        exact absurd payload.isLt (Nat.not_lt_zero payload.val)
  · exact rest

end FX1Poly.Typed
