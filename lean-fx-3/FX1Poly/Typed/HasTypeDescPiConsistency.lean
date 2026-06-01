import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Core.ReducibilityCandidateArrow

/-! # FX1Poly/Typed/HasTypeDescPiConsistency
    — the grown-engine closed-subject shape characterization (the consistency-spine inversion leg)

`HasType.closedSubjectIsType` characterizes closed subjects of the FORMATION engine (no `lam`/`app`): they
are all types.  The GROWN engine `HasTypeDescPi` adds the Π term-formers `lam` (introduction) and `app`
(elimination), so closed subjects are no longer all types.  This file ports the characterization to the
grown engine at the level of the subject's ROOT GENERATOR: a well-typed grown subject is rooted at one of
the six generators the engine can produce — `gen_var`, `gen_universeCode`, `gen_piTyCode`,
`gen_sigmaTyCode` (formation shapes, via `ofFormation` / `genFormationPi`), `gen_lam` (`piIntro`), or
`gen_app` (`piElim`).

This is the inversion leg of the consistency spine (P10, #460 `HasTypeDescPi .empty t Empty → False`).  In
the empty context the `gen_var` disjunct is impossible (`Fin 0`), so consistency REDUCES to the single
`gen_app` case — a closed application, whose classifier is the dependent output `subst0 codomainCode arg`.
Ruling that out is exactly where strong normalization enters; this file delivers the inversion half.

## Mutual-recursion note

`HasTypeDesc` / `HasTypeDescPi` are each mutually inductive with their telescope (`DescTelescope` /
`DescTelescopePi`), so the `induction` tactic is rejected.  But the only recursion these shape lemmas need is
`HasTypeDesc → HasTypeDesc` (the `conv` arm, whose subject is its premise's subject) and `HasTypeDescPi →
HasTypeDescPi` — never into the telescope.  So a term-mode STRUCTURAL-RECURSION `match` on the derivation
closes them without touching the telescope motive: each non-`conv` arm reads its subject's root off the
conclusion cell (`RawTerm.rootGenerator` of `mkGen g …` is `g`, by `rfl`), `conv` recurses on its premise,
and `genFormation` / `genFormationPi` dispatch on the `typingRuleDescOf` generator (Π or Σ, else `none`
contradicts the formation witness).

## Zero-axiom verification

Term-mode structural recursion; the `genFormation` false branch is `simp only [typingRuleDescOf, if_neg,
if_neg]` to `none = some` refuted by `nomatch`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The formation engine's closed-subject root characterization.**  A `HasTypeDesc`-typed subject is rooted
at `gen_var` (`var`), `gen_universeCode` (`universeFormation`), or `gen_piTyCode` / `gen_sigmaTyCode` (the
`genFormation` arm — the only `typingRuleDescOf` generators); `conv` recurses on its premise (same subject).
Term-mode structural recursion to dodge the `HasTypeDesc`/`DescTelescope` mutual-induction rejection. -/
theorem HasTypeDesc.subjectRootGenerator {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDesc profile context subject classifier) :
    subject.rootGenerator = Generator.gen_var ∨
      subject.rootGenerator = Generator.gen_universeCode ∨
      subject.rootGenerator = Generator.gen_piTyCode ∨
      subject.rootGenerator = Generator.gen_sigmaTyCode :=
  match typed with
  | .var _context _index => Or.inl rfl
  | .conv _levelExpr _flag typedPremise _converts _reclassifierTyped =>
      typedPremise.subjectRootGenerator
  | .universeFormation _context _levelExpr _flag => Or.inr (Or.inl rfl)
  | .genFormation _context generator _payload _children _levels _flag _rule isFormation _premises =>
      if isPiFormer : generator = Generator.gen_piTyCode then
        isPiFormer ▸ Or.inr (Or.inr (Or.inl rfl))
      else if isSigmaFormer : generator = Generator.gen_sigmaTyCode then
        isSigmaFormer ▸ Or.inr (Or.inr (Or.inr rfl))
      else
        absurd isFormation (fun isSome => by
          simp only [typingRuleDescOf, if_neg isPiFormer, if_neg isSigmaFormer] at isSome
          nomatch isSome)

/-- **The grown engine's closed-subject root characterization (the consistency-spine inversion leg).**  A
`HasTypeDescPi`-typed subject is rooted at one of the six grown-engine generators: `gen_var` /
`gen_universeCode` / `gen_piTyCode` / `gen_sigmaTyCode` (via `ofFormation` and `genFormationPi`), `gen_lam`
(`piIntro`), or `gen_app` (`piElim`).  Lifts the formation disjunction through `ofFormation`, recurses on
`conv`'s premise, and reads the binder / application / former roots off the conclusion cells.  Term-mode
structural recursion (the `HasTypeDescPi` / `DescTelescopePi` mutual block forbids `induction`). -/
theorem HasTypeDescPi.subjectRootGenerator {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier) :
    subject.rootGenerator = Generator.gen_var ∨
      subject.rootGenerator = Generator.gen_universeCode ∨
      subject.rootGenerator = Generator.gen_piTyCode ∨
      subject.rootGenerator = Generator.gen_sigmaTyCode ∨
      subject.rootGenerator = Generator.gen_lam ∨
      subject.rootGenerator = Generator.gen_app :=
  match typed with
  | .ofFormation formationTyped =>
      match formationTyped.subjectRootGenerator with
      | Or.inl isVar => Or.inl isVar
      | Or.inr (Or.inl isUniverse) => Or.inr (Or.inl isUniverse)
      | Or.inr (Or.inr (Or.inl isPi)) => Or.inr (Or.inr (Or.inl isPi))
      | Or.inr (Or.inr (Or.inr isSigma)) => Or.inr (Or.inr (Or.inr (Or.inl isSigma)))
  | .conv _levelExpr _flag typedPremise _converts _reclassifierTyped =>
      typedPremise.subjectRootGenerator
  | .piIntro _domainLevel _codomainLevel _flag _domainTyped _codomainTyped _bodyTyped =>
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | .piElim _functionTyped _argumentTyped =>
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  | .genFormationPi _context generator _payload _children _levels _flag _rule isFormation _premises =>
      if isPiFormer : generator = Generator.gen_piTyCode then
        isPiFormer ▸ Or.inr (Or.inr (Or.inl rfl))
      else if isSigmaFormer : generator = Generator.gen_sigmaTyCode then
        isSigmaFormer ▸ Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      else
        absurd isFormation (fun isSome => by
          simp only [typingRuleDescOf, if_neg isPiFormer, if_neg isSigmaFormer] at isSome
          nomatch isSome)

/-- **Closed grown subjects are rooted at a type code, a λ, or an application.**  The empty-context
corollary of `subjectRootGenerator`: a closed subject cannot be `gen_var`-rooted (the `gen_var` payload is
`Fin 0`, uninhabited — refuted via `Nat.not_lt_zero`, NOT `Fin.elim0` which routes through the casesOn
propext trap), so a closed grown subject is rooted at `gen_universeCode` / `gen_piTyCode` /
`gen_sigmaTyCode` / `gen_lam` / `gen_app`.  This is the precise statement consistency turns on: of these
five, only `gen_app` can classify at a non-universe / non-Π type, so `HasTypeDescPi .empty t Empty → False`
reduces to ruling out a closed application at the empty type — the strong-normalization obligation the
fundamental theorem discharges. -/
theorem HasTypeDescPi.closedSubjectRootGenerator {profile : PolyProfile}
    {subject classifier : RawTerm 0}
    (typed : HasTypeDescPi profile TypingContext.empty subject classifier) :
    subject.rootGenerator = Generator.gen_universeCode ∨
      subject.rootGenerator = Generator.gen_piTyCode ∨
      subject.rootGenerator = Generator.gen_sigmaTyCode ∨
      subject.rootGenerator = Generator.gen_lam ∨
      subject.rootGenerator = Generator.gen_app := by
  rcases typed.subjectRootGenerator with isVar | rest
  · exfalso
    cases subject with
    | mkGen generator payload children =>
        have isVarGenerator : generator = Generator.gen_var := isVar
        subst isVarGenerator
        exact absurd payload.isLt (Nat.not_lt_zero payload.val)
  · exact rest

end FX1Poly.Typed
