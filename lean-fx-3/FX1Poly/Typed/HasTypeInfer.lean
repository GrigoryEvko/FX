import FX1Poly.Typed.HasTypeDecidable
import FX1Poly.Typed.HasTypeConsistency

/-! # FX1Poly/Typed/HasTypeInfer
    — bidirectional type SYNTHESIS (`infer`) for the current fragment

The decidable-typing triad (#461/#462/#303) answers "does `subject` have the GIVEN
type `T`?".  Synthesis is the dual, more primitive query an agentic FX user asks:
"what IS the type of `subject`?".  `HasType.infer` computes it — returning the
classifier together with its derivation (`Option (Σ' T, HasType Γ subject T)`), so
it is **sound by construction** (a returned `some` carries the typing proof; the
fiber over an unsound cell stays empty, P1).

```
HasType.infer : WfContext Γ → (t : RawTerm scope) → Option (Σ' T, HasType Γ t T)
```

Crucially `infer` is NON-recursive: the type-former recursion already lives in
`IsType.decideWithWitness` (which synthesises a cell's principal universe), so
`infer` delegates the universe / Π / Σ heads to it and handles `var` directly
(a variable is ALWAYS typeable — by its looked-up classifier — whereas
`decideWithWitness` only accepts a variable whose lookup is itself a universe
code, so `var` cannot be delegated).

## What this brick delivers

* `HasType.infer` — the synthesis function (sound by construction).
* `HasType.infer_succeeds` — totality on the typeable domain: a well-typed
  subject always synthesises (`∃ inferred, infer … = some inferred`).  By the
  `subjectIsVariableOrIsType` classification: a variable hits the `gen_var`
  branch; a type (universe / Π / Σ) makes `decideWithWitness` return `.inl`
  (its `.inr` arm's `IsType → False` refutation contradicts the witnessed
  `IsType`).
* `HasType.infer_complete` — completeness: a well-typed subject synthesises a
  type CONVERTIBLE to any actual classifier (`infer_succeeds` + uniqueness of
  typing, #469).  Together with the by-construction soundness this is the
  `infer`-half of the bidirectional checker (P11).

## Zero-axiom verification

`infer` is a `dite` on the head generator delegating to `decideWithWitness`;
the metatheory is the `subjectIsVariableOrIsType` classification + `decideWithWitness`
`.inl`/`.inr` casing + `HasType.uniqueness`, all zero-axiom.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Synthesise the type of `subject`: return its classifier with
the typing derivation, or `none` if untypeable.  Sound by construction — a `some`
carries `HasType Γ subject T`.  `var` is handled directly (always typeable by its
lookup); every other head delegates to `IsType.decideWithWitness`, which
synthesises the principal universe of a universe / Π / Σ code (and refuses any
other head).  Non-recursive: the recursion is `decideWithWitness`'s. -/
def HasType.infer {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContext context)
    (subject : RawTerm scope) :
    Option (Σ' (classifier : RawTerm scope),
      HasType profile context subject classifier) :=
  match subject with
  | .mkGen generator payload children =>
      if hVariable : generator = Generator.gen_var then by
        subst hVariable
        have cellIsVariable :
            (RawTerm.mkGen Generator.gen_var payload children)
              = variableCell payload := by
          rw [RawTermChildren.eq_childNil children]; rfl
        exact some ⟨context.lookup payload, by
          rw [cellIsVariable]; exact HasType.var context payload⟩
      else
        match IsType.decideWithWitness wellFormed
            (RawTerm.mkGen generator payload children) with
        | .inl ⟨levelExpr, flag, typed⟩ =>
            some ⟨universeCodeCell levelExpr flag, typed⟩
        | .inr _ => none

/-- Totality of `infer` on the typeable domain: a well-typed subject always
synthesises.  The `var` disjunct of `subjectIsVariableOrIsType` lands in the
`gen_var` branch (which is unconditional); the `IsType` disjunct forces
`decideWithWitness` to return `.inl` (its `.inr` refutation would contradict the
witnessed `IsType`), so the delegating branch yields `some`. -/
theorem HasType.infer_succeeds {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContext context)
    (typed : HasType profile context subject classifier) :
    ∃ inferred, HasType.infer wellFormed subject = some inferred := by
  -- single-ctor `cases` on the scope-indexed `RawTerm` (universal index ⇒ clean
  -- `casesOn`, no propext leak); mirrors `infer`'s own dispatch on the head.
  cases subject with
  | mkGen generator payload children =>
      by_cases hVariable : generator = Generator.gen_var
      · -- variable head: `infer` reduces to its `gen_var` branch (`dite` decides
        -- `gen_var = gen_var` by computation), so the result is `some` by `rfl`.
        subst hVariable
        exact ⟨_, rfl⟩
      · -- non-variable head: the subject is a type (not a variable, so the
        -- classification's `IsType` disjunct holds), so `decideWithWitness`
        -- returns `.inl`; `infer`'s delegating branch then yields `some`.
        have isTypeSubject : IsType profile context
            (RawTerm.mkGen generator payload children) := by
          rcases typed.subjectIsVariableOrIsType with ⟨index, subjectEq⟩ | isTypeSubject
          · have headEq : generator = Generator.gen_var := by
              have headsAgree := congrArg RawTerm.headGenerator subjectEq
              rw [headGenerator_variableCell] at headsAgree
              exact headsAgree
            exact absurd headEq hVariable
          · exact isTypeSubject
        match hDecide : IsType.decideWithWitness wellFormed
            (RawTerm.mkGen generator payload children) with
        | .inl ⟨levelExpr, flag, witnessTyped⟩ =>
            refine ⟨⟨universeCodeCell levelExpr flag, witnessTyped⟩, ?_⟩
            -- `infer` is definitionally the head `dite`; `dsimp` exposes it
            -- (definitional, no `simp` match eq-lemma), `dif_neg` picks the
            -- delegating branch, `hDecide` reduces the `decideWithWitness` match.
            dsimp only [HasType.infer]
            rw [dif_neg hVariable, hDecide]
        | .inr refute => exact absurd isTypeSubject refute

/-- Completeness of `infer`: a well-typed subject synthesises a type convertible
to any actual classifier.  `infer_succeeds` gives the synthesised `inferred`;
its carried derivation (`inferred.2`, soundness by construction) and the given
`typed` feed uniqueness of typing (#469), which converts the two classifiers. -/
theorem HasType.infer_complete {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContext context)
    (typed : HasType profile context subject classifier) :
    ∃ inferred, HasType.infer wellFormed subject = some inferred ∧
      Conv classifier inferred.1 := by
  obtain ⟨inferred, inferEq⟩ := HasType.infer_succeeds wellFormed typed
  exact ⟨inferred, inferEq, HasType.uniqueness wellFormed typed inferred.2⟩

end FX1Poly.Typed
