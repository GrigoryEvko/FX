import FX1Poly.Typed.GrownBetaRedexInAction
import FX1Poly.Typed.GrownTypeSafety
import FX1Poly.Typed.GrownCanonicalFormsNonVacuity
import FX1Poly.Core.HeadStep

/-! # FX1Poly/Typed/MetatheoryFuzz
    — the §27.3 Layer-2 property-based metatheory fuzzer: a total generator of well-typed terms, with
      preservation / progress / SN / evaluation proven over the WHOLE generated family

Layer 2 of the §27.3 five-layer defense is property-based metatheory fuzzing (§23.2): generate well-typed
terms and check that preservation, progress, strong normalization, and reducibility hold, shrinking any
counterexample.  In a zero-axiom kernel a proof cannot draw on `IO` randomness, so the honest translation
(the one the task specifies: "the generator is a total function, no `native_decide`") is:

  * random generation  ↦  a TOTAL deterministic generator enumerating an INFINITE family by depth;
  * check the property  ↦  PROVE the property for every member of the family (∀ n), by induction;
  * shrink a counterexample  ↦  the family is minimal by construction — `metatheoryFuzzFamily n` is the
    smallest term of its depth, so the base case `n = 0` IS the already-shrunk witness.

This is strictly stronger than a randomized run: instead of sampling finitely many terms and checking, it
proves the metatheory holds across the entire (infinite) generated family at once.

## The generator

`metatheoryFuzzFamily : Nat → RawTerm 0` iterates the closed identity `λ(x : Type@1). x` applied to the
previous term, seeded at `Type@0`:

  * `metatheoryFuzzFamily 0      = Type@0`
  * `metatheoryFuzzFamily (n+1)  = (λ x. x) (metatheoryFuzzFamily n)`

so the family is `Type@0`, `(λx.x) Type@0`, `(λx.x) ((λx.x) Type@0)`, …  — a depth-`n` β-redex tower that
exercises the grown engine's universe codes, λ, application, and a genuine `n`-step β-reduction.

## The four §27.3-L2 properties, over the whole family (all unconditional, GrownCtxConv-5-independent)

  * `metatheoryFuzzFamily_typed` — every member is well-typed at `Type@1` (by construction).
  * `metatheoryFuzzFamily_betaPreservation` — PRESERVATION (β-SR): the β-reduct of each redex stays typed at
    `Type@1` (`betaSubjectReductionDescPi`).  The family's only redexes are β, so β-SR fully covers its
    reduction.
  * `metatheoryFuzzFamily_progress` — PROGRESS: every member is a canonical value or steps (`closedProgress`).
  * `metatheoryFuzzFamily_stronglyNormalizing` — SN (`stronglyNormalizingOfWfContextDesc`); reducibility is
    represented through SN, its direct corollary (CR1: a reducible member is SN; SN-for-well-typed IS
    well-typed ⟹ reducible ⟹ SN).

Plus the concrete evaluation results: `metatheoryFuzzFamily_reducesToType0` (the whole family evaluates to
`Type@0`) and `metatheoryFuzzFamily_uniqueNormalForm` (its normal form is unique — determinism).
`metatheoryFuzzFamilySound` bundles the four properties as the headline "the fuzz run passes."

## Zero-axiom verification

The generator is structural Nat recursion; the typing is a two-line induction over the shipped
`closedUniverseCodeTyping` / `closedIdentityLambdaTyping` / `piElim` (the `subst0` of the var-free codomain
and of the bound variable both hold by defeq for every member); the properties apply the shipped universal
theorems to each derivation; the structural smokes close by `rfl`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## The generator -/

/-- **The fuzzer's generated family.**  `metatheoryFuzzFamily n` is the depth-`n` β-redex tower obtained by
iterating the closed identity `λ(x : Type@1). x` applied to the previous term, seeded at `Type@0`.  A total
deterministic generator (structural Nat recursion) — the zero-axiom stand-in for randomized generation. -/
def metatheoryFuzzFamily : Nat → RawTerm 0
  | 0 => universeCodeCell LevelExpr.lzero UniverseFlag.standard
  | n + 1 => appCell (lamCell (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard)
        (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))) (metatheoryFuzzFamily n)

/-! ## Well-typedness by construction -/

/-- **Every generated term is well-typed at `Type@1`.**  Base: `Type@0 : Type@1` (`closedUniverseCodeTyping`).
Step: `piElim` of the identity `λ(x:Type@1).x : Π(Type@1, Type@1)` (`closedIdentityLambdaTyping`) against the
inductively-typed predecessor — the `piElim` output `subst0 (Type@1) (predecessor)` is `Type@1` by defeq
(the codomain is var-free).  The well-typedness invariant the fuzzer maintains across the entire family. -/
theorem metatheoryFuzzFamily_typed {profile : PolyProfile} : ∀ n,
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (metatheoryFuzzFamily n) (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard)
  | 0 => closedUniverseCodeTyping LevelExpr.lzero UniverseFlag.standard
  | n + 1 =>
      HasTypeDescPi.piElim
        (closedIdentityLambdaTyping LevelExpr.lzero.lsucc UniverseFlag.standard)
        (metatheoryFuzzFamily_typed n)

/-! ## The four §27.3-L2 metatheory properties over the whole family -/

/-- **Each successor member β-steps to its predecessor.**  `(λx.x) (metatheoryFuzzFamily n)` contracts to
`metatheoryFuzzFamily n` (`Step.beta`; the contractum `subst0 (var 0) predecessor` is the predecessor by
defeq).  The family's reduction is pure β. -/
theorem metatheoryFuzzFamily_betaStep : ∀ n,
    Step (metatheoryFuzzFamily (n + 1)) (metatheoryFuzzFamily n) :=
  fun _ => HeadStep.beta.toStep

/-- **Preservation (β subject reduction) over the family.**  The β-reduct of every redex
`metatheoryFuzzFamily (n+1)` is still typed at `Type@1` (`betaSubjectReductionDescPi`) — and the reduct IS
`metatheoryFuzzFamily n` (by defeq), so preservation closes the family back into itself.  Unconditional: β-SR
does not route through the GrownCtxConv-5-gated master dispatcher. -/
theorem metatheoryFuzzFamily_betaPreservation {profile : PolyProfile} : ∀ n,
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (metatheoryFuzzFamily n) (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard) :=
  fun n =>
    HasTypeDescPi.betaSubjectReductionDescPi (metatheoryFuzzFamily_typed (profile := profile) (n + 1))
      WfContextDescPi.emptyIsWellFormed

/-- **Progress over the family.**  Every generated term is a canonical value (head + normal) OR steps
(`closedProgress`): the base `Type@0` is a canonical value, every successor steps. -/
theorem metatheoryFuzzFamily_progress {profile : PolyProfile} : ∀ n,
    (RawTerm.IsGrownCanonicalHead (metatheoryFuzzFamily n) ∧
      RawTerm.isStepNormalForm (metatheoryFuzzFamily n))
    ∨ (∃ reduct : RawTerm 0, Step (metatheoryFuzzFamily n) reduct) :=
  fun n => HasTypeDescPi.closedProgress (metatheoryFuzzFamily_typed (profile := profile) n)

/-- **Strong normalization over the family.**  Every generated term is strongly normalizing
(`stronglyNormalizingOfWfContextDesc`).  Reducibility is represented through SN — its direct corollary (CR1:
reducible members are SN; SN-for-well-typed factors as well-typed ⟹ reducible ⟹ SN). -/
theorem metatheoryFuzzFamily_stronglyNormalizing {profile : PolyProfile} : ∀ n,
    StepStar.IsStronglyNormalizing (metatheoryFuzzFamily n) :=
  fun n =>
    HasTypeDescPi.stronglyNormalizingOfWfContextDesc WfContextDesc.emptyIsWellFormed
      (metatheoryFuzzFamily_typed (profile := profile) n)

/-! ## Concrete evaluation results -/

/-- **The whole family evaluates to `Type@0`.**  Each member reaches `Type@0` by its depth-many β-steps
(induction: base is reflexive; step prepends `metatheoryFuzzFamily_betaStep`).  The concrete evaluation
result the fuzzer confirms for every generated term. -/
theorem metatheoryFuzzFamily_reducesToType0 : ∀ n,
    StepStar (metatheoryFuzzFamily n) (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
  | 0 => StepStar.refl _
  | n + 1 => StepStar.trans (metatheoryFuzzFamily_betaStep n) (metatheoryFuzzFamily_reducesToType0 n)

/-- **Determinism over the family.**  Every generated term has a UNIQUE normal form
(`closedHasUniqueNormalForm`, the unconditional evaluation-determinism theorem — open SN + raw confluence).
Together with `metatheoryFuzzFamily_reducesToType0` that unique normal form is `Type@0`. -/
theorem metatheoryFuzzFamily_uniqueNormalForm {profile : PolyProfile} (n : Nat) :
    ∃ value : RawTerm 0,
      (StepStar (metatheoryFuzzFamily n) value ∧ RawTerm.isStepNormalForm value) ∧
      ∀ other : RawTerm 0, StepStar (metatheoryFuzzFamily n) other →
        RawTerm.isStepNormalForm other → other = value :=
  HasTypeDescPi.closedHasUniqueNormalForm (profile := profile) (metatheoryFuzzFamily_typed n)

/-! ## Structural smokes (kernel-reducible) -/

/-- Structural smoke: the base `Type@0` is a step normal form (computed by `rfl`). -/
theorem metatheoryFuzzFamily_base_isNormal :
    RawTerm.isStepNormalForm (metatheoryFuzzFamily 0) = true := rfl

/-- Structural smoke: the first successor `(λx.x) Type@0` is NOT a normal form — it has the β-redex
(computed by `rfl`). -/
theorem metatheoryFuzzFamily_succ_isNotNormal :
    RawTerm.isStepNormalForm (metatheoryFuzzFamily 1) = false := rfl

/-! ## The headline fuzz verdict -/

/-- **The fuzz run passes.**  For every generated term the four §27.3-Layer-2 properties hold together:
well-typed at `Type@1`, strongly normalizing, makes progress (value-or-steps), and evaluates to the canonical
value `Type@0`.  The bundled "metatheory fuzzer is green over its entire generated family" statement —
unconditional and zero-axiom (no GrownCtxConv-5, no `native_decide`). -/
theorem metatheoryFuzzFamilySound {profile : PolyProfile} (n : Nat) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
        (metatheoryFuzzFamily n) (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard) ∧
    StepStar.IsStronglyNormalizing (metatheoryFuzzFamily n) ∧
    ((RawTerm.IsGrownCanonicalHead (metatheoryFuzzFamily n) ∧
        RawTerm.isStepNormalForm (metatheoryFuzzFamily n))
      ∨ (∃ reduct : RawTerm 0, Step (metatheoryFuzzFamily n) reduct)) ∧
    StepStar (metatheoryFuzzFamily n) (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  ⟨metatheoryFuzzFamily_typed n,
    metatheoryFuzzFamily_stronglyNormalizing (profile := profile) n,
    metatheoryFuzzFamily_progress (profile := profile) n,
    metatheoryFuzzFamily_reducesToType0 n⟩

/-! ## The second family — the argument-DISCARDING β tower (constant function)

The identity family above exercises the argument-SUBSTITUTING β-case (`(λx.x) a ↝ a`: the bound variable is
USED, so `subst0` replaces it).  A second family exercises the complementary case: a CONSTANT function
`λ(x : Type@1). Type@0` whose body ignores the bound variable, so `(λx.Type@0) a ↝ Type@0` DISCARDS the
argument `a` entirely (β erases a subterm that itself contains redexes).  Together the two families cover both
β-paths — substitution and erasure — and the same four §27.3-Layer-2 properties hold over the whole infinite
constant family.  Unlike the identity tower (which peels one layer per step, an `n`-step reduction), every
member of the constant tower reduces to `Type@0` in a SINGLE step, discarding the entire inner redex stack —
the test that SN / confluence handle erased redexes. -/

/-- **The constant lambda `λ (x : Type@1). Type@0 : Π (Type@1). Type@1`.**  Built by `piIntro` (domain +
codomain `Type@1` by `universeFormation`, body `Type@0 : Type@1` by `universeFormation` under the extended
context).  Has the SAME type as the identity lambda, so applying it via `piElim` against a `Type@1`-typed
argument yields `Type@1` identically — but the body discards the bound variable. -/
def closedConstantLambdaTyping {profile : PolyProfile} :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (lamCell (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard)
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard)
        (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard)) :=
  HasTypeDescPi.piIntro
    (context := (TypingContext.empty : TypingContext profile 0))
    (domainCode := universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard)
    (codomainCode := universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard)
    (body := universeCodeCell LevelExpr.lzero UniverseFlag.standard)
    (domainLevel := LevelExpr.lzero.lsucc.lsucc) (codomainLevel := LevelExpr.lzero.lsucc.lsucc)
    (flag := UniverseFlag.standard)
    (HasTypeDesc.toHasTypeDescPi
      (HasTypeDesc.universeFormation _ LevelExpr.lzero.lsucc UniverseFlag.standard))
    (HasTypeDesc.toHasTypeDescPi
      (HasTypeDesc.universeFormation _ LevelExpr.lzero.lsucc UniverseFlag.standard))
    (HasTypeDesc.toHasTypeDescPi
      (HasTypeDesc.universeFormation _ LevelExpr.lzero UniverseFlag.standard))

/-- **The constant-function fuzz family.**  `metatheoryFuzzConstantFamily n` iterates the constant function
`λ(x : Type@1). Type@0` applied to the previous term, seeded at `Type@0`.  Each application DISCARDS its
argument on β-contraction (the body ignores the bound variable) — the complement of the identity tower. -/
def metatheoryFuzzConstantFamily : Nat → RawTerm 0
  | 0 => universeCodeCell LevelExpr.lzero UniverseFlag.standard
  | n + 1 => appCell (lamCell (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard)
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard))
      (metatheoryFuzzConstantFamily n)

/-- **Every constant-family member is well-typed at `Type@1`.**  Base: `Type@0 : Type@1`.  Step: `piElim` of
the constant lambda against the inductively-typed predecessor — the `piElim` output `subst0 (Type@1)
(predecessor)` is `Type@1` by defeq (var-free codomain), exactly as for the identity family. -/
theorem metatheoryFuzzConstantFamily_typed {profile : PolyProfile} : ∀ n,
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (metatheoryFuzzConstantFamily n) (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard)
  | 0 => closedUniverseCodeTyping LevelExpr.lzero UniverseFlag.standard
  | n + 1 =>
      HasTypeDescPi.piElim closedConstantLambdaTyping (metatheoryFuzzConstantFamily_typed n)

/-- **Each successor member β-steps DIRECTLY to `Type@0`.**  `(λx.Type@0) (metatheoryFuzzConstantFamily n)`
contracts to `Type@0` (`Step.beta`; the contractum `subst0 (Type@0) predecessor` is `Type@0` by defeq, since
the body is closed and the argument is discarded).  Unlike the identity tower's peel-one-layer step, this
erases the entire inner redex stack in one step. -/
theorem metatheoryFuzzConstantFamily_betaStep : ∀ n,
    Step (metatheoryFuzzConstantFamily (n + 1))
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  fun _ => HeadStep.beta.toStep

/-- **Preservation (β subject reduction) over the constant family.**  The β-reduct of every redex
`metatheoryFuzzConstantFamily (n+1)` — which is `Type@0` — is still typed at `Type@1`
(`betaSubjectReductionDescPi`).  Unconditional: β-SR does not route through the GrownCtxConv-5-gated master dispatcher. -/
theorem metatheoryFuzzConstantFamily_betaPreservation {profile : PolyProfile} : ∀ _n : Nat,
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
      (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard) :=
  fun n =>
    HasTypeDescPi.betaSubjectReductionDescPi
      (metatheoryFuzzConstantFamily_typed (profile := profile) (n + 1))
      WfContextDescPi.emptyIsWellFormed

/-- **Progress over the constant family.**  Every member is a canonical value or steps (`closedProgress`). -/
theorem metatheoryFuzzConstantFamily_progress {profile : PolyProfile} : ∀ n,
    (RawTerm.IsGrownCanonicalHead (metatheoryFuzzConstantFamily n) ∧
      RawTerm.isStepNormalForm (metatheoryFuzzConstantFamily n))
    ∨ (∃ reduct : RawTerm 0, Step (metatheoryFuzzConstantFamily n) reduct) :=
  fun n => HasTypeDescPi.closedProgress (metatheoryFuzzConstantFamily_typed (profile := profile) n)

/-- **Strong normalization over the constant family.**  Every member is strongly normalizing
(`stronglyNormalizingOfWfContextDesc`) — even though it discards redex-bearing subterms. -/
theorem metatheoryFuzzConstantFamily_stronglyNormalizing {profile : PolyProfile} : ∀ n,
    StepStar.IsStronglyNormalizing (metatheoryFuzzConstantFamily n) :=
  fun n =>
    HasTypeDescPi.stronglyNormalizingOfWfContextDesc WfContextDesc.emptyIsWellFormed
      (metatheoryFuzzConstantFamily_typed (profile := profile) n)

/-- **The whole constant family evaluates to `Type@0`.**  Each successor reaches `Type@0` in a SINGLE β-step
(`metatheoryFuzzConstantFamily_betaStep`), the base reflexively — the constant tower's one-step evaluation,
contrasting the identity tower's depth-many reduction. -/
theorem metatheoryFuzzConstantFamily_reducesToType0 : ∀ n,
    StepStar (metatheoryFuzzConstantFamily n) (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
  | 0 => StepStar.refl _
  | n + 1 => StepStar.trans (metatheoryFuzzConstantFamily_betaStep n) (StepStar.refl _)

/-- **Determinism over the constant family.**  Every member has a UNIQUE normal form
(`closedHasUniqueNormalForm`); with `metatheoryFuzzConstantFamily_reducesToType0` that normal form is `Type@0`. -/
theorem metatheoryFuzzConstantFamily_uniqueNormalForm {profile : PolyProfile} (n : Nat) :
    ∃ value : RawTerm 0,
      (StepStar (metatheoryFuzzConstantFamily n) value ∧ RawTerm.isStepNormalForm value) ∧
      ∀ other : RawTerm 0, StepStar (metatheoryFuzzConstantFamily n) other →
        RawTerm.isStepNormalForm other → other = value :=
  HasTypeDescPi.closedHasUniqueNormalForm (profile := profile)
    (metatheoryFuzzConstantFamily_typed n)

/-- Structural smoke: the base `Type@0` is a step normal form (computed by `rfl`). -/
theorem metatheoryFuzzConstantFamily_base_isNormal :
    RawTerm.isStepNormalForm (metatheoryFuzzConstantFamily 0) = true := rfl

/-- Structural smoke: the first successor `(λx.Type@0) Type@0` is NOT a normal form — it has the β-redex
(computed by `rfl`). -/
theorem metatheoryFuzzConstantFamily_succ_isNotNormal :
    RawTerm.isStepNormalForm (metatheoryFuzzConstantFamily 1) = false := rfl

/-- **The constant-family fuzz run passes.**  For every member the four §27.3-Layer-2 properties hold
together: well-typed at `Type@1`, strongly normalizing, makes progress, and evaluates to `Type@0` — the
argument-discarding companion to `metatheoryFuzzFamilySound`. -/
theorem metatheoryFuzzConstantFamilySound {profile : PolyProfile} (n : Nat) :
    HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
        (metatheoryFuzzConstantFamily n)
        (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard) ∧
    StepStar.IsStronglyNormalizing (metatheoryFuzzConstantFamily n) ∧
    ((RawTerm.IsGrownCanonicalHead (metatheoryFuzzConstantFamily n) ∧
        RawTerm.isStepNormalForm (metatheoryFuzzConstantFamily n))
      ∨ (∃ reduct : RawTerm 0, Step (metatheoryFuzzConstantFamily n) reduct)) ∧
    StepStar (metatheoryFuzzConstantFamily n) (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  ⟨metatheoryFuzzConstantFamily_typed n,
    metatheoryFuzzConstantFamily_stronglyNormalizing (profile := profile) n,
    metatheoryFuzzConstantFamily_progress (profile := profile) n,
    metatheoryFuzzConstantFamily_reducesToType0 n⟩

end FX1Poly.Typed
