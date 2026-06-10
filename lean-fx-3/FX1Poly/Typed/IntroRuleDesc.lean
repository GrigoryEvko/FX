import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/IntroRuleDesc — the introduction-rule description table (GTL-15)

The FORMATION engine (`HasTypeDesc`) is already table-generic: a new dependent type-former is ONE
`typingRuleDescOf` row and ZERO new arms, with the output classifier carried as rule-DATA
(`TypingRuleDesc.outputType`, a function of the children's levels).  Its docstring flags that the
`outputType`-as-DATA design exists precisely to open the §11.8.5 "non-uniform output" seam for the
INTRODUCTION and ELIMINATION rules, whose output is NOT a universe code from levels.

This file is the introduction analogue's first brick.  An introduction rule introduces a MEMBER of a
type built from the rule's type-parameters (for Π/λ: the domain and codomain), so its output is the
introduced TYPE as a function of those parameters — `IntroRuleDesc.outputType`.  The Π-introduction
(λ) rule is the sole current row (`introRuleDescOf .gen_lam`); a future binder-introduction former
(path-λ, mod-intro, …) is one more row.

  * `IntroRuleDesc` / `piIntroOutput` / `introRuleDescOf` — the structure, the Π-intro output, and the
    one-row table (the data-driven introduction substrate, mirroring `TypingRuleDesc`/`typingRuleDescOf`).
  * `introRuleDescOf_lam` / `introRuleDescOf_outputIsPiIntro` / `introRuleDescOf_isLam` — the
    cascade-death metadata lemmas (mirroring `typingRuleDescOf_piTyCode` /
    `typingRuleDescOf_outputIsUniverseFormer` / `typingRuleDescOf_isPiOrSigma`): every consumer obtains
    the introduction rule's output shape / generator tag from HERE, never its own per-generator split.
  * `hasTypeDescPi_piIntro_viaIntroDesc` — **the reconstruction**: the shipped `HasTypeDescPi.piIntro`
    output IS the rule-DATA output (`rule.outputType scope domainCode codomainCode = piTyCodeCell
    domainCode codomainCode` by `rfl`).  The introduction analogue of `hasTypeDesc_piFormation_viaGenArm`;
    NON-VACUOUS (a real λ types at the rule-data output), and the structural prerequisite for folding
    `piIntro` into a generic `genIntro` row (GTL-16) and for data-constructor introduction rows.

This is ADDITIVE — it does not modify `HasTypeDescPi`.  The fully-abstract-generic `genIntro` ARM
(over `mkGen generator payload children` for an abstract generator) is arity-entangled exactly as the
formation `genFormation` arm's reducibility residual is (the child spine forces `generator.binderShifts`),
so the engine-level fold is the deliberate next brick (GTL-16), not this one.

## Zero-axiom

`introRuleDescOf` is a pure-syntax `Option`-valued table; the metadata lemmas are the established
`by_cases` + `Option.some.inj` / `if_neg` + `contradiction` pattern; the reconstruction is `rfl`-reduction
of the rule output to `piTyCodeCell` + `HasTypeDescPi.piIntro`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- An introduction-rule description: the rule's OUTPUT TYPE (the type whose member it introduces) as a
function of the scope and the rule's type-parameters.  For the binder-introduction family (Π/λ) the
parameters are the domain (at `scope`) and the codomain (at `scope+1`).  Pure syntax (no
`HasTypeDescPi`) ⇒ strictly positive, mirroring `TypingRuleDesc`. -/
structure IntroRuleDesc where
  outputType : (scope : Nat) → RawTerm scope → RawTerm (scope + 1) → RawTerm scope

/-- The output of the Π-introduction rule (λ): the Church-style member `lamCell domain body` inhabits
`Π domain. codomain`, i.e. `piTyCodeCell domain codomain`.  Factored out so the table row and the
reconstruction reduce through one definition. -/
def piIntroOutput (scope : Nat) (domain : RawTerm scope) (codomain : RawTerm (scope + 1)) :
    RawTerm scope :=
  piTyCodeCell domain codomain

/-- The per-generator introduction-rule table.  `gen_lam` is the sole current introduction former
(Π-introduction); a future binder-intro former is one more row here — never a new `HasTypeDescPi` arm
(the introduction analogue of P13 cascade-freedom). -/
def introRuleDescOf (generator : Generator) : Option IntroRuleDesc :=
  if generator = .gen_lam then some { outputType := piIntroOutput } else none

/-- `gen_lam`'s description is the `piIntroOutput` rule (metadata check). -/
theorem introRuleDescOf_lam :
    introRuleDescOf .gen_lam = some { outputType := piIntroOutput } := rfl

/-- **Introduction-family invariant: every introduction rule in the current table outputs the Π-intro
rule.**  Any generator carrying an introduction rule has `rule.outputType = piIntroOutput`.  The
cascade-death substrate mirroring `typingRuleDescOf_outputIsUniverseFormer`: a consumer obtains the
introduction rule's output shape from HERE instead of its own per-generator (`by_cases`) split.  Adding a
new introduction row extends this lemma by one `by_cases` case, with no per-consumer cascade.  Zero-axiom
(`subst` + `Option.some.inj` on the `gen_lam` branch; `unfold`/`if_neg`/`contradiction` on the
non-introduction branch). -/
theorem introRuleDescOf_outputIsPiIntro {generator : Generator} {rule : IntroRuleDesc}
    (isIntro : introRuleDescOf generator = some rule) :
    rule.outputType = piIntroOutput := by
  by_cases hLam : generator = .gen_lam
  · subst hLam
    have hRule : rule = { outputType := piIntroOutput } := Option.some.inj isIntro.symm
    rw [hRule]
  · exfalso
    unfold introRuleDescOf at isIntro
    rw [if_neg hLam] at isIntro
    contradiction

/-- **The current introduction table is exactly `{gen_lam}`.**  Any generator carrying an introduction
rule is `gen_lam`.  The "enumerate the current introduction formers" companion (mirror of
`typingRuleDescOf_isPiOrSigma`) — the tool an introduction-DISPATCH consumer uses to obtain its former
tag from `isIntro`.  A new introduction former adds one disjunct.  Zero-axiom (`by_cases` + `if_neg`
non-introduction branch). -/
theorem introRuleDescOf_isLam {generator : Generator} {rule : IntroRuleDesc}
    (isIntro : introRuleDescOf generator = some rule) :
    generator = Generator.gen_lam := by
  by_cases hLam : generator = .gen_lam
  · exact hLam
  · exfalso
    unfold introRuleDescOf at isIntro
    rw [if_neg hLam] at isIntro
    contradiction

/-- **Reconstruction: the shipped `piIntro` output IS the rule-DATA output.**  `lamCell body` inhabits
the introduction rule's `outputType` applied to the type-parameters (`= piTyCodeCell domainCode
codomainCode` by `rfl`), exactly the `HasTypeDescPi.piIntro` conclusion.  This realizes the §11.8.5
"non-uniform output" seam for INTRODUCTION: the introduced type is rule-DATA, not hardwired — the
structural prerequisite for folding `piIntro` into a generic `genIntro` row (GTL-16) and for data
constructor introduction rows.  The introduction analogue of `hasTypeDesc_piFormation_viaGenArm`;
NON-VACUOUS (a genuine λ types at the rule-data output).  The `rule` is obtained from the table
(`introRuleDescOf .gen_lam`), so the reconstruction is genuinely table-DRIVEN, not hardwired to
`piIntroOutput`. -/
theorem hasTypeDescPi_piIntro_viaIntroDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag) (rule : IntroRuleDesc)
    (isIntro : introRuleDescOf .gen_lam = some rule)
    (domainTyped :
      HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeDescPi profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (bodyTyped :
      HasTypeDescPi profile (context.cons domainCode) body codomainCode) :
    HasTypeDescPi profile context (lamCell domainCode body)
      (rule.outputType scope domainCode codomainCode) := by
  have hRule : rule = { outputType := piIntroOutput } :=
    Option.some.inj (isIntro.symm.trans introRuleDescOf_lam)
  subst hRule
  exact HasTypeDescPi.piIntro domainLevel codomainLevel flag domainTyped codomainTyped bodyTyped

/-- **The generic introduction-DISPATCH consumer: route an ARBITRARY intro-carrying generator through the
table.**  For ANY `generator` whose `introRuleDescOf generator = some rule` (currently only `gen_lam`, but
stated generically over the generator so a new introduction former needs ZERO change here), the introduced
Church-style member `lamCell domainCode body` types at the rule-DATA output `rule.outputType scope domainCode codomainCode`.  The
consumer obtains the generator's identity from the table (`introRuleDescOf_isLam` ⟹ `generator = gen_lam`)
rather than performing its own per-generator `by_cases` split, then routes to the shipped reconstruction
`hasTypeDescPi_piIntro_viaIntroDesc` — the cascade-death CONSUMER shape (mirroring how every formation
consumer routes through `typingRuleDescOf` rather than its own split).  This is the consumer-side brick of the
generic `genIntro` fold (GTL-16): a new introduction row extends `introRuleDescOf` + `introRuleDescOf_isLam`
by one case, and this dispatcher absorbs it with no cascade.  NON-VACUOUS (a genuine λ types at the rule-data
output).  The remaining GTL-16 work is the fully-abstract engine-level `genIntro` ARM over
`mkGen generator payload children` (arity-entangled exactly as the formation `genFormationPi` arm). -/
theorem hasTypeDescPi_genIntro_dispatchViaTable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {generator : Generator} {rule : IntroRuleDesc}
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (isIntro : introRuleDescOf generator = some rule)
    (domainTyped :
      HasTypeDescPi profile context domainCode (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeDescPi profile (context.cons domainCode) codomainCode
        (universeCodeCell codomainLevel flag))
    (bodyTyped :
      HasTypeDescPi profile (context.cons domainCode) body codomainCode) :
    HasTypeDescPi profile context (lamCell domainCode body)
      (rule.outputType scope domainCode codomainCode) := by
  have hLam : generator = Generator.gen_lam := introRuleDescOf_isLam isIntro
  subst hLam
  exact hasTypeDescPi_piIntro_viaIntroDesc domainLevel codomainLevel flag rule isIntro
    domainTyped codomainTyped bodyTyped

end FX1Poly.Typed
