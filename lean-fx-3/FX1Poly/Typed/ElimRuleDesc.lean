import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/ElimRuleDesc — the elimination-rule description table (GTL-17)

The elimination twin of `IntroRuleDesc` (GTL-15).  Where formation output is a universe code from the
children's LEVELS and introduction output is a TYPE from the rule's type-parameters, ELIMINATION output
is **children-DEPENDENT**: `appCell f a : codomainCode[a]` (`subst0`) — the motive applied to the
scrutinee.  This is the genuinely-new part of the §11.8.5 "non-uniform output" seam that neither
formation nor introduction exercises: `ElimRuleDesc.outputType` takes a CHILD (the argument) as an
argument, not just type-parameters.

  * `ElimRuleDesc` / `piElimOutput` / `elimRuleDescOf` — the structure, the Π-elim output
    (`subst0 codomain argument`), and the one-row (`gen_app`) table.
  * `elimRuleDescOf_app` / `elimRuleDescOf_outputIsPiElim` / `elimRuleDescOf_isApp` — the cascade-death
    metadata lemmas (mirroring `typingRuleDescOf_*` / `introRuleDescOf_*`): every consumer obtains the
    elimination rule's output shape / generator tag from HERE, never its own per-generator split.
  * `hasTypeDescPi_piElim_viaElimDesc` — **the reconstruction**: the shipped `HasTypeDescPi.piElim`
    output IS the rule-DATA output (`rule.outputType scope codomainCode argument = subst0 codomainCode
    argument` by `rfl`).  The elimination analogue of `hasTypeDescPi_piIntro_viaIntroDesc`; NON-VACUOUS
    (a real application types at the rule-data, scrutinee-dependent output), and the structural
    prerequisite for folding `piElim` into a generic `genElim` row + a generic ι-computation typing rule
    (GTL-18).

ADDITIVE — it does not modify `HasTypeDescPi`.  The engine-level fold (the abstract-generic `genElim`
arm with a generic elimination-premise spine) is GTL-18, arity-entangled exactly as the introduction
fold (GTL-16) and the formation reducibility residual are.

## Zero-axiom

`elimRuleDescOf` is a pure-syntax `Option`-valued table (the output `subst0` is pure syntax — no
`HasTypeDescPi` — so the structure is strictly positive); the metadata lemmas are the established
`by_cases` + `Option.some.inj` / `if_neg` + `contradiction` pattern; the reconstruction is `rfl`-reduction
of the rule output to `subst0` + `HasTypeDescPi.piElim`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- An elimination-rule description: the rule's OUTPUT TYPE as a function of the scope, the eliminated
type's relevant component (for Π-elim: the codomain, at `scope+1`), and the eliminated CHILD (the
argument / scrutinee).  Unlike formation (output from levels) and introduction (output from
type-parameters), the eliminator output depends on a CHILD — the §11.8.5 children-dependent output
(motive applied to scrutinee).  Pure syntax (no `HasTypeDescPi`) ⇒ strictly positive. -/
structure ElimRuleDesc where
  outputType : (scope : Nat) → RawTerm (scope + 1) → RawTerm scope → RawTerm scope

/-- The output of the Π-elimination rule (application): `appCell functionTerm argument` inhabits
`codomain[argument]`, i.e. `RawTerm.subst0 codomain argument` — the dependent application type. -/
def piElimOutput (scope : Nat) (codomain : RawTerm (scope + 1)) (argument : RawTerm scope) :
    RawTerm scope :=
  RawTerm.subst0 codomain argument

/-- The per-generator elimination-rule table.  `gen_app` is the sole current eliminator
(Π-elimination); a future eliminator (Σ-projection, the data recursors) is one more row here — never a
new `HasTypeDescPi` arm. -/
def elimRuleDescOf (generator : Generator) : Option ElimRuleDesc :=
  if generator = .gen_app then some { outputType := piElimOutput } else none

/-- `gen_app`'s description is the `piElimOutput` rule (metadata check). -/
theorem elimRuleDescOf_app :
    elimRuleDescOf .gen_app = some { outputType := piElimOutput } := rfl

/-- **Elimination-family invariant: every elimination rule in the current table outputs the Π-elim
rule.**  Any generator carrying an elimination rule has `rule.outputType = piElimOutput`.  The
cascade-death substrate mirroring `introRuleDescOf_outputIsPiIntro`: a consumer obtains the elimination
rule's output shape from HERE instead of its own per-generator split.  Zero-axiom (`subst` +
`Option.some.inj` on the `gen_app` branch; `unfold`/`if_neg`/`contradiction` on the non-eliminator
branch). -/
theorem elimRuleDescOf_outputIsPiElim {generator : Generator} {rule : ElimRuleDesc}
    (isElim : elimRuleDescOf generator = some rule) :
    rule.outputType = piElimOutput := by
  by_cases hApp : generator = .gen_app
  · subst hApp
    have hRule : rule = { outputType := piElimOutput } := Option.some.inj isElim.symm
    rw [hRule]
  · exfalso
    dsimp only [elimRuleDescOf] at isElim
    rw [if_neg hApp] at isElim
    contradiction

/-- **The current elimination table is exactly `{gen_app}`.**  Any generator carrying an elimination
rule is `gen_app`.  The "enumerate the current eliminators" companion (mirror of `introRuleDescOf_isLam`)
— the tool an elimination-DISPATCH consumer uses to obtain its eliminator tag from `isElim`.  A new
eliminator adds one disjunct.  Zero-axiom (`by_cases` + `if_neg` non-eliminator branch). -/
theorem elimRuleDescOf_isApp {generator : Generator} {rule : ElimRuleDesc}
    (isElim : elimRuleDescOf generator = some rule) :
    generator = Generator.gen_app := by
  by_cases hApp : generator = .gen_app
  · exact hApp
  · exfalso
    dsimp only [elimRuleDescOf] at isElim
    rw [if_neg hApp] at isElim
    contradiction

/-- **Reconstruction: the shipped `piElim` output IS the rule-DATA output.**  `appCell functionTerm
argument` inhabits the elimination rule's `outputType` applied to the codomain and the argument
(`= subst0 codomainCode argument` by `rfl`), exactly the `HasTypeDescPi.piElim` conclusion.  This
realizes the §11.8.5 children-DEPENDENT output seam for ELIMINATION (the output reads off a CHILD, the
scrutinee — not just type-parameters), the structural prerequisite for folding `piElim` into a generic
`genElim` row with a generic ι-computation typing rule (GTL-18).  The elimination analogue of
`hasTypeDescPi_piIntro_viaIntroDesc`; NON-VACUOUS (a genuine application types at the rule-data output).
The `rule` is obtained from the table (`elimRuleDescOf .gen_app`), so the reconstruction is genuinely
table-DRIVEN, not hardwired to `piElimOutput`. -/
theorem hasTypeDescPi_piElim_viaElimDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (rule : ElimRuleDesc) (isElim : elimRuleDescOf .gen_app = some rule)
    (functionTyped :
      HasTypeDescPi profile context functionTerm (piTyCodeCell domainCode codomainCode))
    (argumentTyped : HasTypeDescPi profile context argument domainCode) :
    HasTypeDescPi profile context (appCell functionTerm argument)
      (rule.outputType scope codomainCode argument) := by
  have hRule : rule = { outputType := piElimOutput } :=
    Option.some.inj (isElim.symm.trans elimRuleDescOf_app)
  subst hRule
  exact HasTypeDescPi.piElim functionTyped argumentTyped

end FX1Poly.Typed
