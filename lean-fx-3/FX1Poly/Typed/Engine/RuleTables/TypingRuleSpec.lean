import FX1Poly.Typed.Cell.CellConstructors

/-! # FX1Poly/Typed/TypingRuleSpec — the GROWN-FREE formation typing-rule descriptor

The per-generator formation rule descriptor (`TypingRuleDesc`), its output classifiers
(`universeFormerOutput` / `nullaryFormerOutput`), the level-combining fold (`lmaxFold` / `lmaxAll`),
the description table (`typingRuleDescOf`) and the pure-`rfl` metadata lemmas it satisfies are ALL
PURE SYNTAX — they mention only `RawTerm`, `LevelExpr`, `UniverseFlag`, `Generator`, and
`universeCodeCell`, NEVER the formation engine (`HasTypeDesc`) or the grown engine (`HasTypeDescPi`).

They were formerly hosted inside the grown engine file (`HasTypeDesc.lean`), which forced every
pure-spec consumer of the rule table (the union's formation rule-table layer) to import the grown
engine transitively.  This module extracts the spec so the formation rule tables reach it grown-free
(one import, `CellConstructors`, itself Tier0-only).  The grown engine re-imports this module, so the
54 engine consumers resolve every name unchanged.

## Zero-axiom

Pure structural recursion / `if`-chain table / `rfl` metadata / `Generator.noConfusion` non-former
branches.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Combine a telescope of child universe levels into the former's output level.
For the dependent type-formers (Π, Σ) this is the iterated `lmax` (the level of
`Π A. B` / `Σ A. B` is `lmax (level A) (level B)`).  `lmaxAll [e] = e`,
`lmaxAll [e₀, e₁] = lmax e₀ e₁` (definitionally — the singleton arm precedes the
cons arm), so it matches the binary `piFormation`/`sigmaFormation` output
exactly. -/
def lmaxFold (accumulator : LevelExpr) : List LevelExpr → LevelExpr
  | [] => accumulator
  | headLevel :: restLevels =>
      lmaxFold (LevelExpr.lmax accumulator headLevel) restLevels

def lmaxAll : List LevelExpr → LevelExpr
  | [] => LevelExpr.lzero
  | headLevel :: restLevels => lmaxFold headLevel restLevels

/-- A typing-rule description: the per-generator datum is the rule's OUTPUT
classifier as a function of the children's universe levels (and the flag/scope).
`outputType` lets the output be arbitrary rule-DATA, realizing the §11.8.5
"non-uniform output" seam — the structural prerequisite for non-formation rules.
For the dependent type-formers (Π, Σ) the output is a universe code at the
iterated-`lmax` level, so `outputType _ levels flag = universeCodeCell (lmaxAll
levels) flag`.  This covers output-FROM-LEVELS; the children-dependent eliminator
output (motive applied to scrutinee) is the open part of the seam.  (Binder
structure is read from the generator's `binderShifts`; the children-are-types
premise is the `DescTelescope` spine.) -/
structure TypingRuleDesc where
  /-- The rule's output classifier, as a function of the scope, the children's
  universe levels (from the `DescTelescope` premise), and the flag. -/
  outputType : (scope : Nat) → List LevelExpr → UniverseFlag → RawTerm scope

/-- The output classifier shared by the dependent type-formers: a universe code
at the iterated-`lmax` of the children's levels.  Factored out so the Π and Σ
rows are visibly the same rule (and the `rfl` metadata lemmas + reconstruction
proofs reduce through one definition). -/
def universeFormerOutput (scope : Nat) (levels : List LevelExpr)
    (flag : UniverseFlag) : RawTerm scope :=
  universeCodeCell (lmaxAll levels) flag

/-- The output classifier of a NULLARY (childless) former: pinned to `Type@0(standard)`,
IGNORING both the level list and the flag.  A childless former's telescope premise
`DescTelescope ... [] flag .childNil` holds for EVERY flag (no head child anchors it), so a
flag-USING output would classify one subject at many non-`Conv` universe codes and break
uniqueness of typing; a nullary row must pin its output instead — uniqueness at a nullary
former is then by output CONSTANCY rather than by telescope flag-anchoring.  Matches the
base-type engine's pinning (`baseTypeRuleDescOf` sends every nullary base code to
`Type@0(standard)`). -/
def nullaryFormerOutput (scope : Nat) (_levels : List LevelExpr)
    (_flag : UniverseFlag) : RawTerm scope :=
  universeCodeCell LevelExpr.lzero UniverseFlag.standard

/-- The per-generator description table.  `gen_piTyCode` and `gen_sigmaTyCode`
are the dependent type-formers, both with `universeFormerOutput`; `gen_listCode` /
`gen_optionCode` are the one-child data formers at the same rule; `gen_unitCode` is the
first NULLARY former, with the flag-ignoring `nullaryFormerOutput` (Unit : Type@0).
Adding a future dependent former is one more row here — never a new `HasTypeDesc`
arm (P13). -/
def typingRuleDescOf (generator : Generator) : Option TypingRuleDesc :=
  if generator = .gen_piTyCode then some { outputType := universeFormerOutput }
  else if generator = .gen_sigmaTyCode then some { outputType := universeFormerOutput }
  else if generator = .gen_listCode then some { outputType := universeFormerOutput }
  else if generator = .gen_optionCode then some { outputType := universeFormerOutput }
  else if generator = .gen_unitCode then some { outputType := nullaryFormerOutput }
  else none

/-- `gen_piTyCode`'s description is the `universeFormerOutput` rule (metadata
check). -/
theorem typingRuleDescOf_piTyCode :
    typingRuleDescOf .gen_piTyCode = some { outputType := universeFormerOutput } := rfl

/-- `gen_sigmaTyCode`'s description is the `universeFormerOutput` rule (metadata
check). -/
theorem typingRuleDescOf_sigmaTyCode :
    typingRuleDescOf .gen_sigmaTyCode = some { outputType := universeFormerOutput } := rfl

/-- `gen_listCode`'s description is the `universeFormerOutput` rule (metadata
check).  The data-type-code former (GTL-11): `List A` lives at the universe of its
element `A`, exactly the `universeFormerOutput` rule the dependent formers carry. -/
theorem typingRuleDescOf_listCode :
    typingRuleDescOf .gen_listCode = some { outputType := universeFormerOutput } := rfl

/-- `gen_optionCode`'s description is the `universeFormerOutput` rule (metadata
check).  The one-child data-type-code former (GTL-13): `Option A` lives at the universe of its
element `A`, exactly the `universeFormerOutput` rule the dependent formers and `listCode` carry. -/
theorem typingRuleDescOf_optionCode :
    typingRuleDescOf .gen_optionCode = some { outputType := universeFormerOutput } := rfl

/-- `gen_unitCode`'s description is the `nullaryFormerOutput` rule (metadata check) — the first
NULLARY formation row: `Unit : Type@0(standard)`, the output IGNORING the (empty) level list and
the (unanchored) flag. -/
theorem typingRuleDescOf_unitCode :
    typingRuleDescOf .gen_unitCode = some { outputType := nullaryFormerOutput } := rfl

/-- **A formation generator is never the variable generator.**  `typingRuleDescOf .gen_var = none`
(the variable is not a type former), so any generator carrying a formation rule is non-`gen_var`.  The
discharge for the `generator ≠ .gen_var` side condition of `RawTerm.subst_mkGen_of_ne_var` /
`rename_mkGen_of_ne_var`: every formation-family consumer that reconstructs a formation cell over an
ABSTRACT generator obtains the non-variable witness from HERE.  Zero-axiom (the established
`unfold`/`if_neg`/`contradiction` non-former branch; the `.gen_var ≠` inequalities are
`Generator.noConfusion`). -/
theorem formationRuleImpliesNotVariable {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule) :
    generator ≠ Generator.gen_var := by
  intro isVariable
  subst isVariable
  dsimp only [typingRuleDescOf] at isFormation
  rw [if_neg (fun isPi => Generator.noConfusion isPi),
    if_neg (fun isSigma => Generator.noConfusion isSigma),
    if_neg (fun isList => Generator.noConfusion isList),
    if_neg (fun isOption => Generator.noConfusion isOption),
    if_neg (fun isUnit => Generator.noConfusion isUnit)] at isFormation
  cases isFormation

end FX1Poly.Typed
