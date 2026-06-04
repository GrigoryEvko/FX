import FX1Poly.Typed.HasType

/-! # FX1Poly/Typed/HasTypeDesc — the description-driven generic typing engine
    (the moonshot core: the Natural-Model display map as a data-driven `gen` arm)

polycell.md §11.8.5 Decision 4 / §5.2: the typing display map `Tm ↠ Ty` realized
cellularly by a CASCADE-FREE generic `gen` arm — a new feature is one
`TypingRuleDesc` DATA row, never a new `HasType` arm.  This file carries that arm
for the dependent-type-FORMER family (the most uniform shape).

`HasTypeDesc` runs alongside the bespoke `HasType`.  Its
faithfulness wrt `HasType` on the formation fragment is proved in two halves:
COMPLETENESS (`HasType.toHasTypeDesc`, below — every `HasType` derivation has a
description-engine counterpart) and SOUNDNESS (`HasTypeDesc.toHasType`, in the
companion `HasTypeDescSound.lean` — the engine derives nothing the trusted kernel
wouldn't, 0-FP).  Together they give the full `HasTypeDesc ⟺ HasType` equivalence
on this fragment.
Arms:
* `var`, `conv` — the irreducible core (every typed-layer engine has them).
* `universeFormation` — the nullary universe-code shape.  Genuinely special: its
  output level comes from the PAYLOAD (`lsucc`), not from children, so its output
  is not computed from the children's levels; it stays a (single-generator) arm.
* `genFormation` — THE generic arm.  Over ANY `generator` with a
  `TypingRuleDesc` (the `typingRuleDescOf` table), it types `mkGen generator
  payload children` by checking the children form a dependent telescope of types
  at `levels` (the mutual `DescTelescope` spine), and concludes the cell inhabits
  the rule's OUTPUT classifier `rule.outputType scope levels flag` (for the
  type-formers, `universeCodeCell (lmaxAll levels) flag`).  Adding a new dependent
  type-former (Π, Σ, and future n-ary dependent records …) is ONE
  `typingRuleDescOf` row — ZERO new arms (the two reconstruction theorems below
  witness Π and Σ through the SAME arm; P13 cascade-freedom).  The `outputType`
  field opens the §11.8.5 "non-uniform output" seam: output is rule-DATA, not
  hardwired to a universe code — the structural prerequisite for typing
  non-formers (eliminators).

## Positivity / zero-axiom

The desc (`TypingRuleDesc.outputType : (scope) → List LevelExpr → UniverseFlag →
RawTerm scope`) is PURE syntax — it contains NO `HasTypeDesc`, so the
`genFormation` arm is strictly positive.  `HasTypeDesc` appears only POSITIVELY, in the mutual
`DescTelescope` spine's `cons` premise.  The spine's shift-rebasing discipline:
children indexed at a fixed `baseScope`, only the context grows via
`currentDepth`, so `(baseScope+currentDepth)+1 = baseScope+(currentDepth+1)`
definitionally.  The output universe level is an
explicit INDEX (`Prop`-valued, P14 erasure).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated.
-/

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

/-- The per-generator description table.  `gen_piTyCode` and `gen_sigmaTyCode`
are the dependent type-formers, both with `universeFormerOutput`.  Adding a future
dependent former is one more row here — never a new `HasTypeDesc` arm (P13). -/
def typingRuleDescOf (generator : Generator) : Option TypingRuleDesc :=
  if generator = .gen_piTyCode then some { outputType := universeFormerOutput }
  else if generator = .gen_sigmaTyCode then some { outputType := universeFormerOutput }
  else none

mutual

/-- The description-driven typing judgment (moonshot core).  `var` + `conv` +
nullary `universeFormation` + the generic `genFormation` arm consuming
`typingRuleDescOf`. -/
inductive HasTypeDesc (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope →
      RawTerm scope → RawTerm scope → Prop where
  | var {scope : Nat} (context : TypingContext profile scope)
      (index : Fin scope) :
      HasTypeDesc profile context (variableCell index) (context.lookup index)
  | conv {scope : Nat} {context : TypingContext profile scope}
      {subject classifier reclassifier : RawTerm scope}
      (levelExpr : LevelExpr) (flag : UniverseFlag)
      (typed : HasTypeDesc profile context subject classifier)
      (converts : Conv classifier reclassifier)
      (reclassifierTyped :
        HasTypeDesc profile context reclassifier
          (universeCodeCell levelExpr flag)) :
      HasTypeDesc profile context subject reclassifier
  | universeFormation {scope : Nat} (context : TypingContext profile scope)
      (levelExpr : LevelExpr) (flag : UniverseFlag) :
      HasTypeDesc profile context (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr.lsucc flag)
  | genFormation {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope)
      (levels : List LevelExpr) (flag : UniverseFlag)
      (rule : TypingRuleDesc)
      (isFormation : typingRuleDescOf generator = some rule)
      (premises :
        DescTelescope profile (currentDepth := 0) context levels flag children) :
      HasTypeDesc profile context (.mkGen generator payload children)
        (rule.outputType scope levels flag)

/-- The description engine's premise spine: the children form a cumulative
dependent telescope of TYPES at `levels`.  Mutual with `HasTypeDesc` (its index
signature references only `PolyProfile`/`Nat`/`LevelExpr`/`UniverseFlag`/`List
Nat`/`TypingContext`/`RawTermChildren`, never `HasTypeDesc` — mutual-index rule;
`HasTypeDesc` appears only positively in `cons`'s `headTyped`).  Fixed-`baseScope`,
growing-`currentDepth` rebasing discipline: children stay indexed at `baseScope`
while the context extends. -/
inductive DescTelescope (profile : PolyProfile) :
    {baseScope : Nat} → {currentDepth : Nat} → {binderShifts : List Nat} →
      TypingContext profile (baseScope + currentDepth) →
      List LevelExpr → UniverseFlag →
      RawTermChildren binderShifts baseScope → Prop where
  | nil {baseScope : Nat} {currentDepth : Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (flag : UniverseFlag) :
      DescTelescope profile context [] flag .childNil
  | cons {baseScope : Nat} {currentDepth : Nat} {restShifts : List Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (head : RawTerm (baseScope + currentDepth))
      (headLevel : LevelExpr) (restLevels : List LevelExpr) (flag : UniverseFlag)
      (rest : RawTermChildren restShifts baseScope)
      (headTyped :
        HasTypeDesc profile context head (universeCodeCell headLevel flag))
      (restTyped :
        DescTelescope profile (currentDepth := currentDepth + 1)
          (context.cons head) restLevels flag rest) :
      DescTelescope profile context (headLevel :: restLevels) flag
        (.childCons head rest)

end

/-- `gen_piTyCode`'s description is the `universeFormerOutput` rule (metadata
check). -/
theorem typingRuleDescOf_piTyCode :
    typingRuleDescOf .gen_piTyCode = some { outputType := universeFormerOutput } := rfl

/-- `gen_sigmaTyCode`'s description is the `universeFormerOutput` rule (metadata
check). -/
theorem typingRuleDescOf_sigmaTyCode :
    typingRuleDescOf .gen_sigmaTyCode = some { outputType := universeFormerOutput } := rfl

/-- **Formation-family invariant: every formation rule outputs a universe code.**  The `typingRuleDescOf`
table currently maps EXACTLY the dependent type-formers (`gen_piTyCode` / `gen_sigmaTyCode`) to the SHARED
`universeFormerOutput` rule (a former lives at the `lmax` of its children's levels).  This lemma enumerates
the table ONCE: any generator carrying a formation rule has `rule.outputType = universeFormerOutput`.

It is the cascade-death substrate for the FORMATION-FAMILY metatheory (validity / substitution / weakening /
the FT `genFormation` arm): a consumer obtains `rule.outputType = universeFormerOutput` from HERE instead of
its own `unfold typingRuleDescOf` + per-generator (`by_cases` pi/sigma) split.  Adding a new
`universeFormerOutput` row (a data type code: `product`/`sum`/`list`/`option`/`either`) is then ONE new
`by_cases` case in THIS lemma — every consumer that obtains its output type from here inherits it, with no
per-consumer cascade.  (polycell.md §3.16.19 per-family metatheory inheritance.)

Zero-axiom — the established `subst` + `Option.some.inj` (pi/sigma) and `unfold`/`if_neg`/`contradiction`
(the non-former branch) pattern; no `propext`/`Quot.sound`/`Classical`/`native_decide`/`omega`. -/
theorem typingRuleDescOf_outputIsUniverseFormer {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule) :
    rule.outputType = universeFormerOutput := by
  by_cases hPi : generator = .gen_piTyCode
  · subst hPi
    have hRule : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
    rw [hRule]
  · by_cases hSigma : generator = .gen_sigmaTyCode
    · subst hSigma
      have hRule : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
      rw [hRule]
    · exfalso
      unfold typingRuleDescOf at isFormation
      rw [if_neg hPi, if_neg hSigma] at isFormation
      contradiction

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
  unfold typingRuleDescOf at isFormation
  rw [if_neg (fun isPi => Generator.noConfusion isPi),
    if_neg (fun isSigma => Generator.noConfusion isSigma)] at isFormation
  cases isFormation

/-- **A formation rule IS the universe-former rule (full structure).**  The single-field strengthening of
`typingRuleDescOf_outputIsUniverseFormer`: since `TypingRuleDesc` has exactly the `outputType` field, the
output-type equation upgrades to a structure equation `rule = { outputType := universeFormerOutput }`.  This
is what a cell-RECONSTRUCTION consumer needs — `obtain rfl` makes `rule` concrete (replacing the old
per-branch `Option.some.inj`), so the reconstructed `genFormation` cell carries `isFormation` directly. -/
theorem formationRuleIsUniverseFormer {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule) :
    rule = { outputType := universeFormerOutput } := by
  have outputIsFormer : rule.outputType = universeFormerOutput :=
    typingRuleDescOf_outputIsUniverseFormer isFormation
  cases rule
  rw [← outputIsFormer]

/-- Reconstruction: the generic `genFormation` arm derives Π-formation.  Domain
typed at `Type@(domainLevel, flag)`, codomain at `Type@(codomainLevel, flag)`
UNDER the domain binder ⟹ `piTyCodeCell` inhabits `Type@(lmax domainLevel
codomainLevel, flag)` — the same conclusion as `HasType.piFormation`, through
the data-driven generic arm (`lmaxAll [domainLevel, codomainLevel]` reduces to
`lmax domainLevel codomainLevel`). -/
theorem hasTypeDesc_piFormation_viaGenArm
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (domain : RawTerm scope) (codomain : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (domainTyped :
      HasTypeDesc profile context domain (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeDesc profile (context.cons domain) codomain
        (universeCodeCell codomainLevel flag)) :
    HasTypeDesc profile context (piTyCodeCell domain codomain)
      (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) := by
  refine HasTypeDesc.genFormation context .gen_piTyCode ()
    (RawTermChildren.binderShape domain codomain) [domainLevel, codomainLevel]
    flag { outputType := universeFormerOutput } typingRuleDescOf_piTyCode ?_
  refine DescTelescope.cons (currentDepth := 0) context domain domainLevel
    [codomainLevel] flag (.childCons codomain .childNil) domainTyped ?_
  exact DescTelescope.cons (currentDepth := 1) (context.cons domain) codomain
    codomainLevel [] flag .childNil codomainTyped
    (DescTelescope.nil (currentDepth := 2) (context.cons domain |>.cons codomain) flag)

/-- Reconstruction: the SAME generic `genFormation` arm derives Σ-formation,
with ZERO new code — one `typingRuleDescOf` row (`gen_sigmaTyCode`) suffices.
The P13 cascade-freedom witness for the description engine. -/
theorem hasTypeDesc_sigmaFormation_viaGenArm
    {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (domain : RawTerm scope) (codomain : RawTerm (scope + 1))
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (domainTyped :
      HasTypeDesc profile context domain (universeCodeCell domainLevel flag))
    (codomainTyped :
      HasTypeDesc profile (context.cons domain) codomain
        (universeCodeCell codomainLevel flag)) :
    HasTypeDesc profile context (sigmaTyCodeCell domain codomain)
      (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag) := by
  refine HasTypeDesc.genFormation context .gen_sigmaTyCode ()
    (RawTermChildren.binderShape domain codomain) [domainLevel, codomainLevel]
    flag { outputType := universeFormerOutput } typingRuleDescOf_sigmaTyCode ?_
  refine DescTelescope.cons (currentDepth := 0) context domain domainLevel
    [codomainLevel] flag (.childCons codomain .childNil) domainTyped ?_
  exact DescTelescope.cons (currentDepth := 1) (context.cons domain) codomain
    codomainLevel [] flag .childNil codomainTyped
    (DescTelescope.nil (currentDepth := 2) (context.cons domain |>.cons codomain) flag)

/-- COMPLETENESS of the description engine wrt the bespoke `HasType`:
every `HasType` derivation on the native pi/sigma-formation HasType core has a `HasTypeDesc`
counterpart.  A single induction on `HasType` (NOT mutual — `HasType`'s premises
are direct sub-derivations with IHs): `var`/`conv`/`universeFormation` map to the
matching `HasTypeDesc` arm; `piFormation`/`sigmaFormation` map through the
generic `genFormation` arm via the reconstruction lemmas.  So the data-driven
generic engine is at least as strong as the five hand-written arms — the
cascade-free engine loses nothing. -/
theorem HasType.toHasTypeDesc {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasType profile context subject classifier) :
    HasTypeDesc profile context subject classifier := by
  induction typed with
  | var context index => exact HasTypeDesc.var context index
  | conv levelExpr flag _typed converts _reclassifierTyped ihTyped ihReclassifier =>
      exact HasTypeDesc.conv levelExpr flag ihTyped converts ihReclassifier
  | universeFormation context levelExpr flag =>
      exact HasTypeDesc.universeFormation context levelExpr flag
  | piFormation context domainCode codomainCode domainLevel codomainLevel flag
      _domainTyped _codomainTyped ihDomain ihCodomain =>
      exact hasTypeDesc_piFormation_viaGenArm context domainCode codomainCode
        domainLevel codomainLevel flag ihDomain ihCodomain
  | sigmaFormation context domainCode codomainCode domainLevel codomainLevel flag
      _domainTyped _codomainTyped ihDomain ihCodomain =>
      exact hasTypeDesc_sigmaFormation_viaGenArm context domainCode codomainCode
        domainLevel codomainLevel flag ihDomain ihCodomain

end FX1Poly.Typed
