import FX1Poly.Typed.HasTypeGen

/-! # FX1Poly/Typed/HasTypeDesc — the description-driven generic typing engine
    (the moonshot core: the Natural-Model display map as a data-driven `gen` arm)

polycell.md §11.8.5 Decision 4 / §5.2: the typing display map `Tm ↠ Ty` realized
cellularly by a CASCADE-FREE generic `gen` arm — a new feature is one
`TypingRuleDesc` DATA row, never a new `HasType` arm.  This file ships that arm
for the dependent-type-FORMER family (the first and most uniform shape).

`HasTypeDesc` is a NEW engine built ALONGSIDE the shipped `HasType` / `HasTypeGen`
(parallel-build; `HasTypeDesc ⟺ HasTypeGen` is proved below for the formation
fragment, so the description engine is sound + complete wrt the bespoke arms).
Arms:
* `var`, `conv` — the irreducible core (every typed-layer engine has them).
* `universeFormation` — the nullary universe-code shape.  Genuinely special: its
  output level comes from the PAYLOAD (`lsucc`), not from children, so it is not
  a `combineLevel`-of-children rule; it stays a (single-generator) arm.
* `genFormation` — THE generic arm.  Over ANY `generator` with a
  `TypingRuleDesc` (the `typingRuleDescOf` table), it types `mkGen generator
  payload children` by checking the children form a dependent telescope of types
  at `levels` (the mutual `DescTelescope` spine), and concludes the cell inhabits
  `Type@(rule.combineLevel levels, flag)`.  Adding a new dependent type-former
  (Π, Σ, and future n-ary dependent records …) is ONE `typingRuleDescOf` row —
  ZERO new arms (the two reconstruction theorems below witness Π and Σ through
  the SAME arm; P13 cascade-freedom).

## Positivity / zero-axiom

The desc (`TypingRuleDesc.combineLevel : List LevelExpr → LevelExpr`) is PURE
syntax over levels — it contains NO `HasTypeDesc`, so the `genFormation` arm is
strictly positive.  `HasTypeDesc` appears only POSITIVELY, in the mutual
`DescTelescope` spine's `cons` premise.  The spine reuses the spike's
shift-rebasing discipline (children indexed at a fixed `baseScope`, only the
context grows via `currentDepth`, so `(baseScope+currentDepth)+1 =
baseScope+(currentDepth+1)` definitionally).  The output universe level is an
explicit INDEX (`Prop`-valued, P14 erasure).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- Combine a telescope of child universe levels into the former's output level.
For the dependent type-formers (Π, Σ) this is the iterated `lmax` (the level of
`Π A. B` / `Σ A. B` is `lmax (level A) (level B)`).  `lmaxAll [e] = e`,
`lmaxAll [e₀, e₁] = lmax e₀ e₁` (definitionally — the singleton arm precedes the
cons arm), so it reconstructs the shipped binary `piFormation`/`sigmaFormation`
output exactly. -/
def lmaxFold (accumulator : LevelExpr) : List LevelExpr → LevelExpr
  | [] => accumulator
  | headLevel :: restLevels =>
      lmaxFold (LevelExpr.lmax accumulator headLevel) restLevels

def lmaxAll : List LevelExpr → LevelExpr
  | [] => LevelExpr.lzero
  | headLevel :: restLevels => lmaxFold headLevel restLevels

/-- A typing-rule description for the dependent-type-former family: the only
per-generator datum is how to combine the children's universe levels into the
former's output level.  (Binder structure is read from the generator's
`binderShifts`; the children-are-types premise is the `DescTelescope` spine.)
This is the DATA a new dependent type-former ships — one row, no new arm. -/
structure TypingRuleDesc where
  /-- Output universe level as a function of the children's levels. -/
  combineLevel : List LevelExpr → LevelExpr

/-- The per-generator description table.  `gen_piTyCode` and `gen_sigmaTyCode`
are the dependent type-formers, both combining via `lmaxAll`.  Adding a future
dependent former is one more row here — never a new `HasTypeDesc` arm (P13). -/
def typingRuleDescOf (generator : Generator) : Option TypingRuleDesc :=
  if generator = .gen_piTyCode then some { combineLevel := lmaxAll }
  else if generator = .gen_sigmaTyCode then some { combineLevel := lmaxAll }
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
        (universeCodeCell (rule.combineLevel levels) flag)

/-- The description engine's premise spine: the children form a cumulative
dependent telescope of TYPES at `levels`.  Mutual with `HasTypeDesc` (its index
signature references only `PolyProfile`/`Nat`/`LevelExpr`/`UniverseFlag`/`List
Nat`/`TypingContext`/`RawTermChildren`, never `HasTypeDesc` — mutual-index rule;
`HasTypeDesc` appears only positively in `cons`'s `headTyped`).  Same
fixed-`baseScope`, growing-`currentDepth` rebasing discipline as the validated
`DependentTelescopeChildren` spike. -/
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

/-- `gen_piTyCode`'s description is the `lmaxAll` rule (metadata check). -/
theorem typingRuleDescOf_piTyCode :
    typingRuleDescOf .gen_piTyCode = some { combineLevel := lmaxAll } := rfl

/-- `gen_sigmaTyCode`'s description is the `lmaxAll` rule (metadata check). -/
theorem typingRuleDescOf_sigmaTyCode :
    typingRuleDescOf .gen_sigmaTyCode = some { combineLevel := lmaxAll } := rfl

/-- Reconstruction: the generic `genFormation` arm derives Π-formation.  Domain
typed at `Type@(domainLevel, flag)`, codomain at `Type@(codomainLevel, flag)`
UNDER the domain binder ⟹ `piTyCodeCell` inhabits `Type@(lmax domainLevel
codomainLevel, flag)` — exactly the shipped `HasType.piFormation` conclusion,
now through the data-driven generic arm (`lmaxAll [domainLevel, codomainLevel]`
reduces to `lmax domainLevel codomainLevel`). -/
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
    flag { combineLevel := lmaxAll } typingRuleDescOf_piTyCode ?_
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
    flag { combineLevel := lmaxAll } typingRuleDescOf_sigmaTyCode ?_
  refine DescTelescope.cons (currentDepth := 0) context domain domainLevel
    [codomainLevel] flag (.childCons codomain .childNil) domainTyped ?_
  exact DescTelescope.cons (currentDepth := 1) (context.cons domain) codomain
    codomainLevel [] flag .childNil codomainTyped
    (DescTelescope.nil (currentDepth := 2) (context.cons domain |>.cons codomain) flag)

/-- COMPLETENESS of the description engine wrt the shipped bespoke `HasType`:
every `HasType` derivation on the current fragment has a `HasTypeDesc`
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
