import FX1Poly.Typed.Engine.RuleTables.UnionRuleTables
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescGeneralElim
import FX1Poly.Typed.Engine.Classifier.TypingContext

/-! # FX1Poly/Typed/ElimRuleTable — TYTAB-1 elim-collapse foundation (the uniform eliminator signature)

The six eliminator families — general application (app / pathApp), recursive elimination
(natElim / natRec), two-branch match (boolElim / optionMatch / eitherMatch), path induction (idJ),
projection (fst / snd), and list elimination (listElim) — are shape-HETEROGENEOUS: premise count 1-3,
some premises grown and some union-recursive, one premise at a binder-shifted dependent scope
(natElim's step branch at `scope + 2`), motives at binder arities 0 / 1 / 2, and outputs that read a
stored result type, a projected component, or even a premise term (app's argument).  A six-way sum
would merely re-tag each family with its bespoke signature.  Instead this module gives ONE genuinely
uniform eliminator descriptor that admits ANY arity, nested/dependent motives, and dependent branches:

  * **`ElimObligation`** — a single typing obligation that packs its OWN scope.  This is the enabler
    for heterogeneous-scope branches: natElim's step branch is just an obligation at `scope + 2` in the
    two-cell-extended context, no special arm field.
  * **`ElimRule`** — the row: `argShifts` (= the generator's `binderShifts`, the cell's children), the
    existential `paramShifts` (type indices the derivation chooses), an `obligations` function that
    BUILDS the premise obligation list from the children + params (each classifier / extended context an
    arbitrary function of the earlier data — so "nested" and "dependent" come for free), a `memberCell`
    (the eliminator cell), and a dependent `outputType`.
  * **`elimRuleOf`** — the merged table: every elim generator's row, found by family.  A NEW eliminator
    of any arity is one more `ElimRule` row here, never a new typing arm.

The companion `elim` arm of `HasTypeUnionOver` (landed separately) carries the children + params and a
single `∀ obligation ∈ rule.obligations …, HasTypeUnionOver … obligation.context obligation.subject
obligation.classifier` premise — the union appears strictly positively under the `∀`, so no telescope
inductive and no mutualization are needed (positivity verified by spike).  `listElim`'s nil / cons
branches, previously GROWN premises, become union obligations here — sound because the union embeds the
grown engine via `ofGrown`, and uniform because every branch is now a union obligation.

## Zero-axiom

Pure data: structures, `def`s building obligation lists by total `match` over the concrete-index
children vectors (each `match` is a single-shape total match — no partial-match propext leak), and `rfl`
table metadata.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **A single eliminator typing obligation, packing its OWN scope.**  A branch / scrutinee premise:
the term `subject` must be typed at `classifier` in `context`, all at this obligation's `scope`.  The
scope is a field (not the ambient scope) precisely so a binder-shifted branch — natElim's step branch at
`scope + 2` in a two-cell-extended context — is an ordinary obligation, not a special arm slot. -/
structure ElimObligation (profile : PolyProfile) where
  /-- The scope this obligation lives at (the ambient scope for base premises, `+1` / `+2` for branches
  that bind the constructor's arguments). -/
  scope : Nat
  /-- The context (the ambient context for base premises, extended by the branch's bound cells). -/
  context : TypingContext profile scope
  /-- The premise term (the scrutinee or a branch). -/
  subject : RawTerm scope
  /-- The classifier the premise term must inhabit (a function of the rule's params / earlier children —
  the motive applied to the constructor pattern, or a fixed inductive code). -/
  classifier : RawTerm scope

/-- **The uniform eliminator rule.**  Profile-independent table data describing one eliminator of ANY
arity.  `argShifts` are the cell's children binder-shifts (= the generator's `binderShifts`);
`paramShifts` the existential type-index shifts the derivation supplies.  `obligations` builds the
premise list (dependent classifiers / extended contexts read off the children + params); `memberCell`
is the eliminator cell; `outputType` the dependent result.  A new eliminator is one more value of this
record — no new arm, no arity-specific fields. -/
structure ElimRule where
  /-- The eliminator cell's children binder-shifts (matches the generator's `binderShifts`). -/
  argShifts : List Nat
  /-- The existential type-index binder-shifts (domain / codomain / result type / endpoints …). -/
  paramShifts : List Nat
  /-- The premise obligations the eliminator demands, built from the children, the type indices, AND the
  formation levels/flag (the universe at which the eliminator's RESULT type — and any type-index param not
  already pinned by a premise — must be formed).  EXACTLY mirrors `IntroRule.obligations`: the result-type
  formedness obligation is the LAST entry of each row's list, premised at `universeCodeCell level0 flag`, so
  the elim arm is SELF-CERTIFYING (the result type's validity is read directly off `premisesHold`, no
  bespoke downstream reconstruction).  Polymorphic in the profile (the table is profile-independent); each
  obligation may live at its own scope (binder-shifted branches), so heterogeneous-scope premises are
  uniform list entries. -/
  obligations : {profile : PolyProfile} → (scope : Nat) → TypingContext profile scope →
    RawTermChildren argShifts scope → RawTermChildren paramShifts scope →
    LevelExpr → LevelExpr → UniverseFlag → List (ElimObligation profile)
  /-- The eliminator member cell, built from its children. -/
  memberCell : (scope : Nat) → RawTermChildren argShifts scope → RawTerm scope
  /-- The eliminator's output type, dependent on the children and the type indices. -/
  outputType : (scope : Nat) → RawTermChildren argShifts scope →
    RawTermChildren paramShifts scope → RawTerm scope

/-! ## The eleven rows, by family -/

/-- **app** — eliminate a Π function at its domain, output the dependent application type.

★ The ONE non-self-certifying row (deliberately): `app` is the GROWN engine's eliminator too (`piElim`),
so the host-substitution path (`hostSubstWithUnionImages`'s `piElim` arm in `HasTypeUnionUnionSubstituent`)
reconstructs `app` cells.  A self-certifying app row would demand that path supply the output type's
formedness, which for a bare-variable function requires `WfContext` the unconditional substituent stack does
NOT carry (the var-leaf wall).  So `app`'s output validity is discharged WHERE `WfContextUnion` lives — in
`classifierIsType` via `appOutputFormed_ofValidityAndArg` (Π-codomain inversion + the closed substitution) —
not as a table obligation.  Every OTHER eliminator is native (no grown twin), so its self-certifying result
obligation is supplied table-locally by the surrounding derivation's `ihPremises`.  This asymmetry is the
principled split, not a gap: the result type of a well-typed application IS always a type (validity proves
it), and `classifierIsType`'s app case proves exactly that. -/
def appElimRule : ElimRule where
  argShifts := [0, 0]
  paramShifts := [0, 1]
  obligations := fun _scope context args params _level0 _level1 _flag =>
    match args with
    | .childCons function (.childCons argument .childNil) =>
      match params with
      | .childCons domainCode (.childCons codomainCode .childNil) =>
        [ { scope := _scope, context := context, subject := function,
            classifier := piTyCodeCell domainCode codomainCode },
          { scope := _scope, context := context, subject := argument, classifier := domainCode } ]
  memberCell := fun _scope args =>
    match args with
    | .childCons function (.childCons argument .childNil) => appCell function argument
  outputType := fun _scope args params =>
    match args with
    | .childCons _function (.childCons argument .childNil) =>
      match params with
      | .childCons _domainCode (.childCons codomainCode .childNil) =>
        RawTerm.subst0 codomainCode argument

/-- **pathApp** — eliminate a bridge path at an interval endpoint, output the (constant) carrier. -/
def pathAppElimRule : ElimRule where
  argShifts := [0, 0]
  paramShifts := [0, 0, 0]
  obligations := fun _scope context args params level0 _level1 flag =>
    match args with
    | .childCons path (.childCons argument .childNil) =>
      match params with
      | .childCons carrierCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)) =>
        [ { scope := _scope, context := context, subject := path,
            classifier := bridgeTypeCell carrierCode leftEndpoint rightEndpoint },
          { scope := _scope, context := context, subject := argument,
            classifier := intervalTypeCell },
          { scope := _scope, context := context, subject := carrierCode,
            classifier := universeCodeCell level0 flag } ]
  memberCell := fun _scope args =>
    match args with
    | .childCons path (.childCons argument .childNil) => pathAppCell path argument
  outputType := fun _scope _args params =>
    match params with
    | .childCons carrierCode (.childCons _leftEndpoint (.childCons _rightEndpoint .childNil)) =>
      carrierCode

/-- **natElim** — the recursive eliminator: scrutinee at `Nat`, base branch at the result type, step
branch at the TWICE-weakened result type in the two-cell-extended context (predecessor + IH binders). -/
def natElimRule : ElimRule where
  argShifts := [1, 0, 2, 0]
  paramShifts := [0]
  obligations := fun _scope context args params level0 _level1 flag =>
    match args with
    | .childCons _motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))) =>
      match params with
      | .childCons resultType .childNil =>
        [ { scope := _scope, context := context, subject := scrutinee, classifier := natTypeCell },
          { scope := _scope, context := context, subject := baseBranch, classifier := resultType },
          { scope := _scope + 2,
            context := (context.cons natTypeCell).cons (RawTerm.weaken resultType),
            subject := stepBranch,
            classifier := RawTerm.weaken (RawTerm.weaken resultType) },
          { scope := _scope, context := context, subject := resultType,
            classifier := universeCodeCell level0 flag } ]
  memberCell := fun _scope args =>
    match args with
    | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))) =>
      natElimCell motive baseBranch stepBranch scrutinee
  outputType := fun _scope _args params =>
    match params with
    | .childCons resultType .childNil => resultType

/-- **natRec** — the dependent recursor twin of `natElim` (same substrate, `natRecCell`). -/
def natRecElimRule : ElimRule where
  argShifts := [1, 0, 2, 0]
  paramShifts := [0]
  obligations := fun _scope context args params level0 _level1 flag =>
    match args with
    | .childCons _motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))) =>
      match params with
      | .childCons resultType .childNil =>
        [ { scope := _scope, context := context, subject := scrutinee, classifier := natTypeCell },
          { scope := _scope, context := context, subject := baseBranch, classifier := resultType },
          { scope := _scope + 2,
            context := (context.cons natTypeCell).cons (RawTerm.weaken resultType),
            subject := stepBranch,
            classifier := RawTerm.weaken (RawTerm.weaken resultType) },
          { scope := _scope, context := context, subject := resultType,
            classifier := universeCodeCell level0 flag } ]
  memberCell := fun _scope args =>
    match args with
    | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))) =>
      natRecCell motive baseBranch stepBranch scrutinee
  outputType := fun _scope _args params =>
    match params with
    | .childCons resultType .childNil => resultType

/-- **boolElim** — two-branch match on `Bool`: scrutinee at `Bool`, both branches at the result type. -/
def boolElimRule : ElimRule where
  argShifts := [1, 0, 0, 0]
  paramShifts := [0, 0, 0]
  obligations := fun _scope context args params level0 _level1 flag =>
    match args with
    | .childCons _motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil))) =>
      match params with
      | .childCons _typeParamA (.childCons _typeParamB (.childCons resultType .childNil)) =>
        [ { scope := _scope, context := context, subject := scrutinee, classifier := boolTypeCell },
          { scope := _scope, context := context, subject := thenBranch, classifier := resultType },
          { scope := _scope, context := context, subject := elseBranch, classifier := resultType },
          { scope := _scope, context := context, subject := resultType,
            classifier := universeCodeCell level0 flag } ]
  memberCell := fun _scope args =>
    match args with
    | .childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil))) =>
      boolElimCell motive scrutinee thenBranch elseBranch
  outputType := fun _scope _args params =>
    match params with
    | .childCons _typeParamA (.childCons _typeParamB (.childCons resultType .childNil)) => resultType

/-- **optionMatch** — match on `option(A)`: None branch at the result, Some branch the handler `A → C`. -/
def optionMatchElimRule : ElimRule where
  argShifts := [1, 0, 0, 0]
  paramShifts := [0, 0, 0]
  obligations := fun _scope context args params level0 _level1 flag =>
    match args with
    | .childCons _motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))) =>
      match params with
      | .childCons typeParamA (.childCons _typeParamB (.childCons resultType .childNil)) =>
        [ { scope := _scope, context := context, subject := scrutinee,
            classifier := optionTypeCell typeParamA },
          { scope := _scope, context := context, subject := noneBranch, classifier := resultType },
          { scope := _scope, context := context, subject := someBranch,
            classifier := piTyCodeCell typeParamA (RawTerm.weaken resultType) },
          { scope := _scope, context := context, subject := resultType,
            classifier := universeCodeCell level0 flag } ]
  memberCell := fun _scope args =>
    match args with
    | .childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))) =>
      optionMatchCell motive noneBranch someBranch scrutinee
  outputType := fun _scope _args params =>
    match params with
    | .childCons _typeParamA (.childCons _typeParamB (.childCons resultType .childNil)) => resultType

/-- **eitherMatch** — match on `either(A, B)`: both branches the handlers `A → C` / `B → C`. -/
def eitherMatchElimRule : ElimRule where
  argShifts := [1, 0, 0, 0]
  paramShifts := [0, 0, 0]
  obligations := fun _scope context args params level0 _level1 flag =>
    match args with
    | .childCons _motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))) =>
      match params with
      | .childCons typeParamA (.childCons typeParamB (.childCons resultType .childNil)) =>
        [ { scope := _scope, context := context, subject := scrutinee,
            classifier := eitherTypeCell typeParamA typeParamB },
          { scope := _scope, context := context, subject := leftBranch,
            classifier := piTyCodeCell typeParamA (RawTerm.weaken resultType) },
          { scope := _scope, context := context, subject := rightBranch,
            classifier := piTyCodeCell typeParamB (RawTerm.weaken resultType) },
          { scope := _scope, context := context, subject := resultType,
            classifier := universeCodeCell level0 flag } ]
  memberCell := fun _scope args =>
    match args with
    | .childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))) =>
      eitherMatchCell motive leftBranch rightBranch scrutinee
  outputType := fun _scope _args params =>
    match params with
    | .childCons _typeParamA (.childCons _typeParamB (.childCons resultType .childNil)) => resultType

/-- **idJ** — path induction: witness at the reflexive identity code, base case at the result type. -/
def idJElimRule : ElimRule where
  argShifts := [2, 0, 0]
  paramShifts := [0, 0, 0]
  obligations := fun _scope context args params level0 _level1 flag =>
    match args with
    | .childCons _motive (.childCons baseCase (.childCons witness .childNil)) =>
      match params with
      | .childCons typeCode (.childCons endpoint (.childCons resultType .childNil)) =>
        [ { scope := _scope, context := context, subject := witness,
            classifier := idTypeCell typeCode endpoint endpoint },
          { scope := _scope, context := context, subject := baseCase, classifier := resultType },
          { scope := _scope, context := context, subject := resultType,
            classifier := universeCodeCell level0 flag } ]
  memberCell := fun _scope args =>
    match args with
    | .childCons motive (.childCons baseCase (.childCons witness .childNil)) =>
      idJCell motive baseCase witness
  outputType := fun _scope _args params =>
    match params with
    | .childCons _typeCode (.childCons _endpoint (.childCons resultType .childNil)) => resultType

/-- **fst** — Σ first projection: scrutinee at the product code, output the first component. -/
def fstElimRule : ElimRule where
  argShifts := [0]
  paramShifts := [0, 0]
  obligations := fun _scope context args params level0 _level1 flag =>
    match args with
    | .childCons pairTerm .childNil =>
      match params with
      | .childCons firstType (.childCons secondType .childNil) =>
        [ { scope := _scope, context := context, subject := pairTerm,
            classifier := productTypeCell firstType secondType },
          { scope := _scope, context := context, subject := firstType,
            classifier := universeCodeCell level0 flag } ]
  memberCell := fun _scope args =>
    match args with
    | .childCons pairTerm .childNil => fstCell pairTerm
  outputType := fun _scope _args params =>
    match params with
    | .childCons firstType (.childCons _secondType .childNil) => firstType

/-- **snd** — Σ second projection. -/
def sndElimRule : ElimRule where
  argShifts := [0]
  paramShifts := [0, 0]
  obligations := fun _scope context args params level0 _level1 flag =>
    match args with
    | .childCons pairTerm .childNil =>
      match params with
      | .childCons firstType (.childCons secondType .childNil) =>
        [ { scope := _scope, context := context, subject := pairTerm,
            classifier := productTypeCell firstType secondType },
          { scope := _scope, context := context, subject := secondType,
            classifier := universeCodeCell level0 flag } ]
  memberCell := fun _scope args =>
    match args with
    | .childCons pairTerm .childNil => sndCell pairTerm
  outputType := fun _scope _args params =>
    match params with
    | .childCons _firstType (.childCons secondType .childNil) => secondType

/-- **listElim** — list eliminator: scrutinee at `List(A)`, nil branch at the result, cons branch the
step function `A → List A → C → C`.  Nil / cons are UNION obligations here (homogenized from the prior
grown premises) — sound via the union's `ofGrown` embedding, uniform because every branch is now an
obligation. -/
def listElimRule : ElimRule where
  argShifts := [1, 0, 0, 0]
  paramShifts := [0, 0]
  obligations := fun _scope context args params level0 _level1 flag =>
    match args with
    | .childCons _motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))) =>
      match params with
      | .childCons elementType (.childCons resultType .childNil) =>
        [ { scope := _scope, context := context, subject := scrutinee,
            classifier := listTypeCell elementType },
          { scope := _scope, context := context, subject := nilBranch, classifier := resultType },
          { scope := _scope, context := context, subject := consBranch,
            classifier := listStepFunctionType elementType resultType },
          { scope := _scope, context := context, subject := resultType,
            classifier := universeCodeCell level0 flag } ]
  memberCell := fun _scope args =>
    match args with
    | .childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))) =>
      listElimCell motive scrutinee nilBranch consBranch
  outputType := fun _scope _args params =>
    match params with
    | .childCons _elementType (.childCons resultType .childNil) => resultType

/-! ## The merged table -/

/-- **The uniform eliminator table.**  Every elim generator's `ElimRule` row, found by generator.  The
families are disjoint, so the order is immaterial to membership.  A `ProfileExtension` adding an
eliminator of any arity is one more row here, never a new typing arm. -/
def elimRuleOf (generator : Generator) : Option ElimRule :=
  if generator = .gen_app then some appElimRule
  else if generator = .gen_pathApp then some pathAppElimRule
  else if generator = .gen_natElim then some natElimRule
  else if generator = .gen_natRec then some natRecElimRule
  else if generator = .gen_boolElim then some boolElimRule
  else if generator = .gen_optionMatch then some optionMatchElimRule
  else if generator = .gen_eitherMatch then some eitherMatchElimRule
  else if generator = .gen_idJ then some idJElimRule
  else if generator = .gen_fst then some fstElimRule
  else if generator = .gen_snd then some sndElimRule
  else if generator = .gen_listElim then some listElimRule
  else none

/-! ## Table metadata (cascade-death `rfl` lemmas) -/

theorem elimRuleOf_app : elimRuleOf .gen_app = some appElimRule := rfl
theorem elimRuleOf_pathApp : elimRuleOf .gen_pathApp = some pathAppElimRule := rfl
theorem elimRuleOf_natElim : elimRuleOf .gen_natElim = some natElimRule := rfl
theorem elimRuleOf_natRec : elimRuleOf .gen_natRec = some natRecElimRule := rfl
theorem elimRuleOf_boolElim : elimRuleOf .gen_boolElim = some boolElimRule := rfl
theorem elimRuleOf_optionMatch : elimRuleOf .gen_optionMatch = some optionMatchElimRule := rfl
theorem elimRuleOf_eitherMatch : elimRuleOf .gen_eitherMatch = some eitherMatchElimRule := rfl
theorem elimRuleOf_idJ : elimRuleOf .gen_idJ = some idJElimRule := rfl
theorem elimRuleOf_fst : elimRuleOf .gen_fst = some fstElimRule := rfl
theorem elimRuleOf_snd : elimRuleOf .gen_snd = some sndElimRule := rfl
theorem elimRuleOf_listElim : elimRuleOf .gen_listElim = some listElimRule := rfl

/-- **An eliminator table hit pins one of the eleven rows.**  The reverse-extraction enumeration the
inversion / soundness cascade dispatches on: a `bundle.elim generator = some rule` obligation, once the
subject's generator is known, collapses to the concrete row.  Decidable `by_cases` over the `if`-chain;
the `none` tail refutes any non-eliminator generator.  Zero-axiom (`by_cases` over `DecidableEq
Generator`, no `propext`). -/
theorem elimRuleOf_cases {generator : Generator} {rule : ElimRule}
    (tableHit : elimRuleOf generator = some rule) :
    (generator = .gen_app ∧ rule = appElimRule) ∨
    (generator = .gen_pathApp ∧ rule = pathAppElimRule) ∨
    (generator = .gen_natElim ∧ rule = natElimRule) ∨
    (generator = .gen_natRec ∧ rule = natRecElimRule) ∨
    (generator = .gen_boolElim ∧ rule = boolElimRule) ∨
    (generator = .gen_optionMatch ∧ rule = optionMatchElimRule) ∨
    (generator = .gen_eitherMatch ∧ rule = eitherMatchElimRule) ∨
    (generator = .gen_idJ ∧ rule = idJElimRule) ∨
    (generator = .gen_fst ∧ rule = fstElimRule) ∨
    (generator = .gen_snd ∧ rule = sndElimRule) ∨
    (generator = .gen_listElim ∧ rule = listElimRule) := by
  unfold elimRuleOf at tableHit
  by_cases isApp : generator = .gen_app
  · rw [if_pos isApp] at tableHit
    exact Or.inl ⟨isApp, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isApp] at tableHit
    by_cases isPathApp : generator = .gen_pathApp
    · rw [if_pos isPathApp] at tableHit
      exact Or.inr (Or.inl ⟨isPathApp, (Option.some.inj tableHit).symm⟩)
    · rw [if_neg isPathApp] at tableHit
      by_cases isNatElim : generator = .gen_natElim
      · rw [if_pos isNatElim] at tableHit
        exact Or.inr (Or.inr (Or.inl ⟨isNatElim, (Option.some.inj tableHit).symm⟩))
      · rw [if_neg isNatElim] at tableHit
        by_cases isNatRec : generator = .gen_natRec
        · rw [if_pos isNatRec] at tableHit
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨isNatRec, (Option.some.inj tableHit).symm⟩)))
        · rw [if_neg isNatRec] at tableHit
          by_cases isBoolElim : generator = .gen_boolElim
          · rw [if_pos isBoolElim] at tableHit
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨isBoolElim, (Option.some.inj tableHit).symm⟩))))
          · rw [if_neg isBoolElim] at tableHit
            by_cases isOptionMatch : generator = .gen_optionMatch
            · rw [if_pos isOptionMatch] at tableHit
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨isOptionMatch, (Option.some.inj tableHit).symm⟩)))))
            · rw [if_neg isOptionMatch] at tableHit
              by_cases isEitherMatch : generator = .gen_eitherMatch
              · rw [if_pos isEitherMatch] at tableHit
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨isEitherMatch, (Option.some.inj tableHit).symm⟩))))))
              · rw [if_neg isEitherMatch] at tableHit
                by_cases isIdJ : generator = .gen_idJ
                · rw [if_pos isIdJ] at tableHit
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                    ⟨isIdJ, (Option.some.inj tableHit).symm⟩)))))))
                · rw [if_neg isIdJ] at tableHit
                  by_cases isFst : generator = .gen_fst
                  · rw [if_pos isFst] at tableHit
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                      ⟨isFst, (Option.some.inj tableHit).symm⟩))))))))
                  · rw [if_neg isFst] at tableHit
                    by_cases isSnd : generator = .gen_snd
                    · rw [if_pos isSnd] at tableHit
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inl ⟨isSnd, (Option.some.inj tableHit).symm⟩)))))))))
                    · rw [if_neg isSnd] at tableHit
                      by_cases isListElim : generator = .gen_listElim
                      · rw [if_pos isListElim] at tableHit
                        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                          (Or.inr ⟨isListElim, (Option.some.inj tableHit).symm⟩)))))))))
                      · rw [if_neg isListElim] at tableHit
                        exact absurd tableHit (by intro hit; cases hit)

end FX1Poly.Typed
