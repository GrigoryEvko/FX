import LeanFX.Syntax.TypedTerm

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Term-level substitution.

`TermSubst sourceContext targetContext typeSubstitution` supplies
for each `position : Fin scope` a term in `targetContext` whose type
is `(varType sourceContext position).subst typeSubstitution`.
`TermSubst.lift` extends under a binder by `Term.weaken`-ing
predecessor terms into the extended target. -/

/-- A term-level substitution maps each position of `sourceContext` to
a term in `targetContext` whose type is `varType sourceContext`
substituted by the underlying type-level substitution.  The
type-equality is computed via `Ty.subst`. -/
abbrev TermSubst {mode : Mode} {level sourceScope targetScope : Nat}
    (sourceContext : Ctx mode level sourceScope)
    (targetContext : Ctx mode level targetScope)
    (typeSubstitution : Subst level sourceScope targetScope) : Type :=
  ∀ (position : Fin sourceScope),
    Term targetContext ((varType sourceContext position).subst typeSubstitution)

/-- Lift a term-level substitution under a binder.  Position 0 in the
extended source context maps to `Term.var ⟨0, _⟩` in the extended
target (cast through `Ty.subst_weaken_commute`); positions
`predecessor + 1` weaken the predecessor's image into the extended
target context. -/
@[reducible]
def TermSubst.lift {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {targetContext : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    (termSubstitution : TermSubst sourceContext targetContext typeSubstitution)
    (newType : Ty level sourceScope) :
    TermSubst (sourceContext.cons newType)
      (targetContext.cons (newType.subst typeSubstitution))
      typeSubstitution.lift :=
  fun position =>
    match position with
    | ⟨0, _⟩ =>
        (Ty.subst_weaken_commute newType typeSubstitution).symm ▸
          (Term.var ⟨0, Nat.zero_lt_succ _⟩ :
            Term (targetContext.cons (newType.subst typeSubstitution))
              (newType.subst typeSubstitution).weaken)
    | ⟨predecessor + 1, succBound⟩ =>
        (Ty.subst_weaken_commute
            (varType sourceContext
              ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
            typeSubstitution).symm ▸
          Term.weaken (newType.subst typeSubstitution)
            (termSubstitution
              ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)

/-- Weakening then substituting with the singleton substitution is
the identity on `Ty`.  The shift renames every original variable up
by one, then `Subst.singleton substituent` at position
`predecessor + 1` returns the `Ty.tyVar predecessor` corresponding to
the original position — i.e., the substitution acts as the identity. -/
theorem Ty.weaken_subst_singleton {level scope : Nat}
    (tyValue : Ty level scope) (substituent : Ty level scope) :
    tyValue.weaken.subst (Subst.singleton substituent) = tyValue := by
  show (tyValue.rename Renaming.weaken).subst (Subst.singleton substituent)
     = tyValue
  have renameSubstCommute :=
    Ty.rename_subst_commute tyValue Renaming.weaken (Subst.singleton substituent)
  have substitutionsAgreePointwise :
      Subst.equiv
        (Subst.precompose Renaming.weaken (Subst.singleton substituent))
        Subst.identity :=
    Subst.precompose_weaken_singleton_equiv_identity substituent
  have congCast := Ty.subst_congr substitutionsAgreePointwise tyValue
  have identitySubstIsNeutral := Ty.subst_id tyValue
  exact renameSubstCommute.trans (congCast.trans identitySubstIsNeutral)

/-- Weakening then substituting with a term-singleton substitution is
the identity on `Ty`.  Same proof template as
`Ty.weaken_subst_singleton`; the supplied `rawArg` is irrelevant
because position 0 is no longer referenced after weakening. -/
theorem Ty.weaken_subst_termSingleton {level scope : Nat}
    (tyValue : Ty level scope) (substituent : Ty level scope)
    (rawArg : RawTerm scope) :
    tyValue.weaken.subst (Subst.termSingleton substituent rawArg) = tyValue := by
  show (tyValue.rename Renaming.weaken).subst
        (Subst.termSingleton substituent rawArg)
     = tyValue
  have renameSubstCommute :=
    Ty.rename_subst_commute tyValue Renaming.weaken
      (Subst.termSingleton substituent rawArg)
  have substitutionsAgreePointwise :
      Subst.equiv
        (Subst.precompose Renaming.weaken
          (Subst.termSingleton substituent rawArg))
        Subst.identity :=
    Subst.precompose_weaken_termSingleton_equiv_identity substituent rawArg
  have congCast := Ty.subst_congr substitutionsAgreePointwise tyValue
  have identitySubstIsNeutral := Ty.subst_id tyValue
  exact renameSubstCommute.trans (congCast.trans identitySubstIsNeutral)

/-- The single-substituent term substitution: position 0 maps to
`arg`, positions `predecessor + 1` map to `Term.var ⟨predecessor, _⟩`
in the original context (variable shifts down by one because the
outer scope has one fewer binder than the input).  The underlying
type-level substitution is `Subst.singleton argType` for the
argument's type `argType`.  Both Fin cases require a cast through
`Ty.weaken_subst_singleton` to align the substituted-varType form. -/
def TermSubst.singleton {mode : Mode} {level scope : Nat}
    {sourceContext : Ctx mode level scope} {argType : Ty level scope}
    (arg : Term sourceContext argType) :
    TermSubst (sourceContext.cons argType) sourceContext (Subst.singleton argType) :=
  fun position =>
    match position with
    | ⟨0, _⟩ =>
        (Ty.weaken_subst_singleton argType argType).symm ▸ arg
    | ⟨predecessor + 1, succBound⟩ =>
        (Ty.weaken_subst_singleton
            (varType sourceContext
              ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
            argType).symm ▸
          Term.var ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩

/-- **Term-bearing single substitution.**  Like `TermSubst.singleton`,
but uses the term-bearing joint substitution
`Subst.termSingleton argType (Term.toRaw arg)` so that identity-type
witnesses see the actual substituted argument's raw projection at
position 0.  This variant is the one referenced by the typed→raw
forward bridge for β-reduction: with this substitution,
`RawConsistent` holds by construction at position 0
(`Term.toRaw arg = (Subst.termSingleton argType
(Term.toRaw arg)).forRaw ⟨0, _⟩` definitionally). -/
def TermSubst.termSingleton {mode : Mode} {level scope : Nat}
    {sourceContext : Ctx mode level scope} {argType : Ty level scope}
    (arg : Term sourceContext argType) :
    TermSubst (sourceContext.cons argType) sourceContext
        (Subst.termSingleton argType (Term.toRaw arg)) :=
  fun position =>
    match position with
    | ⟨0, _⟩ =>
        (Ty.weaken_subst_termSingleton argType argType
          (Term.toRaw arg)).symm ▸ arg
    | ⟨predecessor + 1, succBound⟩ =>
        (Ty.weaken_subst_termSingleton
            (varType sourceContext
              ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
            argType
            (Term.toRaw arg)).symm ▸
          Term.var ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩

/-! ## Substitution-substitution commutativity.

`subst0` distributes through an outer subst by lifting the codomain's
substitution and substituting the substituted substituent.  Used by
`Term.subst`'s `appPi` / `pair` / `snd` cases to align result types. -/

/-- The pointwise equivalence underpinning `Ty.subst0_subst_commute`:
substituting then composing with the outer substitution equals lifting
the outer substitution under the binder then composing with the
singleton-substituent (already substituted by the outer substitution).
Both sides at position 0 evaluate to `(substituent).subst
typeSubstitution`; at positions `predecessor + 1`, both evaluate to
`typeSubstitution ⟨predecessor, _⟩`. -/
theorem Subst.singleton_compose_equiv_lift_compose_singleton
    {level scope target : Nat}
    (substituent : Ty level scope)
    (typeSubstitution : Subst level scope target) :
    Subst.equiv
      (Subst.compose (Subst.singleton substituent) typeSubstitution)
      (Subst.compose typeSubstitution.lift
        (Subst.singleton (substituent.subst typeSubstitution))) :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩                            => rfl
      | ⟨predecessor + 1, succBound⟩      => by
          show (Ty.tyVar
                  ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩).subst
                  typeSubstitution
             = ((typeSubstitution
                   ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩).rename
                   Renaming.weaken).subst
                 (Subst.singleton (substituent.subst typeSubstitution))
          have renameSubstCommute :=
            Ty.rename_subst_commute
              (typeSubstitution
                ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
              Renaming.weaken
              (Subst.singleton (substituent.subst typeSubstitution))
          have substitutionsAgreePointwise :
              Subst.equiv
                (Subst.precompose Renaming.weaken
                  (Subst.singleton (substituent.subst typeSubstitution)))
                Subst.identity :=
            Subst.precompose_weaken_singleton_equiv_identity
              (substituent.subst typeSubstitution)
          have congCast := Ty.subst_congr substitutionsAgreePointwise
                          (typeSubstitution
                            ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
          have identitySubstIsNeutral :=
            Ty.subst_id
              (typeSubstitution
                ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
          exact (renameSubstCommute.trans
                  (congCast.trans identitySubstIsNeutral)).symm)
    fun position =>
      match position with
      | ⟨0, _⟩                            => rfl
      | ⟨predecessor + 1, succBound⟩      =>
          (RawTerm.weaken_subst_dropNewest
            (typeSubstitution.forRaw
              ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)).symm

/-- Phase C1 termSingleton analog of
`Subst.singleton_compose_equiv_lift_compose_singleton`.  Composing
`Subst.termSingleton sub rawArg` with `typeSubst` agrees pointwise with
composing `typeSubst.lift` after `Subst.termSingleton (sub.subst
typeSubst) (rawArg.subst typeSubst.forRaw)`.  Both forTy sides at
position 0 evaluate to `sub.subst typeSubst`; both forRaw sides at
position 0 evaluate to `rawArg.subst typeSubst.forRaw`.  At positions
`predecessor + 1`, both forTy sides reduce to
`typeSubst ⟨predecessor, _⟩` (via `weaken_subst_termSingleton`), and
both forRaw sides reduce to `typeSubst.forRaw ⟨predecessor, _⟩` (via
`RawTerm.weaken_subst_singleton`).  Used by the C1
`Term.subst0_term_subst_HEq` workhorse, which closes the typed→raw
β-bridge sorrys after Phase C3 migrates `Step.par.betaApp` to
`subst0_term`. -/
theorem Subst.termSingleton_compose_equiv_lift_compose_termSingleton
    {level scope target : Nat}
    (substituent : Ty level scope) (rawArg : RawTerm scope)
    (typeSubstitution : Subst level scope target) :
    Subst.equiv
      (Subst.compose
        (Subst.termSingleton substituent rawArg) typeSubstitution)
      (Subst.compose typeSubstitution.lift
        (Subst.termSingleton (substituent.subst typeSubstitution)
          (rawArg.subst typeSubstitution.forRaw))) :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩                            => rfl
      | ⟨predecessor + 1, succBound⟩      => by
          show (Ty.tyVar
                  ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩).subst
                  typeSubstitution
             = ((typeSubstitution
                   ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩).rename
                   Renaming.weaken).subst
                 (Subst.termSingleton
                   (substituent.subst typeSubstitution)
                   (rawArg.subst typeSubstitution.forRaw))
          have renameSubstCommute :=
            Ty.rename_subst_commute
              (typeSubstitution
                ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
              Renaming.weaken
              (Subst.termSingleton
                (substituent.subst typeSubstitution)
                (rawArg.subst typeSubstitution.forRaw))
          have substitutionsAgreePointwise :
              Subst.equiv
                (Subst.precompose Renaming.weaken
                  (Subst.termSingleton
                    (substituent.subst typeSubstitution)
                    (rawArg.subst typeSubstitution.forRaw)))
                Subst.identity :=
            Subst.precompose_weaken_termSingleton_equiv_identity
              (substituent.subst typeSubstitution)
              (rawArg.subst typeSubstitution.forRaw)
          have congCast := Ty.subst_congr substitutionsAgreePointwise
                          (typeSubstitution
                            ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
          have identitySubstIsNeutral :=
            Ty.subst_id
              (typeSubstitution
                ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
          exact (renameSubstCommute.trans
                  (congCast.trans identitySubstIsNeutral)).symm)
    fun position =>
      match position with
      | ⟨0, _⟩                            => rfl
      | ⟨predecessor + 1, succBound⟩      =>
          (RawTerm.weaken_subst_singleton
            (typeSubstitution.forRaw
              ⟨predecessor, Nat.lt_of_succ_lt_succ succBound⟩)
            (rawArg.subst typeSubstitution.forRaw)).symm

/-- The practical specialisation: substituting the outermost variable
then applying an outer substitution equals lifting the outer
substitution under the binder then substituting the substituted
substituent. -/
theorem Ty.subst0_subst_commute {level scope target : Nat}
    (codomain : Ty level (scope + 1))
    (substituent : Ty level scope)
    (typeSubstitution : Subst level scope target) :
    (codomain.subst0 substituent).subst typeSubstitution
      = (codomain.subst typeSubstitution.lift).subst0
          (substituent.subst typeSubstitution) := by
  show (codomain.subst (Subst.singleton substituent)).subst typeSubstitution
     = (codomain.subst typeSubstitution.lift).subst
         (Subst.singleton (substituent.subst typeSubstitution))
  have leftCompose :=
    Ty.subst_compose codomain (Subst.singleton substituent) typeSubstitution
  have rightCompose :=
    Ty.subst_compose codomain typeSubstitution.lift
      (Subst.singleton (substituent.subst typeSubstitution))
  have congCast := Ty.subst_congr
    (Subst.singleton_compose_equiv_lift_compose_singleton
      substituent typeSubstitution) codomain
  exact leftCompose.trans (congCast.trans rightCompose.symm)

/-- W9.B1.3a — `termSingleton`-flavored sibling of `Ty.subst0_subst_commute`.
Substituting via `termSingleton substituent rawArg` and then applying an
outer substitution equals lifting the outer substitution under the binder
and then substituting via `termSingleton (substituent.subst _) (rawArg.subst _)`.
The load-bearing subst-commute lemma for `Term.subst`'s `appPi` arm under
the W9.B1.3a equation form. -/
theorem Ty.subst_termSingleton_subst_commute {level scope target : Nat}
    (codomain : Ty level (scope + 1))
    (substituent : Ty level scope) (rawArg : RawTerm scope)
    (typeSubstitution : Subst level scope target) :
    (codomain.subst (Subst.termSingleton substituent rawArg)).subst
        typeSubstitution
      = (codomain.subst typeSubstitution.lift).subst
          (Subst.termSingleton (substituent.subst typeSubstitution)
            (rawArg.subst typeSubstitution.forRaw)) := by
  have leftCompose :=
    Ty.subst_compose codomain (Subst.termSingleton substituent rawArg)
      typeSubstitution
  have rightCompose :=
    Ty.subst_compose codomain typeSubstitution.lift
      (Subst.termSingleton (substituent.subst typeSubstitution)
        (rawArg.subst typeSubstitution.forRaw))
  have congCast := Ty.subst_congr
    (Subst.termSingleton_compose_equiv_lift_compose_termSingleton
      substituent rawArg typeSubstitution) codomain
  exact leftCompose.trans (congCast.trans rightCompose.symm)

/-- **Term-level substitution** — apply a term-level substitution
`termSubstitution` (and the underlying type-level substitution
`typeSubstitution`) to a `Term`, producing a `Term` in the target
context with the substituted type.

The variable case looks up the substituent term via
`termSubstitution`; the binder cases (`lam`, `lamPi`) use
`TermSubst.lift` to extend `termSubstitution` under the new binder
and align body types via `Ty.subst_weaken_commute`; the
projection-laden cases (`appPi`, `pair`, `snd`) use
`Ty.subst0_subst_commute` to align `subst0`-shaped result types. -/
def Term.subst {mode sourceScope targetScope}
    {sourceContext : Ctx mode level sourceScope}
    {targetContext : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    (termSubstitution : TermSubst sourceContext targetContext typeSubstitution) :
    {tyValue : Ty level sourceScope} →
      Term sourceContext tyValue →
      Term targetContext (tyValue.subst typeSubstitution)
  | _, .var position  => termSubstitution position
  | _, .unit          => Term.unit
  | _, .lam (codomainType := codomainType) body =>
      Term.lam (codomainType := codomainType.subst typeSubstitution)
        ((Ty.subst_weaken_commute codomainType typeSubstitution) ▸
          (Term.subst (TermSubst.lift termSubstitution _) body))
  | _, .app functionTerm argumentTerm  =>
      Term.app (Term.subst termSubstitution functionTerm)
               (Term.subst termSubstitution argumentTerm)
  | _, .lamPi (domainType := domainType) body =>
      Term.lamPi
        (Term.subst (TermSubst.lift termSubstitution domainType) body)
  | _, .appPi (domainType := domainType) (codomainType := codomainType)
              (argumentRaw := argumentRaw) resultEq functionTerm argumentTerm =>
      -- W9.B1.3a — termSingleton-flavored appPi.  resultEq : resultType =
      -- codomainType.subst (Subst.termSingleton domainType argumentRaw).
      -- Build the substituted appPi at the canonical post-subst termSingleton
      -- shape (with rawArg substituted via the underlying RawTermSubst), then
      -- cast through resultEq's substituted form and subst-termSingleton-subst-
      -- commute.
      (congrArg (Ty.subst · typeSubstitution) resultEq).symm ▸
        ((Ty.subst_termSingleton_subst_commute codomainType domainType
            argumentRaw typeSubstitution).symm ▸
          Term.appPi (argumentRaw := argumentRaw.subst typeSubstitution.forRaw)
            rfl (Term.subst termSubstitution functionTerm)
                (Term.subst termSubstitution argumentTerm))
  | _, .pair (firstType := firstType) (secondType := secondType)
             firstVal secondVal =>
      Term.pair (Term.subst termSubstitution firstVal)
        ((Ty.subst0_subst_commute secondType firstType typeSubstitution) ▸
          (Term.subst termSubstitution secondVal))
  | _, .fst pairTerm  => Term.fst (Term.subst termSubstitution pairTerm)
  | _, .snd (firstType := firstType) (secondType := secondType)
            pairTerm resultEq =>
      -- W9.B1.2 — equation-bearing snd.  resultEq : resultType =
      -- secondType.subst0 firstType.  We build the substituted snd
      -- at canonical (secondSubst.subst0 firstSubst), then cast
      -- through resultEq's substituted form and subst0_subst_commute.
      (congrArg (Ty.subst · typeSubstitution) resultEq).symm ▸
        ((Ty.subst0_subst_commute secondType firstType typeSubstitution).symm ▸
          Term.snd (Term.subst termSubstitution pairTerm) rfl)
  | _, .boolTrue      => Term.boolTrue
  | _, .boolFalse     => Term.boolFalse
  | _, .boolElim scrutinee thenBranch elseBranch =>
      Term.boolElim (Term.subst termSubstitution scrutinee)
                    (Term.subst termSubstitution thenBranch)
                    (Term.subst termSubstitution elseBranch)
  | _, .natZero       => Term.natZero
  | _, .natSucc predecessor =>
      Term.natSucc (Term.subst termSubstitution predecessor)
  | _, .natRec scrutinee zeroBranch succBranch =>
      Term.natRec (Term.subst termSubstitution scrutinee)
                  (Term.subst termSubstitution zeroBranch)
                  (Term.subst termSubstitution succBranch)
  | _, .natElim scrutinee zeroBranch succBranch =>
      Term.natElim (Term.subst termSubstitution scrutinee)
                   (Term.subst termSubstitution zeroBranch)
                   (Term.subst termSubstitution succBranch)
  | _, .listNil       => Term.listNil
  | _, .listCons headValue tailValue =>
      Term.listCons (Term.subst termSubstitution headValue)
                    (Term.subst termSubstitution tailValue)
  | _, .listElim scrutinee nilBranch consBranch =>
      Term.listElim (Term.subst termSubstitution scrutinee)
                    (Term.subst termSubstitution nilBranch)
                    (Term.subst termSubstitution consBranch)
  | _, .optionNone    => Term.optionNone
  | _, .optionSome value =>
      Term.optionSome (Term.subst termSubstitution value)
  | _, .optionMatch scrutinee noneBranch someBranch =>
      Term.optionMatch (Term.subst termSubstitution scrutinee)
                       (Term.subst termSubstitution noneBranch)
                       (Term.subst termSubstitution someBranch)
  | _, .eitherInl value =>
      Term.eitherInl (Term.subst termSubstitution value)
  | _, .eitherInr value =>
      Term.eitherInr (Term.subst termSubstitution value)
  | _, .eitherMatch scrutinee leftBranch rightBranch =>
      Term.eitherMatch (Term.subst termSubstitution scrutinee)
                       (Term.subst termSubstitution leftBranch)
                       (Term.subst termSubstitution rightBranch)
  | _, .refl rawTerm =>
      Term.refl (rawTerm.subst typeSubstitution.forRaw)
  | _, .idJ baseCase witness =>
      Term.idJ (Term.subst termSubstitution baseCase)
               (Term.subst termSubstitution witness)

/-- **Single-variable term substitution** — substitute `arg` for var 0
in `body`.  Used by β-reduction.  Result type is computed via
`Ty.subst0` at the type level, matching `Term.appPi`'s result-type
shape exactly.  For the term-bearing variant whose type captures
`Term.toRaw arg` at position 0 (used by the typed→raw forward
bridge), see `Term.subst0_term`. -/
@[reducible]
def Term.subst0 {mode : Mode} {level scope : Nat}
    {sourceContext : Ctx mode level scope}
    {argType : Ty level scope} {bodyType : Ty level (scope + 1)}
    (body : Term (sourceContext.cons argType) bodyType)
    (arg : Term sourceContext argType) :
    Term sourceContext (bodyType.subst0 argType) :=
  Term.subst (TermSubst.singleton arg) body

/-- **Term-bearing single-variable substitution.**  Substitute `arg`
for var 0 using `TermSubst.termSingleton`, whose underlying
type substitution is `Subst.termSingleton argType (Term.toRaw arg)`.
The result type captures the argument's raw projection at position 0
— the right shape for the typed→raw forward bridge for
β-reduction. -/
@[reducible]
def Term.subst0_term {mode : Mode} {level scope : Nat}
    {sourceContext : Ctx mode level scope}
    {argType : Ty level scope} {bodyType : Ty level (scope + 1)}
    (body : Term (sourceContext.cons argType) bodyType)
    (arg : Term sourceContext argType) :
    Term sourceContext
      (bodyType.subst (Subst.termSingleton argType (Term.toRaw arg))) :=
  Term.subst (TermSubst.termSingleton arg) body

/-! ## Categorical structure on TermSubst.

The term-level analogues of `Subst.identity` and `Subst.compose`,
witnessing the same enriched-category structure at the term level.
Functoriality theorems (`Term.subst_id`, `Term.subst_compose`) need
dependent-cast wrangling because `Term.subst termSubstitution term :
Term targetContext (tyValue.subst typeSubstitution)` is not
definitionally `Term targetContext tyValue` even when
`typeSubstitution = Subst.identity`. -/

/-- Identity term-substitution: each position maps to its own
`Term.var`, cast through `Ty.subst_id` to live at
`(varType sourceContext position).subst Subst.identity`. -/
def TermSubst.identity {mode : Mode} {level scope : Nat}
    (sourceContext : Ctx mode level scope) :
    TermSubst sourceContext sourceContext Subst.identity :=
  fun position =>
    (Ty.subst_id (varType sourceContext position)).symm ▸ Term.var position

/-- Compose two term-substitutions: apply `firstTermSubstitution`
then substitute the result by `secondTermSubstitution`, casting
through `Ty.subst_compose`. -/
def TermSubst.compose {mode : Mode}
    {level firstScope middleScope finalScope : Nat}
    {firstContext : Ctx mode level firstScope}
    {middleContext : Ctx mode level middleScope}
    {finalContext : Ctx mode level finalScope}
    {firstTypeSubstitution : Subst level firstScope middleScope}
    {secondTypeSubstitution : Subst level middleScope finalScope}
    (firstTermSubstitution :
      TermSubst firstContext middleContext firstTypeSubstitution)
    (secondTermSubstitution :
      TermSubst middleContext finalContext secondTypeSubstitution) :
    TermSubst firstContext finalContext
      (Subst.compose firstTypeSubstitution secondTypeSubstitution) :=
  fun position =>
    Ty.subst_compose
      (varType firstContext position)
      firstTypeSubstitution secondTypeSubstitution
      ▸ Term.subst secondTermSubstitution
          (firstTermSubstitution position)


end LeanFX.Syntax
