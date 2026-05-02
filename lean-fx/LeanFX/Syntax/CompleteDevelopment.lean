import LeanFX.Syntax.TermSubst
import LeanFX.Syntax.TermStrengthen
import LeanFX.Syntax.CompleteDevelopmentRedex

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Complete development.

`Term.cd` performs one structural complete-development pass: it
recursively develops subterms and contracts the β/projection/ι redexes
exposed by that pass.

## Aggressive shape-matching, deep-rule backed

Each redex is matched on the *developed* shape (e.g., when
`developedFunction = Term.lam body`, β-app fires even though the
original `functionTerm` may not have been a literal lam).  The 17
deep `Step.par` rules in `ParRed.lean` are exactly what this matches —
they accept "inner term parallel-reduces to redex shape" as the
premise, so the deep firing here will be witnessed by `cd_lemma`.

## η is deferred to η-postponement

η-arrow and η-sigma are deliberately not contracted by `cd`.  Term-
level structural equality (Term.beq) is infeasible for η-sigma because
Lean's match elaborator does not scale to the 729-case enumeration the
27-ctor mutual recursion would require.  η-arrow lacks a clean
`etaArrowDeep` rule because the dependent-typed inversion of
`body → f.weaken applied to var0` cannot be expressed as a Lean ctor.

`Term.isNewestVar` and `Ty.arrow_weaken_strengthen` remain available
for the η-postponement work that follows β/ι confluence. -/

/-- The eta-arrow strengthening target for a lambda body of shape
`(f.weaken) x`. -/
theorem Ty.arrow_weaken_strengthen {level scope : Nat}
    (domainType codomainType : Ty level scope) :
    (Ty.arrow domainType.weaken codomainType.weaken).strengthen =
      some (Ty.arrow domainType codomainType) :=
  (Ty.strengthen_eq_some_iff_weaken
    (Ty.arrow domainType.weaken codomainType.weaken)
    (Ty.arrow domainType codomainType)).mpr rfl

/-- Recognise the newest variable in a context extended by one binder.

The returned equality identifies the term's type with the weakened
newest-binder type.  Reserved for the η-postponement pass; not used
by the β/ι-only `Term.cd` below.

Every `Term` constructor is enumerated explicitly — no wildcard.
The wildcard form (`| _ => none`) leaks `propext` because Lean 4's
match compiler emits propext while justifying the catch-all on a
dependent inductive.  Full enumeration with universal `candidateType`
keeps the function strictly axiom-free per `AXIOMS.md`. -/
def Term.isNewestVar {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {newType : Ty level scope}
    {candidateType : Ty level (scope + 1)}
    (term : Term (context.cons newType) candidateType) :
    Option (PLift (candidateType = newType.weaken)) :=
  match term with
  | Term.var position =>
      match position with
      | ⟨0, _⟩ => some ⟨rfl⟩
      | ⟨_ + 1, _⟩ => none
  | Term.unit => none
  | Term.lam _ => none
  | Term.app _ _ => none
  | Term.lamPi _ => none
  | Term.appPi _ _ _ => none
  | Term.pair _ _ => none
  | Term.fst _ => none
  | Term.snd _ => none
  | Term.boolTrue => none
  | Term.boolFalse => none
  | Term.boolElim _ _ _ => none
  | Term.natZero => none
  | Term.natSucc _ => none
  | Term.natElim _ _ _ => none
  | Term.natRec _ _ _ => none
  | Term.listNil => none
  | Term.listCons _ _ => none
  | Term.listElim _ _ _ => none
  | Term.optionNone => none
  | Term.optionSome _ => none
  | Term.optionMatch _ _ _ => none
  | Term.eitherInl _ => none
  | Term.eitherInr _ => none
  | Term.eitherMatch _ _ _ => none
  | Term.refl _ => none
  | Term.idJ _ _ => none

/-- Typed inversion: a Term whose `toRaw` is `RawTerm.refl _` and
whose type is the self-loop identity `Ty.id carrier endpoint endpoint`
must structurally be `Term.refl endpoint`.

The proof generalizes the type to a free `ty`, then `cases witness`
runs at universal index (Rule 3 of the zero-axiom match recipe).
Each non-`refl` branch contradicts `rawEq` via `RawTerm` constructor
disagreement; the `refl` branch closes by `cases typeEq` injecting
`Ty.id` constructor.  Zero-axiom verified by smoke. -/
theorem Term.eq_refl_of_toRaw_refl_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {carrier : Ty level scope} {endpoint : RawTerm scope}
    (typeEq : ty = Ty.id carrier endpoint endpoint)
    {rawEnd : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.refl rawEnd) :
    HEq witness (@Term.refl mode level scope ctx carrier endpoint) := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => simp only [Term.toRaw] at rawEq; cases rawEq
  | lam body => simp only [Term.toRaw] at rawEq; cases rawEq
  | app function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | lamPi body => simp only [Term.toRaw] at rawEq; cases rawEq
  | appPi function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | pair firstVal secondVal =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | fst pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | snd pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | boolTrue => simp only [Term.toRaw] at rawEq; cases rawEq
  | boolFalse => simp only [Term.toRaw] at rawEq; cases rawEq
  | boolElim scrutinee thenBranch elseBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natZero => simp only [Term.toRaw] at rawEq; cases rawEq
  | natSucc predecessor =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natElim scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natRec scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | listNil => simp only [Term.toRaw] at rawEq; cases rawEq
  | listCons head tail =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | listElim scrutinee nilBranch consBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | optionNone => simp only [Term.toRaw] at rawEq; cases rawEq
  | optionSome value =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | optionMatch scrutinee noneBranch someBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherInl value =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherInr value =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherMatch scrutinee leftBranch rightBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | refl rawTerm =>
      simp only [Term.toRaw] at rawEq
      cases rawEq
      cases typeEq
      rfl
  | idJ baseCase witness =>
      simp only [Term.toRaw] at rawEq; cases rawEq

/-- Specialization of `eq_refl_of_toRaw_refl_general` to the
self-loop identity type — the form consumed by `cd_dominates_idJ`. -/
theorem Term.eq_refl_of_toRaw_refl
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {endpoint : RawTerm scope}
    (witness : Term ctx (Ty.id carrier endpoint endpoint))
    {rawEnd : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.refl rawEnd) :
    witness = Term.refl endpoint :=
  eq_of_heq (Term.eq_refl_of_toRaw_refl_general
    witness rfl rawEq)

/-- iotaIdJ redex check, aligned-endpoints case.

With both endpoints equal to `leftEnd`, `Term.refl _` is an
admissible pattern for a witness of type
`Ty.id carrier leftEnd leftEnd`, so the iota check reduces to a
binary decision: contract to `developedBase` if the witness is
structurally `Term.refl`; otherwise rebuild as `Term.idJ`.

The dispatch goes via `Term.toRaw` rather than directly on the
typed witness.  A direct typed match
`| Term.refl _ => ... | _ => ...` LEAKS `propext` because Lean 4's
match compiler emits the axiom while discharging the wildcard's
redundancy on a dependent inductive at a restricted type index
(Rule 1 + Rule 4 of the zero-axiom match recipe).  Full Term-ctor
enumeration fails because ctors like `Term.var` cannot have type
`Ty.id _ _ _` (varType is opaque).  toRaw-shape dispatch with full
RawTerm-ctor enumeration is propext-free (Rule 5).  Downstream
`simp + split` proofs see 25 cases instead of 2; the `cd_dominates_idJ`
proof in `CdDominates.lean` handles this with `all_goals exact ...`
after the named `RawTerm.refl` case, mirroring the pattern proven
zero-axiom on the raw side (`RawCdDominates.lean`). -/
def Term.cd_idJ_redex_aligned
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier resultType : Ty level scope}
    {leftEnd : RawTerm scope}
    (developedBase : Term context resultType)
    (developedWitness :
      Term context (Ty.id carrier leftEnd leftEnd)) :
    Term context resultType :=
  match Term.toRaw developedWitness with
  | RawTerm.refl _ => developedBase
  | RawTerm.var _ => Term.idJ developedBase developedWitness
  | RawTerm.unit => Term.idJ developedBase developedWitness
  | RawTerm.lam _ => Term.idJ developedBase developedWitness
  | RawTerm.app _ _ => Term.idJ developedBase developedWitness
  | RawTerm.pair _ _ => Term.idJ developedBase developedWitness
  | RawTerm.fst _ => Term.idJ developedBase developedWitness
  | RawTerm.snd _ => Term.idJ developedBase developedWitness
  | RawTerm.boolTrue => Term.idJ developedBase developedWitness
  | RawTerm.boolFalse => Term.idJ developedBase developedWitness
  | RawTerm.boolElim _ _ _ => Term.idJ developedBase developedWitness
  | RawTerm.natZero => Term.idJ developedBase developedWitness
  | RawTerm.natSucc _ => Term.idJ developedBase developedWitness
  | RawTerm.natElim _ _ _ => Term.idJ developedBase developedWitness
  | RawTerm.natRec _ _ _ => Term.idJ developedBase developedWitness
  | RawTerm.listNil => Term.idJ developedBase developedWitness
  | RawTerm.listCons _ _ => Term.idJ developedBase developedWitness
  | RawTerm.listElim _ _ _ => Term.idJ developedBase developedWitness
  | RawTerm.optionNone => Term.idJ developedBase developedWitness
  | RawTerm.optionSome _ => Term.idJ developedBase developedWitness
  | RawTerm.optionMatch _ _ _ => Term.idJ developedBase developedWitness
  | RawTerm.eitherInl _ => Term.idJ developedBase developedWitness
  | RawTerm.eitherInr _ => Term.idJ developedBase developedWitness
  | RawTerm.eitherMatch _ _ _ => Term.idJ developedBase developedWitness
  | RawTerm.idJ _ _ => Term.idJ developedBase developedWitness

/-- iotaIdJ redex check.  Splits on `leftEnd = rightEnd` (decidable
via `RawTerm`'s `DecidableEq` instance); when the endpoints agree,
casts the witness to the self-loop id type and delegates to
`cd_idJ_redex_aligned`; otherwise falls through to cong. -/
def Term.cd_idJ_redex
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier resultType : Ty level scope}
    {leftEnd rightEnd : RawTerm scope}
    (developedBase : Term context resultType)
    (developedWitness :
      Term context (Ty.id carrier leftEnd rightEnd)) :
    Term context resultType :=
  if endpointsEqual : leftEnd = rightEnd then
    Term.cd_idJ_redex_aligned developedBase
      (endpointsEqual ▸ developedWitness)
  else
    Term.idJ developedBase developedWitness

/-- Complete development for intrinsically typed terms.

Aggressive β/ι firing on developed shapes; no η firing.

Each elimination form delegates its redex contraction to the
corresponding `Term.cd_<head>_redex` helper in
`CompleteDevelopmentRedex.lean`.  That helper dispatches on
`Term.toRaw <developed>` with full 25-RawTerm-ctor enumeration
(propext-free per Rule 5 of the zero-axiom match recipe) and
extracts typed payload via the `Term.<payload>_of_<C>_general`
defs from `TermExtraction.lean`.  Term.cd's outer match runs at
universal index (Rule 3 — clean) with no inner matches, keeping
the whole definition propext-free. -/
def Term.cd {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    {termType : Ty level scope} →
      Term context termType → Term context termType
  | _, .var position => Term.var position
  | _, .unit => Term.unit
  | _, .lam (codomainType := codomainType) body =>
      Term.lam (codomainType := codomainType) (Term.cd body)
  | _, .app functionTerm argumentTerm =>
      Term.cd_app_redex (Term.cd functionTerm) (Term.cd argumentTerm)
  | _, .lamPi body =>
      Term.lamPi (Term.cd body)
  | _, .appPi resultEq functionTerm argumentTerm =>
      -- W9.B1.1 — preserve resultEq across cd; cast result to match input.
      resultEq.symm ▸
        Term.cd_appPi_redex (Term.cd functionTerm) (Term.cd argumentTerm)
  | _, .pair firstVal secondVal =>
      Term.pair (Term.cd firstVal) (Term.cd secondVal)
  | _, .fst pairTerm =>
      Term.cd_fst_redex (Term.cd pairTerm)
  | _, .snd pairTerm =>
      Term.cd_snd_redex (Term.cd pairTerm)
  | _, .boolTrue => Term.boolTrue
  | _, .boolFalse => Term.boolFalse
  | _, .boolElim scrutinee thenBranch elseBranch =>
      Term.cd_boolElim_redex (Term.cd scrutinee)
        (Term.cd thenBranch) (Term.cd elseBranch)
  | _, .natZero => Term.natZero
  | _, .natSucc predecessor =>
      Term.natSucc (Term.cd predecessor)
  | _, .natElim scrutinee zeroBranch succBranch =>
      Term.cd_natElim_redex (Term.cd scrutinee)
        (Term.cd zeroBranch) (Term.cd succBranch)
  | _, .natRec scrutinee zeroBranch succBranch =>
      Term.cd_natRec_redex (Term.cd scrutinee)
        (Term.cd zeroBranch) (Term.cd succBranch)
  | _, .listNil => Term.listNil
  | _, .listCons head tail =>
      Term.listCons (Term.cd head) (Term.cd tail)
  | _, .listElim scrutinee nilBranch consBranch =>
      Term.cd_listElim_redex (Term.cd scrutinee)
        (Term.cd nilBranch) (Term.cd consBranch)
  | _, .optionNone => Term.optionNone
  | _, .optionSome value =>
      Term.optionSome (Term.cd value)
  | _, .optionMatch scrutinee noneBranch someBranch =>
      Term.cd_optionMatch_redex (Term.cd scrutinee)
        (Term.cd noneBranch) (Term.cd someBranch)
  | _, .eitherInl value =>
      Term.eitherInl (Term.cd value)
  | _, .eitherInr value =>
      Term.eitherInr (Term.cd value)
  | _, .eitherMatch scrutinee leftBranch rightBranch =>
      Term.cd_eitherMatch_redex (Term.cd scrutinee)
        (Term.cd leftBranch) (Term.cd rightBranch)
  | _, .refl rawTerm =>
      Term.refl rawTerm
  | _, .idJ baseCase witness =>
      Term.cd_idJ_redex (Term.cd baseCase) (Term.cd witness)

/-- Pushing `Term.cd` through a same-context type-equality cast.
`Term.cd` commutes with `▸` because the cast preserves the term's
underlying syntactic structure.  Used by `Step.par.cd_monotone`'s
β cases to align `cd` of a cast-bearing target with the cast-
bearing source.  Proof: `cases typeEquality; rfl`. -/
theorem Term.cd_cast {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    (typeEquality : sourceType = targetType)
    (term : Term context sourceType) :
    Term.cd (typeEquality ▸ term) = typeEquality ▸ Term.cd term := by
  cases typeEquality
  rfl

end LeanFX.Syntax
