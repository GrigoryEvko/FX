import LeanFX.Syntax.TermExtraction
import LeanFX.Syntax.TermSubst
import LeanFX.Syntax.TermStrengthen

/-! ## Per-arm complete-development redex helpers.

`Term.cd` (in `CompleteDevelopment.lean`) dispatches recursively
through every Term constructor, then for elimination forms it
contracts redexes whose head has the right shape.  Each
contraction is delegated to a `Term.cd_<head>_redex` helper here.

### Why factor out

A direct typed inner match `| Term.lam body => ... | _ => ...`
on the developed scrutinee leaks `propext` (Rule 1 + Rule 4 of
the zero-axiom match recipe).  Each helper here dispatches on
`Term.toRaw <developed>` with full 25-RawTerm-ctor enumeration
(Rule 5 — clean) and extracts typed payload via the
`Term.<payload>_of_<C>_general` defs from `TermExtraction.lean`.

This keeps `Term.cd`'s outer Term-ctor match at universal index
(Rule 3 — clean) with no inner matches, so the whole `Term.cd`
definition stays propext-free.  Downstream `cd_dominates` and
`cd_lemma_star` proofs that `simp + split` through `Term.cd`
inherit zero axioms instead of `[propext, Quot.sound]`. -/

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ### β-app: when developed function reduces to `Term.lam`. -/

/-- Non-dependent application redex check.

If `developedFunction.toRaw` is `RawTerm.lam _`, the function is
a `Term.lam body` (typed inversion via
`Term.body_of_lam_general`); fire β by substituting
`developedArgument` into `body`.  Otherwise rebuild as
`Term.app`. -/
def Term.cd_app_redex
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    (developedFunction :
      Term context (Ty.arrow domainType codomainType))
    (developedArgument : Term context domainType) :
    Term context codomainType :=
  match h_raw : Term.toRaw developedFunction with
  | RawTerm.lam _ =>
      let body :=
        Term.body_of_lam_general developedFunction rfl h_raw
      (Ty.weaken_subst_singleton codomainType domainType) ▸
        Term.subst0 body developedArgument
  | RawTerm.var _ => Term.app developedFunction developedArgument
  | RawTerm.unit => Term.app developedFunction developedArgument
  | RawTerm.app _ _ => Term.app developedFunction developedArgument
  | RawTerm.pair _ _ => Term.app developedFunction developedArgument
  | RawTerm.fst _ => Term.app developedFunction developedArgument
  | RawTerm.snd _ => Term.app developedFunction developedArgument
  | RawTerm.boolTrue => Term.app developedFunction developedArgument
  | RawTerm.boolFalse => Term.app developedFunction developedArgument
  | RawTerm.boolElim _ _ _ =>
      Term.app developedFunction developedArgument
  | RawTerm.natZero => Term.app developedFunction developedArgument
  | RawTerm.natSucc _ => Term.app developedFunction developedArgument
  | RawTerm.natElim _ _ _ =>
      Term.app developedFunction developedArgument
  | RawTerm.natRec _ _ _ =>
      Term.app developedFunction developedArgument
  | RawTerm.listNil => Term.app developedFunction developedArgument
  | RawTerm.listCons _ _ =>
      Term.app developedFunction developedArgument
  | RawTerm.listElim _ _ _ =>
      Term.app developedFunction developedArgument
  | RawTerm.optionNone =>
      Term.app developedFunction developedArgument
  | RawTerm.optionSome _ =>
      Term.app developedFunction developedArgument
  | RawTerm.optionMatch _ _ _ =>
      Term.app developedFunction developedArgument
  | RawTerm.eitherInl _ =>
      Term.app developedFunction developedArgument
  | RawTerm.eitherInr _ =>
      Term.app developedFunction developedArgument
  | RawTerm.eitherMatch _ _ _ =>
      Term.app developedFunction developedArgument
  | RawTerm.refl _ => Term.app developedFunction developedArgument
  | RawTerm.idJ _ _ => Term.app developedFunction developedArgument

/-! ### β-appPi: dependent application redex check. -/

/-- Dependent application redex check.  `Term.lamPi`'s body is
already at scope+1 (no weaken needed); β fires by substituting
`developedArgument` into body. -/
def Term.cd_appPi_redex
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    (developedFunction :
      Term context (Ty.piTy domainType codomainType))
    (developedArgument : Term context domainType) :
    Term context (codomainType.subst0 domainType) :=
  match h_raw : Term.toRaw developedFunction with
  | RawTerm.lam _ =>
      let body :=
        Term.body_of_lamPi_general developedFunction rfl h_raw
      Term.subst0 body developedArgument
  | RawTerm.var _ =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.unit =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.app _ _ =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.pair _ _ =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.fst _ => Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.snd _ => Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.boolTrue =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.boolFalse =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.boolElim _ _ _ =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.natZero =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.natSucc _ =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.natElim _ _ _ =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.natRec _ _ _ =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.listNil =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.listCons _ _ =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.listElim _ _ _ =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.optionNone =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.optionSome _ =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.optionMatch _ _ _ =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.eitherInl _ =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.eitherInr _ =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.eitherMatch _ _ _ =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.refl _ =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument
  | RawTerm.idJ _ _ =>
      Term.appPi (argumentRaw := RawTerm.unit) (Ty.subst0_eq_termSingleton_unit codomainType domainType) developedFunction developedArgument

/-! ### β-fst, β-snd: pair projections. -/

/-- First-projection redex check.  `Term.pair firstVal _` has
its first component extracted directly. -/
def Term.cd_fst_redex
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    (developedPair :
      Term context (Ty.sigmaTy firstType secondType)) :
    Term context firstType :=
  match h_raw : Term.toRaw developedPair with
  | RawTerm.pair _ _ =>
      Term.firstVal_of_pair_general developedPair rfl h_raw
  | RawTerm.var _ => Term.fst developedPair
  | RawTerm.unit => Term.fst developedPair
  | RawTerm.lam _ => Term.fst developedPair
  | RawTerm.app _ _ => Term.fst developedPair
  | RawTerm.fst _ => Term.fst developedPair
  | RawTerm.snd _ => Term.fst developedPair
  | RawTerm.boolTrue => Term.fst developedPair
  | RawTerm.boolFalse => Term.fst developedPair
  | RawTerm.boolElim _ _ _ => Term.fst developedPair
  | RawTerm.natZero => Term.fst developedPair
  | RawTerm.natSucc _ => Term.fst developedPair
  | RawTerm.natElim _ _ _ => Term.fst developedPair
  | RawTerm.natRec _ _ _ => Term.fst developedPair
  | RawTerm.listNil => Term.fst developedPair
  | RawTerm.listCons _ _ => Term.fst developedPair
  | RawTerm.listElim _ _ _ => Term.fst developedPair
  | RawTerm.optionNone => Term.fst developedPair
  | RawTerm.optionSome _ => Term.fst developedPair
  | RawTerm.optionMatch _ _ _ => Term.fst developedPair
  | RawTerm.eitherInl _ => Term.fst developedPair
  | RawTerm.eitherInr _ => Term.fst developedPair
  | RawTerm.eitherMatch _ _ _ => Term.fst developedPair
  | RawTerm.refl _ => Term.fst developedPair
  | RawTerm.idJ _ _ => Term.fst developedPair

/-- Second-projection redex check. -/
def Term.cd_snd_redex
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    (developedPair :
      Term context (Ty.sigmaTy firstType secondType)) :
    Term context (secondType.subst0 firstType) :=
  match h_raw : Term.toRaw developedPair with
  | RawTerm.pair _ _ =>
      Term.secondVal_of_pair_general developedPair rfl h_raw
  | RawTerm.var _ => Term.snd developedPair rfl
  | RawTerm.unit => Term.snd developedPair rfl
  | RawTerm.lam _ => Term.snd developedPair rfl
  | RawTerm.app _ _ => Term.snd developedPair rfl
  | RawTerm.fst _ => Term.snd developedPair rfl
  | RawTerm.snd _ => Term.snd developedPair rfl
  | RawTerm.boolTrue => Term.snd developedPair rfl
  | RawTerm.boolFalse => Term.snd developedPair rfl
  | RawTerm.boolElim _ _ _ => Term.snd developedPair rfl
  | RawTerm.natZero => Term.snd developedPair rfl
  | RawTerm.natSucc _ => Term.snd developedPair rfl
  | RawTerm.natElim _ _ _ => Term.snd developedPair rfl
  | RawTerm.natRec _ _ _ => Term.snd developedPair rfl
  | RawTerm.listNil => Term.snd developedPair rfl
  | RawTerm.listCons _ _ => Term.snd developedPair rfl
  | RawTerm.listElim _ _ _ => Term.snd developedPair rfl
  | RawTerm.optionNone => Term.snd developedPair rfl
  | RawTerm.optionSome _ => Term.snd developedPair rfl
  | RawTerm.optionMatch _ _ _ => Term.snd developedPair rfl
  | RawTerm.eitherInl _ => Term.snd developedPair rfl
  | RawTerm.eitherInr _ => Term.snd developedPair rfl
  | RawTerm.eitherMatch _ _ _ => Term.snd developedPair rfl
  | RawTerm.refl _ => Term.snd developedPair rfl
  | RawTerm.idJ _ _ => Term.snd developedPair rfl

/-! ### ι-boolElim: branch on bool scrutinee. -/

/-- boolElim redex check.  No typed payload extraction needed —
both branches just return the corresponding developed branch. -/
def Term.cd_boolElim_redex
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {resultType : Ty level scope}
    (developedScrutinee : Term context Ty.bool)
    (developedThen : Term context resultType)
    (developedElse : Term context resultType) :
    Term context resultType :=
  match Term.toRaw developedScrutinee with
  | RawTerm.boolTrue => developedThen
  | RawTerm.boolFalse => developedElse
  | RawTerm.var _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.unit =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.lam _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.app _ _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.pair _ _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.fst _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.snd _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.boolElim _ _ _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.natZero =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.natSucc _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.natElim _ _ _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.natRec _ _ _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.listNil =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.listCons _ _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.listElim _ _ _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.optionNone =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.optionSome _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.optionMatch _ _ _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.eitherInl _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.eitherInr _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.eitherMatch _ _ _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.refl _ =>
      Term.boolElim developedScrutinee developedThen developedElse
  | RawTerm.idJ _ _ =>
      Term.boolElim developedScrutinee developedThen developedElse

/-! ### ι-natElim: nat scrutinee dispatch. -/

/-- natElim redex check.  natZero → developedZero;
natSucc pred → app(developedSucc, pred). -/
def Term.cd_natElim_redex
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {resultType : Ty level scope}
    (developedScrutinee : Term context Ty.nat)
    (developedZero : Term context resultType)
    (developedSucc : Term context (Ty.arrow Ty.nat resultType)) :
    Term context resultType :=
  match h_raw : Term.toRaw developedScrutinee with
  | RawTerm.natZero => developedZero
  | RawTerm.natSucc _ =>
      let predecessor :=
        Term.predecessor_of_natSucc_general developedScrutinee rfl h_raw
      Term.app developedSucc predecessor
  | RawTerm.var _ =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.unit =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.lam _ =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.app _ _ =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.pair _ _ =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.fst _ =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.snd _ =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.boolTrue =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.boolFalse =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.boolElim _ _ _ =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.natElim _ _ _ =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.natRec _ _ _ =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.listNil =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.listCons _ _ =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.listElim _ _ _ =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.optionNone =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.optionSome _ =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.optionMatch _ _ _ =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.eitherInl _ =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.eitherInr _ =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.eitherMatch _ _ _ =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.refl _ =>
      Term.natElim developedScrutinee developedZero developedSucc
  | RawTerm.idJ _ _ =>
      Term.natElim developedScrutinee developedZero developedSucc

/-! ### ι-natRec: nat scrutinee dispatch with recursion. -/

/-- natRec redex check. -/
def Term.cd_natRec_redex
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {resultType : Ty level scope}
    (developedScrutinee : Term context Ty.nat)
    (developedZero : Term context resultType)
    (developedSucc : Term context
        (Ty.arrow Ty.nat (Ty.arrow resultType resultType))) :
    Term context resultType :=
  match h_raw : Term.toRaw developedScrutinee with
  | RawTerm.natZero => developedZero
  | RawTerm.natSucc _ =>
      let predecessor :=
        Term.predecessor_of_natSucc_general developedScrutinee rfl h_raw
      Term.app (Term.app developedSucc predecessor)
        (Term.natRec predecessor developedZero developedSucc)
  | RawTerm.var _ =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.unit =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.lam _ =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.app _ _ =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.pair _ _ =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.fst _ =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.snd _ =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.boolTrue =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.boolFalse =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.boolElim _ _ _ =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.natElim _ _ _ =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.natRec _ _ _ =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.listNil =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.listCons _ _ =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.listElim _ _ _ =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.optionNone =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.optionSome _ =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.optionMatch _ _ _ =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.eitherInl _ =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.eitherInr _ =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.eitherMatch _ _ _ =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.refl _ =>
      Term.natRec developedScrutinee developedZero developedSucc
  | RawTerm.idJ _ _ =>
      Term.natRec developedScrutinee developedZero developedSucc

/-! ### ι-listElim: list scrutinee dispatch. -/

/-- listElim redex check.  listNil → nil;
listCons head tail → app(app(cons, head), tail). -/
def Term.cd_listElim_redex
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (developedScrutinee : Term context (Ty.list elementType))
    (developedNil : Term context resultType)
    (developedCons : Term context
        (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))) :
    Term context resultType :=
  match h_raw : Term.toRaw developedScrutinee with
  | RawTerm.listNil => developedNil
  | RawTerm.listCons _ _ =>
      let head :=
        Term.head_of_listCons_general developedScrutinee rfl h_raw
      let tail :=
        Term.tail_of_listCons_general developedScrutinee rfl h_raw
      Term.app (Term.app developedCons head) tail
  | RawTerm.var _ =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.unit =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.lam _ =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.app _ _ =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.pair _ _ =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.fst _ =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.snd _ =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.boolTrue =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.boolFalse =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.boolElim _ _ _ =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.natZero =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.natSucc _ =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.natElim _ _ _ =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.natRec _ _ _ =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.listElim _ _ _ =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.optionNone =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.optionSome _ =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.optionMatch _ _ _ =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.eitherInl _ =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.eitherInr _ =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.eitherMatch _ _ _ =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.refl _ =>
      Term.listElim developedScrutinee developedNil developedCons
  | RawTerm.idJ _ _ =>
      Term.listElim developedScrutinee developedNil developedCons

/-! ### ι-optionMatch: option scrutinee dispatch. -/

/-- optionMatch redex check.  optionNone → none;
optionSome value → app(some, value). -/
def Term.cd_optionMatch_redex
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (developedScrutinee : Term context (Ty.option elementType))
    (developedNone : Term context resultType)
    (developedSome : Term context (Ty.arrow elementType resultType)) :
    Term context resultType :=
  match h_raw : Term.toRaw developedScrutinee with
  | RawTerm.optionNone => developedNone
  | RawTerm.optionSome _ =>
      let value :=
        Term.value_of_optionSome_general developedScrutinee rfl h_raw
      Term.app developedSome value
  | RawTerm.var _ =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.unit =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.lam _ =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.app _ _ =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.pair _ _ =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.fst _ =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.snd _ =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.boolTrue =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.boolFalse =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.boolElim _ _ _ =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.natZero =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.natSucc _ =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.natElim _ _ _ =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.natRec _ _ _ =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.listNil =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.listCons _ _ =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.listElim _ _ _ =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.optionMatch _ _ _ =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.eitherInl _ =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.eitherInr _ =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.eitherMatch _ _ _ =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.refl _ =>
      Term.optionMatch developedScrutinee developedNone developedSome
  | RawTerm.idJ _ _ =>
      Term.optionMatch developedScrutinee developedNone developedSome

/-! ### ι-eitherMatch: either scrutinee dispatch. -/

/-- eitherMatch redex check.  eitherInl value → app(left, value);
eitherInr value → app(right, value). -/
def Term.cd_eitherMatch_redex
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (developedScrutinee : Term context (Ty.either leftType rightType))
    (developedLeft : Term context (Ty.arrow leftType resultType))
    (developedRight : Term context (Ty.arrow rightType resultType)) :
    Term context resultType :=
  match h_raw : Term.toRaw developedScrutinee with
  | RawTerm.eitherInl _ =>
      let value :=
        Term.value_of_eitherInl_general developedScrutinee rfl h_raw
      Term.app developedLeft value
  | RawTerm.eitherInr _ =>
      let value :=
        Term.value_of_eitherInr_general developedScrutinee rfl h_raw
      Term.app developedRight value
  | RawTerm.var _ =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.unit =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.lam _ =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.app _ _ =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.pair _ _ =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.fst _ =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.snd _ =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.boolTrue =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.boolFalse =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.boolElim _ _ _ =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.natZero =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.natSucc _ =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.natElim _ _ _ =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.natRec _ _ _ =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.listNil =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.listCons _ _ =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.listElim _ _ _ =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.optionNone =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.optionSome _ =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.optionMatch _ _ _ =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.eitherMatch _ _ _ =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.refl _ =>
      Term.eitherMatch developedScrutinee developedLeft developedRight
  | RawTerm.idJ _ _ =>
      Term.eitherMatch developedScrutinee developedLeft developedRight

end LeanFX.Syntax
