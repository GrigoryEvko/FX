import LeanFX.Syntax.ToRaw
import LeanFX.Syntax.TermSubst

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Term.toRaw` commute lemmas (substitution-side).

The cast and rename commute lemmas (`Term.toRaw_cast`,
`Term.toRaw_rename`) live in `TypedTerm.lean` so they are reachable
from inside `TermSubst.Commute.*` without an import cycle.  The
lemmas below — `Term.toRaw_subst` and the bridge specialisations —
depend on `TermSubst` and stay here.

Used by:
  * `Step.par.toRawBridge` — translates typed parallel-step into raw.
  * `Term.toRaw_cd` — translates typed `Term.cd` into raw `RawTerm.cd`. -/

/-! ### Substitution-bridge consistency.

A `TermSubst σt` carries term-level data that must be related to
the raw substitution `σ.forRaw` for the bridge to commute
cleanly.  The relation is: at every position `i`, the raw
projection of the term-level data equals `σ.forRaw i`.

This is automatically true for substitutions that come from
type-respecting constructions (e.g., `TermSubst.singleton` when
the Ty-level component is properly aligned with the term-level
data).  When the refl-rule's rawTerm uses the raw component, the
bridge requires this consistency.

We package the consistency as a proposition `TermSubst.RawConsistent`
and add it as a hypothesis to `Term.toRaw_subst`. -/

/-- Consistency of a `TermSubst` with its raw substitution view:
the raw projection of each term-level substituent equals the
raw substitution `σ.forRaw` at the same position. -/
def TermSubst.RawConsistent {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {typeSubst : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx typeSubst) : Prop :=
  ∀ position, Term.toRaw (termSubst position) = typeSubst.forRaw position

/-- `TermSubst.lift` preserves raw-consistency: if `σt` is consistent
with `σ.forRaw`, then the lifted `σt.lift T` is consistent with
`σ.lift.forRaw`. -/
theorem TermSubst.lift_RawConsistent {mode : Mode}
    {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {typeSubst : Subst level sourceScope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx typeSubst}
    (consistency : TermSubst.RawConsistent termSubst) (newType : Ty level sourceScope) :
    TermSubst.RawConsistent (TermSubst.lift termSubst newType) := by
  intro position
  match position with
  | ⟨0, _⟩ =>
      simp only [TermSubst.lift]
      rw [Term.toRaw_cast]
      rfl
  | ⟨k + 1, h⟩ =>
      simp only [TermSubst.lift]
      rw [Term.toRaw_cast]
      show Term.toRaw (Term.rename _ (termSubst ⟨k, _⟩)) = _
      rw [Term.toRaw_rename]
      exact congrArg (fun rt => RawTerm.rename rt Renaming.weaken)
        (consistency ⟨k, _⟩)

/-- Substitution commutes with `toRaw` when the term substitution is
raw-consistent.  Structural induction on the term; uses
`lift_RawConsistent` for the binder cases and `toRaw_cast` to peel
off Ty-level alignment casts in the eliminator cases. -/
theorem Term.toRaw_subst {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {typeSubst : Subst level sourceScope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx typeSubst}
    (consistency : TermSubst.RawConsistent termSubst) :
    {T : Ty level sourceScope} → (t : Term sourceCtx T) →
      Term.toRaw (Term.subst termSubst t) =
        (Term.toRaw t).subst typeSubst.forRaw
  | _, .var i => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact consistency i
  | _, .unit => rfl
  | _, .lam body => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      rw [Term.toRaw_cast]
      exact congrArg RawTerm.lam
        (Term.toRaw_subst (TermSubst.lift_RawConsistent consistency _) body)
  | _, .app function argument => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgTwo (function := RawTerm.app)
        (Term.toRaw_subst consistency function)
        (Term.toRaw_subst consistency argument)
  | _, .lamPi body => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArg RawTerm.lam
        (Term.toRaw_subst (TermSubst.lift_RawConsistent consistency _) body)
  | _, .appPi _ function argument => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      rw [Term.toRaw_cast, Term.toRaw_cast]
      exact congrArgTwo (function := RawTerm.app)
        (Term.toRaw_subst consistency function)
        (Term.toRaw_subst consistency argument)
  | _, .pair firstVal secondVal => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      have secondEq : Term.toRaw (Term.subst termSubst secondVal) =
          (Term.toRaw secondVal).subst typeSubst.forRaw :=
        Term.toRaw_subst consistency secondVal
      exact congrArgTwo (function := RawTerm.pair)
        (Term.toRaw_subst consistency firstVal)
        (by rw [Term.toRaw_cast]; exact secondEq)
  | _, .fst pairTerm => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArg RawTerm.fst
        (Term.toRaw_subst consistency pairTerm)
  | _, .snd pairTerm _ => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      rw [Term.toRaw_cast, Term.toRaw_cast]
      exact congrArg RawTerm.snd
        (Term.toRaw_subst consistency pairTerm)
  | _, .boolTrue => rfl
  | _, .boolFalse => rfl
  | _, .boolElim scrutinee thenBranch elseBranch => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgThree (function := RawTerm.boolElim)
        (Term.toRaw_subst consistency scrutinee)
        (Term.toRaw_subst consistency thenBranch)
        (Term.toRaw_subst consistency elseBranch)
  | _, .natZero => rfl
  | _, .natSucc predecessor => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArg RawTerm.natSucc
        (Term.toRaw_subst consistency predecessor)
  | _, .natElim scrutinee zeroBranch succBranch => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgThree (function := RawTerm.natElim)
        (Term.toRaw_subst consistency scrutinee)
        (Term.toRaw_subst consistency zeroBranch)
        (Term.toRaw_subst consistency succBranch)
  | _, .natRec scrutinee zeroBranch succBranch => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgThree (function := RawTerm.natRec)
        (Term.toRaw_subst consistency scrutinee)
        (Term.toRaw_subst consistency zeroBranch)
        (Term.toRaw_subst consistency succBranch)
  | _, .listNil => rfl
  | _, .listCons head tail => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgTwo (function := RawTerm.listCons)
        (Term.toRaw_subst consistency head)
        (Term.toRaw_subst consistency tail)
  | _, .listElim scrutinee nilBranch consBranch => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgThree (function := RawTerm.listElim)
        (Term.toRaw_subst consistency scrutinee)
        (Term.toRaw_subst consistency nilBranch)
        (Term.toRaw_subst consistency consBranch)
  | _, .optionNone => rfl
  | _, .optionSome value => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArg RawTerm.optionSome
        (Term.toRaw_subst consistency value)
  | _, .optionMatch scrutinee noneBranch someBranch => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgThree (function := RawTerm.optionMatch)
        (Term.toRaw_subst consistency scrutinee)
        (Term.toRaw_subst consistency noneBranch)
        (Term.toRaw_subst consistency someBranch)
  | _, .eitherInl value => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArg RawTerm.eitherInl
        (Term.toRaw_subst consistency value)
  | _, .eitherInr value => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArg RawTerm.eitherInr
        (Term.toRaw_subst consistency value)
  | _, .eitherMatch scrutinee leftBranch rightBranch => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgThree (function := RawTerm.eitherMatch)
        (Term.toRaw_subst consistency scrutinee)
        (Term.toRaw_subst consistency leftBranch)
        (Term.toRaw_subst consistency rightBranch)
  | _, .refl _ => rfl
  | _, .idJ baseCase witness => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgTwo (function := RawTerm.idJ)
        (Term.toRaw_subst consistency baseCase)
        (Term.toRaw_subst consistency witness)

/-! ### Specialization: `subst0` commute under raw-consistent singleton.

For `Term.subst0`, the typed substitution is `TermSubst.singleton arg`
and the raw side wants `RawTermSubst.singleton (toRaw arg)`.  These
agree pointwise iff arg's raw projection matches the singleton's
position-0 substituent — captured by `RawConsistent`. -/

/-- Subst0 commutes with toRaw when the typed singleton substitution
is raw-consistent (i.e., its raw side equals `RawTermSubst.singleton
(toRaw arg)`).  This holds whenever the typed kernel uses the
canonical alignment between TermSubst.singleton and Subst.singleton
on the raw component. -/
theorem Term.toRaw_subst0_of_consistent {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {T_arg : Ty level scope} {T_body : Ty level (scope + 1)}
    (body : Term (context.cons T_arg) T_body) (argument : Term context T_arg)
    (consistency :
      TermSubst.RawConsistent (TermSubst.singleton argument)) :
    Term.toRaw (Term.subst0 body argument) =
      RawTerm.subst (Term.toRaw body) (Subst.singleton T_arg).forRaw := by
  unfold Term.subst0
  exact Term.toRaw_subst consistency body

/-! ### `TermSubst.termSingleton` is raw-consistent by construction.

The term-bearing single substitution `TermSubst.termSingleton arg`
uses the joint substitution `Subst.termSingleton T_arg (Term.toRaw
arg)`, whose `forRaw` is `RawTermSubst.singleton (Term.toRaw arg)`.
At position 0 the raw image is `Term.toRaw arg` (definitionally);
at successor positions both sides are `RawTerm.var ⟨k, _⟩`.  Hence
raw-consistency holds without hypothesis, and the bridge for
`Term.subst0_term` is unconditional.

This is the key payoff of introducing `Subst.termSingleton`: the
typed→raw forward bridge for β-reduction (where the substituted
argument's raw projection must reach identity-type witnesses inside
the body) holds by definition. -/

/-- The term-bearing single substitution is automatically
raw-consistent.  At position 0, `Term.toRaw arg` matches
`(Subst.termSingleton T_arg (Term.toRaw arg)).forRaw ⟨0, _⟩` which
unfolds to `RawTermSubst.singleton (Term.toRaw arg) ⟨0, _⟩ =
Term.toRaw arg`.  At successor positions, both sides decrement to
`RawTerm.var ⟨k, _⟩`.  All four matches are `rfl` modulo the
`Term.toRaw_cast` rewrite that strips the `Ty.weaken_subst_termSingleton`
alignment cast. -/
theorem TermSubst.termSingleton_RawConsistent {mode : Mode}
    {level scope : Nat} {context : Ctx mode level scope}
    {T_arg : Ty level scope} (argument : Term context T_arg) :
    TermSubst.RawConsistent (TermSubst.termSingleton argument) := by
  intro position
  match position with
  | ⟨0, _⟩ =>
      simp only [TermSubst.termSingleton]
      rw [Term.toRaw_cast]
      rfl
  | ⟨k + 1, h⟩ =>
      simp only [TermSubst.termSingleton]
      rw [Term.toRaw_cast]
      rfl

/-- **Unconditional β-bridge.**  `Term.subst0_term body arg` —
the term-bearing single substitution variant — commutes with
`Term.toRaw` *without* a `RawConsistent` hypothesis: the consistency
is inhabited by `TermSubst.termSingleton_RawConsistent`.

The result equals `RawTerm.subst (Term.toRaw body)
(RawTermSubst.singleton (Term.toRaw arg))`, which is exactly
`RawTerm.subst0 (Term.toRaw body) (Term.toRaw arg)` — i.e., the raw
β-reduct.  This is the lemma that closes the typed→raw forward
bridge for `Step.par.betaApp` / `Step.par.betaAppPi`. -/
theorem Term.toRaw_subst0_term {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {T_arg : Ty level scope} {T_body : Ty level (scope + 1)}
    (body : Term (context.cons T_arg) T_body) (argument : Term context T_arg) :
    Term.toRaw (Term.subst0_term body argument) =
      RawTerm.subst (Term.toRaw body)
        (RawTermSubst.singleton (Term.toRaw argument)) := by
  unfold Term.subst0_term
  show Term.toRaw (Term.subst (TermSubst.termSingleton argument) body) =
       RawTerm.subst (Term.toRaw body)
         (RawTermSubst.singleton (Term.toRaw argument))
  have hConsistent := TermSubst.termSingleton_RawConsistent argument
  have hBridge := Term.toRaw_subst hConsistent body
  show Term.toRaw (Term.subst (TermSubst.termSingleton argument) body) =
       RawTerm.subst (Term.toRaw body)
         (RawTermSubst.singleton (Term.toRaw argument))
  exact hBridge

/-- Specialization of `Term.toRaw_subst0_term` to the raw `subst0`
form, useful for the bridge proofs of β-reduction rules. -/
theorem Term.toRaw_subst0_term_raw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {T_arg : Ty level scope} {T_body : Ty level (scope + 1)}
    (body : Term (context.cons T_arg) T_body) (argument : Term context T_arg) :
    Term.toRaw (Term.subst0_term body argument) =
      RawTerm.subst0 (Term.toRaw body) (Term.toRaw argument) :=
  Term.toRaw_subst0_term body argument

/-! ## Phase C `subst0_term`-substitution interaction.

Same as `Term.subst0_subst_HEq` (in `TermSubst/Commute/Subst0Subst.lean`)
but for `Term.subst0_term`.  The headline lemma `Term.subst0_term_subst_HEq`
needs `Term.toRaw_subst` to align the inner `Subst.termSingleton`'s
rawArg field — that's why it lives here rather than next to its sister,
which sits below `ToRawCommute` in the dependency DAG. -/

/-- Subst.equiv between the LHS-shape and RHS-shape outer Substs of
`Term.subst0_term_subst_HEq`.  Threads `Term.toRaw_subst` to align the
inner `Subst.termSingleton`'s rawArg field — this is where the
`RawConsistent` hypothesis is consumed. -/
private theorem Subst.termSingleton_compose_equiv_lift_compose_termSingleton_subst
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {targetContext : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    {termSubstitution : TermSubst sourceContext targetContext typeSubstitution}
    (consistency : TermSubst.RawConsistent termSubstitution)
    (argumentType : Ty level sourceScope)
    (argumentTerm : Term sourceContext argumentType) :
    Subst.equiv
      (Subst.compose
        (Subst.termSingleton argumentType (Term.toRaw argumentTerm))
        typeSubstitution)
      (Subst.compose typeSubstitution.lift
        (Subst.termSingleton (argumentType.subst typeSubstitution)
          (Term.toRaw (Term.subst termSubstitution argumentTerm)))) := by
  have rawArgEq :
      Term.toRaw (Term.subst termSubstitution argumentTerm)
        = (Term.toRaw argumentTerm).subst typeSubstitution.forRaw :=
    Term.toRaw_subst consistency argumentTerm
  rw [rawArgEq]
  exact Subst.termSingleton_compose_equiv_lift_compose_termSingleton
    argumentType (Term.toRaw argumentTerm) typeSubstitution

/-- The Phase C headline: substituting after a `subst0_term` agrees, up
to HEq, with substituting under the lifted outer substitution then
applying `subst0_term` with the substituted argument.

This is the term-bearing analog of `Term.subst0_subst_HEq`.  Required
hypothesis: the outer term substitution is `RawConsistent` — i.e., its
forRaw projection matches `Term.toRaw` on the underlying terms.  Every
Phase C call site (`Step.par.subst_compatible.betaApp` and downstream)
satisfies this. -/
theorem Term.subst0_term_subst_HEq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceContext : Ctx mode level sourceScope}
    {targetContext : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    {termSubstitution : TermSubst sourceContext targetContext typeSubstitution}
    (consistency : TermSubst.RawConsistent termSubstitution)
    {argumentType : Ty level sourceScope}
    {bodyType : Ty level (sourceScope + 1)}
    (bodyTerm : Term (sourceContext.cons argumentType) bodyType)
    (argumentTerm : Term sourceContext argumentType) :
    HEq
      (Term.subst termSubstitution (Term.subst0_term bodyTerm argumentTerm))
      (Term.subst0_term
        (Term.subst (TermSubst.lift termSubstitution argumentType) bodyTerm)
        (Term.subst termSubstitution argumentTerm)) := by
  show HEq
      (Term.subst termSubstitution
        (Term.subst (TermSubst.termSingleton argumentTerm) bodyTerm))
      (Term.subst (TermSubst.termSingleton (Term.subst termSubstitution argumentTerm))
        (Term.subst (TermSubst.lift termSubstitution argumentType) bodyTerm))
  apply HEq.trans
    (Term.subst_compose_HEq (TermSubst.termSingleton argumentTerm)
      termSubstitution bodyTerm)
  apply HEq.trans
    (Term.subst_HEq_pointwise rfl
      (TermSubst.compose (TermSubst.termSingleton argumentTerm) termSubstitution)
      (TermSubst.compose
        (TermSubst.lift termSubstitution argumentType)
        (TermSubst.termSingleton (Term.subst termSubstitution argumentTerm)))
      (Subst.termSingleton_compose_equiv_lift_compose_termSingleton_subst
        consistency argumentType argumentTerm)
      (TermSubst.termSingleton_compose_pointwise termSubstitution argumentTerm)
      bodyTerm)
  exact HEq.symm
    (Term.subst_compose_HEq
      (TermSubst.lift termSubstitution argumentType)
      (TermSubst.termSingleton (Term.subst termSubstitution argumentTerm))
      bodyTerm)

end LeanFX.Syntax
