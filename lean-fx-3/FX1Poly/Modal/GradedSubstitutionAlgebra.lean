import FX1Poly.Modal.UsageDiscipline

/-! # FX1Poly/Modal/GradedSubstitutionAlgebra — the parallel-substitution σ-algebra

The orthogonal-composition thesis reduces graded strong normalization to the TYPE dimension's
STLC strong normalization (`HasSimpleType → SN`, then the trivial `HasUsage.erase` transfer).  That
Tait argument's binder case (the abstraction lemma) needs a substitution that goes under λ — which in
de Bruijn form means a *parallel* substitution whose `lift` composes correctly.  This file builds
that σ-algebra for `GradedLambda`.

Why a renaming sublayer.  The kernel's single substitution `GradedLambda.substAt` carries the shift
`GradedLambda.shift 0` under each binder, and `(shift 0)` iterated `n` times is NOT `shift n` (e.g.
`(shift 0)^2 (var 1) = var 3` but `shift 2 (var 1) = var 1`).  So the index bookkeeping of a direct
substitution-swap is painful.  Factoring through a renaming layer (`renameTerm` over `Nat → Nat`)
makes `liftRenaming`/`liftSubstitution` compose *definitionally*, and the four classic fusion laws
(rename∘rename, subst∘rename, rename∘subst, subst∘subst) drop out by structural induction.

  * `IndexRenaming` / `TermSubstitution` — de Bruijn renamings (`Nat → Nat`) and parallel
    substitutions (`Nat → GradedLambda`).
  * `liftRenaming` / `liftSubstitution` — push a renaming / substitution under one binder.
  * `GradedLambda.renameTerm` / `GradedLambda.applySubstitution` — apply them to a term.
  * `renameTerm_congr` / `applySubstitution_congr` — pointwise-agreeing renamings/substitutions act
    identically (the funext-free congruences).
  * `renameTerm_renameTerm` / `applySubstitution_renameTerm` / `renameTerm_applySubstitution` /
    `applySubstitution_applySubstitution` — the four σ-monoid fusion laws.
  * `applySubstitution_id` — the identity substitution acts as the identity (the σ-monoid unit; the
    base case of the fundamental theorem's identity environment).

## Zero-axiom verification

Funext-free by construction: renamings/substitutions are `Nat → _` functions, but EVERY lemma's
conclusion is a TERM equation, and the only place a function-equality would be tempting (relating two
`lift`ed renamings/substitutions in a binder case) is discharged by the pointwise congruence
(`renameTerm_congr` / `applySubstitution_congr`) fed an inline `intro index; cases index` proof —
never `funext`/`Quot.sound`.  `liftRenaming`/`liftSubstitution` match on `Nat` (full 0 / n+1
enumeration, propext-clean); `renameTerm`/`applySubstitution` recurse structurally on the 3-ctor
`GradedLambda` (propext-clean).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- A de Bruijn index renaming. -/
abbrev IndexRenaming : Type := Nat → Nat

/-- A parallel substitution (each free index mapped to a term). -/
abbrev TermSubstitution : Type := Nat → GradedLambda

/-- Shift every index up by one (the renaming that goes under a binder's fresh variable). -/
def incrementIndex : IndexRenaming := fun index => index + 1

/-- Lift a renaming under a binder: index `0` stays, the rest are renamed then bumped. -/
def liftRenaming (baseRenaming : IndexRenaming) : IndexRenaming :=
  fun index =>
    match index with
    | 0 => 0
    | next + 1 => baseRenaming next + 1

/-- Apply a renaming to a term (binders lift the renaming). -/
def GradedLambda.renameTerm (baseRenaming : IndexRenaming) : GradedLambda → GradedLambda
  | .var index => .var (baseRenaming index)
  | .lam body => .lam (GradedLambda.renameTerm (liftRenaming baseRenaming) body)
  | .app function argument =>
      .app (GradedLambda.renameTerm baseRenaming function) (GradedLambda.renameTerm baseRenaming argument)

/-- Lift a substitution under a binder: index `0` becomes `var 0`, the rest are substituted then
shifted up by one (via the renaming sublayer). -/
def liftSubstitution (substitution : TermSubstitution) : TermSubstitution :=
  fun index =>
    match index with
    | 0 => GradedLambda.var 0
    | next + 1 => GradedLambda.renameTerm incrementIndex (substitution next)

/-- Apply a parallel substitution to a term (binders lift the substitution). -/
def GradedLambda.applySubstitution (substitution : TermSubstitution) : GradedLambda → GradedLambda
  | .var index => substitution index
  | .lam body => .lam (GradedLambda.applySubstitution (liftSubstitution substitution) body)
  | .app function argument =>
      .app (GradedLambda.applySubstitution substitution function)
        (GradedLambda.applySubstitution substitution argument)

/-- **Renaming congruence**: pointwise-agreeing renamings act identically (funext-free). -/
theorem GradedLambda.renameTerm_congr (term : GradedLambda) :
    ∀ (firstRenaming secondRenaming : IndexRenaming),
      (∀ index, firstRenaming index = secondRenaming index) →
      GradedLambda.renameTerm firstRenaming term = GradedLambda.renameTerm secondRenaming term := by
  induction term with
  | var index =>
      intro firstRenaming secondRenaming agree
      show GradedLambda.var (firstRenaming index) = GradedLambda.var (secondRenaming index)
      rw [agree index]
  | lam body bodyIH =>
      intro firstRenaming secondRenaming agree
      have agreeLifted : ∀ index, liftRenaming firstRenaming index = liftRenaming secondRenaming index := by
        intro index
        cases index with
        | zero => rfl
        | succ next => show firstRenaming next + 1 = secondRenaming next + 1; rw [agree next]
      exact congrArg GradedLambda.lam
        (bodyIH (liftRenaming firstRenaming) (liftRenaming secondRenaming) agreeLifted)
  | app function argument functionIH argumentIH =>
      intro firstRenaming secondRenaming agree
      show GradedLambda.app _ _ = GradedLambda.app _ _
      rw [functionIH firstRenaming secondRenaming agree, argumentIH firstRenaming secondRenaming agree]

/-- **Substitution congruence**: pointwise-agreeing substitutions act identically (funext-free). -/
theorem GradedLambda.applySubstitution_congr (term : GradedLambda) :
    ∀ (firstSubstitution secondSubstitution : TermSubstitution),
      (∀ index, firstSubstitution index = secondSubstitution index) →
      GradedLambda.applySubstitution firstSubstitution term
        = GradedLambda.applySubstitution secondSubstitution term := by
  induction term with
  | var index =>
      intro firstSubstitution secondSubstitution agree
      exact agree index
  | lam body bodyIH =>
      intro firstSubstitution secondSubstitution agree
      have agreeLifted : ∀ index,
          liftSubstitution firstSubstitution index = liftSubstitution secondSubstitution index := by
        intro index
        cases index with
        | zero => rfl
        | succ next =>
            show GradedLambda.renameTerm incrementIndex (firstSubstitution next)
              = GradedLambda.renameTerm incrementIndex (secondSubstitution next)
            rw [agree next]
      exact congrArg GradedLambda.lam
        (bodyIH (liftSubstitution firstSubstitution) (liftSubstitution secondSubstitution) agreeLifted)
  | app function argument functionIH argumentIH =>
      intro firstSubstitution secondSubstitution agree
      show GradedLambda.app _ _ = GradedLambda.app _ _
      rw [functionIH firstSubstitution secondSubstitution agree,
        argumentIH firstSubstitution secondSubstitution agree]

/-- **R∘R fusion**: composing two renamings. -/
theorem GradedLambda.renameTerm_renameTerm (term : GradedLambda) :
    ∀ (outerRenaming innerRenaming : IndexRenaming),
      GradedLambda.renameTerm outerRenaming (GradedLambda.renameTerm innerRenaming term)
        = GradedLambda.renameTerm (fun index => outerRenaming (innerRenaming index)) term := by
  induction term with
  | var index => intro _ _; rfl
  | lam body bodyIH =>
      intro outerRenaming innerRenaming
      show GradedLambda.lam _ = GradedLambda.lam _
      rw [bodyIH (liftRenaming outerRenaming) (liftRenaming innerRenaming)]
      apply congrArg GradedLambda.lam
      apply GradedLambda.renameTerm_congr
      intro index
      cases index with
      | zero => rfl
      | succ _ => rfl
  | app function argument functionIH argumentIH =>
      intro outerRenaming innerRenaming
      show GradedLambda.app _ _ = GradedLambda.app _ _
      rw [functionIH outerRenaming innerRenaming, argumentIH outerRenaming innerRenaming]

/-- **S∘R fusion**: a substitution after a renaming is a substitution. -/
theorem GradedLambda.applySubstitution_renameTerm (term : GradedLambda) :
    ∀ (afterSubstitution : TermSubstitution) (beforeRenaming : IndexRenaming),
      GradedLambda.applySubstitution afterSubstitution (GradedLambda.renameTerm beforeRenaming term)
        = GradedLambda.applySubstitution (fun index => afterSubstitution (beforeRenaming index)) term := by
  induction term with
  | var index => intro _ _; rfl
  | lam body bodyIH =>
      intro afterSubstitution beforeRenaming
      show GradedLambda.lam _ = GradedLambda.lam _
      rw [bodyIH (liftSubstitution afterSubstitution) (liftRenaming beforeRenaming)]
      apply congrArg GradedLambda.lam
      apply GradedLambda.applySubstitution_congr
      intro index
      cases index with
      | zero => rfl
      | succ _ => rfl
  | app function argument functionIH argumentIH =>
      intro afterSubstitution beforeRenaming
      show GradedLambda.app _ _ = GradedLambda.app _ _
      rw [functionIH afterSubstitution beforeRenaming, argumentIH afterSubstitution beforeRenaming]

/-- **R∘S fusion**: a renaming after a substitution is a substitution. -/
theorem GradedLambda.renameTerm_applySubstitution (term : GradedLambda) :
    ∀ (afterRenaming : IndexRenaming) (beforeSubstitution : TermSubstitution),
      GradedLambda.renameTerm afterRenaming (GradedLambda.applySubstitution beforeSubstitution term)
        = GradedLambda.applySubstitution
            (fun index => GradedLambda.renameTerm afterRenaming (beforeSubstitution index)) term := by
  induction term with
  | var index => intro _ _; rfl
  | lam body bodyIH =>
      intro afterRenaming beforeSubstitution
      show GradedLambda.lam _ = GradedLambda.lam _
      rw [bodyIH (liftRenaming afterRenaming) (liftSubstitution beforeSubstitution)]
      apply congrArg GradedLambda.lam
      apply GradedLambda.applySubstitution_congr
      intro index
      cases index with
      | zero => rfl
      | succ next =>
          show GradedLambda.renameTerm (liftRenaming afterRenaming)
              (GradedLambda.renameTerm incrementIndex (beforeSubstitution next))
            = GradedLambda.renameTerm incrementIndex
              (GradedLambda.renameTerm afterRenaming (beforeSubstitution next))
          rw [GradedLambda.renameTerm_renameTerm, GradedLambda.renameTerm_renameTerm]
          apply GradedLambda.renameTerm_congr
          intro _
          rfl
  | app function argument functionIH argumentIH =>
      intro afterRenaming beforeSubstitution
      show GradedLambda.app _ _ = GradedLambda.app _ _
      rw [functionIH afterRenaming beforeSubstitution, argumentIH afterRenaming beforeSubstitution]

/-- **S∘S fusion**: composing two substitutions (the σ-monoid multiplication). -/
theorem GradedLambda.applySubstitution_applySubstitution (term : GradedLambda) :
    ∀ (outerSubstitution innerSubstitution : TermSubstitution),
      GradedLambda.applySubstitution outerSubstitution
          (GradedLambda.applySubstitution innerSubstitution term)
        = GradedLambda.applySubstitution
            (fun index => GradedLambda.applySubstitution outerSubstitution (innerSubstitution index)) term := by
  induction term with
  | var index => intro _ _; rfl
  | lam body bodyIH =>
      intro outerSubstitution innerSubstitution
      show GradedLambda.lam _ = GradedLambda.lam _
      rw [bodyIH (liftSubstitution outerSubstitution) (liftSubstitution innerSubstitution)]
      apply congrArg GradedLambda.lam
      apply GradedLambda.applySubstitution_congr
      intro index
      cases index with
      | zero => rfl
      | succ next =>
          show GradedLambda.applySubstitution (liftSubstitution outerSubstitution)
              (GradedLambda.renameTerm incrementIndex (innerSubstitution next))
            = GradedLambda.renameTerm incrementIndex
              (GradedLambda.applySubstitution outerSubstitution (innerSubstitution next))
          rw [GradedLambda.applySubstitution_renameTerm, GradedLambda.renameTerm_applySubstitution]
          apply GradedLambda.applySubstitution_congr
          intro _
          rfl
  | app function argument functionIH argumentIH =>
      intro outerSubstitution innerSubstitution
      show GradedLambda.app _ _ = GradedLambda.app _ _
      rw [functionIH outerSubstitution innerSubstitution, argumentIH outerSubstitution innerSubstitution]

/-- **Identity substitution**: substituting each variable by itself is the identity (the σ-monoid
unit; the base case of the fundamental theorem's identity environment). -/
theorem GradedLambda.applySubstitution_id (term : GradedLambda) :
    GradedLambda.applySubstitution (fun index => GradedLambda.var index) term = term := by
  induction term with
  | var index => rfl
  | lam body bodyIH =>
      show GradedLambda.lam (GradedLambda.applySubstitution
        (liftSubstitution (fun index => GradedLambda.var index)) body) = GradedLambda.lam body
      apply congrArg GradedLambda.lam
      have rewriteLift : GradedLambda.applySubstitution
            (liftSubstitution (fun index => GradedLambda.var index)) body
          = GradedLambda.applySubstitution (fun index => GradedLambda.var index) body := by
        apply GradedLambda.applySubstitution_congr
        intro index
        cases index with
        | zero => rfl
        | succ _ => rfl
      rw [rewriteLift, bodyIH]
  | app function argument functionIH argumentIH =>
      show GradedLambda.app _ _ = GradedLambda.app function argument
      rw [functionIH, argumentIH]

end FX1Poly.Modal
