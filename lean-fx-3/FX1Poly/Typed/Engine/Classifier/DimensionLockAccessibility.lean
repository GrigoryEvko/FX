import FX1Poly.Typed.Engine.Classifier.TypingContext

/-! # FX1Poly/Typed/DimensionLockAccessibility — the Fitch variable-accessibility discipline for the affine lock

The FitchTT TM/VAR variable-accessibility rule (MTT Fig 2, Gratzer-Kavvos-Nuyts-Birkedal 2021) specialized to
FX's single UNPOINTED AFFINE dimension lock (`TypingContext.lockCons`, mode-11/12, structure-class affine).

## The discipline (mode-axis-free for the affine fragment)

MTT's rule: a variable `x : (nu | A)` is usable at the ambient (fibrant) modality iff there is a 2-cell
`nu => locks(Gamma_after_x)`, where `locks(Gamma)` composes the lock modalities of the suffix after `x`.  FX's
`lockCons` is MTT's CX/EXTEND MODAL VARIABLE `i :^mu_affine Interval` — NOT a CX/LOCK `Gamma / mu` — so it is
transparent to the suffix-lock exactly like a plain `cons`: `locks(empty) = 1`, `locks(cons) = locks(rest)`,
`locks(lockCons) = locks(rest)` (Fig 2: `locks(Gamma, x :^mu A) = locks(Gamma)`).  The modality `mu_affine` lives
on the bound variable's ANNOTATION, not on the suffix-lock.

For FX's bridge the only modal annotation is the affine `mu_affine` (mode-12 UNPOINTED: NO 2-cell `1 => mu_affine`
and NO 2-cell `mu_affine => 1`).  Because the suffix-lock is always `1` (CX/EXTEND adds nothing), the general
2-cell check collapses to a purely structural test on the variable's OWN binder — NO `ModeGraph`/`ModalityPath`
is needed yet (that generalization is the later fib-3 wiring):

  * an ORDINARY variable (own binder `cons`, modality `1`) is fibrantly usable iff `1 => locks(suffix) = 1`
    exists — the identity 2-cell — so it is ALWAYS fibrantly usable, regardless of any `lockCons` between its
    binding and the use point (those locks are transparent);
  * the DIMENSION variable (own binder `lockCons`, modality `mu_affine`) is NEVER fibrantly usable — at its own
    use the suffix is empty (`locks = 1`) so fibrant use would need `mu_affine => 1`, which the unpointed
    multiplier does not provide.  It IS usable at the dimensional position (the identity `mu_affine => mu_affine`).

`isFibrantlyAccessibleAt context index` decides exactly this: `true` iff the binding `index` resolves to is a
plain `cons` (an ordinary variable), `false` iff it resolves to a `lockCons` (the locked dimension itself).

## Why this is the subject-reduction fix (count-free, beta-stable)

The previous affine side condition was the syntactic occurrence count `gradedBinderChecks .one body`
(`occurrenceCountAt body 0 <= 1`), which is NOT beta-stable: `pathLam ((fn x : Interval => pair x x) i)` has
count 1 yet beta-reduces to `pathLam (pair i i)` with count 2, breaking subject reduction.  The Fitch discipline
replaces the count with a STRUCTURAL accessibility test on the CONTEXT: under `Gamma.lockCons Interval`, the
dimension `var 0` is not fibrantly accessible (`dimensionIsNotFibrantlyAccessible`), so `pair (var 0) (var 0)`
— a fibrant constructor applied to the locked dimension — does not type at all.  There is no count to break, so
`pathLam` subject reduction is structural.

This file ships the PREDICATE (the data of the discipline).  Wiring it into the variable typing rule (so every
bare fibrant variable use discharges it, a no-op `true` in any lock-free context) is the next increment.

## Zero-axiom verification

A `Bool`-valued structural recursion over the telescope with the `Fin` index destructured by the propext-free
`⟨0, _⟩` / `⟨position + 1, _⟩` structure match (the same recipe as `TypingContext.lookup`), plus `rfl`-closed
unfolders.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Tier0.Syntax

/-- Decide whether the de Bruijn variable `index` may be used as a FIBRANT value in `context` under the Fitch
affine-lock discipline: `true` iff the binding `index` resolves to is a plain `cons` (an ordinary variable),
`false` iff it resolves to a `lockCons` (the locked dimension itself).  The dimension bound by `lockCons` is
never fibrantly accessible (the unpointed affine multiplier has no 2-cell `mu_affine => 1`); ambient variables
behind a `lockCons` STAY accessible — the lock is a CX/EXTEND modal variable, transparent to the suffix-lock
(`locks(Gamma, x :^mu A) = locks(Gamma)`).  The mode-axis-free specialization of MTT's TM/VAR 2-cell check for
the single affine lock. -/
def TypingContext.isFibrantlyAccessibleAt {profile : PolyProfile} :
    {scope : Nat} → TypingContext profile scope → Fin scope → Bool
  | _, .empty, emptyIndex =>
      absurd emptyIndex.isLt (Nat.not_lt_zero emptyIndex.val)
  | _, .cons _ _, ⟨0, _⟩ => true
  | _, .lockCons _ _, ⟨0, _⟩ => false
  | _, .cons restContext _, ⟨position + 1, isLtSucc⟩ =>
      restContext.isFibrantlyAccessibleAt ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩
  | _, .lockCons restContext _, ⟨position + 1, isLtSucc⟩ =>
      restContext.isFibrantlyAccessibleAt ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩

/-- Unfolder: the newest binding of a `cons` telescope is fibrantly accessible. -/
theorem isFibrantlyAccessibleAt_cons_zero {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (bindingType : RawTerm scope)
    (isLtZeroSucc : 0 < scope + 1) :
    (restContext.cons bindingType).isFibrantlyAccessibleAt ⟨0, isLtZeroSucc⟩ = true :=
  rfl

/-- Unfolder: the newest binding of a `lockCons` telescope — the locked dimension — is NOT fibrantly accessible. -/
theorem isFibrantlyAccessibleAt_lockCons_zero {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope)
    (isLtZeroSucc : 0 < scope + 1) :
    (restContext.lockCons dimensionType).isFibrantlyAccessibleAt ⟨0, isLtZeroSucc⟩ = false :=
  rfl

/-- Unfolder: accessibility of a deeper variable past a `cons` binding recurses into the prefix (a plain `cons`
adds no lock to the suffix). -/
theorem isFibrantlyAccessibleAt_cons_succ {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (bindingType : RawTerm scope)
    (position : Nat) (isLtSuccSucc : position + 1 < scope + 1) :
    (restContext.cons bindingType).isFibrantlyAccessibleAt ⟨position + 1, isLtSuccSucc⟩ =
      restContext.isFibrantlyAccessibleAt ⟨position, Nat.lt_of_succ_lt_succ isLtSuccSucc⟩ :=
  rfl

/-- Unfolder: accessibility of a deeper variable past a `lockCons` binding recurses into the prefix.  The
`lockCons` is MTT's CX/EXTEND modal variable `i :^mu_affine Interval` (`locks(Gamma, x :^mu A) = locks(Gamma)`,
Fig 2), so — exactly like a plain `cons` — it adds nothing to the suffix-lock of an AMBIENT variable behind it;
only the dimension's OWN binding (`lockCons_zero`) is locked.  Byte-identical to the `cons_succ` recursion. -/
theorem isFibrantlyAccessibleAt_lockCons_succ {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope)
    (position : Nat) (isLtSuccSucc : position + 1 < scope + 1) :
    (restContext.lockCons dimensionType).isFibrantlyAccessibleAt ⟨position + 1, isLtSuccSucc⟩ =
      restContext.isFibrantlyAccessibleAt ⟨position, Nat.lt_of_succ_lt_succ isLtSuccSucc⟩ :=
  rfl

/-- **★ The subject-reduction mechanism.**  The dimension bound by `lockCons` — `var 0` in the bridge body's
context — is NOT fibrantly accessible.  So a fibrant constructor applied to the dimension (the canonical
SR-breaker `pair (var 0) (var 0)`) cannot type once the variable rule discharges `isFibrantlyAccessibleAt`, and
the affine restriction is enforced STRUCTURALLY (by the context) rather than by a beta-fragile occurrence count.
This is the count-free, beta-stable replacement for `gradedBinderChecks .one`. -/
theorem dimensionIsNotFibrantlyAccessible {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope)
    (isLtZeroSucc : 0 < scope + 1) :
    (restContext.lockCons dimensionType).isFibrantlyAccessibleAt ⟨0, isLtZeroSucc⟩ = false :=
  rfl

/-! ## The lock-free fragment — conservativity backbone

Every context the kernel builds today is lock-free (the affine lock enters only through the re-presented
`pathLam` body, A1-2/#1789).  `isLockFreeContext` names that fragment, and `lockFreeImpliesFibrantlyAccessible`
shows the accessibility side condition is vacuously `true` on it: the Fitch discipline does NOT weaken the
typing relation anywhere a dimension lock is absent — it only bites under `lockCons`.  This is the lemma the
variable-rule flip discharges its lock-free construction sites against. -/

/-- Decide whether `context` is free of dimension locks: `true` iff no `lockCons` appears anywhere in the
telescope (a plain `cons` adds none).  Names the lock-free fragment over which the accessibility discipline
is conservative — the whole kernel today. -/
def TypingContext.isLockFreeContext {profile : PolyProfile} :
    {scope : Nat} → TypingContext profile scope → Bool
  | _, .empty => true
  | _, .cons restContext _bindingType => restContext.isLockFreeContext
  | _, .lockCons _restContext _dimensionType => false

/-- Unfolder: the empty context is lock-free. -/
theorem isLockFreeContext_empty {profile : PolyProfile} :
    (TypingContext.empty : TypingContext profile 0).isLockFreeContext = true :=
  rfl

/-- Unfolder: a `cons` is lock-free exactly when its prefix is (a plain binder adds no lock). -/
theorem isLockFreeContext_cons {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (bindingType : RawTerm scope) :
    (restContext.cons bindingType).isLockFreeContext = restContext.isLockFreeContext :=
  rfl

/-- Unfolder: a `lockCons` is never lock-free (it IS a lock). -/
theorem isLockFreeContext_lockCons {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope) :
    (restContext.lockCons dimensionType).isLockFreeContext = false :=
  rfl

/-- **★ Conservativity backbone.**  In a lock-free context EVERY variable is fibrantly accessible — the
accessibility side condition is vacuously `true` wherever no dimension lock appears.  So the Fitch discipline
does not weaken the typing relation on the lock-free fragment (which is the whole kernel today); it bites only
once `pathLam` introduces a `lockCons`.  Structural recursion on the telescope: the `cons` case splits the
index (newest binder accessible by `cons_zero`, deeper binders by the prefix IH), and the `lockCons` case is
impossible since a lock-free `lockCons` would be `false = true`. -/
theorem TypingContext.lockFreeImpliesFibrantlyAccessible {profile : PolyProfile} :
    {scope : Nat} → (context : TypingContext profile scope) →
      context.isLockFreeContext = true → (index : Fin scope) →
        context.isFibrantlyAccessibleAt index = true
  | _, .empty, _isLockFree, index => absurd index.isLt (Nat.not_lt_zero index.val)
  | _, .cons _restContext _bindingType, _isLockFree, ⟨0, _⟩ => rfl
  | _, .cons restContext _bindingType, isLockFree, ⟨position + 1, isLtSucc⟩ =>
      restContext.lockFreeImpliesFibrantlyAccessible isLockFree
        ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩
  | _, .lockCons restContext dimensionType, isLockFree, _index =>
      Bool.noConfusion ((isLockFreeContext_lockCons restContext dimensionType).symm.trans isLockFree)

/-- Accessibility transfers across a fresh `cons`: if the variable at `position` is fibrantly accessible in
`restContext`, then the shifted variable at `position + 1` is fibrantly accessible in
`restContext.cons bindingType` (a plain binder on top shadows nothing).  The cons-extension discharger the
variable rule's weakening leg consumes. -/
theorem fibrantlyAccessibleConsSucc {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (bindingType : RawTerm scope)
    (position : Nat) (isLtScope : position < scope)
    (accessible : restContext.isFibrantlyAccessibleAt ⟨position, isLtScope⟩ = true) :
    (restContext.cons bindingType).isFibrantlyAccessibleAt
        ⟨position + 1, Nat.succ_lt_succ isLtScope⟩ = true :=
  accessible

/-- Accessibility transfers across a fresh `lockCons` (the affine dimension lock): if the variable at `position`
is fibrantly accessible in `restContext`, then the shifted variable at `position + 1` is fibrantly accessible in
`restContext.lockCons dimensionType` — an AMBIENT variable stays accessible behind the lock (CX/EXTEND
transparency, `locks(Gamma, i :^mu A) = locks(Gamma)`).  The lock-extension discharger the variable rule's
weakening leg consumes for `weakenUnderLockBinding`; byte-identical to `fibrantlyAccessibleConsSucc` because
`lockCons_succ` recurses exactly like `cons_succ`. -/
theorem fibrantlyAccessibleLockConsSucc {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope)
    (position : Nat) (isLtScope : position < scope)
    (accessible : restContext.isFibrantlyAccessibleAt ⟨position, isLtScope⟩ = true) :
    (restContext.lockCons dimensionType).isFibrantlyAccessibleAt
        ⟨position + 1, Nat.succ_lt_succ isLtScope⟩ = true :=
  accessible

/-! ## Use-position modality — the fibrant/dimensional split (the SR mechanism's table field)

The decisive finding (verified against MATT Fig 3/6 + FX's `pathAppElimRule`): the dimension's DIMENSIONAL use
(`pathApp p i`, the bridge's core operation) and its FIBRANT use (`pair i i`, the canonical subject-reduction
breaker) go through the SAME generic obligation `HasTypeUnion ctx (var 0) Interval` — so a BLANKET var-arm
accessibility block conflates them (it would break pathApp, or fail to block `pair i i`).  The distinction is
the USE-POSITION MODALITY, carried as DATA on each rule obligation: a FIBRANT position rejects the locked
dimension (`isFibrantlyAccessibleAt`); a DIMENSIONAL position (pathApp's interval argument) accepts it.  Only
`pathApp`'s dimension-argument obligation is dimensional; every other argument position (pair components, the
lam argument, data constructors) is fibrant.  This is the mode-axis-free specialization (single affine lock) of
MTT's use-modality variable rule (Fig 3, the 2-cell `α : μ ⇒ locks(Δ)`); it generalizes to a full
`ModalityPath` under fib-3.

`dimensionIsAccessibleDimensionally` + `dimensionIsNotAccessibleFibrantly` are the two halves of the split,
machine-checked: the SAME locked `var 0` is accepted at `.dimensional` and rejected at `.fibrant`. -/

/-- The modality at which a rule obligation uses its subject, for the single affine dimension lock. -/
inductive ObligationModality where
  /-- A FIBRANT position — the subject is used as a duplicable value; the locked dimension is rejected here. -/
  | fibrant
  /-- A DIMENSIONAL position (e.g. `pathApp`'s interval argument) — the locked dimension is accepted here. -/
  | dimensional

/-- Decide whether the de Bruijn variable `index` may be used at `modality` in `context`: a FIBRANT position
defers to `isFibrantlyAccessibleAt` (the locked dimension is rejected); a DIMENSIONAL position accepts any
interval-typed term, including the locked dimension (the bridge's `pathApp` argument).  The mode-axis-free
specialization of MTT's use-modality variable rule for the single affine lock. -/
def TypingContext.isAccessibleAtModality {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) (modality : ObligationModality) : Bool :=
  match modality with
  | .fibrant => context.isFibrantlyAccessibleAt index
  | .dimensional => true

/-- Unfolder: at a fibrant position, accessibility is exactly `isFibrantlyAccessibleAt`. -/
theorem isAccessibleAtModality_fibrant {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) :
    context.isAccessibleAtModality index .fibrant = context.isFibrantlyAccessibleAt index :=
  rfl

/-- Unfolder: a dimensional position accepts any variable. -/
theorem isAccessibleAtModality_dimensional {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) :
    context.isAccessibleAtModality index .dimensional = true :=
  rfl

/-- **★ The locked dimension is usable DIMENSIONALLY.**  `var 0` bound by `lockCons` — the bridge dimension —
is accessible at the dimensional modality, so `pathApp p (var 0)` (the bridge's core operation) types.  The
dimensional half of the fibrant/dimensional split. -/
theorem dimensionIsAccessibleDimensionally {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope)
    (isLtZeroSucc : 0 < scope + 1) :
    (restContext.lockCons dimensionType).isAccessibleAtModality ⟨0, isLtZeroSucc⟩ .dimensional = true :=
  rfl

/-- **★ The locked dimension is NOT usable FIBRANTLY.**  `var 0` bound by `lockCons` is rejected at the
fibrant modality — so `pair (var 0) (var 0)` (the canonical SR-breaker) does not type.  The fibrant half of
the split; together with `dimensionIsAccessibleDimensionally` this is the count-free, beta-stable mechanism
that makes `pathApp` work while the duplicating body is untypeable. -/
theorem dimensionIsNotAccessibleFibrantly {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope)
    (isLtZeroSucc : 0 < scope + 1) :
    (restContext.lockCons dimensionType).isAccessibleAtModality ⟨0, isLtZeroSucc⟩ .fibrant = false :=
  rfl

/-! ## Subject usability — the term-level lift of the use-modality accessibility check

The rule obligations (`ElimObligation` / `IntroRule.obligations`) carry a SUBJECT (a `RawTerm`) and a use-position
`ObligationModality`, not a bare `Fin` index.  `isSubjectUsableAtModality` lifts `isAccessibleAtModality` from the
index to the subject: when the subject is a BARE VARIABLE `var k` it discharges `isAccessibleAtModality k modality`
(rejecting the locked dimension at a fibrant position); for any NON-VARIABLE subject it returns `true`, because that
subject is itself re-typed through `HasTypeUnion`, whose own table arms re-impose the accessibility conjunct on
EACH of its sub-obligations — so a deeper fibrant use of the locked dimension (e.g. `pair (var 0) (var 0)`) is
caught at the `pair` intro's leaf `var 0` obligations, not here.  This is exactly the one primitive the premise
field of the three table arms (`formationRule` / `intro` / `elim`) needs: one uniform conjunct
`obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true`, with all
fibrant/dimensional dispatch already inside `isAccessibleAtModality` via the obligation's `modality` field.

The variable head is detected by the propext-clean `occurrenceCountAt` recipe: match the single `mkGen` constructor
(total), decide `generator = .gen_var` (decidable Generator equality, not a partial pattern), and recover the index
through `Eq.rec` over that equality.  Non-`gen_var` heads take the `true` branch. -/

/-- Decide whether `subject` may be used at `modality` in `context` under the Fitch affine-lock discipline: a bare
variable `var k` defers to `isAccessibleAtModality k modality` (the locked dimension is rejected fibrantly, accepted
dimensionally); any non-variable subject is `true` (its nested variables are caught through their own obligations
when `HasTypeUnion` re-types it).  The term-level lift of `isAccessibleAtModality`; the single accessibility
primitive the table-arm premise field consumes. -/
def TypingContext.isSubjectUsableAtModality {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (subject : RawTerm scope)
    (modality : ObligationModality) : Bool :=
  match subject with
  | .mkGen generator payload _children =>
      if generatorIsVar : generator = .gen_var then
        let variablePosition : Fin scope :=
          Eq.rec
            (motive := fun targetGenerator _generatorEq =>
              Generator.payload targetGenerator scope)
            payload generatorIsVar
        context.isAccessibleAtModality variablePosition modality
      else
        true

/-- Unfolder: a bare variable subject `var k` discharges `isAccessibleAtModality` at its own index `k`.  Stated on
the raw `.mkGen .gen_var index .childNil` cell (which `variableCell index` is definitionally equal to, so
`rw [variableCell]` bridges at any call site that has it in scope). -/
theorem isSubjectUsableAtModality_var {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (index : Fin scope) (modality : ObligationModality) :
    context.isSubjectUsableAtModality (.mkGen .gen_var index .childNil) modality
      = context.isAccessibleAtModality index modality := by
  dsimp only [TypingContext.isSubjectUsableAtModality]
  rw [dif_pos rfl]

/-- A dimensional position accepts ANY subject — `isSubjectUsableAtModality _ subject .dimensional = true` holds
unconditionally (no lock-freeness needed): a variable head reduces to `isAccessibleAtModality _ .dimensional = true`,
a non-variable head takes the `true` branch.  The dimensional half of the split at the subject level — the witness
that `pathApp`'s interval-argument obligation is always discharged. -/
theorem isSubjectUsableAtModality_dimensional {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (subject : RawTerm scope) :
    context.isSubjectUsableAtModality subject .dimensional = true := by
  cases subject with
  | mkGen generator _payload _children =>
      dsimp only [TypingContext.isSubjectUsableAtModality]
      split <;> rfl

/-- **★ Conservativity backbone (subject level).**  In a lock-free context EVERY subject is usable at EVERY
modality — the accessibility conjunct the three table arms now carry is vacuously `true` wherever no dimension lock
appears (the whole kernel today).  A variable head reduces to `isAccessibleAtModality`, discharged fibrantly by
`lockFreeImpliesFibrantlyAccessible` and dimensionally by `rfl`; a non-variable head takes the `true` branch.  This
is the single lemma every lock-free premise-construction site dispatches its new conjunct to. -/
theorem TypingContext.lockFreeImpliesSubjectUsable {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (isLockFree : context.isLockFreeContext = true)
    (subject : RawTerm scope) (modality : ObligationModality) :
    context.isSubjectUsableAtModality subject modality = true := by
  cases subject with
  | mkGen generator payload _children =>
      dsimp only [TypingContext.isSubjectUsableAtModality]
      cases generatorEquality : decide (generator = Generator.gen_var) with
      | false =>
          rw [dif_neg (of_decide_eq_false generatorEquality)]
      | true =>
          rw [dif_pos (of_decide_eq_true generatorEquality)]
          cases modality with
          | dimensional => rfl
          | fibrant =>
              dsimp only [TypingContext.isAccessibleAtModality]
              exact context.lockFreeImpliesFibrantlyAccessible isLockFree _

end FX1Poly.Typed
