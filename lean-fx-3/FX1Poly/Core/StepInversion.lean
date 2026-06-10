import FX1Poly.Core.Step

/-! # Foundation/PolyCell/Core/StepInversion — Step inversion lemmas

The `from_X` inversion family the SR cong arm and the SN cascade consume.

## What inversion lemmas are

When a proof proceeds by case analysis on `Step source target`,
each arm needs to know what's structurally possible.  For terminal
terms (units, leaf constructors with empty children spine), the
inversion is "Step is impossible" -- no rule fires.  For non-leaf
terms, inversion characterizes the possible source/target shapes
per Step constructor.

The file builds inversion bottom-up: empty-spine → leaf-ctors →
specific-redex inversions.

## Contents

* `StepChildren.no_step_at_empty_spine` -- StepChildren is
  uninhabited when the input children spine is `.childNil`.
  Foundational because the `cong` arm of any leaf-ctor Step
  inversion needs this fact.

* `Step.no_step_from_unit` and the other leaf no-step lemmas
  (`no_step_from_boolTrue` / `_boolFalse` / `_natZero` /
  `_listNil` / `_optionNone` / `_var`) -- these terms admit no
  Step.  Each applies the empty-spine lemma to the cong arm and
  auto-discharges the redex constructors (whose source patterns
  require a different generator).

* The `from_X` family for non-leaf terms (`from_lam`, `from_app`,
  `from_boolElim`, `from_natElim`, `from_pair`, the type-code
  constructors, etc.) -- each characterizes which Step ctor could
  have fired given the source shape.

## Zero-axiom verification

All declarations pass `#assert_no_axioms`.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace FX1Poly.Core

/-- **StepChildren has no inhabitants at an empty spine.**

`StepChildren` has two constructors (`.here` and `.there`), and
BOTH require the input spine to be a `.childCons` (they pattern-
match on a head-and-tail decomposition).  Neither matches the
`.childNil` input shape, so `StepChildren .childNil _` is
uninhabited.

This is the foundational lemma the cong arm of every leaf-ctor
inversion consumes: when reducing under a generator with an empty
children spine (like `gen_unit`, `gen_boolTrue`, etc.), the cong
rule cannot fire because there's nowhere for the inner Step to
sit.

Proof: `intro h; cases h` -- Lean's `cases` tactic recognizes
neither constructor pattern matches `.childNil` and discharges
the goal automatically. -/
theorem StepChildren.no_step_at_empty_spine
    {parentScope : Nat}
    {children' : RawTermChildren [] parentScope} :
    ¬ StepChildren
        (RawTermChildren.childNil : RawTermChildren [] parentScope)
        children' := by
  intro witness
  cases witness

/-- **The unit term admits no Step reduction.**

`(.mkGen .gen_unit () .childNil)` is a leaf term: 0-arity
constructor, empty children spine, no eliminator that fires on
it.  None of `Step`'s 18 constructors can reduce it:

* `beta` requires source generator `gen_app` -- mismatch.
* Iota constructors require specific eliminators (`gen_boolElim`,
  `gen_fst`, etc.) -- all mismatch `gen_unit`.
* `cong` requires a `StepChildren` over the children spine.  The
  spine here is `.childNil`, and
  `StepChildren.no_step_at_empty_spine` shows that's uninhabited.

Lean's `cases` tactic discharges the 17 mismatched-generator
cases automatically via index unification failure.  Only the cong
case needs explicit handling, which routes through the empty-
spine lemma above.

This is the SIMPLEST Step inversion result: a leaf term blocks
all reduction.  Future inversions will be more complex
(non-leaf terms admit specific Step ctors, and the inversion
characterizes which). -/
theorem Step.no_step_from_unit
    {scope : Nat} {target : RawTerm scope} :
    ¬ Step (.mkGen .gen_unit () .childNil) target := by
  intro reduction
  cases reduction with
  | cong _ _ childStep =>
      exact StepChildren.no_step_at_empty_spine childStep

/-! ## Leaf inversion suite

The unit-term inversion above generalizes to ALL 0-arity leaf
constructors with empty children spines: bool's `true`/`false`,
nat's `zero`, list's `nil`, option's `none`, plus variable
references.  Each one admits no Step at the top level because:

* None of `Step.beta`'s, `Step.iotaXxx`'s redex source patterns
  match the leaf ctor at the OUTER position.  Some leaves (like
  `boolTrue`, `natZero`) appear as SCRUTINEES inside specific
  iotas' source patterns, but never as the outer ctor of those
  iotas -- the iota fires on `boolElim`/`natElim`, not on the
  scrutinee in isolation.
* `Step.cong` requires a `StepChildren` over the leaf's children
  spine, which is `.childNil` for 0-arity ctors.  By the
  `no_step_at_empty_spine` lemma, no such `StepChildren` exists.

Each lemma in the suite proves by the same one-line tactic --
`intro reduction; cases reduction with | cong _ _ childStep =>
exact StepChildren.no_step_at_empty_spine childStep` -- because
Lean's `cases` discharges all non-cong Step ctors automatically
via generator-mismatch unification failure, and only the cong
case needs explicit handling. -/

/-- **The `boolTrue` constructor admits no Step reduction.** -/
theorem Step.no_step_from_boolTrue
    {scope : Nat} {target : RawTerm scope} :
    ¬ Step (.mkGen .gen_boolTrue () .childNil) target := by
  intro reduction
  cases reduction with
  | cong _ _ childStep =>
      exact StepChildren.no_step_at_empty_spine childStep

/-- **The `boolFalse` constructor admits no Step reduction.** -/
theorem Step.no_step_from_boolFalse
    {scope : Nat} {target : RawTerm scope} :
    ¬ Step (.mkGen .gen_boolFalse () .childNil) target := by
  intro reduction
  cases reduction with
  | cong _ _ childStep =>
      exact StepChildren.no_step_at_empty_spine childStep

/-- **The `natZero` constructor admits no Step reduction.** -/
theorem Step.no_step_from_natZero
    {scope : Nat} {target : RawTerm scope} :
    ¬ Step (.mkGen .gen_natZero () .childNil) target := by
  intro reduction
  cases reduction with
  | cong _ _ childStep =>
      exact StepChildren.no_step_at_empty_spine childStep

/-- **The `listNil` constructor admits no Step reduction.** -/
theorem Step.no_step_from_listNil
    {scope : Nat} {target : RawTerm scope} :
    ¬ Step (.mkGen .gen_listNil () .childNil) target := by
  intro reduction
  cases reduction with
  | cong _ _ childStep =>
      exact StepChildren.no_step_at_empty_spine childStep

/-- **The `optionNone` constructor admits no Step reduction.** -/
theorem Step.no_step_from_optionNone
    {scope : Nat} {target : RawTerm scope} :
    ¬ Step (.mkGen .gen_optionNone () .childNil) target := by
  intro reduction
  cases reduction with
  | cong _ _ childStep =>
      exact StepChildren.no_step_at_empty_spine childStep

/-- **No variable reference admits a Step reduction.**

The variable `var idx` is a 0-arity ctor whose payload is the
de-Bruijn index `idx : Fin scope`.  Universal in `idx`: NO
variable reference at ANY index admits a Step.  Proof shape is
identical to the other leaf inversions because `gen_var`'s
binderShifts is `[]` (empty spine, same cong-arm reasoning). -/
theorem Step.no_step_from_var
    {scope : Nat} {idx : Fin scope} {target : RawTerm scope} :
    ¬ Step (.mkGen .gen_var idx .childNil) target := by
  intro reduction
  cases reduction with
  | cong _ _ childStep =>
      exact StepChildren.no_step_at_empty_spine childStep

/-! ## Value-constructor inversions

When the source is a VALUE constructor (lam, natSucc, listCons,
optionSome, eitherInl/Inr, pair, refl), no Step rule with a
specific outer ctor fires -- only `Step.cong` can reduce inside
the constructor's children spine.  These inversions characterize
the target shape and extract the inner Step witness.

Pattern: `Step (mkGen gen () children) target` implies `target =
mkGen gen () children'` for some `children'` such that there's a
StepChildren from `children` to `children'`.  Further specialized
by ctor: for `lam` (1 child at scope+1) it's `Step body body'`
on the body; for `pair` (2 children) it's a step in either
component; etc.

These are STRUCTURALLY more complex than leaf inversions because
the result type is an existential characterizing the target's
shape -- which the SR theorem's cong arm consumes when peeling
back layers of structural reduction. -/

/-- **Inversion for `lam`-rooted Step.**

If `Step (lam body) target` then `target = lam body'` for some
`body'` such that `Step body body'`.  This is THE archetypal
value-ctor inversion: no Step rule has `gen_lam` as outer source
generator (no beta/iota fires on lam directly), so only `cong`
applies.  The cong arm's StepChildren must be the `.here` case
(since `.there` would require Step over empty spine -- impossible
by `no_step_at_empty_spine`).

The proof unpacks the StepChildren witness and reads off the
post-step body. -/
theorem Step.from_lam
    {scope : Nat}
    {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    {target : RawTerm scope}
    (reduction :
      Step
        (.mkGen .gen_lam ()
          (.childCons domainAnn (.childCons body .childNil)))
        target) :
    (∃ (domainAfter : RawTerm scope),
        target =
          .mkGen .gen_lam ()
            (.childCons domainAfter (.childCons body .childNil)) ∧
        Step domainAnn domainAfter) ∨
    (∃ (bodyAfter : RawTerm (scope + 1)),
        target =
          .mkGen .gen_lam ()
            (.childCons domainAnn (.childCons bodyAfter .childNil)) ∧
        Step body bodyAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ domainStep =>
          rename_i domainAfter
          exact Or.inl ⟨domainAfter, rfl, domainStep⟩
      | there _ restStep =>
          cases restStep with
          | here _ bodyStep =>
              rename_i bodyAfter
              exact Or.inr ⟨bodyAfter, rfl, bodyStep⟩
          | there _ emptyStep =>
              exact absurd emptyStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `pathLam`-rooted Step.**

Same binder shape as `from_lam`: the body lives at `scope + 1`, and
the only beta+iota `Step` path from a `pathLam` root is congruence through
that body.  Raw path eta is a sibling relation (`Step.eta`), not a `Step`
constructor, so it does not appear in this inversion. -/
theorem Step.from_pathLam
    {scope : Nat} {body : RawTerm (scope + 1)} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_pathLam () (.childCons body .childNil)) target) :
    ∃ (bodyAfter : RawTerm (scope + 1)),
      target = .mkGen .gen_pathLam () (.childCons bodyAfter .childNil) ∧
      Step body bodyAfter := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ bodyStep =>
          rename_i bodyAfter
          exact ⟨bodyAfter, rfl, bodyStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `diffLambda`-rooted Step.**

Differential lambdas have the same raw binder shape as ordinary lambdas:
their only beta+iota `Step` path is congruence through the single
under-binder body child. -/
theorem Step.from_diffLambda
    {scope : Nat} {body : RawTerm (scope + 1)} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_diffLambda () (.childCons body .childNil)) target) :
    ∃ (bodyAfter : RawTerm (scope + 1)),
      target = .mkGen .gen_diffLambda () (.childCons bodyAfter .childNil) ∧
      Step body bodyAfter := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ bodyStep =>
          rename_i bodyAfter
          exact ⟨bodyAfter, rfl, bodyStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `natSucc`-rooted Step.**

If `Step (natSucc predecessor) target` then `target = natSucc
predecessor'` for some `predecessor'` such that `Step predecessor
predecessor'`.  Same proof as `from_lam` modulo the ctor's name
and binderShifts shape: `gen_natSucc` has `[0]` (child at same
scope, not bound) where `gen_lam` had `[1]`.  Operationally
identical at the inversion-proof level. -/
theorem Step.from_natSucc
    {scope : Nat} {predecessor : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_natSucc () (.childCons predecessor .childNil)) target) :
    ∃ (predecessorAfter : RawTerm scope),
      target = .mkGen .gen_natSucc () (.childCons predecessorAfter .childNil) ∧
      Step predecessor predecessorAfter := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ predecessorStep =>
          rename_i predecessorAfter
          exact ⟨predecessorAfter, rfl, predecessorStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `optionSome`-rooted Step.**

If `Step (optionSome value) target` then `target = optionSome
value'` where `Step value value'`. -/
theorem Step.from_optionSome
    {scope : Nat} {value : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_optionSome () (.childCons value .childNil)) target) :
    ∃ (valueAfter : RawTerm scope),
      target = .mkGen .gen_optionSome () (.childCons valueAfter .childNil) ∧
      Step value valueAfter := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ valueStep =>
          rename_i valueAfter
          exact ⟨valueAfter, rfl, valueStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `eitherInl`-rooted Step.** -/
theorem Step.from_eitherInl
    {scope : Nat} {value : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_eitherInl () (.childCons value .childNil)) target) :
    ∃ (valueAfter : RawTerm scope),
      target = .mkGen .gen_eitherInl () (.childCons valueAfter .childNil) ∧
      Step value valueAfter := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ valueStep =>
          rename_i valueAfter
          exact ⟨valueAfter, rfl, valueStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `eitherInr`-rooted Step.** -/
theorem Step.from_eitherInr
    {scope : Nat} {value : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_eitherInr () (.childCons value .childNil)) target) :
    ∃ (valueAfter : RawTerm scope),
      target = .mkGen .gen_eitherInr () (.childCons valueAfter .childNil) ∧
      Step value valueAfter := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ valueStep =>
          rename_i valueAfter
          exact ⟨valueAfter, rfl, valueStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `refl`-rooted Step.**

If `Step (refl rawWitness) target` then `target = refl
rawWitness'` for some stepped witness.  Note that `refl` itself
is a value (constructor of the identity type), so the
`idJ`/`idStrictRec` iotas fire on the eliminators having `refl`
as scrutinee -- but those iotas don't have `gen_refl` as the
OUTER source generator.  Only cong applies here. -/
theorem Step.from_refl
    {scope : Nat} {rawWitness : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_refl () (.childCons rawWitness .childNil)) target) :
    ∃ (rawWitnessAfter : RawTerm scope),
      target = .mkGen .gen_refl () (.childCons rawWitnessAfter .childNil) ∧
      Step rawWitness rawWitnessAfter := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ witnessStep =>
          rename_i rawWitnessAfter
          exact ⟨rawWitnessAfter, rfl, witnessStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `modIntro`-rooted Step.**

The modal eta rule lives in `Step.eta`; beta+iota `Step` only reduces under
the single modal payload child. -/
theorem Step.from_modIntro
    {scope : Nat} {modalTerm : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_modIntro () (.childCons modalTerm .childNil))
        target) :
    ∃ (modalAfter : RawTerm scope),
      target = .mkGen .gen_modIntro () (.childCons modalAfter .childNil) ∧
      Step modalTerm modalAfter := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ modalStep =>
          rename_i modalAfter
          exact ⟨modalAfter, rfl, modalStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

/-! ## 2-child value-constructor inversions

For value ctors with TWO children (pair, listCons), the cong arm's
StepChildren has more shape options:

* `here` at the outer spine -- first child steps, second
  unchanged.
* `there` at the outer spine -- first child unchanged, descend
  into the tail spine.  The tail is `.childCons secondChild
  .childNil`, so another `cases` on the tail-StepChildren:
  - `here` at the tail -- second child steps, target's tail is
    `.childCons secondChild' .childNil`.
  - `there` at the tail -- recurse into `.childNil` which is
    uninhabited by `no_step_at_empty_spine`.

So the inversion result is a DISJUNCTION of two existentials --
"first child stepped" OR "second child stepped".  This is
structurally different from the 1-child value-ctor inversions
(which had a single existential because only `here` was viable).
-/

/-- **Inversion for `pair`-rooted Step.**

If `Step (pair first second) target` then either:
* `target = pair first' second` and `Step first first'`, OR
* `target = pair first second'` and `Step second second'`.

Proof descends through cong → here-or-there → (if there) here-or-
absurd-no-spine. -/
theorem Step.from_pair
    {scope : Nat} {first second : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_pair ()
              (.childCons first (.childCons second .childNil)))
           target) :
    (∃ (firstAfter : RawTerm scope),
        target = .mkGen .gen_pair ()
          (.childCons firstAfter (.childCons second .childNil)) ∧
        Step first firstAfter)
    ∨
    (∃ (secondAfter : RawTerm scope),
        target = .mkGen .gen_pair ()
          (.childCons first (.childCons secondAfter .childNil)) ∧
        Step second secondAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ firstStep =>
          rename_i firstAfter
          exact Or.inl ⟨firstAfter, rfl, firstStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ secondStep =>
              rename_i secondAfter
              exact Or.inr ⟨secondAfter, rfl, secondStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `listCons`-rooted Step.**

Same disjunctive structure as `from_pair`: either the head steps
or the tail steps.  `gen_listCons` has the same metadata shape as
`gen_pair` (arity 2, binderShifts `[0, 0]`), so the proof is
structurally identical. -/
theorem Step.from_listCons
    {scope : Nat} {headVal tailVal : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_listCons ()
              (.childCons headVal (.childCons tailVal .childNil)))
           target) :
    (∃ (headAfter : RawTerm scope),
        target = .mkGen .gen_listCons ()
          (.childCons headAfter (.childCons tailVal .childNil)) ∧
        Step headVal headAfter)
    ∨
    (∃ (tailAfter : RawTerm scope),
        target = .mkGen .gen_listCons ()
          (.childCons headVal (.childCons tailAfter .childNil)) ∧
        Step tailVal tailAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ headStep =>
          rename_i headAfter
          exact Or.inl ⟨headAfter, rfl, headStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ tailValStep =>
              rename_i tailAfter
              exact Or.inr ⟨tailAfter, rfl, tailValStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `glueIntro`-rooted Step.**

Glue eta is represented by `Step.eta`; beta+iota `Step` only reaches a
`glueIntro` source by reducing one of its two same-scope children. -/
theorem Step.from_glueIntro
    {scope : Nat} {baseValue partialValue : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_glueIntro ()
              (.childCons baseValue (.childCons partialValue .childNil)))
           target) :
    (∃ (baseAfter : RawTerm scope),
        target = .mkGen .gen_glueIntro ()
          (.childCons baseAfter (.childCons partialValue .childNil)) ∧
        Step baseValue baseAfter)
    ∨
    (∃ (partialAfter : RawTerm scope),
        target = .mkGen .gen_glueIntro ()
          (.childCons baseValue (.childCons partialAfter .childNil)) ∧
        Step partialValue partialAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ baseStep =>
          rename_i baseAfter
          exact Or.inl ⟨baseAfter, rfl, baseStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ partialStep =>
              rename_i partialAfter
              exact Or.inr ⟨partialAfter, rfl, partialStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

/-! ## 2-child same-scope type-code inversions

These atom-shape type-code constructors are congruence-only: a `Step` out of
the parent must reduce exactly one same-scope type child. -/

/-- **Inversion for `arrowCode`-rooted Step.** -/
theorem Step.from_arrowCode
    {scope : Nat} {domain codomain : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_arrowCode ()
              (.childCons domain (.childCons codomain .childNil)))
           target) :
    (∃ (domainAfter : RawTerm scope),
        target = .mkGen .gen_arrowCode ()
          (.childCons domainAfter (.childCons codomain .childNil)) ∧
        Step domain domainAfter)
    ∨
    (∃ (codomainAfter : RawTerm scope),
        target = .mkGen .gen_arrowCode ()
          (.childCons domain (.childCons codomainAfter .childNil)) ∧
        Step codomain codomainAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ domainStep =>
          rename_i domainAfter
          exact Or.inl ⟨domainAfter, rfl, domainStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ codomainStep =>
              rename_i codomainAfter
              exact Or.inr ⟨codomainAfter, rfl, codomainStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `productCode`-rooted Step.** -/
theorem Step.from_productCode
    {scope : Nat} {leftType rightType : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_productCode ()
              (.childCons leftType (.childCons rightType .childNil)))
           target) :
    (∃ (leftTypeAfter : RawTerm scope),
        target = .mkGen .gen_productCode ()
          (.childCons leftTypeAfter (.childCons rightType .childNil)) ∧
        Step leftType leftTypeAfter)
    ∨
    (∃ (rightTypeAfter : RawTerm scope),
        target = .mkGen .gen_productCode ()
          (.childCons leftType (.childCons rightTypeAfter .childNil)) ∧
        Step rightType rightTypeAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ leftTypeStep =>
          rename_i leftTypeAfter
          exact Or.inl ⟨leftTypeAfter, rfl, leftTypeStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ rightTypeStep =>
              rename_i rightTypeAfter
              exact Or.inr ⟨rightTypeAfter, rfl, rightTypeStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `sumCode`-rooted Step.** -/
theorem Step.from_sumCode
    {scope : Nat} {leftType rightType : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_sumCode ()
              (.childCons leftType (.childCons rightType .childNil)))
           target) :
    (∃ (leftTypeAfter : RawTerm scope),
        target = .mkGen .gen_sumCode ()
          (.childCons leftTypeAfter (.childCons rightType .childNil)) ∧
        Step leftType leftTypeAfter)
    ∨
    (∃ (rightTypeAfter : RawTerm scope),
        target = .mkGen .gen_sumCode ()
          (.childCons leftType (.childCons rightTypeAfter .childNil)) ∧
        Step rightType rightTypeAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ leftTypeStep =>
          rename_i leftTypeAfter
          exact Or.inl ⟨leftTypeAfter, rfl, leftTypeStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ rightTypeStep =>
              rename_i rightTypeAfter
              exact Or.inr ⟨rightTypeAfter, rfl, rightTypeStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `eitherCode`-rooted Step.** -/
theorem Step.from_eitherCode
    {scope : Nat} {leftType rightType : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_eitherCode ()
              (.childCons leftType (.childCons rightType .childNil)))
           target) :
    (∃ (leftTypeAfter : RawTerm scope),
        target = .mkGen .gen_eitherCode ()
          (.childCons leftTypeAfter (.childCons rightType .childNil)) ∧
        Step leftType leftTypeAfter)
    ∨
    (∃ (rightTypeAfter : RawTerm scope),
        target = .mkGen .gen_eitherCode ()
          (.childCons leftType (.childCons rightTypeAfter .childNil)) ∧
        Step rightType rightTypeAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ leftTypeStep =>
          rename_i leftTypeAfter
          exact Or.inl ⟨leftTypeAfter, rfl, leftTypeStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ rightTypeStep =>
              rename_i rightTypeAfter
              exact Or.inr ⟨rightTypeAfter, rfl, rightTypeStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `equivCode`-rooted Step.** -/
theorem Step.from_equivCode
    {scope : Nat} {sourceType targetType : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_equivCode ()
              (.childCons sourceType (.childCons targetType .childNil)))
           target) :
    (∃ (sourceTypeAfter : RawTerm scope),
        target = .mkGen .gen_equivCode ()
          (.childCons sourceTypeAfter (.childCons targetType .childNil)) ∧
        Step sourceType sourceTypeAfter)
    ∨
    (∃ (targetTypeAfter : RawTerm scope),
        target = .mkGen .gen_equivCode ()
          (.childCons sourceType (.childCons targetTypeAfter .childNil)) ∧
        Step targetType targetTypeAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ sourceTypeStep =>
          rename_i sourceTypeAfter
          exact Or.inl ⟨sourceTypeAfter, rfl, sourceTypeStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ targetTypeStep =>
              rename_i targetTypeAfter
              exact Or.inr ⟨targetTypeAfter, rfl, targetTypeStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

/-! ## 2-child mixed binder inversions

The type-code binder constructors have a same-scope first child and an
under-one-binder second child.  Operationally they are still congruence-only,
but the extracted second-step witness lives at `scope + 1`. -/

/-- **Inversion for `piTyCode`-rooted Step.** -/
theorem Step.from_piTyCode
    {scope : Nat} {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_piTyCode ()
              (.childCons domain (.childCons codomain .childNil)))
           target) :
    (∃ (domainAfter : RawTerm scope),
        target = .mkGen .gen_piTyCode ()
          (.childCons domainAfter (.childCons codomain .childNil)) ∧
        Step domain domainAfter)
    ∨
    (∃ (codomainAfter : RawTerm (scope + 1)),
        target = .mkGen .gen_piTyCode ()
          (.childCons domain (.childCons codomainAfter .childNil)) ∧
        Step codomain codomainAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ domainStep =>
          rename_i domainAfter
          exact Or.inl ⟨domainAfter, rfl, domainStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ codomainStep =>
              rename_i codomainAfter
              exact Or.inr ⟨codomainAfter, rfl, codomainStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `sigmaTyCode`-rooted Step.** -/
theorem Step.from_sigmaTyCode
    {scope : Nat} {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_sigmaTyCode ()
              (.childCons domain (.childCons codomain .childNil)))
           target) :
    (∃ (domainAfter : RawTerm scope),
        target = .mkGen .gen_sigmaTyCode ()
          (.childCons domainAfter (.childCons codomain .childNil)) ∧
        Step domain domainAfter)
    ∨
    (∃ (codomainAfter : RawTerm (scope + 1)),
        target = .mkGen .gen_sigmaTyCode ()
          (.childCons domain (.childCons codomainAfter .childNil)) ∧
        Step codomain codomainAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ domainStep =>
          rename_i domainAfter
          exact Or.inl ⟨domainAfter, rfl, domainStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ codomainStep =>
              rename_i codomainAfter
              exact Or.inr ⟨codomainAfter, rfl, codomainStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `polyFunctor`-rooted Step.** -/
theorem Step.from_polyFunctor
    {scope : Nat} {positionType : RawTerm scope}
    {positionFamily : RawTerm (scope + 1)}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_polyFunctor ()
              (.childCons positionType
                (.childCons positionFamily .childNil)))
           target) :
    (∃ (positionTypeAfter : RawTerm scope),
        target = .mkGen .gen_polyFunctor ()
          (.childCons positionTypeAfter
            (.childCons positionFamily .childNil)) ∧
        Step positionType positionTypeAfter)
    ∨
    (∃ (positionFamilyAfter : RawTerm (scope + 1)),
        target = .mkGen .gen_polyFunctor ()
          (.childCons positionType
            (.childCons positionFamilyAfter .childNil)) ∧
        Step positionFamily positionFamilyAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ positionTypeStep =>
          rename_i positionTypeAfter
          exact Or.inl ⟨positionTypeAfter, rfl, positionTypeStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ positionFamilyStep =>
              rename_i positionFamilyAfter
              exact Or.inr ⟨positionFamilyAfter, rfl, positionFamilyStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

/-! ## Eliminator inversions (introducing iota disjuncts)

Eliminator constructors (fst, snd, boolElim, natElim, ...) have a
fundamentally different inversion shape from value ctors: they
admit BOTH iota rules AND cong.  The inversion conclusion
disjuncts over which reduction fired:

* Iota arm(s): source children match an iota redex pattern,
  target is the iota reduct.
* Cong arm: source children spine has a Step at some position,
  target preserves the outer ctor with the stepped spine.

The simplest eliminators (fst, snd) have ONE iota arm each (only
on pair) and a 1-child source spine, so the disjunction is 2-way
(iota OR cong-at-child). More complex eliminators (boolElim has
iotaBoolTrue+iotaBoolFalse, natElim has zero+succ) accumulate
more disjuncts.

This file builds eliminator inversions in order of complexity:
fst/snd first (2-way), then boolElim (6-way: iota+iota plus a
cong arm per child of the Phase-Z `(motive, then, else, scrutinee)`
spine), then the multi-child eliminators (5+ way). -/

/-- **Inversion for `fst`-rooted Step.**

Two-way disjunction characterizing which Step ctor fired:
* **Iota arm**: `arg` is structurally `pair first second`, and
  `target = first`.
* **Cong arm**: `arg` stepped to `argAfter`, and
  `target = fst argAfter`.

The proof uses `cases reduction` to dispatch the 18 Step ctors;
all iota constructors EXCEPT `iotaFstPair` are auto-discharged
by generator mismatch; `iotaFstPair` succeeds (constraining `arg`
to be a literal pair); `cong` recurses into the 1-child spine
via the `from_lam`-style pattern. -/
theorem Step.from_fst
    {scope : Nat} {arg : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_fst () (.childCons arg .childNil)) target) :
    (∃ (firstValue secondValue : RawTerm scope),
        arg = .mkGen .gen_pair ()
                (.childCons firstValue (.childCons secondValue .childNil)) ∧
        target = firstValue)
    ∨
    (∃ (argAfter : RawTerm scope),
        target = .mkGen .gen_fst () (.childCons argAfter .childNil) ∧
        Step arg argAfter) := by
  cases reduction with
  | iotaFstPair =>
      exact Or.inl ⟨_, _, rfl, rfl⟩
  | cong _ _ childStep =>
      cases childStep with
      | here _ argStep =>
          rename_i argAfter
          exact Or.inr ⟨argAfter, rfl, argStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `snd`-rooted Step.**

Symmetric to `Step.from_fst`: the iota arm picks the SECOND
component instead of the first.  Same 2-way disjunction
structure. -/
theorem Step.from_snd
    {scope : Nat} {arg : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_snd () (.childCons arg .childNil)) target) :
    (∃ (firstValue secondValue : RawTerm scope),
        arg = .mkGen .gen_pair ()
                (.childCons firstValue (.childCons secondValue .childNil)) ∧
        target = secondValue)
    ∨
    (∃ (argAfter : RawTerm scope),
        target = .mkGen .gen_snd () (.childCons argAfter .childNil) ∧
        Step arg argAfter) := by
  cases reduction with
  | iotaSndPair =>
      exact Or.inl ⟨_, _, rfl, rfl⟩
  | cong _ _ childStep =>
      cases childStep with
      | here _ argStep =>
          rename_i argAfter
          exact Or.inr ⟨argAfter, rfl, argStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `boolElim`-rooted Step.**

Six-way disjunction characterizing which Step ctor fired on a
boolElim term.  Phase-Z motive shape: the spine is
`(motive, thenBranch, elseBranch, scrutinee)` with the motive a
term under one binder (`RawTerm (scope + 1)`) and the scrutinee LAST.

* **iotaBoolTrue arm**: scrutinee was `boolTrue`, target =
  thenBranch.
* **iotaBoolFalse arm**: scrutinee was `boolFalse`, target =
  elseBranch.
* **cong-at-motive arm**: motive stepped (at `scope + 1`).
* **cong-at-then arm**: thenBranch stepped.
* **cong-at-else arm**: elseBranch stepped.
* **cong-at-scrutinee arm**: scrutinee stepped, target preserves
  the outer boolElim with the stepped scrutinee.

The proof descends through:
1. `cases reduction` — dispatches the 18 Step ctors; iotaBoolTrue,
   iotaBoolFalse, and cong are the only matches; rest auto-discharge.
2. For cong, `cases childStep` — dispatches `here` (motive
   position) and `there` (descend into tail).
3. The tail descends `then`, then `else`, then `scrutinee`, each
   reached via another `there`.
4. For the inner-most `there`, `cases restStep` — dispatches the
   scrutinee position and the impossible-empty-spine case. -/
theorem Step.from_boolElim
    {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {thenBranch elseBranch scrutinee : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_boolElim ()
              (.childCons motive
                (.childCons thenBranch
                  (.childCons elseBranch (.childCons scrutinee .childNil)))))
           target) :
    (scrutinee = .mkGen .gen_boolTrue () .childNil ∧ target = thenBranch)
    ∨
    (scrutinee = .mkGen .gen_boolFalse () .childNil ∧ target = elseBranch)
    ∨
    (∃ (motiveAfter : RawTerm (scope + 1)),
        target = .mkGen .gen_boolElim ()
          (.childCons motiveAfter
            (.childCons thenBranch
              (.childCons elseBranch (.childCons scrutinee .childNil)))) ∧
        Step motive motiveAfter)
    ∨
    (∃ (thenAfter : RawTerm scope),
        target = .mkGen .gen_boolElim ()
          (.childCons motive
            (.childCons thenAfter
              (.childCons elseBranch (.childCons scrutinee .childNil)))) ∧
        Step thenBranch thenAfter)
    ∨
    (∃ (elseAfter : RawTerm scope),
        target = .mkGen .gen_boolElim ()
          (.childCons motive
            (.childCons thenBranch
              (.childCons elseAfter (.childCons scrutinee .childNil)))) ∧
        Step elseBranch elseAfter)
    ∨
    (∃ (scrutineeAfter : RawTerm scope),
        target = .mkGen .gen_boolElim ()
          (.childCons motive
            (.childCons thenBranch
              (.childCons elseBranch (.childCons scrutineeAfter .childNil)))) ∧
        Step scrutinee scrutineeAfter) := by
  cases reduction with
  | iotaBoolTrue =>
      exact Or.inl ⟨rfl, rfl⟩
  | iotaBoolFalse =>
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | cong _ _ childStep =>
      cases childStep with
      | here _ motiveStep =>
          rename_i motiveAfter
          exact Or.inr (Or.inr (Or.inl ⟨motiveAfter, rfl, motiveStep⟩))
      | there _ tailStep =>
          cases tailStep with
          | here _ thenStep =>
              rename_i thenAfter
              exact Or.inr (Or.inr (Or.inr (Or.inl ⟨thenAfter, rfl, thenStep⟩)))
          | there _ restStep =>
              cases restStep with
              | here _ elseStep =>
                  rename_i elseAfter
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨elseAfter, rfl, elseStep⟩))))
              | there _ restRestStep =>
                  cases restRestStep with
                  | here _ scrutineeStep =>
                      rename_i scrutineeAfter
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        ⟨scrutineeAfter, rfl, scrutineeStep⟩))))
                  | there _ restRestRestStep =>
                      exact absurd restRestRestStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `natElim`-rooted Step.**

Five-way disjunction with a COMPLEX-IOTA disjunct.  The Succ
iota's target is a nested app `app (app succBranch pred)
(natElim pred zeroBranch succBranch)` -- so the Succ-iota
disjunct must existentially characterize `pred` AND the resulting
nested-app target.

The five disjuncts:
* iotaNatElimZero arm: scrutinee = natZero, target = zeroBranch.
* iotaNatElimSucc arm: ∃ pred, scrutinee = natSucc pred ∧
  target = app (app succBranch pred) (natElim pred zeroBranch succBranch).
* cong-at-scrutinee arm.
* cong-at-zero arm.
* cong-at-succ arm. -/
theorem Step.from_natElim
    {scope : Nat}
    {scrutinee zeroBranch succBranch : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_natElim ()
              (.childCons scrutinee
                (.childCons zeroBranch (.childCons succBranch .childNil))))
           target) :
    (scrutinee = .mkGen .gen_natZero () .childNil ∧ target = zeroBranch)
    ∨
    (∃ (predecessor : RawTerm scope),
        scrutinee = .mkGen .gen_natSucc () (.childCons predecessor .childNil) ∧
        target = .mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons succBranch (.childCons predecessor .childNil)))
            (.childCons
              (.mkGen .gen_natElim ()
                (.childCons predecessor
                  (.childCons zeroBranch (.childCons succBranch .childNil))))
              .childNil)))
    ∨
    (∃ (scrutineeAfter : RawTerm scope),
        target = .mkGen .gen_natElim ()
          (.childCons scrutineeAfter
            (.childCons zeroBranch (.childCons succBranch .childNil))) ∧
        Step scrutinee scrutineeAfter)
    ∨
    (∃ (zeroAfter : RawTerm scope),
        target = .mkGen .gen_natElim ()
          (.childCons scrutinee
            (.childCons zeroAfter (.childCons succBranch .childNil))) ∧
        Step zeroBranch zeroAfter)
    ∨
    (∃ (succAfter : RawTerm scope),
        target = .mkGen .gen_natElim ()
          (.childCons scrutinee
            (.childCons zeroBranch (.childCons succAfter .childNil))) ∧
        Step succBranch succAfter) := by
  cases reduction with
  | iotaNatElimZero =>
      exact Or.inl ⟨rfl, rfl⟩
  | iotaNatElimSucc =>
      exact Or.inr (Or.inl ⟨_, rfl, rfl⟩)
  | cong _ _ childStep =>
      cases childStep with
      | here _ scrutineeStep =>
          rename_i scrutineeAfter
          exact Or.inr (Or.inr (Or.inl ⟨scrutineeAfter, rfl, scrutineeStep⟩))
      | there _ tailStep =>
          cases tailStep with
          | here _ zeroStep =>
              rename_i zeroAfter
              exact Or.inr (Or.inr (Or.inr (Or.inl ⟨zeroAfter, rfl, zeroStep⟩)))
          | there _ restStep =>
              cases restStep with
              | here _ succStep =>
                  rename_i succAfter
                  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨succAfter, rfl, succStep⟩)))
              | there _ restRestStep =>
                  exact absurd restRestStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `natRec`-rooted Step.**

Same shape as `from_natElim` — the v2 substrate's metadata
treats `gen_natElim` and `gen_natRec` identically.  The
recursive call inside the Succ iota refers to `natRec`. -/
theorem Step.from_natRec
    {scope : Nat}
    {scrutinee zeroBranch succBranch : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_natRec ()
              (.childCons scrutinee
                (.childCons zeroBranch (.childCons succBranch .childNil))))
           target) :
    (scrutinee = .mkGen .gen_natZero () .childNil ∧ target = zeroBranch)
    ∨
    (∃ (predecessor : RawTerm scope),
        scrutinee = .mkGen .gen_natSucc () (.childCons predecessor .childNil) ∧
        target = .mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons succBranch (.childCons predecessor .childNil)))
            (.childCons
              (.mkGen .gen_natRec ()
                (.childCons predecessor
                  (.childCons zeroBranch (.childCons succBranch .childNil))))
              .childNil)))
    ∨
    (∃ (scrutineeAfter : RawTerm scope),
        target = .mkGen .gen_natRec ()
          (.childCons scrutineeAfter
            (.childCons zeroBranch (.childCons succBranch .childNil))) ∧
        Step scrutinee scrutineeAfter)
    ∨
    (∃ (zeroAfter : RawTerm scope),
        target = .mkGen .gen_natRec ()
          (.childCons scrutinee
            (.childCons zeroAfter (.childCons succBranch .childNil))) ∧
        Step zeroBranch zeroAfter)
    ∨
    (∃ (succAfter : RawTerm scope),
        target = .mkGen .gen_natRec ()
          (.childCons scrutinee
            (.childCons zeroBranch (.childCons succAfter .childNil))) ∧
        Step succBranch succAfter) := by
  cases reduction with
  | iotaNatRecZero =>
      exact Or.inl ⟨rfl, rfl⟩
  | iotaNatRecSucc =>
      exact Or.inr (Or.inl ⟨_, rfl, rfl⟩)
  | cong _ _ childStep =>
      cases childStep with
      | here _ scrutineeStep =>
          rename_i scrutineeAfter
          exact Or.inr (Or.inr (Or.inl ⟨scrutineeAfter, rfl, scrutineeStep⟩))
      | there _ tailStep =>
          cases tailStep with
          | here _ zeroStep =>
              rename_i zeroAfter
              exact Or.inr (Or.inr (Or.inr (Or.inl ⟨zeroAfter, rfl, zeroStep⟩)))
          | there _ restStep =>
              cases restStep with
              | here _ succStep =>
                  rename_i succAfter
                  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨succAfter, rfl, succStep⟩)))
              | there _ restRestStep =>
                  exact absurd restRestStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `listElim`-rooted Step.**

Six-way disjunction characterizing which Step ctor fired on a
listElim term.  Phase-Z motive shape: the spine is
`(motive, nilBranch, consBranch, scrutinee)` with the motive a
term under one binder (`RawTerm (scope + 1)`) and the scrutinee LAST.

* **iotaListElimNil arm**: scrutinee was `listNil`, target =
  nilBranch.
* **iotaListElimCons arm**: scrutinee was `listCons headVal tailVal`,
  target is the TRIPLE-nested app referencing both the head and
  tail components plus the recursive `listElim` spine that THREADS
  the same motive through the tail.  Two existentials needed.
* **cong-at-motive arm**: motive stepped (at `scope + 1`).
* **cong-at-nil arm**: nilBranch stepped.
* **cong-at-cons arm**: consBranch stepped.
* **cong-at-scrutinee arm**: scrutinee stepped, target preserves
  the outer listElim with the stepped scrutinee.

The proof descends through cong → here (motive) → there here (nil)
→ there there here (cons) → there^3 here (scrutinee), mirroring
`Step.from_boolElim` (the listElim Cons iota carries the extra
head/tail existentials and the motive-threaded recursive spine). -/
theorem Step.from_listElim
    {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {nilBranch consBranch scrutinee : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_listElim ()
              (.childCons motive
                (.childCons nilBranch
                  (.childCons consBranch (.childCons scrutinee .childNil)))))
           target) :
    (scrutinee = .mkGen .gen_listNil () .childNil ∧ target = nilBranch)
    ∨
    (∃ (headVal tailVal : RawTerm scope),
        scrutinee = .mkGen .gen_listCons ()
                      (.childCons headVal (.childCons tailVal .childNil)) ∧
        target = .mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_app ()
                  (.childCons consBranch (.childCons headVal .childNil)))
                (.childCons tailVal .childNil)))
            (.childCons
              (.mkGen .gen_listElim ()
                (.childCons motive
                  (.childCons nilBranch
                    (.childCons consBranch (.childCons tailVal .childNil)))))
              .childNil)))
    ∨
    (∃ (motiveAfter : RawTerm (scope + 1)),
        target = .mkGen .gen_listElim ()
          (.childCons motiveAfter
            (.childCons nilBranch
              (.childCons consBranch (.childCons scrutinee .childNil)))) ∧
        Step motive motiveAfter)
    ∨
    (∃ (nilAfter : RawTerm scope),
        target = .mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilAfter
              (.childCons consBranch (.childCons scrutinee .childNil)))) ∧
        Step nilBranch nilAfter)
    ∨
    (∃ (consAfter : RawTerm scope),
        target = .mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch
              (.childCons consAfter (.childCons scrutinee .childNil)))) ∧
        Step consBranch consAfter)
    ∨
    (∃ (scrutineeAfter : RawTerm scope),
        target = .mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch
              (.childCons consBranch (.childCons scrutineeAfter .childNil)))) ∧
        Step scrutinee scrutineeAfter) := by
  cases reduction with
  | iotaListElimNil =>
      exact Or.inl ⟨rfl, rfl⟩
  | iotaListElimCons =>
      exact Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)
  | cong _ _ childStep =>
      cases childStep with
      | here _ motiveStep =>
          rename_i motiveAfter
          exact Or.inr (Or.inr (Or.inl ⟨motiveAfter, rfl, motiveStep⟩))
      | there _ tailStep =>
          cases tailStep with
          | here _ nilStep =>
              rename_i nilAfter
              exact Or.inr (Or.inr (Or.inr (Or.inl ⟨nilAfter, rfl, nilStep⟩)))
          | there _ restStep =>
              cases restStep with
              | here _ consStep =>
                  rename_i consAfter
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨consAfter, rfl, consStep⟩))))
              | there _ restRestStep =>
                  cases restRestStep with
                  | here _ scrutineeStep =>
                      rename_i scrutineeAfter
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        ⟨scrutineeAfter, rfl, scrutineeStep⟩))))
                  | there _ restRestRestStep =>
                      exact absurd restRestRestStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `optionMatch`-rooted Step.**

Five-way disjunction.  Some-iota arm has a 1-arg app-chain target
`app someBranch value` requiring one existential for the wrapped
value. -/
theorem Step.from_optionMatch
    {scope : Nat}
    {scrutinee noneBranch someBranch : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_optionMatch ()
              (.childCons scrutinee
                (.childCons noneBranch (.childCons someBranch .childNil))))
           target) :
    (scrutinee = .mkGen .gen_optionNone () .childNil ∧ target = noneBranch)
    ∨
    (∃ (value : RawTerm scope),
        scrutinee = .mkGen .gen_optionSome () (.childCons value .childNil) ∧
        target = .mkGen .gen_app ()
                  (.childCons someBranch (.childCons value .childNil)))
    ∨
    (∃ (scrutineeAfter : RawTerm scope),
        target = .mkGen .gen_optionMatch ()
          (.childCons scrutineeAfter
            (.childCons noneBranch (.childCons someBranch .childNil))) ∧
        Step scrutinee scrutineeAfter)
    ∨
    (∃ (noneAfter : RawTerm scope),
        target = .mkGen .gen_optionMatch ()
          (.childCons scrutinee
            (.childCons noneAfter (.childCons someBranch .childNil))) ∧
        Step noneBranch noneAfter)
    ∨
    (∃ (someAfter : RawTerm scope),
        target = .mkGen .gen_optionMatch ()
          (.childCons scrutinee
            (.childCons noneBranch (.childCons someAfter .childNil))) ∧
        Step someBranch someAfter) := by
  cases reduction with
  | iotaOptionMatchNone =>
      exact Or.inl ⟨rfl, rfl⟩
  | iotaOptionMatchSome =>
      exact Or.inr (Or.inl ⟨_, rfl, rfl⟩)
  | cong _ _ childStep =>
      cases childStep with
      | here _ scrutineeStep =>
          rename_i scrutineeAfter
          exact Or.inr (Or.inr (Or.inl ⟨scrutineeAfter, rfl, scrutineeStep⟩))
      | there _ tailStep =>
          cases tailStep with
          | here _ noneStep =>
              rename_i noneAfter
              exact Or.inr (Or.inr (Or.inr (Or.inl ⟨noneAfter, rfl, noneStep⟩)))
          | there _ restStep =>
              cases restStep with
              | here _ someStep =>
                  rename_i someAfter
                  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨someAfter, rfl, someStep⟩)))
              | there _ restRestStep =>
                  exact absurd restRestStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `eitherMatch`-rooted Step.**

Five-way disjunction.  BOTH iota arms have 1-arg app-chain
targets (no nullary base case for either) -- so the first two
disjuncts are existential, characterizing the wrapped value in
each case. -/
theorem Step.from_eitherMatch
    {scope : Nat}
    {scrutinee leftBranch rightBranch : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_eitherMatch ()
              (.childCons scrutinee
                (.childCons leftBranch (.childCons rightBranch .childNil))))
           target) :
    (∃ (value : RawTerm scope),
        scrutinee = .mkGen .gen_eitherInl () (.childCons value .childNil) ∧
        target = .mkGen .gen_app ()
                  (.childCons leftBranch (.childCons value .childNil)))
    ∨
    (∃ (value : RawTerm scope),
        scrutinee = .mkGen .gen_eitherInr () (.childCons value .childNil) ∧
        target = .mkGen .gen_app ()
                  (.childCons rightBranch (.childCons value .childNil)))
    ∨
    (∃ (scrutineeAfter : RawTerm scope),
        target = .mkGen .gen_eitherMatch ()
          (.childCons scrutineeAfter
            (.childCons leftBranch (.childCons rightBranch .childNil))) ∧
        Step scrutinee scrutineeAfter)
    ∨
    (∃ (leftAfter : RawTerm scope),
        target = .mkGen .gen_eitherMatch ()
          (.childCons scrutinee
            (.childCons leftAfter (.childCons rightBranch .childNil))) ∧
        Step leftBranch leftAfter)
    ∨
    (∃ (rightAfter : RawTerm scope),
        target = .mkGen .gen_eitherMatch ()
          (.childCons scrutinee
            (.childCons leftBranch (.childCons rightAfter .childNil))) ∧
        Step rightBranch rightAfter) := by
  cases reduction with
  | iotaEitherMatchInl =>
      exact Or.inl ⟨_, rfl, rfl⟩
  | iotaEitherMatchInr =>
      exact Or.inr (Or.inl ⟨_, rfl, rfl⟩)
  | cong _ _ childStep =>
      cases childStep with
      | here _ scrutineeStep =>
          rename_i scrutineeAfter
          exact Or.inr (Or.inr (Or.inl ⟨scrutineeAfter, rfl, scrutineeStep⟩))
      | there _ tailStep =>
          cases tailStep with
          | here _ leftStep =>
              rename_i leftAfter
              exact Or.inr (Or.inr (Or.inr (Or.inl ⟨leftAfter, rfl, leftStep⟩)))
          | there _ restStep =>
              cases restStep with
              | here _ rightStep =>
                  rename_i rightAfter
                  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rightAfter, rfl, rightStep⟩)))
              | there _ restRestStep =>
                  exact absurd restRestStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `idJ`-rooted Step.**

Three-way disjunction: iotaIdJRefl arm + 2 cong positions.  The
iota arm characterizes "witness was refl" with an existential
witness for the wrapped value.  Standard eliminator-inversion
template at 2-child arity. -/
theorem Step.from_idJ
    {scope : Nat} {baseCase witness : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_idJ ()
              (.childCons baseCase (.childCons witness .childNil))) target) :
    (∃ (rawWitness : RawTerm scope),
        witness = .mkGen .gen_refl () (.childCons rawWitness .childNil) ∧
        target = baseCase)
    ∨
    (∃ (baseAfter : RawTerm scope),
        target = .mkGen .gen_idJ ()
          (.childCons baseAfter (.childCons witness .childNil)) ∧
        Step baseCase baseAfter)
    ∨
    (∃ (witnessAfter : RawTerm scope),
        target = .mkGen .gen_idJ ()
          (.childCons baseCase (.childCons witnessAfter .childNil)) ∧
        Step witness witnessAfter) := by
  cases reduction with
  | iotaIdJRefl =>
      exact Or.inl ⟨_, rfl, rfl⟩
  | cong _ _ childStep =>
      cases childStep with
      | here _ baseStep =>
          rename_i baseAfter
          exact Or.inr (Or.inl ⟨baseAfter, rfl, baseStep⟩)
      | there _ tailStep =>
          cases tailStep with
          | here _ witnessStep =>
              rename_i witnessAfter
              exact Or.inr (Or.inr ⟨witnessAfter, rfl, witnessStep⟩)
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `idStrictRec`-rooted Step.**

Symmetric to `Step.from_idJ` for the strict identity eliminator. -/
theorem Step.from_idStrictRec
    {scope : Nat} {baseCase witness : RawTerm scope}
    {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_idStrictRec ()
              (.childCons baseCase (.childCons witness .childNil))) target) :
    (∃ (rawWitness : RawTerm scope),
        witness = .mkGen .gen_refl () (.childCons rawWitness .childNil) ∧
        target = baseCase)
    ∨
    (∃ (baseAfter : RawTerm scope),
        target = .mkGen .gen_idStrictRec ()
          (.childCons baseAfter (.childCons witness .childNil)) ∧
        Step baseCase baseAfter)
    ∨
    (∃ (witnessAfter : RawTerm scope),
        target = .mkGen .gen_idStrictRec ()
          (.childCons baseCase (.childCons witnessAfter .childNil)) ∧
        Step witness witnessAfter) := by
  cases reduction with
  | iotaIdStrictRecRefl =>
      exact Or.inl ⟨_, rfl, rfl⟩
  | cong _ _ childStep =>
      cases childStep with
      | here _ baseStep =>
          rename_i baseAfter
          exact Or.inr (Or.inl ⟨baseAfter, rfl, baseStep⟩)
      | there _ tailStep =>
          cases tailStep with
          | here _ witnessStep =>
              rename_i witnessAfter
              exact Or.inr (Or.inr ⟨witnessAfter, rfl, witnessStep⟩)
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `app`-rooted Step.**

THE LOAD-BEARING INVERSION FOR SR'S BETA ARM.

Three-way disjunction: beta iota + 2 cong positions.  The beta
arm structurally requires `fn` (the function child) to be a
lambda -- the inversion characterizes this with an existential
for the lambda's body.  This existential is exactly the `body`
that SR's beta arm substitutes into via the cell-level
substitution boundary lemma.

The function child lives at the same scope as `fn`; the
lambda's body lives at `scope + 1` (the `gen_lam`'s binderShifts
are `[0, 1]`: a domain annotation at the same scope plus the body
under one binder).  Church-style: the beta arm exposes the
lambda's domain annotation as an existential alongside the body;
contraction discards the annotation so the reduct is unchanged. -/
theorem Step.from_app
    {scope : Nat} {fn arg : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_app ()
              (.childCons fn (.childCons arg .childNil))) target) :
    (∃ (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)),
        fn = .mkGen .gen_lam ()
          (.childCons domainAnn (.childCons body .childNil)) ∧
        target = RawTerm.subst0 body arg)
    ∨
    (∃ (fnAfter : RawTerm scope),
        target = .mkGen .gen_app () (.childCons fnAfter (.childCons arg .childNil)) ∧
        Step fn fnAfter)
    ∨
    (∃ (argAfter : RawTerm scope),
        target = .mkGen .gen_app () (.childCons fn (.childCons argAfter .childNil)) ∧
        Step arg argAfter) := by
  cases reduction with
  | beta =>
      exact Or.inl ⟨_, _, rfl, rfl⟩
  | cong _ _ childStep =>
      cases childStep with
      | here _ fnStep =>
          rename_i fnAfter
          exact Or.inr (Or.inl ⟨fnAfter, rfl, fnStep⟩)
      | there _ tailStep =>
          cases tailStep with
          | here _ argStep =>
              rename_i argAfter
              exact Or.inr (Or.inr ⟨argAfter, rfl, argStep⟩)
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

end FX1Poly.Core
