import FX1Poly.Typed.Metatheory.SubjectReduction.UnionChildSubjectReductionBounded
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionRootStepToTypedOrCongruence

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/WellFormedSubjectReductionClosure
    — the well-formed-context tie-off frame for single- and multi-step union subject reduction (SR-WF-TIEOFF #1784)

The SR full arc's last open node is the single-step-SR self-reference `UnionChildSubjectReduction` (re-type any
once-stepped union-typed term), to be discharged by STRUCTURAL-FUEL recursion on subject size.  Two shipped
facts FIX the precise shape that self-reference must take:

  * **The root-step router needs a well-formed context.**  `unionRootStepSubjectReductionToTypedOrCongruence`
    routes a single step into a typed reduct OR a top-level congruence, and the app-chain ι closers it calls
    (`unionSubjectReductionListElimCons`, `…OptionMatchSome`, `…EitherMatch{Inl,Inr}`) genuinely consume
    `WfContextUnion context` — they invert the scrutinee's element-type VALIDITY (`classifierIsType`, irreducible
    over `WfContextUnion`) and the motive's fibrant usability.  So re-typing a once-stepped term cannot be done in
    an arbitrary context.
  * **General regularity is REFUTED** (`WfContextUnionIrreducibility.regularityRefuted`): a `WfContextUnion`
    context is NOT derivable from a typing (the premise-free `var` / `universeFormation` leaves fire in
    ill-formed contexts).

Together these say the single-step-SR self-reference is NOT provable over an arbitrary context — it must carry
`WfContextUnion context` as a PRESUPPOSITION.  The shipped `UnionChildSubjectReduction` /
`UnionChildSubjectReductionBelow` (no `WfContextUnion`) are therefore TRUE only vacuously where the context
happens to be well-formed, and unprovable in general; this file ships their **well-formed-context twins**
(`…Wf`), for which the closure genuinely goes through.

## What this file ships (the architecture decision)

Route chosen: **thread `WfContextUnion context` into the self-reference, by ADDITION** — a new well-formed-context
predicate family, leaving the shipped (no-`Wf`) predicates and their consumers untouched (the no-`Wf` frame stays
green; nothing is deleted).  The new predicate is the one the router can actually feed, so the fuel induction
closes its REDEX half outright:

  * `UnionChildSubjectReductionBelowWf profile bound` — fuel-bounded single-step SR, gated by `subterm.size <
    bound`, carrying `WfContextUnion context`;
  * `UnionChildSubjectReductionWf profile` — its universal (no bound);
  * `.toBelowWf` / `.weakenWf` / `unionChildSubjectReductionWfOfAllBelow` — the closure frame (the universal is
    the bounded family at every bound, instantiated at `subterm.size + 1`);
  * `unionChildSubjectReductionBelowWfOfCongruenceCloser` — ★ the fuel INDUCTION on `bound`: the zero case is
    vacuous (`Nat.not_lt_zero`); the successor case routes the step through
    `unionRootStepSubjectReductionToTypedOrCongruence` (now fed the predicate's own `WfContextUnion`) — the
    typed-reduct disjunct closes outright, the congruence disjunct delegates to the ONE residual gate
    `UnionCongruenceClosesBoundedWf`, fed `BelowWf subject.size` from the IH (children are strictly smaller);
  * `HasTypeUnion.singleStepSubjectReductionWf` / `…PreservingWf` / `…multiStep…` — ★ the final single- and
    multi-step union SR masters, modulo ONLY the residual congruence gate (no self-reference hypothesis left).

So the whole tie-off now rests on ONE crisp obligation — `UnionCongruenceClosesBoundedWf`, the well-formed-context
fuel-bounded congruence master (re-type a parent cell when one child steps).  That is the well-formed-context twin
of `HasTypeUnion.congruenceClosesGenericAuxBounded`; inhabiting it re-threads the bounded congruence gates with
the carried `WfContextUnion` (deriving each binder child's context well-formedness from the parent's via
`WfContextUnion.cons` for concrete-typed binders / `.lockCons` for the affine interval).  The honest residual
inside that gate is the FUNCTION/PAIR-domain binder row — re-typing a `gen_lam` body / Π-Σ codomain under
`context.cons domainCode` needs `WfContextUnion (context.cons domainCode)`, hence `¬ Conv domainCode
intervalTypeCell` for an ARBITRARY universe-typed `domainCode`, a non-fibrancy fact entangled with type-level SR;
the recursor binder rows (motive under `context.cons natTypeCell` / `boolTypeCell` / `listTypeCell _`) are
unobstructed (concrete codes are rigidly non-interval).

## Zero-axiom

`Nat` order arithmetic + a structural `Nat`-induction on the fuel `bound` (NOT `WellFounded.fix`) + the shipped
zero-axiom router + `Conv.sym` + `HasTypeUnion.reclassifyToType` / `.classifierIsType` + a `StepStar` induction.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated
in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **The fuel-bounded single-step subject-reduction self-reference, carrying context well-formedness.**  The
well-formed-context twin of `UnionChildSubjectReductionBelow`: single-step SR holds for every union-typed
`subterm` of structural size `< bound` IN A WELL-FORMED CONTEXT.  The `WfContextUnion` presupposition is what the
fuel induction's root-step router consumes (the app-chain ι closers need element-type validity, irreducible over
`WfContextUnion`); without it the self-reference is unprovable (regularity is refuted). -/
def UnionChildSubjectReductionBelowWf (profile : PolyProfile) (bound : Nat) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope} {subterm reduct subtermType : RawTerm scope},
    WfContextUnion context → subterm.size < bound →
    HasTypeUnion profile context subterm subtermType → Step subterm reduct →
      ∃ reductType : RawTerm scope,
        HasTypeUnion profile context reduct reductType ∧ Conv subtermType reductType

/-- **The universal single-step subject-reduction self-reference, carrying context well-formedness.**  The
well-formed-context twin of `UnionChildSubjectReduction`: any union-typed term, stepped once IN A WELL-FORMED
CONTEXT, re-types at a `Conv`-equal classifier.  This is the genuinely-provable shape of the SR self-reference;
the bounded family collapses to it via `unionChildSubjectReductionWfOfAllBelow`. -/
def UnionChildSubjectReductionWf (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope} {subterm reduct subtermType : RawTerm scope},
    WfContextUnion context →
    HasTypeUnion profile context subterm subtermType → Step subterm reduct →
      ∃ reductType : RawTerm scope,
        HasTypeUnion profile context reduct reductType ∧ Conv subtermType reductType

/-- The universal well-formed self-reference gives the bounded form at ANY bound — forget the size hypothesis. -/
theorem UnionChildSubjectReductionWf.toBelowWf {profile : PolyProfile} {bound : Nat}
    (childSubjectReduction : UnionChildSubjectReductionWf profile) :
    UnionChildSubjectReductionBelowWf profile bound :=
  fun wellFormed _sizeLt typed step => childSubjectReduction wellFormed typed step

/-- The bounded well-formed form is ANTITONE in the bound: a larger bound's SR specializes to a smaller bound
(a term of size `< bound` is a fortiori of size `< bound'` when `bound ≤ bound'`).  The fuel-induction step uses
this to feed a `BelowWf (n + 1)` obligation from the `BelowWf n` inductive hypothesis once the cell's children
are known strictly smaller. -/
theorem UnionChildSubjectReductionBelowWf.weakenWf {profile : PolyProfile} {bound bound' : Nat}
    (boundLe : bound ≤ bound')
    (childSubjectReductionBelow : UnionChildSubjectReductionBelowWf profile bound') :
    UnionChildSubjectReductionBelowWf profile bound :=
  fun wellFormed sizeLt typed step =>
    childSubjectReductionBelow wellFormed (Nat.lt_of_lt_of_le sizeLt boundLe) typed step

/-- ★ **The closure enabler (well-formed twin).**  If the fuel-bounded well-formed single-step SR holds at EVERY
bound, the UNIVERSAL `UnionChildSubjectReductionWf` holds — instantiate the bound at `subterm.size + 1`.  So the
tie-off reduces to `∀ bound, UnionChildSubjectReductionBelowWf profile bound`, which the structural fuel induction
`unionChildSubjectReductionBelowWfOfCongruenceCloser` closes. -/
theorem unionChildSubjectReductionWfOfAllBelow {profile : PolyProfile}
    (allBelow : ∀ bound : Nat, UnionChildSubjectReductionBelowWf profile bound) :
    UnionChildSubjectReductionWf profile := by
  intro _scope _context subterm _reduct _subtermType wellFormed typed step
  exact allBelow (subterm.size + 1) wellFormed (Nat.lt_succ_self _) typed step

/-- **The fuel-bounded congruence master, carrying context well-formedness — the ONE residual gate.**  The
well-formed-context twin of `HasTypeUnion.congruenceClosesGenericAuxBounded`: a union typing of a `.mkGen` cell
whose children step re-types at a `Conv`-equal classifier, given the carried `WfContextUnion`, a free fuel `bound`
dominating the subject's size, and the fuel-bounded well-formed child-SR at that bound.  This is the sole
remaining obligation of the SR-WF-TIEOFF: inhabiting it re-threads the three bounded congruence gates with the
carried `WfContextUnion` (each binder child's context well-formedness derived from the parent's via
`WfContextUnion.cons` / `.lockCons`). -/
def UnionCongruenceClosesBoundedWf (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
    HasTypeUnion profile context subject classifier →
    WfContextUnion context →
    (bound : Nat) → subject.size ≤ bound →
    UnionChildSubjectReductionBelowWf profile bound →
    ∀ {gen : Generator} {payload : gen.payload scope}
      {before after : RawTermChildren gen.binderShifts scope},
      subject = RawTerm.mkGen gen payload before →
      StepChildren before after →
      ∃ pinned : RawTerm scope,
        HasTypeUnion profile context (RawTerm.mkGen gen payload after) pinned ∧ Conv pinned classifier

/-- ★ **The fuel induction (REDEX half discharged).**  `∀ bound, UnionChildSubjectReductionBelowWf profile bound`
by STRUCTURAL `Nat`-induction on `bound` (the propext-safe substitute for `WellFounded.fix`), modulo the residual
well-formed congruence master.  Zero case: vacuous (`subterm.size < 0` is impossible).  Successor case: route the
step through `unionRootStepSubjectReductionToTypedOrCongruence` fed the predicate's own `WfContextUnion` — the
typed-reduct disjunct closes outright (re-orienting the router's `Conv` via `.sym`), the congruence disjunct
delegates to `congruenceCloser` at `bound := subject.size` (`Nat.le_refl`), supplying `BelowWf subject.size` from
the IH `BelowWf n` weakened along `subject.size ≤ n` (children are strictly smaller than the stepping cell). -/
theorem unionChildSubjectReductionBelowWfOfCongruenceCloser {profile : PolyProfile}
    (congruenceCloser : UnionCongruenceClosesBoundedWf profile) :
    ∀ bound : Nat, UnionChildSubjectReductionBelowWf profile bound := by
  intro bound
  induction bound with
  | zero =>
      intro _scope _context _subterm _reduct _subtermType _wellFormed sizeLt _typed _step
      exact absurd sizeLt (Nat.not_lt_zero _)
  | succ predecessorBound innerHypothesis =>
      intro _scope _context subterm _reduct _subtermType wellFormed sizeLt typed step
      rcases unionRootStepSubjectReductionToTypedOrCongruence typed wellFormed step with
        typedReduct |
        ⟨generator, payload, childrenBefore, childrenAfter, redexEq, reductEq, childStep⟩
      · obtain ⟨pinnedClassifier, reductTyped, classifierConv⟩ := typedReduct
        exact ⟨pinnedClassifier, reductTyped, classifierConv.sym⟩
      · obtain ⟨pinned, reductTyped, classifierConv⟩ :=
          congruenceCloser typed wellFormed subterm.size (Nat.le_refl _)
            (innerHypothesis.weakenWf (Nat.le_of_lt_succ sizeLt)) redexEq childStep
        subst reductEq
        exact ⟨pinned, reductTyped, classifierConv.sym⟩

/-- ★ **The single-step union SR master (up to `Conv`), modulo the residual congruence gate.**  A single `Step`
of a union-typed term IN A WELL-FORMED CONTEXT yields a reduct union-typed at a `Conv`-equal classifier — the
universal `UnionChildSubjectReductionWf`, assembled from the fuel induction.  NO single-step-SR self-reference
hypothesis remains; the only standing obligation is the well-formed congruence master. -/
theorem HasTypeUnion.singleStepSubjectReductionWf {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reduct classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier)
    (wellFormed : WfContextUnion context)
    (congruenceCloser : UnionCongruenceClosesBoundedWf profile)
    (step : Step subject reduct) :
    ∃ pinned : RawTerm scope,
      HasTypeUnion profile context reduct pinned ∧ Conv classifier pinned :=
  unionChildSubjectReductionWfOfAllBelow
    (unionChildSubjectReductionBelowWfOfCongruenceCloser congruenceCloser) wellFormed typed step

/-- ★ **The classifier-PRESERVING single-step union SR master, modulo the residual congruence gate.**  Lands the
reduct at the EXACT original classifier: the up-to-`Conv` reduct is reclassified back via the conv arm
`HasTypeUnion.reclassifyToType`, whose type-of-the-classifier obligation is discharged by the unconditional
validity `HasTypeUnion.classifierIsType` over the carried `WfContextUnion`.  The drop-in shape the consistency
route's `singleStepSubjectReduction` gate consumes. -/
theorem HasTypeUnion.singleStepSubjectReductionPreservingWf {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reduct classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier)
    (wellFormed : WfContextUnion context)
    (congruenceCloser : UnionCongruenceClosesBoundedWf profile)
    (step : Step subject reduct) :
    HasTypeUnion profile context reduct classifier := by
  obtain ⟨pinned, reductTyped, classifierConv⟩ :=
    HasTypeUnion.singleStepSubjectReductionWf typed wellFormed congruenceCloser step
  exact HasTypeUnion.reclassifyToType reductTyped classifierConv.sym
    (HasTypeUnion.classifierIsType typed wellFormed)

/-- ★ **The classifier-PRESERVING MULTI-step union SR master, modulo the residual congruence gate.**  Folds the
classifier-preserving single-step master along a whole `StepStar subject reduct`: the context is FIXED across the
chain (single-step SR preserves the context), so the carried `WfContextUnion` threads unchanged and each head step
re-types the intermediate at the SAME classifier.  The free multi-step subject-reduction closure. -/
theorem HasTypeUnion.multiStepSubjectReductionPreservingWf {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reduct classifier : RawTerm scope}
    (typed : HasTypeUnion profile context subject classifier)
    (wellFormed : WfContextUnion context)
    (congruenceCloser : UnionCongruenceClosesBoundedWf profile)
    (steps : StepStar subject reduct) :
    HasTypeUnion profile context reduct classifier := by
  revert typed
  induction steps with
  | refl _ => exact id
  | trans headStep _restSteps tailPreserves =>
      exact fun startTyped =>
        tailPreserves
          (HasTypeUnion.singleStepSubjectReductionPreservingWf startTyped wellFormed congruenceCloser headStep)

end FX1Poly.Typed
