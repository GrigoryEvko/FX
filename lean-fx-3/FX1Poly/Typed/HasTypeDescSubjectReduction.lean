import FX1Poly.Typed.HasTypeDescContextConversion
import FX1Poly.Core.StepInversion

/-! # FX1Poly/Typed/HasTypeDescSubjectReduction
    — subject reduction for the FORMATION engine `HasTypeDesc` (discharges the dispatcher's ofFormation arm)

The grown-engine SR dispatcher (SN-055) inducts on a `HasTypeDescPi` derivation; its `ofFormation` arm carries
a `HasTypeDesc` premise (the formation engine: `var` / `conv` / `universeFormation` / `genFormation`).  To
preserve typing there, that premise must itself be subject-reduction-closed: a Step of a FORMATION-typed
subject lands at the SAME classifier (formation classifiers are stable — there is no β/ι that changes the
classifier of a var, a universe code, or a Π/Σ-former code).

This file ships that — the formation-engine subject reduction, as a MUTUAL pair mirroring the
`convContext` / `convTelescope` template (`HasTypeDescContextConversion`):

  * **`HasTypeDesc.subjectReduction`** — `var` and `universeFormation` are NORMAL (no Step: `no_step_from_var`
    / `no_step_from_universeCode`), `conv` re-types the premise and re-wraps, `genFormation` decomposes the
    Step into a child congruence (`former_step_inv`) and re-types the premise telescope.
  * **`DescTelescope.subjectReduction`** — the premise telescope under a child Step: `here` (the binding head
    steps) re-types the head via the mutual `HasTypeDesc.subjectReduction` and re-types the tail under the
    stepped binding via `convTelescope` (`convContextCondition_consStep` supplies the
    `cons head ⤳ cons headAfter` context-condition); `there` recurses into the tail.

**Honesty correction (the formation fragment is NORMAL — this SR is VACUOUSLY true).**  The formation engine
types ONLY normal forms.  Its arms are var / universeFormation / conv / `genFormation`, and a Π/Σ-former code's
components are re-typed at universe codes BY THE SAME ENGINE (the `DescTelescope` premise), hence are
recursively formation-typed and therefore normal — so the former code itself heads no redex.  The engine has no
app / eliminator / λ arm, so NO formation-typed subject ever steps.  `HasTypeDesc.subjectAdmitsNoStep` (below)
is that honest characterization; it makes this `subjectReduction` VACUOUSLY true (the mutual machinery handles
the structurally-possible child congruences that never fire on a normal subject — exactly like the bespoke
leaf-only `HasType.subjectReduction`, also a no-step lemma).  The dispatcher's `ofFormation` arm discharges via
`subjectAdmitsNoStep` (no step → vacuous), NOT via the heavier `subjectReduction`.  (An earlier draft of this
header overclaimed "genuinely non-vacuous"; corrected here.)

The genFormation arm is generic over the formation generator: `former_step_inv` rules out root redexes for the
whole formation family (currently `{gen_piTyCode, gen_sigmaTyCode}` via `typingRuleDescOf_isPiOrSigma`), so a
new ≥1-child formation row (a data type code) extends it with no per-consumer cascade.

## Zero-axiom verification

The per-cell Step inversions (`no_step_from_var` / `no_step_from_universeCode` / `no_step_at_empty_spine`) +
the formation-table enumeration (`typingRuleDescOf_isPiOrSigma`) + the shipped formation context-conversion
(`convTelescope`) + `Conv.rename` of a one-step `Conv`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **A universe-code cell admits no Step.**  `universeCodeCell` is a nullary leaf
(`mkGen gen_universeCode (level, flag) childNil`): no eliminator fires on it and its child spine is empty, so
the only candidate reduction is a `cong` whose `StepChildren` is on `childNil` — uninhabited by
`no_step_at_empty_spine`.  The `universeFormation` arm's vacuity witness. -/
theorem Step.no_step_from_universeCode {scope : Nat} {levelExpr : LevelExpr}
    {flag : UniverseFlag} {target : RawTerm scope} :
    ¬ Step (universeCodeCell levelExpr flag) target := by
  intro reduction
  cases reduction with
  | cong _ _ childStep => exact StepChildren.no_step_at_empty_spine childStep

/-- **A formation cell heads no root redex, so any Step is a child congruence.**  A formation generator
(`typingRuleDescOf generator = some rule` ⟹ `gen_piTyCode` or `gen_sigmaTyCode`, by
`typingRuleDescOf_isPiOrSigma`) is a TYPE-FORMER code, not an eliminable/applicable cell — no `beta`, no
`iota*` fires on it.  So a `Step (mkGen generator payload children) target` can only be `cong`, exposing a
`StepChildren children children'` with `target = mkGen generator payload children'`.  The generic
step-decomposition the `genFormation` SR arm consumes; adding a future ≥1-child formation row extends the
`isPiOrSigma` enumeration by one disjunct, with no change here. -/
theorem former_step_inv {scope : Nat} {generator : Generator}
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    {rule : TypingRuleDesc} {target : RawTerm scope}
    (isFormation : typingRuleDescOf generator = some rule)
    (step : Step (.mkGen generator payload children) target) :
    ∃ children', target = .mkGen generator payload children' ∧ StepChildren children children' := by
  rcases typingRuleDescOf_isPiOrSigma isFormation with rfl | rfl
  · cases step with
    | cong _ _ childStep => exact ⟨_, rfl, childStep⟩
  · cases step with
    | cong _ _ childStep => exact ⟨_, rfl, childStep⟩

/-- **The context-condition for re-typing a telescope tail when the binding head steps.**  When a telescope
binding `head ⤳ headAfter`, the tail — typed under `context.cons head` — must be re-typed under
`context.cons headAfter`.  Both contexts cons onto the SAME prefix `context`, so index `0` looks up the
stepped binding (`Conv head headAfter`, weakened by `Conv.rename`) and index `k+1` looks up the shared
prefix (`Conv.refl`).  This is the `cons head ⤳ cons headAfter` instance of the pointwise context-Conv that
`convTelescope` consumes — the head-conv analogue of `convContextCondition_cons` (same binding). -/
theorem convContextCondition_consStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {head headAfter : RawTerm scope}
    (headConv : Conv head headAfter) :
    ∀ index : Fin (scope + 1),
      Conv ((context.cons head).lookup index) ((context.cons headAfter).lookup index) := by
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show Conv (RawTerm.rename RawRenaming.weaken head)
        (RawTerm.rename RawRenaming.weaken headAfter)
      exact Conv.rename RawRenaming.weaken headConv
  | succ k =>
      show Conv (RawTerm.rename RawRenaming.weaken
          (context.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
        (RawTerm.rename RawRenaming.weaken
          (context.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
      exact Conv.refl _

mutual

/-- **Formation-engine subject reduction.**  A `HasTypeDesc` derivation is preserved under a Step of its
subject, at the SAME classifier.  `var` / `universeFormation` are normal (no Step); `conv` re-types its
premise (mutual recursion on `typed`) and re-wraps at the reclassifier; `genFormation` decomposes the Step
via `former_step_inv` and re-types the premise telescope via the mutual `DescTelescope.subjectReduction`.
The dispatcher's `ofFormation` arm wraps the conclusion with `HasTypeDescPi.ofFormation`. -/
theorem HasTypeDesc.subjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDesc profile context subject classifier) :
    ∀ (reduct : RawTerm scope), Step subject reduct →
      HasTypeDesc profile context reduct classifier :=
  match derivation with
  | .var _context _index => fun _reduct step => (Step.no_step_from_var step).elim
  | .conv levelExpr flag typed converts reclassifierTyped => fun reduct step =>
      HasTypeDesc.conv levelExpr flag (HasTypeDesc.subjectReduction typed reduct step) converts
        reclassifierTyped
  | .universeFormation _context _levelExpr _flag => fun _reduct step =>
      (Step.no_step_from_universeCode step).elim
  | .genFormation context generator payload children levels flag rule isFormation premises =>
      fun _reduct step => by
        obtain ⟨children', reductEq, stepChildren⟩ := former_step_inv isFormation step
        subst reductEq
        exact HasTypeDesc.genFormation context generator payload children' levels flag rule
          isFormation (DescTelescope.subjectReduction premises children' stepChildren)

/-- **Telescope subject reduction.**  A formation premise telescope is preserved under a child Step.  `here`
(the binding head `head ⤳ headAfter`): re-type the head via the mutual `HasTypeDesc.subjectReduction`, then
re-type the tail under the stepped binding via `convTelescope` (with `convContextCondition_consStep` supplying
the `cons head ⤳ cons headAfter` context-condition).  `there` (a tail child steps): recurse into the tail. -/
theorem DescTelescope.subjectReduction {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile context levels flag children) :
    ∀ (children' : RawTermChildren binderShifts baseScope),
      StepChildren children children' → DescTelescope profile context levels flag children' :=
  match telescope with
  | .nil _context _flag => fun _children' stepChildren =>
      (StepChildren.no_step_at_empty_spine stepChildren).elim
  | .cons context head headLevel restLevels flag rest headTyped restTyped =>
      fun _children' stepChildren => by
        cases stepChildren with
        | here _rest headStep =>
            rename_i headAfter
            refine DescTelescope.cons context headAfter headLevel restLevels flag rest
              (HasTypeDesc.subjectReduction headTyped headAfter headStep) ?_
            exact DescTelescope.convTelescope restTyped (context.cons headAfter)
              (convContextCondition_consStep ⟨headAfter, StepStar.single headStep, StepStar.refl _⟩)
        | there _head restStep =>
            rename_i restAfter
            exact DescTelescope.cons context head headLevel restLevels flag restAfter headTyped
              (DescTelescope.subjectReduction restTyped restAfter restStep)

end

mutual

/-- **The formation fragment is NORMAL: every `HasTypeDesc`-typed subject admits no `Step`.**  This is the
honest characterization of the formation engine (it types only normal forms), and the genuinely content-bearing
statement that `subjectReduction` is vacuously true: `var` / `universeFormation` are leaves (no_step_from_var /
no_step_from_universeCode); `conv` re-uses the premise (same subject); `genFormation` decomposes any candidate
Step into a child congruence (`former_step_inv`, root-redex-free over the formation family) and contradicts it
via the mutual telescope normality.  Unlike `subjectReduction` (whose mutual machinery RE-TYPES under a step
that never fires), this concludes the step is IMPOSSIBLE — so it is the tool the SR dispatcher's `ofFormation`
arm uses (`absurd step (formationTyped.subjectAdmitsNoStep _)`).  Non-vacuous as a statement: it characterizes
EVERY formation-typed term as normal. -/
theorem HasTypeDesc.subjectAdmitsNoStep {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDesc profile context subject classifier) :
    ∀ (reduct : RawTerm scope), ¬ Step subject reduct :=
  match derivation with
  | .var _context _index => fun _reduct step => Step.no_step_from_var step
  | .conv _levelExpr _flag typed _converts _reclassifierTyped => fun reduct step =>
      HasTypeDesc.subjectAdmitsNoStep typed reduct step
  | .universeFormation _context _levelExpr _flag => fun _reduct step =>
      Step.no_step_from_universeCode step
  | .genFormation _context _generator _payload _children _levels _flag _rule isFormation premises =>
      fun _reduct step => by
        obtain ⟨children', _reductEq, stepChildren⟩ := former_step_inv isFormation step
        exact DescTelescope.childrenAdmitNoStep premises children' stepChildren

/-- **A formation premise telescope's children admit no `StepChildren`** — the mutual normality witness for the
spine: `nil` is empty (`no_step_at_empty_spine`); `cons` contradicts a head Step via the mutual
`HasTypeDesc.subjectAdmitsNoStep` on `headTyped` and a tail Step via the recursive telescope normality. -/
theorem DescTelescope.childrenAdmitNoStep {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile context levels flag children) :
    ∀ (children' : RawTermChildren binderShifts baseScope),
      ¬ StepChildren children children' :=
  match telescope with
  | .nil _context _flag => fun _children' stepChildren =>
      StepChildren.no_step_at_empty_spine stepChildren
  | .cons _context _head _headLevel _restLevels _flag _rest headTyped restTyped =>
      fun _children' stepChildren => by
        cases stepChildren with
        | here _rest headStep =>
            rename_i headAfter
            exact HasTypeDesc.subjectAdmitsNoStep headTyped headAfter headStep
        | there _head restStep =>
            rename_i restAfter
            exact DescTelescope.childrenAdmitNoStep restTyped restAfter restStep

end

end FX1Poly.Typed
