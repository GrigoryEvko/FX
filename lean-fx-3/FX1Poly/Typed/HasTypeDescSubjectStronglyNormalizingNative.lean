import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Typed.HasTypeDescSubjectReduction
import FX1Poly.Core.StrongNormalizationConstructors
import FX1Poly.Core.StrongNormalizationLeaves

/-! # FX1Poly/Typed/HasTypeDescSubjectStronglyNormalizingNative
    — native subject strong normalization for the description formation engine

This file ships `HasTypeDesc.subjectStronglyNormalizingNative`: every formation-typed SUBJECT is strongly
normalizing, proved directly on the formation engine's own structure.  The public
`HasTypeDesc.isStronglyNormalizing` (`HasTypeDescStronglyNormalizing.lean`) delegates to it, parallel to
`HasTypeDesc.uniquenessNative`.

## Structure

A formation subject is a variable, a universe code, a conversion of a subject, or a formed cell `mkGen
generator payload children` whose children are the formation telescope's types.  Variables and universe codes
are normal leaves; the `conv` arm preserves the subject; a formed cell steps only by stepping a child, so it is
SN once every child is SN.

* `RawTermChildren.allStronglyNormalizing` — the structural "every child is SN" predicate over a child spine.
* `StepChildrenSuccessor` + `accStepChildrenSuccessor_cons` + `accStepChildrenSuccessor_of_allStronglyNormalizing`
  — the N-child accessibility substrate: an all-SN child spine is `Acc`-essible under the flipped `StepChildren`
  relation (the spine-level analogue of `StepSuccessor` / `IsStronglyNormalizing`, generalizing
  `isStronglyNormalizing_of_twoChildCong` to arbitrary arity).
* `formerCell_isStronglyNormalizing_of_accChildren` — a cell over a congruence-only generator is SN once its
  child spine is accessible (generic over the generator, parameterized by a uniform child-congruence inversion).
* `formerCellStronglyNormalizingOfChildren` — the CASCADE-FREE assembly: a formation former cell with all
  children SN is SN, routed through the GENERIC `former_step_inv` (shared with the formation SR arms — the single
  isolated `typingRuleDescOf_isPiOrSigma` enumeration site) + the accessibility substrate.  No per-former
  `by_cases`: a new ≥1-child formation row extends it with no change here.
* `HasTypeDesc.subjectStronglyNormalizingNative` ⋈ `DescTelescope.childrenStronglyNormalizingNative` — the
  genuine MUTUAL recursion (the `toHasType` shape): the subject recursion bottoms out the `genFormation` arm in
  the telescope recursion, which proves each head child SN by calling the subject recursion (a structural
  sub-derivation).  Equation-`match` form so the mutual recursion is recognised structural.

## Zero-axiom verification

Term-mode mutual recursion + the propext-free leaf-SN endpoints (`isStronglyNormalizing_of_noStep` +
`noStep_var` / `noStep_universeCode`) + the accessibility substrate (`Acc.ndrec` over `StepSuccessor` /
`StepChildrenSuccessor` + clean full-enumeration `cases` over the concrete-index `StepChildren` spine — `here` /
`there`, no partial match) + the generic `former_step_inv` + `simp only` on the structural predicate.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Universe StepStar

/-- **Every child of a child spine is strongly normalizing.**  The structural per-child SN predicate the
formation telescope's SN recursion accumulates, consumed by `formerCellStronglyNormalizingOfChildren`. -/
def RawTermChildren.allStronglyNormalizing {binderShifts : List Nat} {baseScope : Nat} :
    RawTermChildren binderShifts baseScope → Prop
  | .childNil => True
  | .childCons head rest => IsStronglyNormalizing head ∧ rest.allStronglyNormalizing

/-- **Flipped child-spine relation for accessibility.**  `laterChildren` sits below `earlierChildren` when the
earlier spine `StepChildren`-reduces to it — the spine-level analogue of `StepSuccessor`.  A spine is strongly
normalizing exactly when it is `Acc`-essible under this relation. -/
def StepChildrenSuccessor {binderShifts : List Nat} {baseScope : Nat}
    (laterChildren earlierChildren : RawTermChildren binderShifts baseScope) : Prop :=
  StepChildren earlierChildren laterChildren

/-- **A cons spine is accessible when its head is SN and its tail spine is accessible.**  The spine-level twin
of `isStronglyNormalizing_of_twoChildCong`: nested `Acc.ndrec` over the head's `StepSuccessor` accessibility and
the tail's `StepChildrenSuccessor` accessibility, casing a `StepChildren` out of the cons into the head-step
(`here`) and tail-step (`there`) positions. -/
theorem accStepChildrenSuccessor_cons {parentScope headShift : Nat} {restShifts : List Nat}
    {head : RawTerm (parentScope + headShift)}
    {rest : RawTermChildren restShifts parentScope}
    (headTerminates : IsStronglyNormalizing head)
    (restAccessible : Acc StepChildrenSuccessor rest) :
    Acc StepChildrenSuccessor (RawTermChildren.childCons head rest) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentHead =>
      ∀ (currentRest : RawTermChildren restShifts parentScope),
        Acc StepChildrenSuccessor currentRest →
          Acc StepChildrenSuccessor (RawTermChildren.childCons currentHead currentRest))
    (m := fun currentHead _ headIH currentRest currentRestAccessible =>
      Acc.ndrec
        (r := StepChildrenSuccessor)
        (C := fun innerRest =>
          Acc StepChildrenSuccessor (RawTermChildren.childCons currentHead innerRest))
        (m := fun currentInnerRest currentInnerRestPred restIH =>
          Acc.intro (RawTermChildren.childCons currentHead currentInnerRest)
            (fun _predecessor stepRelation => by
              cases stepRelation with
              | here _restSame headStep =>
                  rename_i headAfter
                  exact headIH headAfter headStep currentInnerRest
                    (Acc.intro currentInnerRest currentInnerRestPred)
              | there _headSame restStep =>
                  rename_i innerRestAfter
                  exact restIH innerRestAfter restStep))
        currentRestAccessible)
    headTerminates)
    rest restAccessible

/-- **Every all-SN child spine is accessible under `StepChildrenSuccessor`.**  Structural recursion on the
spine: `childNil` is accessible vacuously (`no_step_at_empty_spine` refutes any entering `StepChildren`), and
`childCons` combines its head's strong normalization with the tail's accessibility via
`accStepChildrenSuccessor_cons`. -/
theorem accStepChildrenSuccessor_of_allStronglyNormalizing
    {binderShifts : List Nat} {baseScope : Nat}
    {children : RawTermChildren binderShifts baseScope}
    (childrenStronglyNormalizing : children.allStronglyNormalizing) :
    Acc StepChildrenSuccessor children :=
  match children with
  | .childNil =>
      Acc.intro RawTermChildren.childNil
        (fun _predecessor stepRelation =>
          (StepChildren.no_step_at_empty_spine stepRelation).elim)
  | .childCons _head _rest => by
      dsimp only [RawTermChildren.allStronglyNormalizing] at childrenStronglyNormalizing
      exact accStepChildrenSuccessor_cons childrenStronglyNormalizing.1
        (accStepChildrenSuccessor_of_allStronglyNormalizing childrenStronglyNormalizing.2)

/-- **A cell over a congruence-only generator is SN once its child spine is accessible.**  Generic over the
generator: the `inversion` hypothesis states that EVERY `Step` out of `mkGen generator payload _` is a child
congruence (a `StepChildren`), so `Acc.ndrec` over the spine accessibility lifts to cell accessibility — the
reduct's SN is exactly the spine IH at the stepped spine.  Consumed by `formerCellStronglyNormalizingOfChildren`
with `inversion := former_step_inv`, replacing the arity-bound per-former dispatch. -/
theorem formerCell_isStronglyNormalizing_of_accChildren {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    (inversion :
      ∀ {currentChildren : RawTermChildren generator.binderShifts scope}
        {target : RawTerm scope},
        Step (RawTerm.mkGen generator payload currentChildren) target →
          ∃ nextChildren, target = RawTerm.mkGen generator payload nextChildren ∧
            StepChildren currentChildren nextChildren)
    {children : RawTermChildren generator.binderShifts scope}
    (childrenAccessible : Acc StepChildrenSuccessor children) :
    IsStronglyNormalizing (RawTerm.mkGen generator payload children) :=
  Acc.ndrec
    (r := StepChildrenSuccessor)
    (C := fun currentChildren =>
      IsStronglyNormalizing (RawTerm.mkGen generator payload currentChildren))
    (m := fun currentChildren _ childrenIH =>
      Acc.intro (RawTerm.mkGen generator payload currentChildren)
        (fun _target cellStep => by
          obtain ⟨nextChildren, targetEq, stepChildren⟩ := inversion cellStep
          rw [targetEq]
          exact childrenIH nextChildren stepChildren))
    childrenAccessible

end FX1Poly.Core

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- **A formation former cell with all children strongly normalizing is strongly normalizing.**  CASCADE-FREE
generic assembly: a formation generator (`typingRuleDescOf generator = some rule`) heads no root redex
(`former_step_inv`), so every Step out of the cell is a child congruence; the cell is therefore SN once its
child spine is accessible, which all-children-SN supplies via `accStepChildrenSuccessor_of_allStronglyNormalizing`.
This routes through the GENERIC `former_step_inv` (the single isolated `typingRuleDescOf_isPiOrSigma` enumeration
site, shared with the formation SR arms) rather than re-casing the formation table here — so a new ≥1-child
formation row (a data type code) extends it with no change to this proof, exactly mirroring the cascade-free
formation `subjectReduction` / `subjectAdmitsNoStep`. -/
theorem formerCellStronglyNormalizingOfChildren {scope : Nat} {generator : Generator}
    {rule : TypingRuleDesc}
    {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope}
    (isFormation : typingRuleDescOf generator = some rule)
    (childrenSN : children.allStronglyNormalizing) :
    IsStronglyNormalizing (RawTerm.mkGen generator payload children) :=
  formerCell_isStronglyNormalizing_of_accChildren
    (fun cellStep => former_step_inv isFormation cellStep)
    (accStepChildrenSuccessor_of_allStronglyNormalizing childrenSN)

mutual

/-- **Native subject strong normalization for the description formation engine.**  Every
formation-typed subject is strongly normalizing, proved on the formation engine's own structure:
`var` / `universeFormation` are normal leaves; `conv` preserves the subject; the
`genFormation` former cell is SN once its telescope children are SN, discharged by
`formerCellStronglyNormalizingOfChildren` over the mutual telescope recursion.  The public
`HasTypeDesc.isStronglyNormalizing` delegates to it. -/
theorem HasTypeDesc.subjectStronglyNormalizingNative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasTypeDesc profile context subject classifier) :
    IsStronglyNormalizing subject :=
  match typed with
  | .var _context index =>
      isStronglyNormalizing_of_noStep (fun _ step => noStep_var index step)
  | .conv _levelExpr _flag typedPremise _converts _reclassifierTyped =>
      HasTypeDesc.subjectStronglyNormalizingNative typedPremise
  | .universeFormation _context levelExpr flag =>
      isStronglyNormalizing_of_noStep (fun _ step => noStep_universeCode (levelExpr, flag) step)
  | .genFormation _context _generator _payload _children _levels _flag _rule isFormation premises =>
      formerCellStronglyNormalizingOfChildren isFormation
        (DescTelescope.childrenStronglyNormalizingNative premises)

/-- Every child of a formation telescope is strongly normalizing.  STANDALONE-shaped recursion on the
telescope but MUTUAL with the subject recursion: each head child's SN is `HasTypeDesc.subjectStronglyNormalizingNative`
of the head typing (a structural sub-derivation), and the rest accumulates recursively. -/
theorem DescTelescope.childrenStronglyNormalizingNative {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile context levels flag children) :
    children.allStronglyNormalizing :=
  match telescope with
  | .nil _ _ => True.intro
  | .cons _ _head _headLevel _restLevels _flag _rest headTyped restTyped =>
      ⟨HasTypeDesc.subjectStronglyNormalizingNative headTyped,
        DescTelescope.childrenStronglyNormalizingNative restTyped⟩

end

end FX1Poly.Typed
