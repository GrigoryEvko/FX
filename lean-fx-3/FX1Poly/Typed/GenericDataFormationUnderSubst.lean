import FX1Poly.Typed.ReducibleSemanticRules
import FX1Poly.Typed.HasTypeDescSubjectStronglyNormalizing

/-! # FX1Poly/Typed/GenericDataFormationUnderSubst
   — the SYMBOLIC-generator non-Pi formation membership arm (GTL-06 kernel, brick 3 headline)

The six reducibility dispatch files each carry a five-deep `by_cases` chain enumerating the
formation rows (Pi, Sigma, list, option, unit) because the universe-membership assembly was
only ever stated at LITERAL generators (`sigmaFormationUnderSubst` and its clones).  Every
ingredient of that assembly is already table-generic — `formationGenerator_noWeakHeadStep`
names no former, `formerCellStronglyNormalizingOfChildren` is generator-symbolic, and
`dataFormerInUniverse` excludes only Pi and universe roots.  This module states the assembly
itself at a SYMBOLIC generator, eliminating the per-row enumeration from the membership half:

  * `formationRowIsNotVariable` / `formationRowIsNotUniverse` — cascade-free table-miss
    discriminations: at the literal `gen_var` / `gen_universeCode` the rule table reduces
    DEFINITIONALLY to `none`, contradicting the row hypothesis.  No row is named, so a new
    formation row is absorbed zero-touch (the same defeq-`show` mechanism
    `formationGenerator_noWeakHeadStep` uses for redex heads).
  * `IsReducibleMemberAt.dataFormationUnderSubst` — the headline: for ANY generator carrying a
    formation row other than Pi, the substituted former cell is a reducible member of any
    universe, given only strong normalization of its substituted children.  The substitution
    distributes by `subst_nonVar_reduces` (the generator is not the variable, by table-miss);
    SN of the whole cell is the TG-6 accessibility assembly; weak-head normality and the two
    root discriminations are the generic facts above.

With this arm, a dispatch file needs ONE `by_cases` (Pi — the sole former classified by the
genuine arrow candidate rather than the strong-normalization candidate) and ONE generic call;
the Sigma/list/option/unit chains collapse.  The remaining brick (recorded in the tracker
metadata) is the arity-dispatch child-SN supplier — extracting the substituted-children
strong normalization from `TelescopeReducible` at a symbolic generator via the shape equation
cast, which feeds this lemma's `substitutedChildrenNormalizing` hypothesis at every call site.

## Zero-axiom verification

The discriminations are defeq `show`s; the headline is `rw` along two shipped equations plus
one application of `dataFormerInUniverse` over three shipped generic facts.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTypedReducibilityCandidates.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **A formation row is never the variable** — cascade-free table-miss discrimination: at the
literal `gen_var` the rule table reduces definitionally to `none`. -/
theorem formationRowIsNotVariable {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule) : generator ≠ .gen_var := by
  intro isVariable
  subst isVariable
  exact nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)

/-- **A formation row is never the universe** — the same defeq table-miss discrimination at the
literal `gen_universeCode` (the universe is typed by the `universeFormation` arm, not by a
table row; this is the no-Type-in-Type discipline surfacing in the table). -/
theorem formationRowIsNotUniverse {generator : Generator} {rule : TypingRuleDesc}
    (isFormation : typingRuleDescOf generator = some rule) :
    generator ≠ .gen_universeCode := by
  intro isUniverse
  subst isUniverse
  exact nomatch (show (none : Option TypingRuleDesc) = some rule from isFormation)

/-- **Semantic non-Pi formation under a closing substitution, at a SYMBOLIC generator** — the
table-generic membership arm.  Any former carrying a formation row other than Pi is, under a
closing substitution, a reducible member of any universe, given strong normalization of its
substituted children: the substitution distributes over the cell (`subst_nonVar_reduces`; the
generator is not the variable by table-miss), the substituted cell is strongly normalizing
(the generic N-child accessibility assembly), weak-head normal (the generic redex-head
discrimination), and root-distinct from Pi (hypothesis) and the universe (table-miss).  The
symbolic-generator generalization of `sigmaFormationUnderSubst` — one arm for the whole
non-Pi formation family, absorbing every future data-former row with zero new lines. -/
theorem IsReducibleMemberAt.dataFormationUnderSubst {scope targetScope : Nat} {predLevel : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope} {rule : TypingRuleDesc}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (substitution : RawTermSubst scope targetScope)
    (isFormation : typingRuleDescOf generator = some rule)
    (isNotPiFormer : generator ≠ .gen_piTyCode)
    (substitutedChildrenNormalizing :
      (foldChildren GenAlgebra.canonical substitution children).allStronglyNormalizing) :
    IsReducibleMemberAt (predLevel + 1)
      (RawTerm.subst substitution (universeCodeCell levelExpr flag))
      (RawTerm.subst substitution (.mkGen generator payload children)) := by
  rw [subst_universeCodeCell,
    RawTerm.subst_nonVar_reduces substitution (formationRowIsNotVariable isFormation)
      payload children]
  exact IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (formerCellStronglyNormalizingOfChildren isFormation substitutedChildrenNormalizing)
    (formationGenerator_noWeakHeadStep isFormation)
    isNotPiFormer
    (formationRowIsNotUniverse isFormation)

/-- **Non-vacuity smoke: the nullary unit row through the generic arm.**  The unit former's
substituted spine is the empty spine, so its all-SN obligation is trivial and the generic arm
yields the membership the bespoke unit branch currently produces — the drop-in shape for the
dispatch-file refit. -/
theorem unitFormationUnderSubstViaGenericArm {scope targetScope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (substitution : RawTermSubst scope targetScope) :
    IsReducibleMemberAt (predLevel + 1)
      (RawTerm.subst substitution (universeCodeCell levelExpr flag))
      (RawTerm.subst substitution (.mkGen .gen_unitCode () .childNil)) :=
  IsReducibleMemberAt.dataFormationUnderSubst levelExpr flag substitution
    typingRuleDescOf_unitCode (fun piEq => nomatch piEq) True.intro

end FX1Poly.Typed
