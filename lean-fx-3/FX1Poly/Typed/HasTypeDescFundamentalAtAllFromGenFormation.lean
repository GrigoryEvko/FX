import FX1Poly.Typed.FundamentalAtAllLeafArms
import FX1Poly.Typed.FundamentalAtAllVectorPremises
import FX1Poly.Typed.FundamentalAtAllFormerChildren

/-! # FX1Poly/Typed/HasTypeDescFundamentalAtAllFromGenFormation
    — the all-level formation-engine fundamental theorem, with the three non-former arms discharged.

The dependent SN chain (`HasTypeDescPiFundamentalVectorFromFormation.lean`) is committed and gated
CONDITIONAL on the formation engine `HasTypeDesc` satisfying the fundamental theorem.  `HasTypeDesc` has four
term constructors — `var`, `conv`, `universeFormation`, `genFormation`.  Over the ALL-LEVEL closing
environment (`ReducibleEnvAtAllLevels`) the first three are unconditional: `var` is off-by-one-free precisely
because the all-level environment supplies every variable's reducibility at every level (the resolution of the
vector-shape `var` wall, where `var`'s level is env-fixed — see `fundamentalVarAtVectorMatchingLevel`).

This file discharges those three arms by the kernel mutual recursor and factors the `genFormation` former arm
as an explicit hypothesis — exactly the factoring methodology the committed `fundamentalVectorFromFormation`
uses for the whole formation engine.  The net reduction: proving the formation FT (and hence
unconditionalizing SN) now reduces from "all four `HasTypeDesc` arms" to "the `genFormation` former arm
alone."  The remaining obligation is the genuinely-recursive one: a former cell's reducibility from its
premise telescope's binder-threaded reducibility (the codomain-under-argument premise that
`FundamentalAtAllFormerChildren` / `FundamentalAtAllPositiveArguments` factor as "the recursive
binder/telescope obligation").

* `HasTypeDesc.fundamentalAtAllFromGenFormation` — `var`/`conv`/`universeFormation` proven over the all-level
  environment via the committed leaf arms; `genFormation` is the explicit premise.

## Zero-axiom verification

One `HasTypeDesc.rec` application.  `var` = `fundamentalVarAtAll`; `conv` = `fundamentalConvAtAll` on the two
sub-IHs; `universeFormation` = `fundamentalUniverseFormationAtAll`; `genFormation` = the explicit premise; the
telescope motive is `True` (the flat former premise does not consume the telescope IH).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **All-level formation fundamental theorem, modulo the `genFormation` former arm.**  Over the all-level
environment, `var` / `conv` / `universeFormation` are discharged unconditionally (the all-level environment
makes `var` off-by-one-free); the former arm is the explicit `genFormationFundamental` premise.  Reduces the
formation-engine FT to the single recursive former obligation. -/
theorem HasTypeDesc.fundamentalAtAllFromGenFormation {profile : PolyProfile}
    (genFormationFundamental :
      ∀ {scope : Nat} (context : TypingContext profile scope)
        (generator : Generator) (payload : generator.payload scope)
        (children : RawTermChildren generator.binderShifts scope)
        (levels : List LevelExpr) (flag : UniverseFlag) (rule : TypingRuleDesc),
        typingRuleDescOf generator = some rule →
        DescTelescope profile (currentDepth := 0) context levels flag children →
          FundamentalConclusionAtAll context (.mkGen generator payload children)
            (rule.outputType scope levels flag))
    {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDesc profile context subject classifier) :
    FundamentalConclusionAtAll context subject classifier := by
  refine HasTypeDesc.rec
    (motive_1 := fun context subject classifier _typed =>
      FundamentalConclusionAtAll context subject classifier)
    (motive_2 := fun _context _levels _flag _children _telescope => True)
    ?var ?conv ?universeFormation ?genFormation ?nilTelescope ?consTelescope typed
  · -- var: off-by-one-free over the all-level environment
    intro _scope context index
    exact fundamentalVarAtAll context index
  · -- conv: cast the subject IH across the conversion using the reclassifier IH
    intro _scope _context _subject _classifier _reclassifier _levelExpr _flag _typed converts
      _reclassifierTyped subjectIH reclassifierIH
    exact fundamentalConvAtAll subjectIH reclassifierIH converts
  · -- universeFormation: Type@e is a member of Type@(lsucc e)
    intro _scope context levelExpr flag
    exact fundamentalUniverseFormationAtAll context levelExpr flag
  · -- genFormation: the factored recursive former obligation
    intro _scope context generator payload children levels flag rule isFormation premises _premisesIH
    exact genFormationFundamental context generator payload children levels flag rule isFormation premises
  · -- DescTelescope.nil (telescope motive is `True`)
    intro _baseScope _currentDepth _context _flag
    exact True.intro
  · -- DescTelescope.cons (telescope motive is `True`)
    intro _baseScope _currentDepth _restShifts _context _head _headLevel _restLevels _flag _rest
      _headTyped _restTyped _headIH _restIH
    exact True.intro

end FX1Poly.Typed
