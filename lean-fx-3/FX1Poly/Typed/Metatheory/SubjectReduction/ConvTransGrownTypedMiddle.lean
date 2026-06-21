import FX1Poly.Typed.Corpus.Smoke.OpenStronglyNormalizingUnconditional
import FX1Poly.Core.Rewriting.Confluence.StepStarConfluence

/-! # ConvTransGrownTypedMiddle — `Conv` transitivity through a grown-typeable middle term

The native single-step subject-reduction (the residual of the TYTAB-2-FT consistency route, #1697) hits a
`Conv.trans` wall in its conversion arm: composing two conversion chains that share a middle classifier needs
Church-Rosser for the chains LEAVING that middle, and the only UNCONDITIONAL Conv-transitivity closers are
`Conv.trans_of_confluence`/`Conv.trans_of_strongNormalization`, both of which demand the GLOBAL
`StepStar.HasStrongNormalization` — false for raw terms (the `gen_natRec`/`gen_fixedPoint` partial-class
diverge).  The per-middle closer `Conv.trans_of_middle_accessible` needs only `IsStronglyNormalizing middle`,
and the grown engine already proves exactly that for any grown-typeable middle in a well-formed context
(`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`, the unconditional open-term SN capstone).

This file composes the two into the wall closer: **`Conv` is transitive through any middle term that types in
the grown engine over a well-formed context.**  Since every classifier the typed layer reasons about is
grown-typeable at a universe code, this is the conversion-arm `Conv.trans` the native SR consumes —
unconditionally and zero-axiom, with NO appeal to the (false) global strong-normalization hypothesis. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **★ `Conv` transitivity through a grown-typeable middle.**  When the shared middle term of two conversion
chains types in the grown engine `HasTypeDescPi` over a well-formed context, it is strongly normalizing
(`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`), so the source-local Newman bridge
`Conv.trans_of_middle_accessible` composes the chains — WITHOUT the global `HasStrongNormalization` witness the
unconditional closers demand.  This is the conversion-arm closer for the native single-step subject reduction:
the SR conv arm carries `Conv classifier reclassifier` with `reclassifier` typed at a universe code, so its
chains always pass through a grown-typeable middle. -/
theorem Conv.trans_of_grownTypedMiddle {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {firstTerm middleTerm lastTerm classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (middleTyped : HasTypeDescPi profile context middleTerm classifier)
    (firstMiddle : Conv firstTerm middleTerm)
    (middleLast : Conv middleTerm lastTerm) :
    Conv firstTerm lastTerm :=
  Conv.trans_of_middle_accessible
    (HasTypeDescPi.stronglyNormalizingOfWfContextDesc contextWellFormed middleTyped)
    firstMiddle middleLast

end FX1Poly.Typed
