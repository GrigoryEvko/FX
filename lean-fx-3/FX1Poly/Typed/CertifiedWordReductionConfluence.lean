import FX1Poly.Core.StepWordRewriteSoundness
import FX1Poly.Core.StepStarConfluence
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional

/-! # FX1Poly/Typed/CertifiedWordReductionConfluence — Leg-3 word-rewrite confluence on the certified fragment (SN-132)

Companion to `CertifiedWordReductionTermination.lean` (SN-131).  Leg-3 needs both legs of convergence —
termination (SN-131) AND confluence — on the certified fragment (words that are `RawTerm.toCode`-images of
typed-term reductions).  As with termination, the FULL word system is the wrong target: word-level local
confluence of arbitrary `fxStepSystem` rewriting is a STRING-rewriting critical-pair question (overlaps of
rule left-hand-side words under concatenation), a different and harder object than the term redex analysis,
and the full system is not even terminating (SN-131's `untypedWordReductionDiverges`).  The honest, Leg-3-
relevant confluence is the CERTIFIED-IMAGE reflection: term-layer confluence (the shipped `cd_lemma` /
`StepStar` Newman) lifted through `toWordRewrites` — exactly what the roadmap's "reuse the term-layer
cd_lemma" signals.

  * **`certifiedWordLocalConfluence`** — LOCAL confluence (the literal SN-132 ask): two single `Step`s from a
    common term have `toCode`-images that JOIN as `fxStepSystem` word reductions.  Routes the term `cd_lemma`
    local join (`StepStar.localJoin_of_cdLemma`) through `StepStar.toWordRewrites` on both legs.  No SN needed
    — pure `cd_lemma` reuse.
  * **`certifiedWordConfluence`** — the GLOBAL upgrade on the certified fragment: two `StepStar` reductions
    from a WELL-TYPED root have `toCode`-images that join.  Combines the SN-131 ingredient (typed SN, SN-043 /
    `stronglyNormalizingOfWfContextDesc`) with the term-layer Newman global confluence
    (`StepStar.confluence_of_localJoin_and_accessible`, which consumes `IsStronglyNormalizing` of the source),
    lifted through `toWordRewrites`.  This is Leg-3's convergence reflected to the word layer: on the certified
    fragment the `fxStepSystem` is terminating (SN-131) AND confluent (here), the two ingredients Newman
    assembles at the term layer.

## Zero-axiom

Both are `obtain` on the shipped term-layer join (`localJoin_of_cdLemma` / `confluence_of_localJoin_and_
accessible`) followed by `StepStar.toWordRewrites` on each leg of the resulting `StepStar.Join`; the global
one feeds `stronglyNormalizingOfWfContextDesc` (SN-043) as the accessibility witness.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **Local confluence on the certified image.**  Two single `Step`s out of a common term have `toCode`-images
that JOIN as `fxStepSystem` word reductions: the term `cd_lemma` local join (`StepStar.localJoin_of_cdLemma`)
mapped through `StepStar.toWordRewrites` on both legs.  The Leg-3 LOCAL confluence — reflected from the term
layer, NOT a string-rewriting critical-pair analysis of the full word system. -/
theorem certifiedWordLocalConfluence {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (leftStep : Step sourceTerm leftReduct)
    (rightStep : Step sourceTerm rightReduct) :
    ∃ joinTerm : RawTerm scope,
      FxWordRewritesMany fxStepSystem leftReduct.toCode joinTerm.toCode ∧
      FxWordRewritesMany fxStepSystem rightReduct.toCode joinTerm.toCode := by
  obtain ⟨joinTerm, leftStar, rightStar⟩ := StepStar.localJoin_of_cdLemma leftStep rightStep
  exact ⟨joinTerm, leftStar.toWordRewrites, rightStar.toWordRewrites⟩

/-- ★ **Global confluence on the certified fragment.**  Two `StepStar` reductions out of a WELL-TYPED root
have `toCode`-images that JOIN as `fxStepSystem` word reductions.  Combines the SN-131 ingredient — typed SN
(`stronglyNormalizingOfWfContextDesc`, SN-043) as the accessibility witness — with the term-layer Newman
confluence (`StepStar.confluence_of_localJoin_and_accessible`), lifted through `StepStar.toWordRewrites`.  On
the certified fragment the `fxStepSystem` is therefore terminating (SN-131) AND confluent: the two ingredients
the Newman theorem assembles into convergence, reflected to the word layer.  Needs the ROOT typed only — the
intermediate reducts need not stay typed (GrownCtxConv-5-free, exactly as in SN-131). -/
theorem certifiedWordConfluence {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {rootTerm rootType : RawTerm scope}
    {leftReduct rightReduct : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context rootTerm rootType)
    (leftChain : StepStar rootTerm leftReduct)
    (rightChain : StepStar rootTerm rightReduct) :
    ∃ joinTerm : RawTerm scope,
      FxWordRewritesMany fxStepSystem leftReduct.toCode joinTerm.toCode ∧
      FxWordRewritesMany fxStepSystem rightReduct.toCode joinTerm.toCode := by
  obtain ⟨joinTerm, leftStar, rightStar⟩ :=
    StepStar.confluence_of_localJoin_and_accessible
      (HasTypeDescPi.stronglyNormalizingOfWfContextDesc contextWellFormed typed)
      leftChain rightChain
  exact ⟨joinTerm, leftStar.toWordRewrites, rightStar.toWordRewrites⟩

end FX1Poly.Typed
