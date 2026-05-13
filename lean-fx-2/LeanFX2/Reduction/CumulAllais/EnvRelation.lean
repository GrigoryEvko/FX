import LeanFX2.Reduction.CumulCastElim

/-! # LeanFX2.Reduction.CumulAllais.EnvRelation

Allais et al. ICFP'18 paired-environment predicate
`TermSubstHet.PointwiseCompat`.  Two `TermSubstHet`s at the same
`SubstHet` are POINTWISE COMPAT when their per-position substituents
are `ConvCumul`-related.  Direct FX instance of Allais's
`All 𝓥ᴿ Γ ρᴬ ρᴮ` for `𝓥ᴿ = ConvCumul`.

Ships the predicate plus its `refl` / `sym` / `trans` combinators.

Reference: arxiv:1804.00119 §5 (Simulation framework), record
`Simulation`.  FX memory `reference_pattern_allais_simulation`.

## Root status

Layer 3 cumulativity-via-Allais helper. -/

namespace LeanFX2

/-- **Allais paired-env predicate.**  Two `TermSubstHet`s at the
same `SubstHet` are POINTWISE COMPAT when their per-position
substituents are `ConvCumul`-related.  Direct FX instance of
Allais's `All 𝓥ᴿ Γ ρᴬ ρᴮ` for `𝓥ᴿ = ConvCumul`. -/
def TermSubstHet.PointwiseCompat
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma) :
    Prop :=
  ∀ position, ConvCumul (termSubstA position) (termSubstB position)

/-- Reflexivity of pointwise compat: any TermSubstHet is compat with itself. -/
theorem TermSubstHet.PointwiseCompat.refl
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubst : TermSubstHet sourceCtx targetCtx sigma) :
    TermSubstHet.PointwiseCompat termSubst termSubst :=
  fun position => ConvCumul.refl (termSubst position)

/-- Symmetry of pointwise compat. -/
theorem TermSubstHet.PointwiseCompat.sym
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (compat : TermSubstHet.PointwiseCompat termSubstA termSubstB) :
    TermSubstHet.PointwiseCompat termSubstB termSubstA :=
  fun position => ConvCumul.sym (compat position)

/-- Transitivity of pointwise compat. -/
theorem TermSubstHet.PointwiseCompat.trans
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB termSubstC : TermSubstHet sourceCtx targetCtx sigma}
    (compatAB : TermSubstHet.PointwiseCompat termSubstA termSubstB)
    (compatBC : TermSubstHet.PointwiseCompat termSubstB termSubstC) :
    TermSubstHet.PointwiseCompat termSubstA termSubstC :=
  fun position => ConvCumul.trans (compatAB position) (compatBC position)

end LeanFX2
