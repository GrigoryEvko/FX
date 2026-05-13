import LeanFX2.Reduction.CumulAllais.MultiSubtermArms

/-! # LeanFX2.Reduction.CumulAllais.CumulPromotionArms

Allais arms for the cumulativity-promotion ctor + the two binder
ctors:

* `cumulUp`: lifts via `cumulUpCong` over level promotion; the
  substituted typeCode-pair on each side gives `ConvCumul`.
* `lam` / `lamPi`: binder Term constructors close the per-ctor
  Allais catalogue.  Each takes a body-level inner ConvCumul
  (typically produced by a recursive call on the body under a
  lifted `TermSubstHet`) and applies the matching `lamCong` /
  `lamPiCong` rule, peeling `Ty.weaken_substHet_commute` casts via
  `cast_eq_both_benton` where needed.

## Root status

Layer 3 cumulativity-via-Allais helper. -/

namespace LeanFX2

/-! ### Allais cumul-promotion arm

The `cumulUp` ctor's `Term.substHet` arm preserves `lowerTerm`
verbatim (its `scopeLow` is decoupled from outer `scope`).  Both
substituted sides produce literally the same Term value →
`ConvCumul.refl _`.

This mirrors the existing `ConvCumul.subst_compatible_cumulUp_term`
in `Reduction/Cumul.lean` (line ~1289) but takes the source ctor
fields directly rather than via specialized signature. -/

/-- Allais arm for `cumulUp` — Phase CUMUL-2.6 Design D.
The substituted typeCode-pair on each side gives ConvCumul; wrap via
cumulUpCong to lift over the cumul-promotion. -/
theorem ConvCumul.subst_compatible_cumulUp_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma)
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ sourceLevel)
    (levelLeHigh : higherLevel.toNat + 1 ≤ sourceLevel)
    {codeRaw : RawTerm sourceScope}
    (typeCode :
      Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw)
    (innerCompat :
      ConvCumul (typeCode.substHet termSubstA) (typeCode.substHet termSubstB)) :
    ConvCumul ((Term.cumulUp (context := sourceCtx)
                             lowerLevel higherLevel cumulMonotone
                             levelLeLow levelLeHigh typeCode).substHet termSubstA)
              ((Term.cumulUp (context := sourceCtx)
                             lowerLevel higherLevel cumulMonotone
                             levelLeLow levelLeHigh typeCode).substHet termSubstB) :=
  ConvCumul.cumulUpCong lowerLevel higherLevel cumulMonotone
                        (Nat.le_trans levelLeLow sigma.cumulOk)
                        (Nat.le_trans levelLeHigh sigma.cumulOk)
                        innerCompat

/-! ## Allais kernel-gap note: missing eliminator cong rules

The current `ConvCumul` inductive (`Reduction/Cumul.lean`) ships
cong rules for the data ctors above but DOES NOT ship cong rules
for the five eliminator ctors:
* `natElim` (3-subterm: scrutinee, zero branch, succ branch)
* `natRec`  (3-subterm: same shape as natElim)
* `listElim` (3-subterm: scrutinee, nil branch, cons branch)
* `optionMatch` (3-subterm: scrutinee, none branch, some branch)
* `eitherMatch` (3-subterm: scrutinee, left branch, right branch)

Without these cong rules, the Allais-style structural recursion on
the source Term cannot construct the substituted ConvCumul for
these five ctors.  Pre-existing kernel gap; documented as future
follow-up.  Tracked separately as a kernel extension task — adding
five cong rules to `ConvCumul` and an Allais arm for each follows
the same shape as `boolElimCong` / `subst_compatible_boolElim_allais`
above.

The remaining 25 ctors (var + unit + arrow + sigma + bool +
nat-data-without-eliminators + list-data-without-eliminator +
option-data-without-eliminator + either-data-without-eliminator +
identity-types + modal + universe + cumul-promotion) ARE covered
by the per-ctor Allais arms shipped above, contingent on the
binder lift (lam, lamPi) which awaits the Benton rename theorem
in the next section. -/

/-! # Allais binder arms (Step C — lam + lamPi)

The two binder Term constructors close the per-ctor Allais
catalogue.  Each takes a body-level inner ConvCumul (typically
produced by a recursive call on the body under a lifted
TermSubstHet) and applies the matching `lamCong` / `lamPiCong`
rule, peeling `Term.substHet`'s `Ty.weaken_substHet_commute` cast
via `cast_eq_both_benton` where needed.

The user is responsible for constructing the inner compat for
the lifted TermSubstHets — that's the standard Allais
`Simulation.alg` discharge pattern (arxiv:1804.00119 §5.1).  The
kernel does not auto-generate `PointwiseCompat.lift` because
weakening preserves heterogeneous-source-ctx ConvCumul requires
`induction cumulRel` (the Lean 4.29.1 wall described above) for
the general case.  For homogeneous compat (compat = refl), the
lifted compat is trivially refl.
-/

/-- Allais arm for `lam`: binder cong via `lamCong`.

`Term.substHet`'s `lam` arm wraps the body in
`Ty.weaken_substHet_commute ▸ ·` — same cast on both sides (same
sigma), peeled via `cast_eq_both_benton`. -/
theorem ConvCumul.subst_compatible_lam_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {domainType codomainType : Ty sourceLevel sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw)
    (innerCompat :
      ConvCumul (body.substHet (termSubstA.lift domainType))
                (body.substHet (termSubstB.lift domainType))) :
    ConvCumul ((Term.lam body).substHet termSubstA)
              ((Term.lam body).substHet termSubstB) :=
  ConvCumul.lamCong (ConvCumul.cast_eq_both_benton _ innerCompat)

/-- Allais arm for `lamPi`: binder cong via `lamPiCong`.

`Term.substHet`'s `lamPi` arm has NO cast (body type is just
codomainType in extended scope) — direct cong application. -/
theorem ConvCumul.subst_compatible_lamPi_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    {domainType : Ty sourceLevel sourceScope}
    {codomainType : Ty sourceLevel (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons domainType) codomainType bodyRaw)
    (innerCompat :
      ConvCumul (body.substHet (termSubstA.lift domainType))
                (body.substHet (termSubstB.lift domainType))) :
    ConvCumul ((Term.lamPi body).substHet termSubstA)
              ((Term.lamPi body).substHet termSubstB) :=
  ConvCumul.lamPiCong innerCompat

end LeanFX2
